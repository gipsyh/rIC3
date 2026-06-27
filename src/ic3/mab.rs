//! Contextual multi-armed bandit (PA-LinUCB) for adaptive inductive
//! generalization strategy selection (A-IC3).
//!
//! Before each generalization, a proof-aware context vector is extracted from
//! the IC3 state and a LinUCB agent selects among generalization strategies
//! (arms) of varying aggressiveness. After generalization and the intermediate
//! push, the agent receives a reward combining size reduction, push quality,
//! and bonus events, and updates its linear model online.

use crate::ic3::{
    IC3,
    mic::{DropVarParameter, MicType},
    proofoblig::ProofObligation,
};
use log::{debug, warn};
use nalgebra::{DMatrix, DVector};

/// Dimension of the proof-aware context vector (6 features + bias).
const CONTEXT_DIM: usize = 7;

/// Dynamic (activity-aware) arms.
const BALANCED_ARM: usize = 0;
const AGGRESSIVE_ARM: usize = 1;
const CONSERVATIVE_ARM: usize = 2;
const NUM_DYNAMIC_ARMS: usize = 3;

/// Static arms: fixed (limit, max, level) configurations of DropVarParameter.
const FIXED_ARM_CONFIGS: [(usize, usize, usize); 4] = [
    (0, 0, 0), // basic: no CTG
    (1, 3, 1), // conservative CTG
    (2, 5, 1), // balanced CTG
    (8, 4, 1), // aggressive deep CTG
];

const NUM_ARMS: usize = NUM_DYNAMIC_ARMS + FIXED_ARM_CONFIGS.len();

pub struct CtxMab {
    alpha: f64,
    lambda: f64,
    a: Vec<DMatrix<f64>>,
    a_inv: Vec<DMatrix<f64>>,
    b: Vec<DVector<f64>>,
    theta: Vec<DVector<f64>>,
    arm_pulls: Vec<usize>,
    avg_cube_size: f64,
    cube_size_count: usize,
    /// arm chosen for the generalization currently in flight
    pending: Option<usize>,
}

impl CtxMab {
    pub fn new(alpha: f64, lambda: f64) -> Self {
        Self {
            alpha,
            lambda,
            a: vec![DMatrix::identity(CONTEXT_DIM, CONTEXT_DIM); NUM_ARMS],
            a_inv: vec![DMatrix::identity(CONTEXT_DIM, CONTEXT_DIM); NUM_ARMS],
            b: vec![DVector::zeros(CONTEXT_DIM); NUM_ARMS],
            theta: vec![DVector::zeros(CONTEXT_DIM); NUM_ARMS],
            arm_pulls: vec![0; NUM_ARMS],
            avg_cube_size: 0.0,
            cube_size_count: 0,
            pending: None,
        }
    }

    /// LinUCB arm selection: argmax of theta^T x + alpha * sqrt(x^T A^-1 x).
    fn select(&mut self, ctx: &DVector<f64>) -> usize {
        let mut best_arm = 0;
        let mut best_score = f64::NEG_INFINITY;
        for arm in 0..NUM_ARMS {
            let predicted = self.theta[arm].dot(ctx);
            let uncertainty = (ctx.transpose() * &self.a_inv[arm] * ctx)[(0, 0)];
            let score = predicted + self.alpha * uncertainty.max(0.0).sqrt();
            if score > best_score {
                best_score = score;
                best_arm = arm;
            }
        }
        self.arm_pulls[best_arm] += 1;
        best_arm
    }

    /// LinUCB update: A += x x^T, b += r x, theta = (A + lambda I)^-1 b.
    fn update(&mut self, arm: usize, ctx: &DVector<f64>, reward: f64) {
        self.a[arm] += ctx * ctx.transpose();
        self.b[arm] += ctx * reward;
        let regularized = &self.a[arm] + DMatrix::identity(CONTEXT_DIM, CONTEXT_DIM) * self.lambda;
        if let Some(inv) = regularized.try_inverse() {
            self.theta[arm] = &inv * &self.b[arm];
            self.a_inv[arm] = inv;
        } else {
            warn!("MAB: matrix A for arm {arm} became non-invertible, resetting arm");
            self.a[arm] = DMatrix::identity(CONTEXT_DIM, CONTEXT_DIM);
            self.a_inv[arm] = DMatrix::identity(CONTEXT_DIM, CONTEXT_DIM);
            self.b[arm] = DVector::zeros(CONTEXT_DIM);
            self.theta[arm] = DVector::zeros(CONTEXT_DIM);
        }
    }

    pub fn statistic(&self) -> String {
        format!("MAB arm pulls: {:?}", self.arm_pulls)
    }
}

/// Max activity along the successor chain of the po (up to 3 hops), used by
/// the dynamic arms to gauge the difficulty of blocking the current CTI.
pub(super) fn branch_act(po: &ProofObligation) -> Option<f64> {
    let mut n = po.next.as_ref()?;
    let mut act = n.act;
    for _ in 0..2 {
        if let Some(nn) = n.next.as_ref() {
            n = nn;
            act = act.max(n.act);
        } else {
            break;
        }
    }
    Some(act)
}

/// Balanced dynamic arm: the original DynAMic activity mapping.
fn balanced_params(po: &ProofObligation) -> DropVarParameter {
    let Some(act) = branch_act(po) else {
        return DropVarParameter::default();
    };
    match act {
        40.0.. => {
            let limit = ((act - 40.0).powf(0.3) * 2.0 + 5.0).round() as usize;
            DropVarParameter::new(limit, 5, 1)
        }
        10.0..40.0 => {
            let max = (act - 10.0) as usize / 10 + 2;
            DropVarParameter::new(1, max, 1)
        }
        _ => DropVarParameter::new(0, 0, 0),
    }
}

/// Aggressive dynamic arm: lower thresholds, stronger generalization effort.
fn aggressive_params(po: &ProofObligation) -> DropVarParameter {
    let Some(act) = branch_act(po) else {
        return DropVarParameter::new(1, 1, 1);
    };
    match act {
        25.0.. => {
            let limit = ((act - 25.0).powf(0.3) * 2.5 + 6.0).round() as usize;
            DropVarParameter::new(limit, 6, 1)
        }
        5.0..25.0 => {
            let max = (act - 5.0) as usize / 8 + 3;
            DropVarParameter::new(2, max, 1)
        }
        _ => DropVarParameter::new(1, 1, 1),
    }
}

/// Conservative dynamic arm: higher thresholds, capped generalization effort.
fn conservative_params(po: &ProofObligation) -> DropVarParameter {
    let Some(act) = branch_act(po) else {
        return DropVarParameter::default();
    };
    match act {
        50.0.. => {
            let limit = (((act - 50.0).powf(0.3) * 1.5 + 4.0).round() as usize).min(6);
            DropVarParameter::new(limit, 3, 1)
        }
        15.0..50.0 => {
            let max = ((act - 15.0) as usize / 12 + 1).min(3);
            DropVarParameter::new(1, max, 0)
        }
        _ => DropVarParameter::new(0, 0, 0),
    }
}

impl IC3 {
    /// Proof-aware context vector: [relative level, relative cube size,
    /// push potential, relative depth, frame saturation, activity, bias].
    /// Also maintains the running average cube size used for normalization.
    fn mab_context_vector(&mut self, po: &ProofObligation) -> DVector<f64> {
        let relative_level = po.frame as f64 / self.level() as f64;
        let mab = &mut self.mab;
        let total_cube_size = mab.cube_size_count as f64 * mab.avg_cube_size;
        mab.cube_size_count += 1;
        mab.avg_cube_size = (total_cube_size + po.state.len() as f64) / mab.cube_size_count as f64;
        let relative_cube_size = po.state.len() as f64 / mab.avg_cube_size.max(1.0);
        let potential_of_push = 1.0 - relative_level;
        let relative_depth = po.frame as f64 / (po.frame + po.depth) as f64;
        let saturation = if po.frame < self.frame.len() && !self.frame[po.frame].is_empty() {
            self.frame[po.frame][0].len()
        } else {
            0
        };
        let frame_saturation = (saturation as f64 / 100.0).min(1.0);
        let act_feat = (po.act / 100.0).clamp(0.0, 1.0);
        DVector::from_column_slice(&[
            relative_level,
            relative_cube_size,
            potential_of_push,
            relative_depth,
            frame_saturation,
            act_feat,
            1.0,
        ])
    }

    /// Select a generalization strategy with LinUCB and record it as pending
    /// until the matching `mab_feedback` after generalization.
    pub(super) fn mab_choose_mic_type(&mut self, po: &ProofObligation) -> MicType {
        let ctx = self.mab_context_vector(po);
        let arm = self.mab.select(&ctx);
        self.mab.pending = Some(arm);
        let p = match arm {
            BALANCED_ARM => balanced_params(po),
            AGGRESSIVE_ARM => aggressive_params(po),
            CONSERVATIVE_ARM => conservative_params(po),
            _ => {
                let (limit, max, level) = FIXED_ARM_CONFIGS[arm - NUM_DYNAMIC_ARMS];
                DropVarParameter::new(limit, max, level)
            }
        };
        debug!("MAB chose arm {arm}: {p:?}");
        MicType::DropVar(p)
    }

    /// Compute the reward of the pending arm from the generalization outcome
    /// and update the LinUCB model.
    pub(super) fn mab_feedback(
        &mut self,
        po: &ProofObligation,
        original_cube_size: usize,
        generalized_cube_size: usize,
        pushed_frame: usize,
    ) {
        let Some(arm) = self.mab.pending.take() else {
            return;
        };
        let level = self.level();
        let pushing_power = pushed_frame as f64 - po.frame as f64;
        let size_reduction_ratio = if original_cube_size > 0 {
            (original_cube_size as f64 - generalized_cube_size as f64) / original_cube_size as f64
        } else {
            0.0
        };
        let max_possible_push = level as f64 - po.frame as f64 + 1.0;
        let pushing_power_ratio = if max_possible_push > 0.0 {
            pushing_power / max_possible_push
        } else {
            0.0
        };
        // push quality: reward effective pushes, penalize unpushable clauses
        let push_quality = if pushing_power > 0.0 {
            pushing_power_ratio
        } else {
            -0.1
        };
        // ideal vs over-generalization
        let generalization_quality = if size_reduction_ratio > 0.5 && pushing_power_ratio > 0.3 {
            0.3
        } else if size_reduction_ratio > 0.7 && pushing_power_ratio < 0.1 {
            -0.2
        } else {
            0.0
        };
        // bonus events: frontier push, complete generalization, high-level push
        let mut bonus = 0.0;
        if pushed_frame >= level {
            bonus += 0.4;
        }
        if generalized_cube_size == 1 {
            bonus += 0.2;
        }
        if po.frame as f64 > 0.7 * level as f64 && pushing_power > 0.0 {
            bonus += 0.1;
        }
        let reward =
            (size_reduction_ratio * 0.35 + push_quality * 0.45 + generalization_quality + bonus)
                .clamp(-0.5, 2.0);
        debug!("MAB arm {arm} got reward {reward:.2}");
        let ctx = self.mab_context_vector(po);
        self.mab.update(arm, &ctx, reward);
    }
}
