#include "cadical.hpp"
#include "craigtracer.hpp"
#include "stdio.h"
#include <cassert>
#include <cstddef>

using namespace CaDiCaL;

extern "C" {
void *cadical_solver_new() { return new Solver(); }

void cadical_solver_free(void *s) {
  Solver *slv = (Solver *)s;
  delete slv;
}

void cadical_solver_reserve(void *s, int max_var) {
  Solver *slv = (Solver *)s;
  slv->reserve(max_var);
}

void cadical_solver_add_clause(void *s, int *clause, int len) {
  Solver *slv = (Solver *)s;
  for (int i = 0; i < len; ++i) {
    slv->add(clause[i]);
  }
  slv->add(0);
}

int cadical_solver_solve(void *s, int *assumps, int len) {
  Solver *slv = (Solver *)s;
  for (int i = 0; i < len; ++i)
    slv->assume(assumps[i]);
  return slv->solve();
}

int cadical_solver_model_value(void *s, int lit) {
  Solver *slv = (Solver *)s;
  return slv->val(lit);
}

bool cadical_solver_conflict_has(void *s, int lit) {
  Solver *slv = (Solver *)s;
  return slv->failed(lit);
}

void cadical_solver_constrain(void *s, int *constrain, int len) {
  Solver *slv = (Solver *)s;
  for (int i = 0; i < len; ++i) {
    slv->constrain(constrain[i]);
  }
  slv->constrain(0);
}

int cadical_solver_simplify(void *s) {
  Solver *slv = (Solver *)s;
  return slv->simplify();
}

int cadical_solver_fixed(void *s, int lit) {
  Solver *slv = (Solver *)s;
  return slv->fixed(lit);
}

void cadical_solver_freeze(void *s, int lit) {
  Solver *slv = (Solver *)s;
  slv->freeze(lit);
}

void cadical_terminate(void *s) {
  Solver *slv = (Solver *)s;
  slv->terminate();
}

struct ClauseIter : ClauseIterator {
  using Callback = void (*)(void *, const int *, size_t);
  ClauseIter(void *state, Callback callback)
      : state(state), callback(callback) {}

  bool clause(const std::vector<int> &c) override {
    callback(state, c.data(), c.size());
    return true;
  }

  void *state;
  Callback callback;
};

void cadical_solver_clauses(void *s, void *state,
                            ClauseIter::Callback callback) {
  ClauseIter clause_iter(state, callback);
  Solver *slv = (Solver *)s;
  slv->traverse_clauses(clause_iter);
}

size_t cadical_solver_num_clauses(void *s) {
  struct Counter : ClauseIterator {
    size_t count = 0;
    bool clause(const std::vector<int> &) override {
      ++count;
      return true;
    }
  } counter;
  ((Solver *)s)->traverse_clauses(counter);
  return counter.count;
}

void cadical_set_polarity(void *s, int lit) {
  Solver *slv = (Solver *)s;
  slv->phase(lit);
}

void cadical_unset_polarity(void *s, int lit) {
  Solver *slv = (Solver *)s;
  slv->unphase(lit);
}

void cadical_set_seed(void *s, int seed) {
  Solver *slv = (Solver *)s;
  slv->set("seed", seed);
}

void *cadical_craig_new(void *s) {
  Solver *solver = (Solver *)s;
  CaDiCraig::CraigTracer *tracer = new CaDiCraig::CraigTracer();
  solver->connect_proof_tracer(tracer, true);
  tracer->set_craig_construction(CaDiCraig::CraigConstruction::ASYMMETRIC);
  return tracer;
}

void cadical_craig_free(void *s, void *c) {
  Solver *solver = (Solver *)s;
  CaDiCraig::CraigTracer *tracer = (CaDiCraig::CraigTracer *)c;
  solver->disconnect_proof_tracer(tracer);
  delete tracer;
}

void cadical_craig_label_var(void *c, int var, uint8_t t) {
  // printf("var_label: %d %d\n", var, t);
  CaDiCraig::CraigTracer *tracer = (CaDiCraig::CraigTracer *)c;
  tracer->label_variable(var, (CaDiCraig::CraigVarType)t);
}

void cadical_craig_label_clause(void *c, int id, uint8_t t) {
  // printf("clause_label: %d %d\n", id, t);
  CaDiCraig::CraigTracer *tracer = (CaDiCraig::CraigTracer *)c;
  tracer->label_clause(id, (CaDiCraig::CraigClauseType)t);
}

void *cadical_craig_create_craig_interpolant(void *c, int *next_var, int *len) {
  CaDiCraig::CraigTracer *tracer = (CaDiCraig::CraigTracer *)c;
  std::vector<std::vector<int>> clauses;
  CaDiCraig::CraigCnfType result = tracer->create_craig_interpolant(
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, *next_var);
  assert(result == CaDiCraig::CraigCnfType::NORMAL);

  std::vector<void *> *res = new std::vector<void *>();
  for (int i = 0; i < clauses.size(); ++i) {
    std::vector<int> *cls = new std::vector<int>;
    for (int j = 0; j < clauses[i].size(); ++j)
      cls->push_back(clauses[i][j]);
    res->push_back(cls->data());
    res->push_back((void *)cls->size());
  }
  *len = res->size();
  return res->data();
}

void cadical_craig_test() {
  CaDiCaL::Solver *solver = new CaDiCaL::Solver();
  CaDiCraig::CraigTracer *tracer =
      (CaDiCraig::CraigTracer *)cadical_craig_new(solver);

  cadical_craig_label_var(tracer, 1, 0);
  cadical_craig_label_var(tracer, 2, 2);
  cadical_craig_label_var(tracer, 3, 2);
  cadical_craig_label_var(tracer, 4, 1);
  cadical_craig_label_clause(tracer, 1, 0);
  cadical_craig_label_clause(tracer, 2, 0);
  cadical_craig_label_clause(tracer, 3, 0);
  cadical_craig_label_clause(tracer, 4, 1);
  cadical_craig_label_clause(tracer, 5, 1);
  cadical_craig_label_clause(tracer, 6, 1);
  solver->add(1);
  solver->add(-2);
  solver->add(0);
  solver->add(-1);
  solver->add(-3);
  solver->add(0);
  solver->add(2);
  solver->add(0);
  solver->add(-2);
  solver->add(3);
  solver->add(0);
  solver->add(2);
  solver->add(4);
  solver->add(0);
  solver->add(-4);
  solver->add(0);
  assert(solver->solve() == CaDiCaL::Status::UNSATISFIABLE);

  int next_var = 5;
  std::vector<std::vector<int>> clauses;
  CaDiCraig::CraigCnfType result = tracer->create_craig_interpolant(
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_var);
  assert(result == CaDiCraig::CraigCnfType::NORMAL);
  printf("%d %d\n\n", clauses.size(), next_var);
  for (int i = 0; i < clauses.size(); ++i) {
    for (int j = 0; j < clauses[i].size(); ++j)
      printf("%d ", clauses[i][j]);
    printf("\n");
  }
  // assert (clauses == std::vector<std::vector<int>>{{-1}});
  // assert (next_var == 2);

  cadical_craig_free(solver, tracer);
  delete solver;
}
}

class RustTracer : public Tracer {
private:
  void *t;
  void *add_original_clause_fn;
  void *add_derived_clause_fn;
  void *delete_clause_fn;
  void *conclude_unsat_fn;

public:
  RustTracer(void *_t, void *add_original_clause, void *add_derived_clause,
             void *delete_clause, void *conclude_unsat)
      : t(_t), add_original_clause_fn(add_original_clause),
        add_derived_clause_fn(add_derived_clause),
        delete_clause_fn(delete_clause), conclude_unsat_fn(conclude_unsat) {}

  ~RustTracer() {}

  void add_original_clause(uint64_t id, bool redundant,
                           const std::vector<int> &c, bool restore) {
    ((void (*)(void *, uint64_t, bool, const void *, uint64_t, bool))(
        add_original_clause_fn))(t, id, redundant, c.data(), c.size(), restore);
  }

  void add_derived_clause(uint64_t id, bool redundant,
                          const std::vector<int> &c,
                          const std::vector<uint64_t> &proof_chain) {
    ((void (*)(void *, uint64_t, bool, const void *, uint64_t, const void *,
               uint64_t))(add_derived_clause_fn))(t, id, redundant, c.data(),
                                                  c.size(), proof_chain.data(),
                                                  proof_chain.size());
  }

  void delete_clause(uint64_t id, bool redundant, const std::vector<int> &c) {
    ((void (*)(void *, uint64_t, bool, const void *, uint64_t))(
        delete_clause_fn))(t, id, redundant, c.data(), c.size());
  }

  void weaken_minus(uint64_t, const std::vector<int> &) {}

  void strengthen(uint64_t) {}

  void report_status(int, uint64_t) {}

  void finalize_clause(uint64_t, const std::vector<int> &) {}

  void begin_proof(uint64_t) {}

  void solve_query() {}

  void add_assumption(int) {}

  void add_constraint(const std::vector<int> &) {}

  void reset_assumptions() {}

  void add_assumption_clause(uint64_t, const std::vector<int> &,
                             const std::vector<uint64_t> &) {}

  void conclude_unsat(ConclusionType conclusion,
                      const std::vector<uint64_t> &proof_chain) {
    ((void (*)(void *, int, const void *, uint64_t))(conclude_unsat_fn))(
        t, conclusion, proof_chain.data(), proof_chain.size());
  }

  void conclude_sat(const std::vector<int> &) {}
};

extern "C" {

void *cadical_tracer_new(void *s, void *t, void *add_original_clause,
                         void *add_derived_clause, void *delete_clause,
                         void *conclude_unsat) {
  Solver *solver = (Solver *)s;
  RustTracer *tracer =
      new RustTracer(t, add_original_clause, add_derived_clause, delete_clause,
                     conclude_unsat);
  solver->connect_proof_tracer(tracer, true);
  return tracer;
}

void cadical_tracer_free(void *s, void *t) {
  Solver *solver = (Solver *)s;
  RustTracer *tracer = (RustTracer *)t;
  solver->disconnect_proof_tracer(tracer);
  delete tracer;
}
}
