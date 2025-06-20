# rIC3 Hardware Model Checker

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![CI](https://github.com/gipsyh/rIC3/actions/workflows/ci.yml/badge.svg)](https://github.com/gipsyh/rIC3/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/rIC3.svg?logo=rust)](https://crates.io/crates/rIC3)
[![Docker](https://img.shields.io/docker/v/gipsyh/ric3?label=Docker&logo=docker)](https://hub.docker.com/r/gipsyh/ric3)

### HWMCC
rIC3 achieved first place in both the bit-level track and the word-level bit-vector track at the 2024 Hardware Model Checking Competition ([HWMCC'24](https://hwmcc.github.io/2024/)).

<p align="center">
	<img width="250" height="auto" src="./images/hwmcc24_aiger.png" style="display:inline-block;">
	<img width="250" height="auto" src="./images/hwmcc24_btor2_bv.png" style="display:inline-block;">
</p>

To view the submission for HWMCC'24, please checkout the `HWMCC24` branch or download the binary release at https://github.com/gipsyh/rIC3-HWMCC24.

### Publications
- [CAV2025] [The rIC3 Hardware Model Checker](https://arxiv.org/abs/2502.13605)
- [CAV2025] [Deeply Optimizing the SAT Solver for the IC3 Algorithm](https://arxiv.org/abs/2501.18612)
- [DAC2024] [Predicting Lemmas in Generalization of IC3](http://doi.org/10.1145/3649329.3655970)
- [arXiv] [Extended CTG Generalization and Dynamic Adjustment of Generalization Strategies in IC3](https://arxiv.org/abs/2501.02480)

### rIC3 Tool Flow
<p align="center">
	<img width="500" height="auto" src="./images/toolflow.jpg" style="display:inline-block;">
</p>

### Install From Crates.io
```cargo install rIC3```

### Install From Source
- Install the Rust compiler https://www.rust-lang.org/
- Switch to nightly ```rustup default nightly```
- ```git clone --recurse-submodules https://github.com/gipsyh/rIC3```
- Build ```cd rIC3 && cargo b --release```
- Run ```cargo r --release -- <AIGER FILE>```
- Install ```cargo install --path .```

### Run
- 16-threads Portfolio ```rIC3 <AIGER FILE>```
- single-thread IC3 ```rIC3 -e ic3 <AIGER FILE>```

### Docker
- build image: ```docker build -t ric3 .```
- run: ```docker run -v <AIGER FILE>:/model.aig ric3 model.aig```

Copyright (C) 2023 - Present, Yuheng Su (gipsyh.icu@gmail.com). All rights reserved.
