# Measure the Coq development

We use [cloc](https://github.com/AlDanial/cloc) to get the statistics on the complete specifications and proofs of CertrBPF.

| | Interpreter (locs) | Verifier (locs) |
| --- | --- | --- |
| Proof Model     | 2445  | 1459  |
| Properties      | 4885  | 547   |
| Synthesis Model | 3285  |       |
| Equivalence     | 635   |       |
| Clightlogic     | 4413  |       |
| Simulation      | 10820 | 8331  |
| (Total)         | 26483 | 10337 |


```shell
# 0. install cloc firstly
sudo apt install cloc

# current folder: /home/cav/CertrBPF/rbpf-dx
# 1. measure CertrBPF-interpreter Proof model (2445 locs)
cloc comm model

# 2. measure CertrBPF-interpreter Properties (4885 locs)
cloc isolation

# 3. measure CertrBPF-interpreter Synthesis Model (3285 locs)
cloc monadicmodel dxcomm dxmodel

# 4. measure CertrBPF-interpreter Equivalence (635 locs)
cloc equivalence

# 5. measure CertrBPF-interpreter Clightlogic (4413 locs)
cloc clightlogic

# 6. measure CertrBPF-interpreter Simulation (10820 locs)
cloc simulation

# 7. measure CertrBPF-verifier Proof model (1459 locs)
cloc verifier/comm verifier/dxmodel verifier/synthesismodel

# 8. measure CertrBPF-verifier Properties (547 locs)
cloc verifier/property

# 9. measure CertrBPF-verifier Simulation (8331 locs)
cloc verifier/simulation
```
