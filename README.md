# Weak Equivalence Spectroscopy

This Isabelle/HOL theory formalizes the paper [“Linear-Time–Branching-Time Spectroscopy Accounting for Silent Steps“](https://doi.org/10.48550/arXiv.2305.17671). It describes the *weak spectroscopy game*, an energy game where the attacker wins iff two states in a transition system can be distinguished using Hennessy–Milner logic with modalities for silent steps (\<tau>-transitions). The initial budget of energy the attacker needs to win corresponds to a lattice of HML sublogics, which again corresponds to common weak equivalences such as weak traces, weak bisimilarity, or branching bisimilarity.

## Building

To build this project, run:

```bash
./build.sh
```

The resulting files are placed into `out/`.

The script assumes that the command `isabelle` resolves to your Isabelle installation. The theory has been tested with Isabelle2023 and Isabelle2024.