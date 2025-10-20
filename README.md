# A weak spectroscopy game to characterize behavioral equivalences

This Isabelle/HOL theory formalizes the paper [“One Energy Game for the Spectrum between Branching Bisimilarity and Weak Trace Semantics”](https:/doi.org/10.4204/EPTCS.412.6) along the lines of [its tech report](https://doi.org/10.48550/arXiv.2305.17671).
It describes the *weak spectroscopy game*, an energy game where the attacker wins precisely if two states in a transition system can be distinguished using Hennessy–Milner logic with modalities for silent steps (τ-transitions).
The initial budget of energy the attacker needs to win corresponds to a hierarchy of HML sublogics, which again correspond to common weak equivalences such as weak traces, weak bisimilarity, or branching bisimilarity.

More on the approach underlying this work and its research context can be found in Benjamin Bisping's PhD thesis [“Generalized Equivalence Checking of Concurrent Programs”](https://generalized-equivalence-checking.equiv.io/).

## Building

To build this project, run:

```bash
./build.sh
```

The resulting files are placed into `out/`.

The script assumes that the command `isabelle` resolves to your Isabelle installation. The theory has been tested with Isabelle2024 and Isabelle2025.

## Authors

Lisa Annett Barthel¹, Leonard Moritz Hübner¹, [Caroline Lemke](https://uol.de/caroline-lemke)¹˒², Karl Parvis Philipp Mattes¹, Lenard Mollenkopf¹, [Benjamin Bisping](https://bbisping.de)¹˒³

(¹ Technische Universität Berlin; ² Carl von Ossietzky Universität Oldenburg; ³ Télécom SudParis, Institut Polytechnique de Paris)



