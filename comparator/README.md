# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Essakine2026Tight/`.

**Status.** Every challenge is proved. `scripts/comparator-verify.sh --insecure` passed on all three
challenges on 2026-09-16; they were regenerated on 2026-09-17, after the generalization of the MDP
library, and on 2026-11-09, when the project moved to LMLExplore. Against the challenges of
2026-09-17, the statements and the definitions they rest on are unchanged up to LML's renames
(`stationaryEnv` is `Environment.bandit`, `detAlgorithm` is `Algorithm.deterministic`, and the
stopping time takes values in `WithTop ℕ`, so that its coercion to `ℝ≥0∞` is written
`ENat.toENNReal`); `scripts/comparator-verify.sh` has to be run again on them.

Each challenge is one file that imports LML and Mathlib modules only (the project does not use
LMLExplore's definitions yet), no project modules and no sibling helpers.

## The trust story

For each headline theorem `Essakine2026Tight.<name>` there is a challenge file
`Challenge_<name>.lean` and a config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 3 (lower bound on the expected number of episodes of every PAC algorithm on the hard instance) | `exists_hardMDP_lowerBound_le_lintegral_stoppingTime` |
| Theorem 4, PAC (Entropic-BPI is (ε, δ)-PAC) | `isEntropicPAC_entropicBPI` |
| Theorem 4, sample complexity (Entropic-BPI stops within `upperBound` episodes with probability 1 - δ) | `probReal_stoppingTime_entropicBPI_le_ge` |

Each challenge states the theorem with `sorry`, with every definition of the project that the
statement rests on copied verbatim from its source by
[challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen); the definitions of
LMLExplore, LML, Tau Ceti and Mathlib that it uses are imported. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
