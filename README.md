# Essakine2026Tight

A Lean 4 formalization of *Tight Sample Complexity Bounds for Entropic Best Policy Identification*
(Amer Essakine and Claire Vernade, COLT 2026,
[arXiv:2605.13717](https://arxiv.org/abs/2605.13717)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the two results of the paper on best-policy identification under the entropic risk
measure in finite-horizon tabular MDPs: the lower bound
$\Omega\big(\frac{(e^{|\beta| G_{\max}} - 1)^2}{e^{|\beta| G_{\max}}} \frac{SAH}{(e^{|\beta|\varepsilon} - 1)^2}\log\frac1\delta\big)$
on the expected number of episodes of every $(\varepsilon, \delta)$-PAC algorithm (Theorem 3), and
the PAC property and the matching sample complexity of the algorithm Entropic-BPI (Theorem 4).
Writing the blueprint uncovered several errors in the paper (a false bound on the binary
divergence and a misplaced Condition A in the lower bound, a bonus with the wrong rate, off-by-one
clips, a false self-bounding lemma, ...): the formalized statements are the corrected ones, see
the errata. Every headline result is proved, with no `sorry`.

- Website: https://RemyDegenne.github.io/Essakine2026Tight/, with the blueprint, the referee site and the
  literature links (which declarations formalize which results of the paper). CI builds it on each
  push to `main`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Essakine2026Tight/EV2026/`, listed with their status in
  `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `Essakine2026Tight/ForLMLExplore/`, which Tau Ceti workers port to
  LMLExplore; `PAPER_ROADMAP.md` says where each item goes. It holds the finite-horizon MDP theory
  (`MarkovDecisionProcess/`), the empirical models and the concentration at the visits of a
  state-action pair (`ReinforcementLearning/Episodic/`), the change of measure for identification
  algorithms (`Identification/`), stopped histories and the divergence decomposition
  (`SequentialLearning/`), and Mathlib-shaped files at their Mathlib paths.
- The blueprint outline, the design decisions, the upstreaming candidates and the other findings
  of the formalization: `notes/`.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.
