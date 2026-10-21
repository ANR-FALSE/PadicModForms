# *p*-adic modular forms in Lean

[![CI](https://github.com/ANR-FALSE/PadicModForms/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ANR-FALSE/PadicModForms/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/documentation-doc--gen4-blue)](https://anr-false.github.io/PadicModForms/docs/)

A formalization, in Lean 4 and `mathlib`, of the theory of *p*-adic modular forms in the sense of
Serre, from the definition up to the construction of the eigenvariety. Part of the ANR FALSE effort.

📖 **[Website](https://anr-false.github.io/PadicModForms/)**: the definitions of the project and
the design decisions behind them, as a Verso document built from the code (sources in
[`verso/`](verso/)). The [API documentation](https://anr-false.github.io/PadicModForms/docs/) is
at `/docs`.

## Serre's definition

Fix a prime *p*. On ℚ_*p*⟦q⟧ define the valuation

$$v(f) \;=\; \inf_{n \ge 0} v_p(a_n), \qquad f = \sum_{n \ge 0} a_n q^n,$$

with values in ℤ ∪ {±∞}. A **_p_-adic modular form** is a power series *f* ∈ ℚ_*p*⟦q⟧ which is a
limit, for *v*, of *q*-expansions of classical modular forms of level one:

$$f = \lim_{i \to \infty} f_i, \qquad f_i \in M_{k_i}(\mathrm{SL}_2(\mathbb{Z})) \otimes \mathbb{Q}.$$

Everything in this repository is phrased through *q*-expansions: a modular form **is** a power
series satisfying a predicate, over ℚ, over ℤ localized at *p*, over ℤ/*p*ℤ or over ℚ_*p*. The
analytic modular forms of `mathlib` appear only once, as the witness in the definition over ℚ.

## Relation to other projects

`PadicModForms` is part of the broader ANR FALSE effort on formalizing arithmetic in Lean. It is
also closely connected with ongoing developments in `mathlib`, especially around modular forms,
*L*-functions, and arithmetic computation.

The long-term aim is not just to formalize isolated theorems, but to build a coherent and reusable
library of arithmetic theories that can support future developments in number theory and arithmetic
geometry.

## References

- J.-P. Serre, *Formes modulaires et fonctions zêta p-adiques*, in *Modular Functions of One
  Variable III*, Lecture Notes in Mathematics 350, Springer, 1973, 191–268.
- H. P. F. Swinnerton-Dyer, *On ℓ-adic representations and congruences for coefficients of modular
  forms*, in the same volume, 1–55.
- J.-P. Serre, *Congruences et formes modulaires (d'après H. P. F. Swinnerton-Dyer)*, Séminaire
  Bourbaki 416, 1971/72.
