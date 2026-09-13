# *p*-adic modular forms in Lean

[![CI](https://github.com/ANR-FALSE/PadicModForms/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ANR-FALSE/PadicModForms/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/documentation-doc--gen4-blue)](https://anr-false.github.io/PadicModForms/docs/)

A formalization, in Lean 4 and `mathlib`, of the theory of *p*-adic modular forms in the sense of
Serre. Part of the ANR FALSE effort.

📖 **[Browse the API documentation](https://anr-false.github.io/PadicModForms/docs/)**. Good entry
points are [`PAdic.Defs`](https://anr-false.github.io/PadicModForms/docs/PadicModForms/PAdic/Defs.html)
for the definition of a *p*-adic modular form and
[`Rational.Basic`](https://anr-false.github.io/PadicModForms/docs/PadicModForms/Rational/Basic.html)
for the classical layer everything rests on.

## Serre's definition

Fix a prime *p*. On ℚ_*p*⟦q⟧ define the valuation

$$v(f) \;=\; \inf_{n \ge 0} v_p(a_n), \qquad f = \sum_{n \ge 0} a_n q^n,$$

with values in ℤ ∪ {±∞}. A **_p_-adic modular form** is a power series *f* ∈ ℚ_*p*⟦q⟧ which is a
limit, for *v*, of *q*-expansions of classical modular forms of level one:

$$f = \lim_{i \to \infty} f_i, \qquad f_i \in M_{k_i}(\mathrm{SL}_2(\mathbb{Z})) \otimes \mathbb{Q}.$$

Such a sequence, together with its weights, is a *presentation* of *f* (`pAdicModularFormStruct`),
and `PowerSeries.isPAdicModularForm` is the resulting predicate. Everything in this repository is
phrased through *q*-expansions: a modular form **is** a power series satisfying a predicate, never
an analytic object. `mathlib`'s analytic `ModularForm 𝒮ℒ k` occurs only at the bottom of the tower,
as the witness in the defining predicate.

Serre's first theorem is that the classical weights *k*ᵢ of a presentation of a nonzero *f*
converge in the weight space

$$\mathcal{X} = \mathrm{Hom}_{\mathrm{cont}}(\mathbb{Z}_p^\times, \mathbb{Z}_p^\times),$$

and that the limit depends only on *f*, not on the presentation. This is what makes the **weight**
of a *p*-adic modular form well defined. Its proof rests in turn on a congruence between the
weights of congruent classical forms, Serre's *Théorème 1*: for *p* ≥ 5 and *m* ≥ 1, if two
*p*-integral forms of weights *k* and *k*′ satisfy *v*(*f* − *f*′) ≥ *v*(*f*) + *m* and *f* ≢ 0
mod *p*, then

$$k' \equiv k \pmod{(p-1)p^{m-1}}.$$

## The coefficient tower

Reducing modulo *p* is what drives the whole theory, so the library is built as a tower of
coefficient rings, each layer defined by a lift or a reduction to the layer below. Results flow
upward.

| directory | coefficients | a form of weight *k* is a power series such that … |
| --- | --- | --- |
| `Rational/` | ℚ | … it is the *q*-expansion of a level-one `ModularForm` of weight *k* (`PowerSeries.isModularForm`) |
| `pLocalInt/` | ℤ localized at *p* | … its scalar extension to ℚ is a rational modular form (`isPLocalIntModularForm`) |
| `ModP/` | ℤ/*p*ℤ | … it is the reduction of some *p*-integral form (`isModPModularForm`) |
| `PAdic/` | ℚ_*p* | … it is a limit of rational forms, in Serre's sense (`PowerSeries.isPAdicModularForm`) |

The same pattern recurs at every layer, which makes each directory quick to read: a predicate with
its closure lemmas, a `Submodule` of weight-*k* forms, a `SetLike.GradedMonoid` instance turning
`⨁ k, …ModularForms k` into a graded ring, a *q*-expansion algebra map out of that direct sum, and
an evaluation map from ℤ/*p*ℤ[X₀, X₁] sending X₀ ↦ E₄ and X₁ ↦ E₆, whose injectivity in each fixed
weight transports the structure theorem for the graded ring down the tower.

Outside the tower, `ForMathlib/` holds material destined for `mathlib`, written to its standards
and independent of the rest of the project.

## The mod-*p* structure theory

Assume *p* ≥ 5 and grade ℤ/*p*ℤ[X₀, X₁] by the weights (4, 6), so that the evaluation
φ : *F* ↦ *F*(E₄, E₆) sends weighted homogeneous polynomials of weight *k* to mod-*p* modular forms
of weight *k*. The Eisenstein series E_{*p*−1} ≡ 1 mod *p* is a weighted homogeneous polynomial
*A* = `hasseInvPoly` of weight *p* − 1 in E₄ and E₆ — the **Hasse invariant** — and *A* − 1 is
therefore in ker φ. The following are proved here.

- **Swinnerton-Dyer's kernel theorem** (`ker_evalE₄E₆ModP`): ker φ = (*A* − 1), and *A* − 1 is
  irreducible (`irreducible_hasseInvPoly_sub_one`).
- **Weights are well defined modulo *p* − 1** (`natCast_eq_of_evalE₄E₆ModP_eq`): two weighted
  homogeneous polynomials of weights *k* and *k*′ with the same nonzero evaluation satisfy
  *k* ≡ *k*′ mod (*p* − 1).
- **The filtration** (`modPFiltration`): the least weight of a weighted homogeneous representative.
  Two homogeneous representatives of the same form differ by a power of *A*
  (`eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq`), a representative computes the filtration exactly
  when *A* does not divide it (`modPFiltration_eq_of_not_dvd`), forms of unequal filtration do not
  cancel (`modPFiltration_add_of_lt`), and fil(*f* ᵖ) = *p* · fil(*f*)
  (`modPFiltration_pow_prime`).
- **The Hasse invariant is squarefree** (`hasseInvPoly_squarefree`), via the relative primality of
  *A* and its Ramanujan derivative (`isRelPrime_hasseInvPoly_δModP`).
- **Normality of the degree-zero forms** (`mem_modPWeightZeroForms_of_isIntegral`): a power series
  *f* = *u*/*w* with *u*, *w* of degree zero which is integral over the degree-zero forms 𝓜⁰ is
  itself of degree zero. The proof is the integral root theorem in the unique factorization domain
  ℤ/*p*ℤ[X₀, X₁], not the normality of a homogeneous localization.
- **The structure theorem over ℤ_(*p*)** (`pLocalIntModularFormsEquivMvPolynomial`): for *p* ≥ 5,
  evaluation at E₄ and E₆ identifies the polynomial ring in two variables with the graded ring of
  *p*-integral modular forms. Its ingredients — the discriminant Δ as a *p*-integral unit series
  and division by Δ — are in `pLocalInt/Discriminant.lean`.
- **Serre's Théorème 1 for *m* = 1** (`natCast_eq_of_map_toZMod_eq`): congruent rational forms
  modulo *p* have weights congruent modulo *p* − 1.

## Current state

Every result listed in the previous section is proved. Three developments are under way: the
convergence of the weights of a presentation in 𝒳, which is what makes the *p*-adic weight well
defined; Serre's Théorème 1 for *m* ≥ 2; and the theta operator Θ = *q* d/d*q*, which preserves
mod-*p* modular forms and raises the filtration by *p* + 1, sharply when *p* ∤ fil(*f*).

## Objectives

Beyond those three, the direction of the project is:

- families of Eisenstein series over weight space, and the continuity of their Fourier
  coefficients;
- the *p*-adic zeta function, obtained from the constant term of the Eisenstein family, with its
  interpolation and continuity properties;
- the first objects of Λ-adic theory: Hecke operators, the U_*p*-operator acting on power series,
  and the algebraic prerequisites for Hida families and ordinary Hecke algebras.

The scope is deliberately the Serre-style theory, which is far more accessible to formalization
than overconvergent modular forms in the sense of Katz, while remaining a genuine test case for
research-level number theory in Lean.

## Relation to other projects

`PadicModForms` is part of the broader ANR FALSE effort on formalizing arithmetic in Lean. It is
also closely connected with ongoing developments in `mathlib`, especially around modular forms,
*L*-functions, and arithmetic computation.

The long-term aim is not just to formalize isolated theorems, but to build a coherent and reusable
library of arithmetic theories that can support future developments in number theory and arithmetic
geometry.

## Building

The toolchain is pinned in `lean-toolchain` and `mathlib`'s revision in `lake-manifest.json`; the
two must always be changed together. With [`elan`](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get                    # fetch cached mathlib oleans (fresh clone, or after `lake update`)
lake build                            # build the whole library
lake build PadicModForms.ModP.Hasse   # build one module and its dependencies
```

## References

- J.-P. Serre, *Formes modulaires et fonctions zêta p-adiques*, in *Modular Functions of One
  Variable III*, Lecture Notes in Mathematics 350, Springer, 1973, 191–268.
- H. P. F. Swinnerton-Dyer, *On ℓ-adic representations and congruences for coefficients of modular
  forms*, in the same volume, 1–55.
- J.-P. Serre, *Congruences et formes modulaires (d'après H. P. F. Swinnerton-Dyer)*, Séminaire
  Bourbaki 416, 1971/72.
