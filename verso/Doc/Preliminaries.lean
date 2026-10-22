import VersoManual
import PadicModForms
import Doc.References
import Doc.TitleMath

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Doc

set_option pp.rawOnError true

#doc (Manual) "Preliminaries" =>
%%%
htmlSplit := .never
%%%

# Modular forms as power series

Let $`R` be one of the rings $`\mathbb{Q}`, $`\mathbb{Z}_{(p)}`, $`\mathbb{F}_p`. For every
$`k \in \mathbb{Z}` we define a predicate on $`R\llbracket X\rrbracket` expressing that a power
series is a modular form of weight $`k` over $`R`, and we denote by $`M_k(R)` the $`R`-submodule
of $`R\llbracket X\rrbracket` of power series satisfying it. The variable $`X` plays the role of
$`q`. The three predicates are defined one from the other, starting from the definition of modular
forms over $`\mathbb{C}` in Mathlib: a power series over $`\mathbb{Q}` is a modular form of weight
$`k` if its image in $`\mathbb{C}\llbracket X\rrbracket` is the $`q`-expansion of a modular form
of weight $`k` over $`\mathbb{C}`; a power series over $`\mathbb{Z}_{(p)}` is a modular form of
weight $`k` if its image in $`\mathbb{Q}\llbracket X\rrbracket` is a modular form of weight $`k`
over $`\mathbb{Q}`; and a power series over $`\mathbb{F}_p` is a modular form of weight $`k` if it
is the reduction modulo $`p` of a modular form of weight $`k` over $`\mathbb{Z}_{(p)}`.

The family $`(M_k(R))_{k \in \mathbb{Z}}` is a graded monoid: $`1 \in M_0(R)` and
$`M_k(R)\, M_l(R) \subseteq M_{k+l}(R)`. Hence $`\bigoplus_{k \in \mathbb{Z}} M_k(R)` is a graded
$`R`-algebra. The $`R`-algebra homomorphism

$$`\bigoplus_{k \in \mathbb{Z}} M_k(R) \longrightarrow R\llbracket X\rrbracket`

sending a family of forms to the sum of the corresponding power series is called the
$`q`-expansion map. For $`R = \mathbb{Q}` and $`R = \mathbb{Z}_{(p)}` the $`q`-expansion map is
injective; in the code, injectivity is proved for the $`q`-expansion map of level-one modular
forms over $`\mathbb{C}`
({name ModularForm.levelOne_qExpansionRingHom_injective}`levelOne_qExpansionRingHom_injective`).
For $`R = \mathbb{F}_p` and $`p \geq 5` it is not injective: since $`E_{p-1} \equiv 1 \pmod{p}`
({name EisensteinSeries.E_p_sub_one_mod_p}`E_p_sub_one_mod_p`), the element of
$`\bigoplus_k M_k(\mathbb{F}_p)` whose components are $`1` in weight $`0` and $`-1` in weight
$`p - 1` is nonzero and has $`q`-expansion $`0`.

# The ring $`\mathbb{Z}_{(p)}`
%%%
tag := "the-ring-z-p"
%%%

We define $`\mathbb{Z}_{(p)}` as the valuation subring of $`\mathbb{Q}` associated with the prime
ideal $`p\mathbb{Z}`, viewed as an element of the height one spectrum of $`\mathbb{Z}`.

{docstring heightOneSpec}

{docstring pLocalInt}

The ring $`\mathbb{Z}_{(p)}` is the localization of $`\mathbb{Z}` at $`p\mathbb{Z}`, and the
reduction maps $`\mathbb{Z}_{(p)} \to \mathbb{Z}/p\mathbb{Z}` and
$`\mathbb{Z}_{(p)} \to \mathbb{Z}/p^m\mathbb{Z}` are defined by the universal property of the
localization.

{docstring pLocalInt.toZMod}

{docstring pLocalInt.toZModPow}

A power series over $`\mathbb{Z}_{(p)}` is mapped to a power series over $`\mathbb{Q}` by applying
the inclusion $`\mathbb{Z}_{(p)} \subseteq \mathbb{Q}` to its coefficients, and a rational power
series whose coefficients lie in $`\mathbb{Z}_{(p)}` defines a power series over
$`\mathbb{Z}_{(p)}`.

# Operators on power series

Let $`R` be a commutative semiring. We define $`\Theta = q\,\frac{d}{dq}` on
$`R\llbracket X\rrbracket` as $`X` times the formal derivative.

{docstring PowerSeries.Θ}

For $`k \in \mathbb{N}` and a prime $`p` we define the power series

$$`\sum_{n \geq 1} \sigma_k(n)\, q^n \qquad \text{and} \qquad \sum_{p \nmid n} \sigma_k(n)\, q^n`

over $`R`. Here $`\sigma_k(n) = \sum_{d \mid n} d^k` for $`n \geq 1` and $`\sigma_k(0) = 0`.

{docstring PowerSeries.sigmaSeries}

{docstring PowerSeries.sigmaSeriesPrimeTo}

With this notation, Serre's series $`\varphi_h` and $`\psi` are `sigmaSeries (ZMod p) (h - 1)`
and `sigmaSeriesPrimeTo (ZMod p) p (p - 2)`.

# Uniform convergence of power series

Let $`R` be a uniform space. We endow $`R\llbracket X\rrbracket` with the uniform structure
induced by the map $`f \mapsto (n \mapsto \operatorname{coeff}_n f)` to the space of functions
$`\mathbb{N} \to R` with the uniform structure of uniform convergence.

{docstring PowerSeries.WithUniformConvergence.uniformSpace}

# Weighted homogeneous polynomials

Let $`R` be a commutative semiring. We grade $`R[X_0, X_1]` by giving $`X_0` weight $`4` and
$`X_1` weight $`6`, the weights of $`E_4` and $`E_6`: a polynomial that is weighted homogeneous of
weight $`k` for this grading evaluates at $`X_0 = E_4`, $`X_1 = E_6` to a modular form of weight
$`k`. We denote by $`R[X_0, X_1]_k` the $`R`-submodule of polynomials that are weighted
homogeneous of weight $`k` for this grading, in the sense of
{name MvPolynomial.IsWeightedHomogeneous}`MvPolynomial.IsWeightedHomogeneous`.

{docstring ModularForm.E₄E₆Weights}

{docstring ModularForm.E₄E₆WeightedHomogeneous}

For a polynomial $`P` with weighted homogeneous components $`P_n`, we also define
$`\sum_n P_n T^n \in R[X_0, X_1][T]`
({name MvPolynomial.toWeightPolynomial}`toWeightPolynomial`) and, for $`N \in \mathbb{N}`, the
weighted homogenization $`\sum_n P_n T^{N-n}`
({name MvPolynomial.weightedHomogenize}`weightedHomogenize`).
