import VersoManual
import PadicModForms
import Doc.References
import Doc.TitleMath

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Doc

set_option pp.rawOnError true

#doc (Manual) "Rational modular forms" =>
%%%
tag := "rational-modular-forms"
htmlSplit := .never
%%%

```lean -show
open UpperHalfPlane MatrixGroups

variable (k : ℤ) (g : ModularForm 𝒮ℒ k)
```

# The definition
%%%
tag := "rational-definition"
%%%

Let $`k \in \mathbb{Z}`. A power series $`f \in \mathbb{Q}\llbracket X\rrbracket` is a _modular form
of weight $`k`_ if there is a modular form $`g` of level one and weight $`k` over $`\mathbb{C}`
whose $`q`-expansion is the image of $`f` in $`\mathbb{C}\llbracket X\rrbracket`. We denote by
$`M_k(\mathbb{Q})` the $`\mathbb{Q}`-submodule of $`\mathbb{Q}\llbracket X\rrbracket` of modular
forms of weight $`k`.

{docstring PowerSeries.isModularForm}

{docstring rationalModularForms}

Here {lean}`ModularForm 𝒮ℒ k` is the type of modular forms of weight $`k` for
$`\mathrm{SL}_2(\mathbb{Z})`, and {lean}`qExpansion 1 g` is the $`q`-expansion of $`g`, a power
series over $`\mathbb{C}`. We have $`M_k(\mathbb{Q}) = 0` if $`k < 0` or $`k = 2`
({name ModularForm.rationalModularForms_eq_bot_of_neg}`rationalModularForms_eq_bot_of_neg`,
{name ModularForm.rationalModularForms_two_eq_bot}`rationalModularForms_two_eq_bot`).

Choosing a witness $`g` for every element of $`M_k(\mathbb{Q})` defines a semilinear map
$`M_k(\mathbb{Q}) \to M_k(\mathbb{C})` over $`\mathbb{Q} \to \mathbb{C}`
({name ModularForm.rationalModularFormToComplex}`rationalModularFormToComplex`).

# The graded algebra
%%%
tag := "rational-graded-algebra"
%%%

For $`R = \mathbb{Q}`, the {tech}[$`q`-expansion map] is
{name ModularForm.rationalQExpansionAlgHom}`rationalQExpansionAlgHom`. Its restriction to
$`M_k(\mathbb{Q})` is {name ModularForm.rationalQExpansion}`rationalQExpansion`.

{docstring ModularForm.rationalQExpansionAlgHom}

{docstring ModularForm.rationalQExpansion}

# Eisenstein series
%%%
tag := "rational-eisenstein-series"
%%%

For $`k \in \mathbb{N}` we define the rational power series $`E_k` and $`G_k` by
{ref "normalization-eisenstein-series"}[the formulas of the introduction], and $`E_2` as $`E_k`
for $`k = 2`.

{docstring EisensteinSeries.ERatAux}

{docstring EisensteinSeries.E₂Rat}

{docstring EisensteinSeries.G_rat}

If $`k \geq 4` is even, the image of $`E_k` in $`\mathbb{C}\llbracket X\rrbracket` is the
$`q`-expansion of the Eisenstein series of weight $`k` of Mathlib
({name EisensteinSeries.qExpansion_E_eq_ERatAux_map}`qExpansion_E_eq_ERatAux_map`), so $`E_k` and
$`G_k` are rational modular forms of weight $`k`. In the code the hypotheses on $`k` are
`hk : 3 ≤ k` and `hk2 : Even k`.

{docstring ModularForm.ERat}

{docstring ModularForm.GRat}

{docstring ModularForm.E₄Rat}

{docstring ModularForm.E₆Rat}

The image of $`E_2` in $`\mathbb{C}\llbracket X\rrbracket` is the $`q`-expansion of the series
{name EisensteinSeries.E2}`E2` of Mathlib
({name EisensteinSeries.qExpansion_E2_eq_E₂Rat_map}`qExpansion_E2_eq_E₂Rat_map`).

# The structure theorem
%%%
tag := "rational-structure-theorem"
%%%

We define the $`\mathbb{Q}`-algebra homomorphism
$`\mathbb{Q}[X_0, X_1] \to \bigoplus_k M_k(\mathbb{Q})` sending $`X_0` to $`E_4` and $`X_1` to
$`E_6`.

{docstring ModularForm.evalE₄E₆Rat}

The homomorphism {name ModularForm.evalE₄E₆Rat}`evalE₄E₆Rat` is an isomorphism of
$`\mathbb{Q}`-algebras, and it maps $`\mathbb{Q}[X_0, X_1]_k` onto $`M_k(\mathbb{Q})` for every
$`k \in \mathbb{N}`. In particular $`E_4` and $`E_6` generate $`\bigoplus_k M_k(\mathbb{Q})` as a
$`\mathbb{Q}`-algebra.

{docstring ModularForm.rationalModularFormsEquivMvPolynomial}

{docstring ModularForm.E₄E₆Rat_generate}

The restriction of {name ModularForm.evalE₄E₆Rat}`evalE₄E₆Rat` to $`\mathbb{Q}[X_0, X_1]_k`,
with values in $`M_k(\mathbb{Q})`, is
{name ModularForm.evalE₄E₆RatAtWeight}`evalE₄E₆RatAtWeight`.
