import VersoManual
import PadicModForms
import Doc.References
import Doc.TitleMath

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Doc

set_option pp.rawOnError true

#doc (Manual) "{tight}[$`p`-integral modular forms]" =>
%%%
tag := "p-integral-modular-forms"
htmlSplit := .never
%%%

# The definition
%%%
tag := "pint-definition"
%%%

Let $`k \in \mathbb{Z}`. A power series $`f \in \mathbb{Z}_{(p)}\llbracket X\rrbracket` is a
_$`p`-integral modular form of weight $`k`_ if its image in $`\mathbb{Q}\llbracket X\rrbracket` is
a rational modular form of weight $`k`. We denote by $`M_k(\mathbb{Z}_{(p)})` the
$`\mathbb{Z}_{(p)}`-submodule of $`\mathbb{Z}_{(p)}\llbracket X\rrbracket` of $`p`-integral
modular forms of weight $`k`.

{docstring PowerSeries.isPLocalIntModularForm}

{docstring pLocalIntModularForms}

For $`R = \mathbb{Z}_{(p)}`, the {tech}[$`q`-expansion map] is
{name ModularForm.pLocalIntQExpansionAlgHom}`pLocalIntQExpansionAlgHom`.

{docstring ModularForm.pLocalIntQExpansionAlgHom}

# Integral Eisenstein series
%%%
tag := "integral-eisenstein-series"
%%%

Let $`k \geq 4` be even and assume that $`B_k^{-1} \in \mathbb{Z}_{(p)}`. Then the coefficients of
$`E_k` lie in $`\mathbb{Z}_{(p)}`, and we denote by {name EisensteinSeries.E_int}`E_int` the
corresponding $`p`-integral modular form of weight $`k`. The hypothesis holds if $`p - 1 \mid k`
({name inv_bernoulli_mem_pLocalInt}`inv_bernoulli_mem_pLocalInt`). The coefficients of $`E_2`,
$`E_4` and $`E_6` lie in $`\mathbb{Z}_{(p)}` for every $`p`, and we denote the corresponding power
series over $`\mathbb{Z}_{(p)}` by {name EisensteinSeries.E₂_int}`E₂_int`,
{name EisensteinSeries.E₄_int}`E₄_int` and {name EisensteinSeries.E₆_int}`E₆_int`.

{docstring EisensteinSeries.E_int}

{docstring EisensteinSeries.E₂_int}

{docstring EisensteinSeries.E₄_int}

{docstring EisensteinSeries.E₆_int}

# Evaluation at $`E_4`, $`E_6` and the discriminant
%%%
tag := "pint-evaluation-discriminant"
%%%

We define the $`\mathbb{Z}_{(p)}`-algebra homomorphism
$`\mathbb{Z}_{(p)}[X_0, X_1] \to \bigoplus_k M_k(\mathbb{Z}_{(p)})` sending $`X_0` to $`E_4` and
$`X_1` to $`E_6`, and its restriction to $`\mathbb{Z}_{(p)}[X_0, X_1]_k`, with values in
$`M_k(\mathbb{Z}_{(p)})`.

{docstring ModularForm.evalE₄E₆Int}

{docstring ModularForm.evalE₄E₆IntAtWeight}

Assume $`p \geq 5`. Since $`1728 = 2^6 \cdot 3^3` is a unit of $`\mathbb{Z}_{(p)}`, we define
$`\Delta = (E_4^3 - E_6^2)/1728 \in \mathbb{Z}_{(p)}\llbracket X\rrbracket`. Its image in
$`\mathbb{C}\llbracket X\rrbracket` is the $`q`-expansion of the discriminant of Mathlib
({name ModularForm.discriminant_int_map_complex}`discriminant_int_map_complex`), and
$`\Delta = uX` for a unit $`u` of $`\mathbb{Z}_{(p)}\llbracket X\rrbracket`. For
$`f \in \mathbb{Z}_{(p)}\llbracket X\rrbracket` we define
$`f/\Delta = u^{-1} \sum_{n \geq 0} \operatorname{coeff}_{n+1}(f)\, X^n`.

{docstring ModularForm.discriminant_int}

{docstring ModularForm.divDiscriminant_int}

Let $`p \geq 5` and let $`f` be a $`p`-integral modular form of weight $`k` whose constant
coefficient is $`0`. Then $`f/\Delta` is a $`p`-integral modular form of weight $`k - 12`.

{docstring ModularForm.divDiscriminant_int_isPLocalIntModularForm}

Let $`p \geq 5`. The homomorphism {name ModularForm.evalE₄E₆Int}`evalE₄E₆Int` is an isomorphism of
$`\mathbb{Z}_{(p)}`-algebras, and for every $`k \in \mathbb{N}` it restricts to an isomorphism
$`\mathbb{Z}_{(p)}[X_0, X_1]_k \simeq M_k(\mathbb{Z}_{(p)})`.

{docstring ModularForm.pLocalIntModularFormsEquivMvPolynomial}

{docstring ModularForm.evalE₄E₆IntAtWeightEquiv}

# Eisenstein congruences
%%%
tag := "eisenstein-congruences"
%%%

Let $`k \geq 4` be even and $`m \geq 1`. If $`(p-1)p^{m-1} \mid k`, then
$`E_k \equiv 1 \pmod{p^m}`. If $`p` is odd and $`p - 1 \mid k`, then there is a unit
$`\lambda \in \mathbb{Z}_{(p)}^\times` such that

$$`E_k - 1 = p^{v_p(k) + 1} \lambda \sum_{n \geq 1} \sigma_{k-1}(n)\, q^n.`

{docstring EisensteinSeries.E_int_mod_p_pow_of_dvd}

{docstring EisensteinSeries.E_int_sub_one_eq_unit_smul_sigmaSeries}

The second statement follows from the fact that $`-2k/B_k` and $`p^{v_p(k)+1}` are associated in
$`\mathbb{Z}_{(p)}`
({name EisensteinSeries.associated_pow_neg_two_mul_inv_bernoulli}`associated_pow_neg_two_mul_inv_bernoulli`).

Let $`p \geq 5`. Then $`E_2 \equiv E_{p+1} \pmod{p}`, where $`E_{p+1}` is
{name EisensteinSeries.E_p_add_one}`E_p_add_one`.

{docstring EisensteinSeries.E₂_int_map_toZMod}
