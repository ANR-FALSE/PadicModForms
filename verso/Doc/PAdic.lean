import VersoManual
import PadicModForms
import Doc.References
import Doc.TitleMath

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Doc

set_option pp.rawOnError true

#doc (Manual) "{tight}[$`p`-adic modular forms]" =>
%%%
tag := "p-adic-modular-forms"
htmlSplit := .never
%%%

```lean -show
open PowerSeries

variable {p : ℕ} [Fact p.Prime]
```

# Weight space
%%%
tag := "weight-space"
%%%

We define the weight space $`\mathcal{X}` as the group of continuous homomorphisms
$`\mathbb{Z}_p^\times \to \mathbb{Z}_p^\times`, with the compact-open topology, and for
$`n \in \mathbb{Z}` we denote by $`\iota(n) \in \mathcal{X}` the homomorphism $`u \mapsto u^n`. In
the code, $`\mathcal{X}` is written {lean}`X_[p]`, a notation for
{lean}`ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ`.

{docstring ι}

The weight space is not identified with $`\mathbb{Z}/(p-1)\mathbb{Z} \times \mathbb{Z}_p`.

# The definition
%%%
tag := "padic-definition"
%%%

Let $`f \in \mathbb{Q}_p\llbracket X\rrbracket`. A _presentation_ of $`f` is a sequence of
integers $`(w_i)_{i \in \mathbb{N}}` together with rational modular forms
$`F_i \in M_{w_i}(\mathbb{Q})` such that the coefficients of $`F_i`, viewed in $`\mathbb{Q}_p`,
converge to those of $`f` uniformly in $`n`. The power series $`f` is a _$`p`-adic modular form_
if it has a presentation.

{docstring pAdicModularFormStruct}

{docstring PowerSeries.isPAdicModularForm}

{docstring PAdicModularForms}

We denote by {name EisensteinSeries.E₂PAdic}`E₂PAdic`, {name EisensteinSeries.E₄PAdic}`E₄PAdic`
and {name EisensteinSeries.E₆PAdic}`E₆PAdic` the images of $`E_2`, $`E_4` and $`E_6` in
$`\mathbb{Q}_p\llbracket X\rrbracket`.

# The valuation
%%%
tag := "padic-valuation"
%%%

The valuation of $`f = \sum a_n X^n \in \mathbb{Q}_p\llbracket X\rrbracket` is
$`v(f) = \inf_n v_p(a_n) \in \overline{\mathbb{Z}}`.

{docstring PowerSeries.Padic.coeffPadicValuation}

{docstring PowerSeries.Padic.v}

Here $`\overline{\mathbb{Z}} = \{-\infty\} \cup \mathbb{Z} \cup \{+\infty\}` is
{name EInt}`EInt`, defined as {lean}`WithBotTop ℤ`. We have $`v(f) \neq -\infty` if $`f` is the
image of a rational modular form
({name PowerSeries.rationalQExpansion_v_ne_bot}`rationalQExpansion_v_ne_bot`).

# Théorème 1
%%%
tag := "theoreme-1"
%%%

Let $`p \geq 5` and $`m \geq 1`. Let $`f` and $`f'` be rational modular forms of weights $`k` and
$`k'`, with $`f \neq 0` and $`v(f - f') \geq v(f) + m`. Then $`k \equiv k' \pmod{(p-1)p^{m-1}}`.

{docstring ModularForm.natCast_eq_of_v_sub_le_pow}

Let $`p \geq 5` and $`m \geq 1`. Let $`f` and $`f'` be $`p`-integral modular forms of weights
$`k` and $`k'`, congruent modulo $`p^m`, such that the reduction of $`f` modulo $`p` is nonzero.
Then $`k \equiv k' \pmod{(p-1)p^{m-1}}`.

{docstring ModularForm.natCast_eq_of_map_toZModPow_eq}

The case $`m = 1` is {name ModularForm.natCast_eq_of_v_sub_le}`natCast_eq_of_v_sub_le`, together
with {name ModularForm.natCast_eq_of_map_toZMod_eq}`natCast_eq_of_map_toZMod_eq` and
{name ModularForm.natCast_eq_of_v_eq_zero}`natCast_eq_of_v_eq_zero`.

# Théorème 2 and the weight
%%%
tag := "theoreme-2"
%%%

Let $`p \geq 5` and let $`f \neq 0` be a $`p`-adic modular form. For every presentation
$`(w_i, F_i)` of $`f` the sequence $`(\iota(w_i))` converges in $`\mathcal{X}`, and its limit does
not depend on the presentation.
From here on, the hypothesis $`p \geq 5` is the instance argument `[Fact (5 ≤ p)]`.

{docstring w_tendsto}

{docstring limit_unique}

Let $`p \geq 5`. The _weight_ of a $`p`-adic modular form $`f \neq 0` is the limit of
$`(\iota(w_i))` for a presentation $`(w_i, F_i)` of $`f`. The weight of $`0` is $`\iota(0)`.

{docstring w}

The presentation and the limit are chosen with the axiom of choice.
