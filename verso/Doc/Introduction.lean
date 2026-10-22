import VersoManual
import PadicModForms
import Doc.References
import Doc.TitleMath

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Doc

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
%%%

Let $`p` be a prime number, often assumed to be at least $`5`. Serre's $`p`-adic modular forms
{citep serre73}[] are limits of classical modular forms of level one with rational coefficients.
The limit is a limit of $`q`-expansions: a $`p`-adic modular form is a power series
$`f = \sum a_n q^n` with $`a_n \in \mathbb{Q}_p` for which there are classical forms
$`f_i = \sum a_{i,n} q^n` with $`a_{i,n} \in \mathbb{Q}` and $`a_{i,n} \to a_n` $`p`-adically,
uniformly in $`n`. No function on the upper half plane is attached to $`f`, and nothing is
required of the weights of the $`f_i`; that they converge, in the weight space
$`\mathcal{X} = \operatorname{Hom}_{\mathrm{cont}}(\mathbb{Z}_p^\times, \mathbb{Z}_p^\times)`,
is Serre's Théorème 2, a consequence of his Théorème 1 on the weights of congruent classical
forms.

The project aims at formalizing this theory, from the definition through weight space, Eisenstein
families, the $`p`-adic zeta function and $`\Lambda`-adic forms, up to the construction of the
eigenvariety, including classicality results.

Our starting point is the following way of thinking about modular forms: _a modular form is a
power series_. A modular form is an element of a ring of formal power series
$`R\llbracket X\rrbracket` satisfying a predicate, and this makes it possible to consider various
coefficient rings, namely

$$`\mathbb{Q},\quad \mathbb{Z}_{(p)},\quad \mathbb{F}_p,\quad \mathbb{Q}_p,`

where the forms over $`\mathbb{Q}_p` are the _$`p`-adic modular forms_. The analytic modular forms
of Mathlib (functions on the upper half plane with a transformation law) appear only once, at the
very start, in the definition over $`\mathbb{Q}`: a rational power series is a modular form when
it is the $`q`-expansion of a complex modular form. All later layers are defined by lifting or
reducing to the previous one, so that results can be transported from one coefficient ring to
another.

# Normalization of the Eisenstein series

Let $`k \geq 4` be even. We use the two normalizations

$$`E_k = 1 - \frac{2k}{B_k} \sum_{n \geq 1} \sigma_{k-1}(n)\, q^n, \qquad G_k = -\frac{B_k}{2k} + \sum_{n \geq 1} \sigma_{k-1}(n)\, q^n,`

where $`B_k` is the $`k`-th Bernoulli number and $`\sigma_{k-1}(n) = \sum_{d \mid n} d^{k-1}`. We
have $`G_k = -\frac{B_k}{2k} E_k`, the constant term of $`E_k` is $`1`, the coefficient of $`q` in
$`G_k` is $`1`, and the constant term of $`G_k` is $`\frac12 \zeta(1-k)`. For instance
$`E_4 = 1 + 240 \sum \sigma_3(n) q^n` and $`E_6 = 1 - 504 \sum \sigma_5(n) q^n`. The series
$`E_2 = 1 - 24 \sum \sigma_1(n) q^n` is given by the formula for $`E_k` with $`k = 2`; it is not a
modular form.

# Naming conventions

The same mathematical object appears once per coefficient ring, with a suffix naming the ring: the
Eisenstein series $`E_2` is {name EisensteinSeries.E₂Rat}`E₂Rat` over $`\mathbb{Q}`,
{name EisensteinSeries.E₂_int}`E₂_int` over $`\mathbb{Z}_{(p)}`,
{name EisensteinSeries.E₂ModP}`E₂ModP` over $`\mathbb{F}_p` and
{name EisensteinSeries.E₂PAdic}`E₂PAdic` over $`\mathbb{Q}_p`, and similarly for $`E_4`, $`E_6` and
the evaluation maps {name ModularForm.evalE₄E₆Rat}`evalE₄E₆Rat`,
{name ModularForm.evalE₄E₆Int}`evalE₄E₆Int`, {name ModularForm.evalE₄E₆ModP}`evalE₄E₆ModP`. Serre's
letters $`P`, $`Q`, $`R` for $`E_2`, $`E_4`, $`E_6` are only used in docstrings, to connect with the
paper.
