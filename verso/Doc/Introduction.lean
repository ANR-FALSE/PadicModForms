import VersoManual
import PadicModForms
import Doc.References

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Doc

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
%%%

Serre's $`p`-adic modular forms {citep serre73}[] are limits of classical modular forms of level
one with rational coefficients. The limit is a limit of $`q`-expansions: a $`p`-adic modular form
is a power series $`f = \sum a_n q^n` with $`a_n \in \mathbb{Q}_p` for which there are classical
forms $`f_i = \sum a_{i,n} q^n` with $`a_{i,n} \in \mathbb{Q}` and $`a_{i,n} \to a_n`
$`p`-adically, uniformly in $`n`. No function on the upper half plane is attached to $`f`, and
nothing is required of the weights of the $`f_i`; that they converge, in the weight space
$`\mathcal{X} = \operatorname{Hom}_{\mathrm{cont}}(\mathbb{Z}_p^\times, \mathbb{Z}_p^\times)`,
to a weight of $`f` is Serre's Théorème 2, a consequence of his Théorème 1 on the weights of
congruent classical forms.

The project aims at formalizing this theory, from the definition through weight space, Eisenstein
families, the $`p`-adic zeta function and $`\Lambda`-adic forms, up to the construction of the
eigenvariety, including classicality results.

Our starting point is the following way of thinking about modular forms: _a modular form is a
power series_. A modular form is an element of a ring of formal power series
$`R\llbracket X\rrbracket` satisfying a predicate, and this makes it possible to consider various
coefficient rings, namely

$$`\mathbb{Q}, \qquad \mathbb{Z}_{(p)}, \qquad \mathbb{F}_p, \qquad \mathbb{Q}_p,`

where the forms over $`\mathbb{Q}_p` are the _$`p`-adic modular forms_. The analytic modular forms
of Mathlib (functions on the upper half plane with a transformation law) appear only once, at the
very start, in the definition over $`\mathbb{Q}`: a rational power series is a modular form when
it is the $`q`-expansion of a complex modular form. Each later layer is defined by lifting or
reducing to the previous one, so that results can be transported from one coefficient ring to
another.

# Naming conventions

The same mathematical object appears once per coefficient ring, with a suffix naming the ring:
the Eisenstein series $`E_2` is {name}`EisensteinSeries.E₂Rat` over $`\mathbb{Q}`,
{name}`EisensteinSeries.E₂_int` over $`\mathbb{Z}_{(p)}`, {name}`EisensteinSeries.E₂ModP` over
$`\mathbb{F}_p` and {name}`EisensteinSeries.E₂PAdic` over $`\mathbb{Q}_p`, and similarly for
$`E_4`, $`E_6` and the evaluation maps {name}`ModularForm.evalE₄E₆Rat`,
{name}`ModularForm.evalE₄E₆Int`, {name}`ModularForm.evalE₄E₆ModP`. Serre's letters $`P`, $`Q`,
$`R` for $`E_2`, $`E_4`, $`E_6` are only used in docstrings, to connect with the paper. The Hasse
invariant is {name}`ModularForm.hasseInvPoly`, and multiplying a polynomial by a power of it is
called _raising the weight_. Polynomials homogeneous for the grading by modular weight are called
weighted homogeneous, after Mathlib's {name}`MvPolynomial.IsWeightedHomogeneous`. A prime is a
natural number $`p`; the hypothesis $`p \geq 5` is written `hp : 5 ≤ p` and is explicit in every
statement that needs it.
