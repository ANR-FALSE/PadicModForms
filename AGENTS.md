# AGENTS.md

These are the project instructions for coding agents working in this repository. `AGENTS.md` is the
single source of truth: Codex and other agents read it directly, and `CLAUDE.md` is a one-line
`@AGENTS.md` import so Claude Code reads the same text. Edit this file, never the pointer.

## Project

Formalization of *p*-adic modular forms in Lean 4 using mathlib, following Serre's approach. Part of
the ANR FALSE effort. See `README.md` for the mathematical program and long-term goals (weight
space, Eisenstein families, the *p*-adic zeta function, Λ-adic forms).

## Build Commands

```bash
lake exe cache get      # Fetch cached mathlib oleans (fresh clone / after `lake update`)
lake build              # Build the whole library
lake build PadicModForms.ModP.Hasse   # Build one module and its dependencies
lake env lean PadicModForms/ModP/Hasse.lean   # Check a single file
lake clean
```

There are no tests: correctness is the build. CI (`.github/workflows/lean_action_ci.yml`) runs
`lean-action` plus `docgen-action` on push to `master` and on PRs. Mathlib is pinned to `master` and
bumped by `leanprover-community/mathlib-update-action` (manual `workflow_dispatch`), which opens a PR
on success and an issue on failure.

Toolchain: `lean-toolchain` (currently `v4.35.0-rc2`) — mathlib's revision in `lake-manifest.json`
must match it, so never edit one without the other.

## Module system (important)

This project uses Lean's **module system**. **Every** `.lean` file begins with `module` before its
imports — the root `PadicModForms.lean` included, where all the imports are `public import`. There
are no legacy files, and a new file must not introduce one. Visibility is explicit:

- `public import Foo` — re-exported to downstream modules; `import Foo` — private to this file.
  Use a private `import` for anything needed only inside proofs (e.g. `Rational/Basic.lean` keeps
  `DimensionFormula` private).
- `@[expose] public section` after the module docstring is the default idiom: it makes subsequent
  declarations public *and* their bodies visible for defeq/`simp`. Files needing `noncomputable`
  everywhere use `@[expose] public noncomputable section`, or plain `noncomputable section` with
  `public` written per declaration (`Rational/Basic.lean`, `Rational/Graded.lean`,
  `Rational/Eisenstein.lean`).
- Inside a non-exposed section, mark each intended-public declaration (`public def`,
  `public theorem`). Helper lemmas are deliberately left non-`public`.

When adding a file, copy the header of a neighbouring file in the same directory rather than
inventing a layout, and add it to the root `PadicModForms.lean` as `public import` (alphabetical,
`«…»` quoting for names starting with a digit, e.g. `PadicModForms.ForMathlib.«38813»`).

Stragglers are found with

```bash
for f in $(find PadicModForms.lean PadicModForms -name '*.lean'); do
  grep -qE '^module\b' "$f" || echo "$f"
done
```

## Architecture

Everything is defined **through *q*-expansions**: a modular form is a *power series* satisfying a
predicate, not an analytic object. mathlib's analytic `ModularForm 𝒮ℒ k` appears only at the bottom
layer, as the witness in the defining predicate and via the scalar-extension map
`ModularForm.rationalModularFormToComplex`.

### The coefficient-ring tower

Each layer defines forms over a coefficient ring by requiring a lift/reduction to the layer below,
so results flow upward. Directories mirror the tower:

- `Rational/` — over `ℚ`. `PowerSeries.isModularForm k f` ⟺ `f` is the `q`-expansion of a level-one
  `ModularForm 𝒮ℒ k`. Base of everything.
- `pLocalInt/` — over `pLocalInt p`, the localization of `ℤ` at `p` (a `ValuationSubring ℚ`, defined
  in `ForMathlib/IntLocalization.lean`). `isPLocalIntModularForm` ⟺ scalar extension to `ℚ` is a
  rational modular form.
- `ModP/` — over `ZMod p`. `isModPModularForm` ⟺ the reduction (`pLocalInt.toZMod`) of some
  `p`-integral form.
- `PAdic/` — over `ℚ_[p]`. Serre's definition: a limit of rational forms
  (`pAdicModularFormStruct`), plus weight space.

### The pattern repeated at each layer

Recognizing it makes each directory fast to read:

1. A predicate `PowerSeries.isXModularForm k f`, with `zero_`/`one_`/`.neg`/`.smul`/`.mul`/`.add`
   closure lemmas (stated using `variable`-bound hypotheses plus `include`/`omit`).
2. A `Submodule` of weight-`k` forms (`rationalModularForms`, `pLocalIntModularForms p`,
   `modPModularForms p`) with a `mem_…` `@[simp]` lemma proved by `.rfl`.
3. A `SetLike.GradedMonoid` instance, making `⨁ i, …ModularForms i` a graded ring.
4. A `qExpansion` algebra hom out of that direct sum (`rationalQExpansionAlgHom`,
   `pLocalIntQExpansionAlgHom`) forgetting the weight, with `…_of` simp lemmas.
5. An evaluation map `evalE₄E₆…` from `MvPolynomial (Fin 2)` sending `X 0 ↦ E₄`, `X 1 ↦ E₆`
   (`Rational/Graded.lean`, `pLocalInt/Graded.lean`, `ModP/Graded.lean`), together with its
   injectivity — this is how the structure theorem for the graded ring is transported down the tower.

### Naming conventions for the standard forms

The same object appears at every layer with a layer suffix: `E₂Rat`/`E₄Rat`/`E₆Rat`/`ERat`/`GRat`
(ℚ), `E₂_int`/`E₄_int`/`E₆_int`/`E_int` (`pLocalInt`), `E₂ModP`/`E₄ModP`/`E₆ModP` (`ZMod p`), and
`E₂PAdic`/`E₄PAdic`/`E₆PAdic` (`ℚ_[p]`, `PAdic/Eisenstein.lean`). `E_int` takes the hypothesis
`p - 1 ∣ k`; `Discriminant.lean` and `Hasse.lean` assume `5 ≤ p`.

The Hasse polynomial is always called `hasseInvPoly`; do not introduce a single-letter alias.
Serre's letters `P`, `Q`, and `R` (for `E₂`, `E₄`, and `E₆`) are **never** used as identifiers:
always use the `E…` names above, and mention Serre's notation only in docstrings to connect the code
with the literature.

### Notable pieces

- `PAdic/Defs.lean` — weight space `X_[p] := ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ`, the integral-weight
  map `ι : ℤ → X_[p]`, `pAdicModularFormStruct` (a sequence of rational forms of weights `w i` whose
  coefficients converge uniformly), `PowerSeries.isPAdicModularForm`.
- `PAdic/Basic.lean` — the valuation `v : ℚ_[p]⟦X⟧ → EInt` (infimum of coefficient valuations) and
  its API; the bridge between `Tendsto` in `ℚ_[p]⟦X⟧` and `v (F i - f) → ⊤`.
- `PAdic/Weights/` — `Defs.lean` has `w_tendsto` and `limit_unique` (both `sorry`): the classical
  weights of a presentation converge in `X_[p]`, and the limit is independent of the presentation;
  `w` is defined from them via `Classical.choice`. `Congruence.lean` is the case `m = 1` of Serre's
  Théorème 1 and `CongruencePow.lean` the case `m ≥ 2`, whose informal proof is in
  `notes/serre_theorem_1_rest.tex`.
- `ModP/WeightZero.lean` — the degree-zero forms `𝓜⁰` and their normality, in the working form
  `mem_modPWeightZeroForms_of_isIntegral`. It is proved by the integral root theorem in the UFD
  `(ZMod p)[X₀, X₁]` (`ForMathlib/RationalRoot.lean`), **not** through the homogeneous localization
  `(ZMod p)[X₀, X₁][A⁻¹]`; `ForMathlib/HomogeneousLocalization.lean` is a leftover of that abandoned
  route and is imported by nothing.
- `ModP/Congruences.lean` → `ModP/Hasse.lean` — congruences `E_k ≡ 1 mod p^m` feeding the Hasse
  invariant as a weighted homogeneous polynomial `hasseInvPoly` of weight `p - 1` in `E₄`, `E₆`.
- `pLocalInt/Discriminant.lean` — `Δ` over `pLocalInt`, its unit-series form, division by `Δ`, and
  the structure theorem `pLocalIntModularFormsEquivMvPolynomial` for `p ≥ 5`.

### `ForMathlib/`

Staging area for material destined for mathlib; it must not depend on the rest of the project.
Several files carry a `-- should go to Mathlib.X` comment naming their target. `38813.lean`
backports mathlib PR #38813 and should be deleted once that PR lands upstream. Write these files to
mathlib's standards (full generality, complete docstrings), since they are meant to be upstreamed
verbatim.

## Lean options (from `lakefile.toml`)

`autoImplicit = false` and `relaxedAutoImplicit = false` (declare every variable, in a `variable`
block or in the signature), `pp.unicode.fun = true`, `maxSynthPendingDepth = 3`, and mathlib's own
linter set: `weak.linter.mathlibStandardSet`, `weak.linter.style.header`,
`weak.linter.checkInitImports`, `weak.linter.allScriptsDocumented`, `weak.linter.pythonStyle`,
`weak.linter.style.longFile = 1500`. The header linter enforces the copyright block and the module
docstring, and only sees files listed in `PadicModForms.lean`.

## Conventions

Full mathlib style: naming, copyright header, module docstring with `# Title` and (for substantial
files) a `## Main results` section, 100-column lines, `variable` blocks with `include`/`omit`.
`p : ℕ` always comes with `[Fact p.Prime]`.

Terminology — in docstrings, comments and identifiers alike, use the standard words:

- never *isobaric*: say **weighted homogeneous**, matching mathlib's `IsWeightedHomogeneous`;
- never *padding* / *to pad*: multiplying a weighted homogeneous polynomial by `hasseInvPoly hp ^ t`
  raises its weight by `t * (p - 1)` without changing its evaluation
  (`isWeightedHomogeneous_hasseInvPoly_pow_mul`, `evalE₄E₆ModP_hasseInvPoly_pow_mul`) — say
  **multiplying by a power of the Hasse invariant**, or *raising the weight*, and name the lemma.

In general, prefer a phrase that names the operation and the lemma that performs it to a coined
term the reader has to decode.

Proof style specific to this project:

- In proofs already written in tactic mode, use `ext` instead of applying `Subtype.ext` directly.
  Keep existing term-mode proofs in term mode. Prefer plain `ext` to `ext : n` whenever it works;
  specify a depth only when needed.
- Avoid `change`, and avoid proving goals by a bare `rfl`. A *named* lemma proved by `rfl` is fine
  when the definitional equality is a mathematically meaningful part of the API (as in the
  `mem_…ModularForms` simp lemmas).
- Never `unfold` a definition inside a proof. If a proof needs to see through a definition, state
  the unfolding once as a named `rfl` lemma next to the definition and `rw` with it — as
  `modPFiltration_def` does for `ModularForm.modPFiltration` in `ModP/Filtration.lean`. The lemma
  documents the definitional content and keeps the proofs stable if the definition is later
  restated.
