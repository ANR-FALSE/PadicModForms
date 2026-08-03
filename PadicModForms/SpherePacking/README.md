# Vendored code from Sphere-Packing-Lean

This directory contains files copied from the **Sphere-Packing-Lean** project:

* Source: <https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean>
* Commit: `d5e6f1181c804a87f667e6f2fd0870e47f63de1a`
* Licence: Apache 2.0 (a verbatim copy is in `LICENSE` next to this file)

The original copyright of the Sphere-Packing-Lean authors is retained.  This project is also
Apache 2.0, so the licences are compatible; nothing here is claimed as original work.

## Bridge.lean — the only file the project imports

`Bridge.lean` is the contract.  It imports the vendored material **privately**, so none of it is
visible downstream (verified: `ramanujan_E₂`, `serre_D`, `weight_four_one_dimensional` are all
unreachable from a module that imports `Bridge`).  Its three statements mention only Mathlib
notions — `Derivative.normalizedDerivOfComplex`, `EisensteinSeries.E2`, `ModularForm.E₄`,
`ModularForm.E₆` — because the vendored definitions turn out to be *definitionally equal* to the
Mathlib ones (`D = Derivative.normalizedDerivOfComplex`, `serre_D k = Derivative.serreDerivative k`
and the coercions of `E₄`, `E₆` agree, all by `rfl`).

So when Mathlib acquires Ramanujan's identities, reproving `Bridge.lean` and deleting everything
else in this directory is the whole migration.  Nothing outside this directory refers to
Sphere-Packing-Lean.

**No file outside `Bridge.lean` may be imported from the rest of the project.**

## Why it is here

We need Ramanujan's differential identities

```
12 Θ E₂ = E₂² - E₄,   12 Θ E₄ = 4 E₂E₄ - 4 E₆,   12 Θ E₆ = 6 E₂E₆ - 6 E₄²
```

as an input to the mod-`p` theory (see `notes/kernel_eval_mod_p.tex`, §9).  Sphere-Packing-Lean
already proves them, `sorry`-free, via the Serre derivative and the fact that `M₄`, `M₆`, `M₈`
are one-dimensional.  Rather than redo that analysis we vendor it.  The results we are after are

* `ramanujan_E₂`, `ramanujan_E₄`, `ramanujan_E₆` — the `D`-forms;
* `ramanujan_E₂'`, `ramanujan_E₄'`, `ramanujan_E₆'` — the Serre-derivative forms;
* `serre_D_ModularForm` — the Serre derivative of a modular form is a modular form
  (still a `TODO` in Mathlib);
* `weight_four_one_dimensional`, `weight_six_one_dimensional`, `weight_eight_one_dimensional`.

All of these are `sorry`-free; this is checked by `#print axioms` (only `propext`,
`Classical.choice`, `Quot.sound`).

**Nothing in this directory should be edited to add new mathematics.**  Anything we prove
ourselves belongs outside it.

## Adaptations made when vendoring

Upstream targets Lean `v4.32.0`; this project is on `v4.33.0-rc1`, so a few proofs needed
repair.  The complete list of changes:

1. **Module prefix.**  `SpherePacking.*` renamed to `PadicModForms.SpherePacking.*` throughout
   (mechanical, applies to every file).
2. **Attribution header** prepended to each file.
3. `ModularForms/SlashActionAuxil.lean`:
   * the `Gamma 2` elements `α`, `β`, `negI` and the lemmas about them were removed — unused
     downstream, and their `by simp`/`decide` proofs no longer compile;
   * the `slashaction_generators*` section (≈260 lines proving `SL(2, ℤ)` and `Γ 2` are generated
     by `{S, T, -I}` and `{α, β, -I}`) was removed — entirely unused downstream.  It existed to
     derive the slash action of `E₂` from generators; current Mathlib proves
     `EisensteinSeries.E2_slash_action` for every `γ` directly;
   * `modular_slash_S_apply` and `modular_slash_T_apply` (the two lemmas that *are* used) were
     reproved using Mathlib's `ModularGroup.denom_S` and `SpecialLinearGroup.map_apply_coe`.
4. Each vendored file carries `set_option linter.mathlibStandardSet false` after its module
   docstring, so Mathlib's style linters do not fire on third-party proofs.  Upstream already
   disables `linter.flexible` project-wide in its `lakefile.toml`, and Mathlib forbids scoping
   that particular option per file, so the whole set is switched off instead.  `Bridge.lean` is
   *not* exempted: it is our code and is fully linted.
5. `ModularForms/DimensionFormulas.lean`: `dim_gen_cong_levels` was removed.  It was stated with
   a `sorry` upstream, is unused here, and none of the `weight_*_one_dimensional` lemmas depend
   on it.  With it gone this directory contains no `sorry`.

No other file required changes.

## Updating

Re-vendoring is a matter of re-copying the import closure of
`SpherePacking/ModularForms/RamanujanIdentities.lean` (20 files, including `meta import`s) and
reapplying the list above.
