# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Formalization of p-adic modular forms in Lean 4 using mathlib, following Serre's approach. Part of the ANR FALSE effort. Currently at an early stage with core definitions and key theorems (with `sorry` placeholders).

## Build Commands

```bash
lake build              # Build the project
lake env lean <file>    # Check a single file
lake clean              # Clean build artifacts
lake update             # Update mathlib dependency
```

After updating mathlib or on a fresh clone, fetch cached oleans:
```bash
lake exe cache get
```

## Architecture

Single-library project (`PadicModForms`) depending on mathlib v4.28.0 / Lean 4.28.0.

- `PadicModForms.lean` — root import file
- `PadicModForms/Defs.lean` — core definitions: `pAdicModularFormStruct`, `PowerSeries.isPAdicModularForm`, p-adic weight space (`X_[p]`), weight function `w`, and key theorems `w_tendsto` and `limit_unique` (both currently `sorry`)

## Lean Options (from lakefile.toml)

- `relaxedAutoImplicit = false` — all variables must be explicitly declared
- `pp.unicode.fun = true` — uses `fun a ↦ b` notation
- `weak.linter.mathlibStandardSet = true` — mathlib linting conventions apply

## Conventions

This project follows mathlib conventions: naming, style, linting. Code imports `Mathlib` directly. The universe variable `p` is always a natural number with `[Fact p.Prime]`.
