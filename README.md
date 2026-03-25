# *p*-adic modular forms in Lean

A Lean 4 project devoted to the formalization of *p*-adic modular forms in Lean, following Serre’s approach.

## Overview

This repository is part of a broader program on the formalization of modern number theory in Lean. Its immediate goal is to develop the basic theory of *p*-adic modular forms for GL₂/**Q**, with a particular emphasis on:

- the definition of *p*-adic modular forms as limits of classical modular forms in terms of their *q*-expansions;
- the construction of the weight space and the weight of a nonzero *p*-adic modular form;
- families of Eisenstein series over weight space;
- the definition and continuity of the *p*-adic zeta function;
- the first algebraic structures needed for later work on Hecke operators, Λ-adic modular forms, and Hida theory.

The project is intended to contribute reusable arithmetic infrastructure to `mathlib`, and to serve as a test case for the formalization of research-level number theory in Lean.

## The mathematics

In Serre’s point of view, a *p*-adic modular form is a power series
*f*(*q*) ∈ **Q**\_*p*⟦*q*⟧
which arises as the coefficientwise limit of a sequence of classical modular forms. One of the key facts is that, for a nonzero *f*, the corresponding sequence of classical weights converges in *p*-adic weight space. This makes it possible to attach a well-defined *p*-adic weight to *f*.

A central example is provided by Eisenstein series. Their Fourier coefficients interpolate in *p*-adic families, giving rise to a family over weight space whose constant term defines the *p*-adic zeta function. A major long-term objective is to formalize these constructions in sufficient generality to support later developments in *p*-adic *L*-functions and ordinary *p*-adic families.

## Project goals

The current direction of the repository includes the following steps.

### 1. Basic definitions

- Formalize *p*-adic modular forms as power series equipped with approximating sequences of classical modular forms.
- Relate these definitions to modular forms already present in `mathlib` via *q*-expansions.
- Develop the surrounding infrastructure for modular forms over rings such as **Q** and **Q**\_*p*.

### 2. Weight space

- Define the *p*-adic weight space as the space of continuous characters of **Z**\_*p*ˣ.
- Construct the natural map from integral weights to weight space.
- Prove that the weight attached to a nonzero *p*-adic modular form is well defined.

### 3. Eisenstein families and the *p*-adic zeta function

- Study Eisenstein series as a first source of nontrivial *p*-adic families.
- Formalize the continuity of their Fourier coefficients over weight space.
- Define the *p*-adic zeta function from the constant term of the Eisenstein family and prove its basic interpolation and continuity properties.

### 4. Toward Λ-adic forms and Hida theory

- Introduce the first objects needed for Λ-adic modular forms.
- Study Hecke operators, especially the *U*\_*p*-operator, through their action on power series.
- Build the algebraic prerequisites for later formal work on Hida families and ordinary Hecke algebras.

## Scope

This repository focuses on the Serre-style theory, which is currently much more accessible to formalization than the theory of overconvergent modular forms in the sense of Katz. In particular, the project emphasizes algebraic and analytic structures that can be developed within the present ecosystem of Lean and `mathlib`, while keeping in view more ambitious future directions in *p*-adic automorphic forms.

## Relation to other projects

`PadicModForms` is part of the broader ANR FALSE effort on formalizing arithmetic in Lean. It is also closely connected with ongoing developments in `mathlib`, especially around modular forms, *L*-functions, and arithmetic computation.

The long-term aim is not just to formalize isolated theorems, but to build a coherent and reusable library of arithmetic theories that can support future developments in number theory and arithmetic geometry.
