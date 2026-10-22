import VersoManual
import Doc.References
import Doc.TitleMath
import Doc.Introduction
import Doc.Preliminaries
import Doc.Rational
import Doc.PLocalInt
import Doc.ModP
import Doc.PAdic

open Verso.Genre Manual
open Doc

set_option pp.rawOnError true

#doc (Manual) "{tight}[$`p`-adic modular forms in Lean]" =>
%%%
authors := ["Riccardo Brasca"]
%%%

{include 1 Doc.Introduction}

{include 1 Doc.Preliminaries}

{include 1 Doc.Rational}

{include 1 Doc.PLocalInt}

{include 1 Doc.ModP}

{include 1 Doc.PAdic}
