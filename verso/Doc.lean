import VersoManual
import Doc.References
import Doc.TitleMath
import Doc.Introduction
import Doc.Preliminaries
import Doc.Rational

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
