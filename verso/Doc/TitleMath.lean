import VersoManual

/-!
Plain-text form of mathematics in titles.

Verso parses the title of `#doc` and of every `#` section as markup, so a title may contain
mathematics, as in `"$`p`-adic modular forms in Lean"`. It also needs a plain string for each
title: the HTML `<title>` element, the directory name of a chapter, section permalinks and
search-result breadcrumbs. That string is computed by `inline_to_string` conversions, and Verso
registers none for mathematics, so a title with a formula reads `<missing>` in those places.
The conversions below use the LaTeX source of the formula, so `$`p`-adic` becomes `p-adic`.
-/

open Lean Lean.Doc Verso.Doc Verso.Doc.Elab

namespace Doc

/-- Inline mathematics in a title is represented by its LaTeX source in plain text. -/
@[inline_to_string Lean.Doc.Parser.Inline.inline_math]
def inlineMathToString : InlineToString
  | _, stx => MathView.of ⟨stx⟩ |>.map (·.getVersoCode)

/-- Display mathematics in a title is represented by its LaTeX source in plain text. -/
@[inline_to_string Lean.Doc.Parser.Inline.display_math]
def displayMathToString : InlineToString
  | _, stx => MathView.of ⟨stx⟩ |>.map (·.getVersoCode)

/-- The plain-text form of a sequence of inlines joins them with spaces, so the title
`$`p`-adic modular forms` reads `p -adic modular forms`. The role `{tight}[...]` renders its
content unchanged, and the plain-text form of a role joins its content without separators. -/
@[role]
def tight : RoleExpanderOf Unit
  | (), contents => do ``(Verso.Doc.Inline.concat #[$(← contents.mapM elabInline),*])

end Doc
