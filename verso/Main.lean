import VersoManual
import Doc

open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

/-- Generate the site. The stylesheet `theme.css` is read when the site is generated, so that
editing it does not require rebuilding the generator. -/
def main (options : List String) : IO UInt32 := do
  let css ← IO.FS.readFile "theme.css"
  let theme : CssFile := { filename := "theme.css", contents := ⟨css⟩ }
  manualMain (%doc Doc) (options := options)
    (config := { config with extraCssFiles := ({} : Std.HashSet CssFile).insert theme })
