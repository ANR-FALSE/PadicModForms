import VersoManual

open Verso.Genre.Manual

namespace Doc

/-- Serre's paper defining `p`-adic modular forms. -/
def serre73 : InProceedings where
  title := inlines!"Formes modulaires et fonctions zêta p-adiques"
  authors := #[inlines!"Jean-Pierre Serre"]
  year := 1973
  booktitle := inlines!"Modular functions of one variable III"
  series := some (inlines!"Lecture Notes in Mathematics 350, Springer")

/-- Swinnerton-Dyer's paper on congruences for coefficients of modular forms. -/
def swinnertonDyer73 : InProceedings where
  title := inlines!"On ℓ-adic representations and congruences for coefficients of modular forms"
  authors := #[inlines!"H. P. F. Swinnerton-Dyer"]
  year := 1973
  booktitle := inlines!"Modular functions of one variable III"
  series := some (inlines!"Lecture Notes in Mathematics 350, Springer")

end Doc
