import Scripts.Templates.WalkN3
import Scripts.Templates.PrimeCongruent
import Scripts.Templates.Coxeter

/-!
Registry of templates known to `lake exe oeis-template`. Adding a new template means
adding a `Scripts/Templates/<Name>.lean` file that defines a `Template` value and
appending it to `templates` below.
-/

namespace Oeis.Template

/-- All available templates. -/
def templates : Array Template := #[WalkN3.template, PrimeCongruent.template, Coxeter.template]

/-- Looks a template up by (case-sensitive) name. -/
def findTemplate? (name : String) : Option Template :=
  templates.find? fun t => t.name == name

end Oeis.Template
