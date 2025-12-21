import TMENudos.Basic
import TMENudos.Schubert

/-!
# Puente entre Nudos Racionales y Nudos Abstractos

Este archivo conecta las definiciones de nudos racionales (basadas en aritmética modular)
con la teoría general de nudos (basada en diagramas y cocientes).
-/

namespace TMENudos.Bridge

open TMENudos.SchubertTheorems
open TMENudos.Reidemeister.ReidemeisterMoves

/--
**Axioma de Construcción de Diagramas**

Existe un procedimiento canónico para convertir una configuración racional
(definida por pares de puntos en un círculo) en un diagrama de nudo estándar.
-/
axiom rational_to_diagram {n : ℕ} (rc : RationalConfiguration n) : Diagram

/--
**Inyección al Espacio de Nudos**

Todo nudo racional corresponde a un nudo abstracto bien definido (su clase de equivalencia).
-/
noncomputable def rational_to_knot {n : ℕ} (rc : RationalConfiguration n) : Knot :=
  Quotient.mk DiagramSetoid (rational_to_diagram rc)

/--
**Teorema de Consistencia (Axiomático)**

Si dos configuraciones racionales son equivalentes bajo movimientos de nudos racionales
(que aún no están formalizados como tales en Basic.lean, pero se asumen en la teoría),
entonces sus nudos abstractos correspondientes son isotópicos.
-/
axiom rational_equivalence_preserves_isotopy {n m : ℕ}
  {rc₁ : RationalConfiguration n} {rc₂ : RationalConfiguration m} :
  HEq rc₁ rc₂ → rational_to_knot rc₁ ≅ rational_to_knot rc₂

end TMENudos.Bridge
