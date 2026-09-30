import TMENudos.Schubert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# BORRADOR (2026-09-30): la Opción 1 del documento de diseño, compilada contra `Schubert.lean`

Este archivo NO forma parte de la biblioteca ni modifica `Schubert.lean`. Muestra el texto exacto
que se añadiría a la capa abstracta de `Schubert.lean` si el autor adopta la Opción 1, y comprueba
que con él `granny_distinct_from_square` se demuestra a partir de la especificación.

Los cuatro axiomas nuevos (`jones2` y su especificación) son:
* verdaderos para nudos reales (el Jones evaluado en A = 2 es multiplicativo, vale 1 en el nudo
  trivial y toma esos valores en el trébol derecho y el izquierdo);
* consistentes con los 34 axiomas de `Reidemeister`, `Schubert` y `Bridge`: ver
  `11_modelo_jones2.lean`, que extiende el modelo de consistencia con ellos;
* justificados por el trabajo de la rama `etapa1-spike-gauss`, que demuestra las mismas propiedades
  para los diagramas concretos (`Etapa1_Nudos.lean`). **La conexión entre el `Knot` abstracto y ese
  módulo concreto es lo que quedaría axiomático.**
-/

namespace TMENudos.SchubertTheorems.Borrador

open TMENudos.SchubertTheorems

/-- Polinomio de Jones evaluado en A = 2 (valor en ℚ). -/
axiom jones2 : Knot → ℚ

/-- Es multiplicativo bajo la suma conexa. -/
axiom jones2_connected_sum (K₁ K₂ : Knot) : jones2 (K₁ # K₂) = jones2 K₁ * jones2 K₂

/-- Vale 1 en el nudo trivial. -/
axiom jones2_unknot : jones2 unknot = 1

/-- Valor en el trébol (derecho): t + t³ - t⁴ con t = A⁻⁴ = 1/16. -/
axiom jones2_trefoil : jones2 trefoil = 4111 / 65536

/-- Valor en su imagen especular (el trébol izquierdo). -/
axiom jones2_mirror_trefoil : jones2 (mirror trefoil) = -61424

/-- El enunciado de `Schubert.lean` (`granny_distinct_from_square`), demostrado a partir de la
    especificación. -/
theorem granny_distinct_from_square_borrador : ¬(granny_knot ≅ square_knot) := by
  intro h
  have h' : granny_knot = square_knot := h
  unfold granny_knot square_knot at h'
  have := congrArg jones2 h'
  rw [jones2_connected_sum, jones2_connected_sum, jones2_trefoil, jones2_mirror_trefoil] at this
  linarith

#print axioms granny_distinct_from_square_borrador

end TMENudos.SchubertTheorems.Borrador
