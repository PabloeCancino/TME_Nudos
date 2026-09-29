/- PRUEBA HISTÓRICA (2026-09-29). Muestra que la primera corrección (hipótesis `move.add_twist = true ∨ 1 ≤ n`) seguía siendo inconsistente: con n=1, "eliminar y luego agregar" obligaba a un mapa inyectivo de un conjunto infinito (KnotConfig 1) a uno de un solo elemento (KnotConfig 0). YA NO COMPILA con la versión final (hipótesis `move.add_twist = true`, commit df86e7b). -/
import TMENudos.Reidemeister
open TMENudos.Reidemeister TMENudos.Reidemeister.ReidemeisterMoves

theorem inconsistent2 : False := by
  let a : KnotConfig 1 := ⟨fun _ => ⟨0, 0, 0⟩⟩
  let b : KnotConfig 1 := ⟨fun _ => ⟨0, 0, 1⟩⟩
  have hab : a ≠ b := by
    intro e
    have := congrArg (fun k => (k.crossings 0).ratio_val) e
    simp [a, b] at this
  let mv : R1Move := ⟨⟨0, 0⟩, .Positive, false⟩
  have h1 := R1_inverse a mv (Or.inr (by decide))
  have h2 := R1_inverse b mv (Or.inr (by decide))
  have e : apply_R1 a mv = apply_R1 b mv := by
    have hs : Subsingleton (KnotConfig (if mv.add_twist = true then 1 + 1 else 1 - 1)) :=
      (show Subsingleton (KnotConfig 0) from ⟨fun x y => by
        cases x; cases y; congr; funext i; exact i.elim0⟩)
    exact hs.elim _ _
  simp only at h1 h2
  rw [e] at h1
  exact hab (eq_of_heq (h1.symm.trans h2))
#print axioms inconsistent2
