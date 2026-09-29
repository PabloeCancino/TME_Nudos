/- PRUEBA HISTÓRICA (2026-09-29). Deriva `False` del axioma R1_inverse ORIGINAL (sin hipótesis): con n=0 y un movimiento que elimina un giro, el axioma exigía KnotConfig 1 = KnotConfig 0 (cardinalidades distintas). Este archivo YA NO COMPILA tras la corrección (commit df86e7b); eso es lo esperado y confirma que la contradicción quedó bloqueada. -/
import TMENudos.Reidemeister
open TMENudos.Reidemeister TMENudos.Reidemeister.ReidemeisterMoves

theorem inconsistent : False := by
  let K : KnotConfig 0 := ⟨fun x => x.elim0⟩
  let mv : R1Move := ⟨⟨0, 0⟩, .Positive, false⟩
  have h := R1_inverse K mv
  have ht := type_eq_of_heq h
  have h1 : KnotConfig 1 = KnotConfig 0 := ht
  let a : KnotConfig 1 := ⟨fun _ => ⟨0, 0, 0⟩⟩
  let b : KnotConfig 1 := ⟨fun _ => ⟨0, 0, 1⟩⟩
  have hab : a ≠ b := by
    intro e
    have := congrArg (fun k => (k.crossings 0).ratio_val) e
    simp [a, b] at this
  have hs : Subsingleton (KnotConfig 0) := ⟨fun x y => by
    cases x; cases y; congr; funext i; exact i.elim0⟩
  rw [← h1] at hs
  exact hab (hs.elim a b)
#print axioms inconsistent
