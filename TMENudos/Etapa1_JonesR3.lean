import TMENudos.Etapa1_R3
import TMENudos.Etapa1_Jones

/-!
# Etapa 1: el Jones es invariante bajo R3

`writhe_tri`: las dos caras de R3 comparten los tres cruces nuevos (mismos signos `sgc c`),
luego tienen el mismo writhe; `jones_tri` sigue el patrón de `jones_r2` con `bracket_r3`.
-/

namespace TMENudos.Invariancia

namespace GDiag

variable {ι : Type} [DecidableEq ι] [Fintype ι]
  (D : GDiag ι) (e : Fin 3 → ι) (he : Function.Injective e) (o ovc sgc : Fin 3 → Bool)

/-- El writhe de `tri` es el de `D` más la suma local de los tres signos (independiente de `o`). -/
theorem writhe_tri :
    (tri D e he o ovc sgc).writhe =
      D.writhe + ∑ c : Fin 3, if sgc c then (1 : ℤ) else -1 := by
  unfold writhe
  rw [Fintype.sum_equiv (r3Cross D e he o ovc sgc) _
    (fun w => Sum.elim (fun x : D.Cross => if D.sign x.1 then (1 : ℤ) else -1)
      (fun c : Fin 3 => if sgc c then (1 : ℤ) else -1) w)]
  · rw [Fintype.sum_sum_type]
    rfl
  · rintro ⟨z, hz⟩
    rcases z with i | l
    · rfl
    · rfl

section Jones

variable {K : Type*} [Field K] (A : K)

/-- **Invariancia del polinomio de Jones bajo R3.** -/
theorem jones_tri (hA : A ≠ 0)
    (hv : R3.validR3 (o 0) (o 1) (o 2) (sgc 0) (sgc 1) (sgc 2) = true) :
    (tri D e he o ovc sgc).jones A = (tri D e he (fun i => !o i) ovc sgc).jones A :=
  jones_of_bracket A (D := tri D e he (fun i => !o i) ovc sgc) _
    (by rw [writhe_tri, writhe_tri]) (bracket_r3 D e he o ovc sgc A hA hv)

end Jones

end GDiag

end TMENudos.Invariancia

open TMENudos.Invariancia in
#print axioms GDiag.writhe_tri
open TMENudos.Invariancia in
#print axioms GDiag.jones_tri
