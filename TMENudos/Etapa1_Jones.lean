import TMENudos.Etapa1_R2
import TMENudos.Etapa1_Puente
import TMENudos.Etapa1_GaussWord

/-!
# Etapa 1: del corchete al polinomio de Jones invariante sobre `GDiag`

Writhe de un diagrama abstracto, su comportamiento bajo isomorfismo, R1 y R2, y el Jones
`(-A³)^(-writhe) · ⟨D⟩`. Puente con `Word.writhe` / `Word.jones` del spike.
R3 se añade después: solo hace falta `writhe_tri` (mismo writhe en las dos caras) y
`jones_tri` sigue el patrón de `jones_r2` (ver `jones_of_bracket`).
-/

namespace TMENudos.Invariancia

namespace GDiag

variable {ι ι' : Type} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']

/-- Writhe: suma de `+1`/`-1` según el signo de cada cruce. -/
def writhe (D : GDiag ι) : ℤ := ∑ x : D.Cross, if D.sign x.1 then (1 : ℤ) else -1

theorem writhe_map (D : GDiag ι) (e : ι ≃ ι') : (D.map e).writhe = D.writhe := by
  unfold writhe
  refine Fintype.sum_equiv (crossEquiv D e) _ _ ?_
  intro x
  rfl

section Moves

variable (D : GDiag ι)

theorem writhe_r1 (e : ι) (o1 s : Bool) :
    (r1 D e o1 s).writhe = D.writhe + (if s then 1 else -1) := by
  unfold writhe
  rw [Fintype.sum_equiv (r1Cross D e o1 s) _
    (fun w => Sum.elim (fun x : D.Cross => if D.sign x.1 then (1 : ℤ) else -1)
      (fun _ => if s then (1 : ℤ) else -1) w)]
  · rw [Fintype.sum_sum_type]
    simp
  · rintro ⟨z, hz⟩
    rcases z with i | b <;> rfl

theorem writhe_r1F (o1 s : Bool) :
    (r1F D o1 s).writhe = D.writhe + (if s then 1 else -1) := by
  unfold writhe
  rw [Fintype.sum_equiv (r1FCross D o1 s) _
    (fun w => Sum.elim (fun x : D.Cross => if D.sign x.1 then (1 : ℤ) else -1)
      (fun _ => if s then (1 : ℤ) else -1) w)]
  · rw [Fintype.sum_sum_type]
    simp
  · rintro ⟨z, hz⟩
    rcases z with i | b <;> rfl

theorem writhe_r2 (e f : ι) (hef : e ≠ f) (ov par s : Bool) :
    (r2 D e f hef ov par s).writhe = D.writhe := by
  unfold writhe
  rw [Fintype.sum_equiv (r2Cross D e f hef ov par s) _
    (fun w => Sum.elim (fun x : D.Cross => if D.sign x.1 then (1 : ℤ) else -1)
      (fun c : Bool => if xor s c then (1 : ℤ) else -1) w)]
  · rw [Fintype.sum_sum_type]
    cases s <;> simp
  · rintro ⟨z, hz⟩
    rcases z with i | ⟨c, k⟩ <;> rfl

end Moves

/-- Polinomio de Jones: `(-A³)^{-w} ⟨D⟩`. -/
noncomputable def jones {K : Type*} [Field K] (A : K) (D : GDiag ι) : K :=
  (-(A ^ 3)) ^ (-D.writhe) * D.bracket A

section Invariance

variable {K : Type*} [Field K] (A : K)

/-- Si el writhe es igual y el corchete es igual, el Jones es igual (patrón para R2, R3). -/
theorem jones_of_bracket {D : GDiag ι}
    (D'' : GDiag ι') (hw : D''.writhe = D.writhe) (hb : D''.bracket A = D.bracket A) :
    D''.jones A = D.jones A := by
  unfold jones
  rw [hw, hb]

theorem jones_map (D : GDiag ι) (e : ι ≃ ι') : (D.map e).jones A = D.jones A :=
  jones_of_bracket A (D := D) (D.map e) (writhe_map D e) (bracket_map A D e)

theorem jones_r2 (hA : A ≠ 0) (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool) :
    (r2 D e f hef ov par s).jones A = D.jones A :=
  jones_of_bracket A (D := D) _ (writhe_r2 D e f hef ov par s) (bracket_r2 D e f hef ov s A hA par)

/-- El factor de un rizo se cancela con el cambio de writhe. -/
theorem jones_kink_factor (hA : A ≠ 0) (s : Bool) (w : ℤ) (B : K) :
    (-(A ^ 3)) ^ (-(w + (if s then 1 else -1))) * ((if s then -A ^ 3 else -A⁻¹ ^ 3) * B) =
      (-(A ^ 3)) ^ (-w) * B := by
  have hu : -(A ^ 3) ≠ 0 := neg_ne_zero.2 (pow_ne_zero 3 hA)
  cases s
  · have h : -A⁻¹ ^ 3 = (-(A ^ 3))⁻¹ := by rw [inv_neg, inv_pow]
    have e1 : -(w + -1) = -w + 1 := by ring
    simp only [Bool.false_eq_true, if_false, h, e1, zpow_add₀ hu, zpow_one]
    field_simp
  · have e1 : -(w + 1) = -w + -1 := by ring
    simp only [if_true, e1, zpow_add₀ hu, zpow_neg_one]
    field_simp

theorem jones_r1 (hA : A ≠ 0) [Nonempty ι] (D : GDiag ι) (e : ι) (o1 s : Bool) :
    (r1 D e o1 s).jones A = D.jones A := by
  unfold jones
  rw [writhe_r1, bracket_r1 D e o1 s A hA]
  exact jones_kink_factor A hA s _ _

theorem jones_r1F (hA : A ≠ 0) (D : GDiag ι) (hfree : 1 ≤ D.free) (o1 s : Bool) :
    (r1F D o1 s).jones A = D.jones A := by
  unfold jones
  rw [writhe_r1F, bracket_r1_free D o1 s A hA hfree]
  exact jones_kink_factor A hA s _ _

end Invariance

end GDiag

end TMENudos.Invariancia

/-! ### Puente con el spike -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia

/-- La suma de una lista filtrada es la suma con ceros en los descartados. -/
theorem sum_filter_map (w : Word) (g : Letter → ℤ) :
    ((w.filter (·.over)).map g).sum = (w.map fun l => if l.over then g l else 0).sum := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    by_cases h : a.over = true
    · simp [h, ih]
    · simp [h, ih]

/-- El writhe abstracto del diagrama de una palabra es el `Word.writhe` (suma sobre las letras
superiores; los cruces de `ofWordP` son las posiciones con `over = true`). -/
theorem writhe_ofWordP {w : Word} (h : WfP w) : (ofWordP w h).writhe = Word.writhe w := by
  unfold GDiag.writhe Word.writhe
  rw [sum_filter_map w (fun l => if l.pos then (1 : ℤ) else -1),
    ← Fin.sum_univ_fun_getElem w]
  change (∑ x : {i : Fin w.length // w[i.1].over = true},
      if w[x.1.1].pos then (1 : ℤ) else -1) = _
  have := Finset.sum_subtype (Finset.univ.filter fun i : Fin w.length => w[i.1].over = true)
    (p := fun i : Fin w.length => w[i.1].over = true) (F := inferInstance) (by simp)
    (fun i : Fin w.length => if w[i.1].pos then (1 : ℤ) else -1)
  rw [← this, Finset.sum_filter]

theorem writhe_ofWord (w : Word) (hw : Word.wf w = true) :
    (ofWord w hw).writhe = Word.writhe w :=
  writhe_ofWordP _

/-- **Jones abstracto = Jones computable** de la palabra. -/
theorem jones_ofWord (w : Word) (hw : Word.wf w = true) {K : Type*} [Field K] (A : K) :
    (ofWord w hw).jones A = Word.jones A w := by
  unfold GDiag.jones Word.jones
  rw [writhe_ofWord, bracket_ofWord]

theorem writhe_trefoil : Word.writhe trefoil = 3 := by decide

theorem writhe_swap_trefoil : Word.writhe (Word.swap trefoil) = -3 := by decide

/-- **Jones del trébol derecho**: `t + t³ - t⁴` con `t = A⁻⁴`. -/
theorem jones_ofWord_trefoil {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    (ofWord trefoil wf_trefoil).jones A = A⁻¹ ^ 4 + A⁻¹ ^ 12 - A⁻¹ ^ 16 := by
  unfold GDiag.jones
  rw [writhe_ofWord, writhe_trefoil, bracket_ofWord_trefoil A hA]
  have : (-(3 : ℤ)) = -((3 : ℕ) : ℤ) := by norm_num
  rw [this, zpow_neg, zpow_natCast]
  field_simp
  ring

/-- **Jones del trébol izquierdo**: el mismo polinomio con `A ↔ A⁻¹`. -/
theorem jones_ofWord_swap_trefoil {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    (ofWord (Word.swap trefoil) wf_swap_trefoil).jones A = A ^ 4 + A ^ 12 - A ^ 16 := by
  unfold GDiag.jones
  rw [writhe_ofWord, writhe_swap_trefoil, bracket_ofWord_swap_trefoil A hA]
  have : (-(-3 : ℤ)) = ((3 : ℕ) : ℤ) := by norm_num
  rw [this, zpow_natCast]
  field_simp
  ring

#print axioms TMENudos.Invariancia.GDiag.jones_map
#print axioms TMENudos.Invariancia.GDiag.jones_r1
#print axioms TMENudos.Invariancia.GDiag.jones_r1F
#print axioms TMENudos.Invariancia.GDiag.jones_r2
#print axioms writhe_ofWord
#print axioms jones_ofWord
#print axioms jones_ofWord_trefoil
#print axioms jones_ofWord_swap_trefoil

end TMENudos.Puente
