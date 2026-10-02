import Mathlib
import TMENudos.Etapa1_Invariancia
import TMENudos.SpanGenero
import TMENudos.Etapa1_Puente

/-!
# Cota por estados (etapa S2)

Combinatoria pura sobre el grafo de estados de un `GDiag`: cambiar una suavizacion cambia el
numero de lazos en a lo sumo 1; de ahi cotas de lazos y de exponente por estado.
-/

open SpanGenero Relation

section Generico

variable {ι : Type*}

/-- Las componentes conexas de `fromRel r` son las clases de la clausura de equivalencia. -/
theorem reachableSetoid_fromRel (r : ι → ι → Prop) :
    (SimpleGraph.fromRel r).reachableSetoid = EqvGen.setoid r := by
  ext a b
  change (SimpleGraph.fromRel r).Reachable a b ↔ EqvGen r a b
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact EqvGen.refl _
    | @cons u v _ h _ ih =>
      have h1 : EqvGen r u v := by
        rcases (SimpleGraph.fromRel_adj r u v).1 h with ⟨_, h2 | h2⟩
        · exact EqvGen.rel _ _ h2
        · exact EqvGen.symm _ _ (EqvGen.rel _ _ h2)
      exact EqvGen.trans _ _ _ h1 ih
  · intro h
    induction h with
    | rel x y h =>
      by_cases hxy : x = y
      · subst hxy; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj r x y).2 ⟨hxy, Or.inl h⟩)
    | refl x => exact SimpleGraph.Reachable.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Nucleo: si `s'` cabe en `s` mas una arista `p — q`, entonces `s` tiene a lo sumo una clase
mas que `s'`. -/
theorem ncs_le_of_join [Finite ι] {s s' : Setoid ι} (p q : ι)
    (h : ∀ x y, s' x y → (join1 s p q) x y) : ncs s ≤ ncs s' + 1 := by
  have h1 := ncs_le_join1 s p q
  have h2 : ncs (join1 s p q) ≤ ncs s' := ncs_le_of_le h
  omega

end Generico

namespace TMENudos.Invariancia

namespace GDiag

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Los lazos como numero de clases de la clausura de equivalencia de `rel σ`, mas los libres. -/
theorem lazos_eq (σ : D.Cross → Bool) :
    D.lazos σ = ncs (EqvGen.setoid (D.rel σ)) + D.free := by
  unfold GDiag.lazos
  rw [← reachableSetoid_fromRel (D.rel σ)]
  rfl

/-- Aristas de `rel σ` que no vienen del cruce `x`. -/
def relH (σ : D.Cross → Bool) (x : D.Cross) (a b : ι) : Prop :=
  ∃ y : D.Cross, y ≠ x ∧ D.smoothRel y.1 (σ y == D.sign y.1) a b

theorem rel_iff (σ : D.Cross → Bool) (x : D.Cross) (a b : ι) :
    D.rel σ a b ↔ D.relH σ x a b ∨ D.smoothRel x.1 (σ x == D.sign x.1) a b := by
  constructor
  · rintro ⟨y, hy⟩
    by_cases h : y = x
    · subst h; exact Or.inr hy
    · exact Or.inl ⟨y, h, hy⟩
  · rintro (⟨y, _, hy⟩ | h)
    · exact ⟨y, hy⟩
    · exact ⟨x, h⟩

theorem relH_congr {σ σ' : D.Cross → Bool} {x : D.Cross} (h : ∀ y, y ≠ x → σ' y = σ y)
    (a b : ι) : D.relH σ' x a b ↔ D.relH σ x a b := by
  constructor <;> rintro ⟨y, hy, hs⟩ <;> refine ⟨y, hy, ?_⟩
  · rwa [h y hy] at hs
  · rwa [← h y hy] at hs

theorem smoothRel_true (x a b : ι) :
    D.smoothRel x true a b ↔
      (a = D.prev x ∧ b = D.partner x) ∨ (a = D.prev (D.partner x) ∧ b = x) := by
  simp [GDiag.smoothRel]

theorem smoothRel_false (x a b : ι) :
    D.smoothRel x false a b ↔
      (a = D.prev x ∧ b = D.prev (D.partner x)) ∨ (a = x ∧ b = D.partner x) := by
  simp [GDiag.smoothRel]

/-- Paso orientada -> no orientada. -/
theorem ncs_step_ori {σ σ' : D.Cross → Bool} {x : D.Cross} (h : ∀ y, y ≠ x → σ' y = σ y)
    (ho : (σ x == D.sign x.1) = true) (ho' : (σ' x == D.sign x.1) = false) :
    ncs (EqvGen.setoid (D.rel σ)) ≤ ncs (EqvGen.setoid (D.rel σ')) + 1 := by
  set s := EqvGen.setoid (D.rel σ) with hs
  have hc : ∀ u v, D.rel σ u v → (join1 s (D.prev x.1) (D.prev (D.partner x.1))) u v :=
    fun u v hr => le_join1 _ _ _ u v (EqvGen.rel _ _ hr)
  have ecx : D.rel σ (D.prev (D.partner x.1)) x.1 := by
    refine (D.rel_iff σ x _ _).2 (Or.inr ?_)
    rw [ho, smoothRel_true]; exact Or.inr ⟨rfl, rfl⟩
  have eab : D.rel σ (D.prev x.1) (D.partner x.1) := by
    refine (D.rel_iff σ x _ _).2 (Or.inr ?_)
    rw [ho, smoothRel_true]; exact Or.inl ⟨rfl, rfl⟩
  refine ncs_le_of_join (D.prev x.1) (D.prev (D.partner x.1)) ?_
  intro u v huv
  refine eqvGen_le (s := join1 s (D.prev x.1) (D.prev (D.partner x.1))) ?_ huv
  intro u v hr
  rcases (D.rel_iff σ' x u v).1 hr with hH | hS
  · exact hc u v ((D.rel_iff σ x u v).2 (Or.inl ((D.relH_congr h u v).1 hH)))
  · rw [ho', smoothRel_false] at hS
    rcases hS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact join1_edge _ _ _
    · exact Setoid.trans' _ (Setoid.symm' _ (hc _ _ ecx))
        (Setoid.trans' _ (Setoid.symm' _ (join1_edge _ _ _)) (hc _ _ eab))

/-- Paso no orientada -> orientada. -/
theorem ncs_step_nori {σ σ' : D.Cross → Bool} {x : D.Cross} (h : ∀ y, y ≠ x → σ' y = σ y)
    (ho : (σ x == D.sign x.1) = false) (ho' : (σ' x == D.sign x.1) = true) :
    ncs (EqvGen.setoid (D.rel σ)) ≤ ncs (EqvGen.setoid (D.rel σ')) + 1 := by
  set s := EqvGen.setoid (D.rel σ) with hs
  have hc : ∀ u v, D.rel σ u v → (join1 s (D.prev x.1) (D.partner x.1)) u v :=
    fun u v hr => le_join1 _ _ _ u v (EqvGen.rel _ _ hr)
  have eac : D.rel σ (D.prev x.1) (D.prev (D.partner x.1)) := by
    refine (D.rel_iff σ x _ _).2 (Or.inr ?_)
    rw [ho, smoothRel_false]; exact Or.inl ⟨rfl, rfl⟩
  have exb : D.rel σ x.1 (D.partner x.1) := by
    refine (D.rel_iff σ x _ _).2 (Or.inr ?_)
    rw [ho, smoothRel_false]; exact Or.inr ⟨rfl, rfl⟩
  refine ncs_le_of_join (D.prev x.1) (D.partner x.1) ?_
  intro u v huv
  refine eqvGen_le (s := join1 s (D.prev x.1) (D.partner x.1)) ?_ huv
  intro u v hr
  rcases (D.rel_iff σ' x u v).1 hr with hH | hS
  · exact hc u v ((D.rel_iff σ x u v).2 (Or.inl ((D.relH_congr h u v).1 hH)))
  · rw [ho', smoothRel_true] at hS
    rcases hS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact join1_edge _ _ _
    · exact Setoid.trans' _ (Setoid.symm' _ (hc _ _ eac))
        (Setoid.trans' _ (join1_edge _ _ _) (Setoid.symm' _ (hc _ _ exb)))

/-- LEMA CLAVE: dos estados que difieren a lo sumo en el cruce `x` tienen lazos que difieren
en a lo sumo 1 (en este sentido). -/
theorem lazos_le_succ {σ σ' : D.Cross → Bool} {x : D.Cross} (h : ∀ y, y ≠ x → σ' y = σ y) :
    D.lazos σ ≤ D.lazos σ' + 1 := by
  rw [lazos_eq, lazos_eq]
  cases ho : (σ x == D.sign x.1) <;> cases ho' : (σ' x == D.sign x.1)
  · have : D.rel σ = D.rel σ' := by
      funext a b
      apply propext
      rw [D.rel_iff σ x, D.rel_iff σ' x, ho, ho', D.relH_congr h]
    rw [this]; omega
  · have := D.ncs_step_nori h ho ho'; omega
  · have := D.ncs_step_ori h ho ho'; omega
  · have : D.rel σ = D.rel σ' := by
      funext a b
      apply propext
      rw [D.rel_iff σ x, D.rel_iff σ' x, ho, ho', D.relH_congr h]
    rw [this]; omega

/-- Estado todo-A. -/
def allA : D.Cross → Bool := fun _ => true

/-- Estado todo-B. -/
def allB : D.Cross → Bool := fun _ => false

/-- Numero de suavizaciones B del estado. -/
def nB (σ : D.Cross → Bool) : ℕ := (Finset.univ.filter fun x => σ x = false).card

/-- Numero de suavizaciones A del estado. -/
def nA (σ : D.Cross → Bool) : ℕ := Fintype.card D.Cross - D.nB σ

/-- Exponente de `A` del peso del estado. -/
def expo (σ : D.Cross → Bool) : ℤ := (D.nA σ : ℤ) - (D.nB σ : ℤ)

theorem nB_le (σ : D.Cross → Bool) : D.nB σ ≤ Fintype.card D.Cross :=
  Finset.card_filter_le _ _

theorem nA_add_nB (σ : D.Cross → Bool) : D.nA σ + D.nB σ = Fintype.card D.Cross := by
  have := D.nB_le σ
  unfold nA; omega

theorem nA_eq (σ : D.Cross → Bool) :
    D.nA σ = (Finset.univ.filter fun x => σ x = true).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D.Cross))
    (fun x => σ x = true)
  have h2 : (Finset.univ.filter fun x => ¬ σ x = true) =
      Finset.univ.filter fun x => σ x = false := by simp
  rw [h2] at h
  have := D.nA_add_nB σ
  have hc : Fintype.card D.Cross = (Finset.univ : Finset D.Cross).card := by simp
  unfold nB at this
  omega

/-- Cota general por induccion sobre los cruces donde difieren. -/
theorem lazos_le_aux (τ : D.Cross → Bool) :
    ∀ (T : Finset D.Cross) (σ : D.Cross → Bool), (∀ x, x ∉ T → σ x = τ x) →
      D.lazos σ ≤ D.lazos τ + T.card := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro σ h
    have : σ = τ := funext fun x => h x (by simp)
    subst this; simp
  | insert x T hx ih =>
    intro σ h
    let σ1 : D.Cross → Bool := Function.update σ x (τ x)
    have h1 : ∀ y, y ∉ T → σ1 y = τ y := by
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp [σ1]
      · simp only [σ1, Function.update_of_ne hyx]
        exact h y (by simp [hyx, hy])
    have h2 : ∀ y, y ≠ x → σ1 y = σ y := fun y hy => by simp [σ1, Function.update_of_ne hy]
    have a := D.lazos_le_succ (σ := σ) (σ' := σ1) (x := x) (fun y hy => h2 y hy)
    have b := ih σ1 h1
    rw [Finset.card_insert_of_notMem hx]
    omega

/-- Cota por estados desde todo-A: `lazos σ ≤ lazos allA + nB σ`. -/
theorem lazos_le_allA (σ : D.Cross → Bool) : D.lazos σ ≤ D.lazos D.allA + D.nB σ := by
  have := D.lazos_le_aux D.allA (Finset.univ.filter fun x => σ x = false) σ (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simpa [allA] using hx)
  exact this

/-- Cota por estados desde todo-B: `lazos σ ≤ lazos allB + nA σ`. -/
theorem lazos_le_allB (σ : D.Cross → Bool) : D.lazos σ ≤ D.lazos D.allB + D.nA σ := by
  rw [D.nA_eq]
  exact D.lazos_le_aux D.allB (Finset.univ.filter fun x => σ x = true) σ (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simpa [allB] using hx)

/-- Cota superior del exponente del termino del estado. -/
theorem expo_upper (σ : D.Cross → Bool) :
    D.expo σ + 2 * ((D.lazos σ : ℤ) - 1) ≤
      (Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2 := by
  have h1 := D.lazos_le_allA σ
  have h2 := D.nA_add_nB σ
  unfold expo
  omega

/-- Cota inferior del exponente del termino del estado. -/
theorem expo_lower (σ : D.Cross → Bool) :
    -(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2 ≤
      D.expo σ - 2 * ((D.lazos σ : ℤ) - 1) := by
  have h1 := D.lazos_le_allB σ
  have h2 := D.nA_add_nB σ
  unfold expo
  omega

theorem expo_allA : D.expo D.allA = Fintype.card D.Cross := by
  have : D.nB D.allA = 0 := by simp [nB, allA]
  have h2 := D.nA_add_nB D.allA
  unfold expo
  omega

theorem expo_allB : D.expo D.allB = -(Fintype.card D.Cross : ℤ) := by
  have : D.nB D.allB = Fintype.card D.Cross := by simp [nB, allB]
  have h2 := D.nA_add_nB D.allB
  unfold expo
  omega

end GDiag

end TMENudos.Invariancia

/-! ### Sanidad con el trebol -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia

theorem wf_trefoil : Word.wf trefoil = true := by decide

/-- Para el trebol: `c = 3`, `s_A = 2`, `s_B = 3`; las cotas de exponente se cumplen. -/
theorem sanidad_trefoil :
    Fintype.card (ofWord trefoil wf_trefoil).Cross = 3 ∧
    (ofWord trefoil wf_trefoil).lazos (ofWord trefoil wf_trefoil).allA = 2 ∧
    (ofWord trefoil wf_trefoil).lazos (ofWord trefoil wf_trefoil).allB = 3 := by
  have hw := wfP_of_wf trefoil wf_trefoil
  refine ⟨?_, ?_, ?_⟩
  · change Fintype.card (ofWordP trefoil hw).Cross = 3
    rw [Fintype.card_congr (crossEquiv trefoil hw), Fintype.card_fin]
    decide +kernel
  · have e : Word.loops trefoil (List.ofFn fun _ : Fin (Word.crossings trefoil).length => true)
        = 2 := by decide +kernel
    exact (loops_eq hw (fun _ => true)).symm.trans e
  · have e : Word.loops trefoil (List.ofFn fun _ : Fin (Word.crossings trefoil).length => false)
        = 3 := by decide +kernel
    exact (loops_eq hw (fun _ => false)).symm.trans e

end TMENudos.Puente

#print axioms TMENudos.Invariancia.GDiag.lazos_le_succ
#print axioms TMENudos.Invariancia.GDiag.lazos_le_allA
#print axioms TMENudos.Invariancia.GDiag.lazos_le_allB
#print axioms TMENudos.Invariancia.GDiag.expo_upper
#print axioms TMENudos.Invariancia.GDiag.expo_lower
#print axioms TMENudos.Invariancia.GDiag.expo_allA
#print axioms TMENudos.Invariancia.GDiag.expo_allB
#print axioms TMENudos.Puente.sanidad_trefoil
