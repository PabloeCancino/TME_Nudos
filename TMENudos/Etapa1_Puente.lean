import TMENudos.Etapa1_Invariancia
import TMENudos.Etapa1_GaussWord

/-!
# Etapa 1: puente entre palabras de Gauss computables y diagramas abstractos

`ofWord w hw : GDiag (Fin w.length)` y el teorema `bracket_ofWord`:
el corchete abstracto coincide con el corchete computable de `Etapa1_GaussWord`.
-/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia

/-! ### Buena formación en forma de proposición -/

theorem two_le_countP {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j →
      p l[i] = true → p l[j] = true → 2 ≤ l.countP p
  | [], i, j, hi, _, _, _, _ => absurd hi (by simp)
  | a :: t, 0, j + 1, _, hj, _, hpa, hpj => by
      have h1 : 0 < t.countP p := by
        rw [List.countP_pos_iff]
        exact ⟨t[j]'(by simpa using hj), List.getElem_mem _, by simpa using hpj⟩
      have : (a :: t).countP p = t.countP p + 1 := List.countP_cons_of_pos (by simpa using hpa)
      omega
  | a :: t, i + 1, j + 1, hi, hj, hij, hpi, hpj => by
      have := two_le_countP p t i j (by simpa using hi) (by simpa using hj) (by omega)
        (by simpa using hpi) (by simpa using hpj)
      have h2 : t.countP p ≤ (a :: t).countP p := by
        rw [List.countP_cons]; split <;> omega
      omega

/-- Buena formación: unicidad y existencia del otro paso, y coherencia de signos. -/
def WfP (w : Word) : Prop :=
  (∀ i j : Fin w.length, w[i.1].label = w[j.1].label → w[i.1].over = w[j.1].over → i = j) ∧
  (∀ i : Fin w.length, ∃ j : Fin w.length, w[j.1].label = w[i.1].label ∧
    w[j.1].over = !w[i.1].over) ∧
  (∀ a ∈ w, ∀ b ∈ w, a.label = b.label → a.pos = b.pos)

theorem wfP_of_wf (w : Word) (h : Word.wf w = true) : WfP w := by
  have h' : ∀ l ∈ w, (w.filter (fun k => k.label == l.label && k.over)).length = 1 ∧
      (w.filter (fun k => k.label == l.label && !k.over)).length = 1 ∧
      (∀ a ∈ w, a.label = l.label → a.pos = l.pos) := by
    intro l hl
    have := List.all_eq_true.1 h l hl
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff,
      bne_iff_ne, ne_eq, not_and, Decidable.not_not] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ i j : Fin w.length, i < j → w[i.1].label = w[j.1].label →
        w[i.1].over = w[j.1].over → False := by
      intro i j hij hl ho
      have hh := h' w[i.1] (List.getElem_mem _)
      cases hov : w[i.1].over
      · have h2 := hh.2.1
        rw [← List.countP_eq_length_filter] at h2
        have := two_le_countP (fun k => k.label == w[i.1].label && !k.over) w i j i.2 j.2 hij
          (by simp [hov]) (by simp [← hl, ← ho, hov])
        omega
      · have h2 := hh.1
        rw [← List.countP_eq_length_filter] at h2
        have := two_le_countP (fun k => k.label == w[i.1].label && k.over) w i j i.2 j.2 hij
          (by simp [hov]) (by simp [← hl, ← ho, hov])
        omega
    intro i j hl ho
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact (key i j h1 hl ho).elim
    · exact h1
    · exact (key j i h1 hl.symm ho.symm).elim
  · intro i
    have hh := h' w[i.1] (List.getElem_mem _)
    cases hov : w[i.1].over
    · have h2 := hh.1
      have : 0 < (w.filter (fun k => k.label == w[i.1].label && k.over)).length := by omega
      obtain ⟨k, hk⟩ := List.length_pos_iff_exists_mem.1 this
      obtain ⟨hkw, hkp⟩ := List.mem_filter.1 hk
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hkw
      refine ⟨⟨j, hj⟩, ?_, ?_⟩ <;> simp_all
    · have h2 := hh.2.1
      have : 0 < (w.filter (fun k => k.label == w[i.1].label && !k.over)).length := by omega
      obtain ⟨k, hk⟩ := List.length_pos_iff_exists_mem.1 this
      obtain ⟨hkw, hkp⟩ := List.mem_filter.1 hk
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hkw
      refine ⟨⟨j, hj⟩, ?_, ?_⟩ <;> simp_all
  · intro a ha b hb hab
    exact ((h' a ha).2.2 b hb hab.symm).symm

/-! ### Construcción del diagrama -/

section Build

variable (w : Word)

/-- Índice (sin cota) del otro paso por el mismo cruce. -/
def pIdx (i : Fin w.length) : ℕ :=
  w.findIdx (fun k => k.label == w[i.1].label && k.over == !w[i.1].over)

theorem pIdx_lt (h : WfP w) (i : Fin w.length) : pIdx w i < w.length := by
  obtain ⟨j, hj1, hj2⟩ := h.2.1 i
  exact List.findIdx_lt_length_of_exists ⟨w[j.1], List.getElem_mem _, by simp [hj1, hj2]⟩

/-- El otro paso por el mismo cruce. -/
def partnerF (h : WfP w) (i : Fin w.length) : Fin w.length := ⟨pIdx w i, pIdx_lt w h i⟩

theorem partnerF_spec (h : WfP w) (i : Fin w.length) :
    w[(partnerF w h i).1].label = w[i.1].label ∧ w[(partnerF w h i).1].over = !w[i.1].over := by
  have := @List.findIdx_getElem _
    (fun k : Letter => k.label == w[i.1].label && k.over == !w[i.1].over)
    w (pIdx_lt w h i)
  simpa using this

theorem partnerF_unique (h : WfP w) (i j : Fin w.length) (hl : w[j.1].label = w[i.1].label)
    (ho : w[j.1].over = !w[i.1].over) : j = partnerF w h i :=
  h.1 j _ (by rw [hl, (partnerF_spec w h i).1]) (by rw [ho, (partnerF_spec w h i).2])

/-- El diagrama abstracto de una palabra bien formada (versión con hipótesis en `Prop`). -/
def ofWordP (h : WfP w) : GDiag (Fin w.length) where
  next := finRotate _
  partner := partnerF w h
  ovr i := w[i.1].over
  sign i := w[i.1].pos
  partner_partner i := by
    have hs := partnerF_spec w h i
    exact (partnerF_unique w h (partnerF w h i) i hs.1.symm (by simp [hs.2])).symm
  partner_ne i := by
    intro hi
    have h3 := (partnerF_spec w h i).2
    have h4 : w[(partnerF w h i).1].over = w[i.1].over := by simp [hi]
    rw [h4] at h3
    cases hb : w[i.1].over <;> simp [hb] at h3
  ovr_partner i := (partnerF_spec w h i).2
  sign_partner i :=
    h.2.2 _ (List.getElem_mem _) _ (List.getElem_mem _) (partnerF_spec w h i).1
  free := if w.length = 0 then 1 else 0

/-- **El diagrama abstracto de una palabra de Gauss bien formada.** -/
def ofWord (hw : Word.wf w = true) : GDiag (Fin w.length) := ofWordP w (wfP_of_wf w hw)

end Build

/-! ### Corrección de la unión-búsqueda -/

section UF

theorem nodup_eraseDups (l : List ℕ) : l.eraseDups.Nodup := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, ih _ ?_ _ rfl⟩
      · simp [List.mem_eraseDups]
      · subst hn
        exact lt_of_le_of_lt (List.length_filter_le _ _) (by simp)

theorem eqv_of_false {α : Type} {i j : α} (h : Relation.EqvGen (fun _ _ : α => False) i j) :
    i = j := by
  induction h with
  | rel a b hab => exact hab.elim
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem eqv_add {α : Type} {r : α → α → Prop} {P Q : α} (h : Relation.EqvGen r P Q) {i j : α}
    (hij : Relation.EqvGen (fun a b => r a b ∨ (a = P ∧ b = Q)) i j) :
    Relation.EqvGen r i j := by
  induction hij with
  | rel a b hab =>
    rcases hab with hab | ⟨rfl, rfl⟩
    · exact Relation.EqvGen.rel _ _ hab
    · exact h
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem eqv_mono {α : Type} {r s : α → α → Prop} (hrs : ∀ a b, r a b → s a b) {i j : α}
    (h : Relation.EqvGen r i j) : Relation.EqvGen s i j := by
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (hrs _ _ hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Invariante de la unión-búsqueda: `comp` etiqueta las `m` aristas y dos aristas tienen la misma
etiqueta si y solo si están relacionadas por la clausura equivalencia de `r`. -/
def Inv (m : ℕ) (comp : List ℕ) (r : Fin m → Fin m → Prop) : Prop :=
  comp.length = m ∧ ∀ i j : Fin m, comp.getD i.1 0 = comp.getD j.1 0 ↔ Relation.EqvGen r i j

theorem inv_congr {m : ℕ} {comp : List ℕ} {r s : Fin m → Fin m → Prop}
    (hrs : ∀ a b, r a b ↔ s a b) (h : Inv m comp r) : Inv m comp s := by
  have : r = s := by
    funext a b
    exact propext (hrs a b)
  rw [← this]; exact h

theorem inv_range (m : ℕ) : Inv m (List.range m) (fun _ _ => False) := by
  refine ⟨by simp, fun i j => ?_⟩
  have h : ∀ k : Fin m, (List.range m).getD k.1 0 = k.1 := by
    intro k
    simp [List.getD_eq_getElem?_getD]
  rw [h, h]
  constructor
  · intro hij
    rw [Fin.ext hij]
    exact Relation.EqvGen.refl _
  · intro hij
    rw [eqv_of_false hij]

theorem gval {ca cb x : ℕ} :
    (if x == cb then ca else x) = if x = cb then ca else x := by simp

theorem getD_map_lt (comp : List ℕ) (g : ℕ → ℕ) (i : ℕ) (hi : i < comp.length) :
    (comp.map g).getD i 0 = g (comp.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem inv_unite {m : ℕ} {comp : List ℕ} {r : Fin m → Fin m → Prop} (hI : Inv m comp r)
    (P Q : Fin m) :
    Inv m (Word.unite comp (P.1, Q.1)) (fun a b => r a b ∨ (a = P ∧ b = Q)) := by
  obtain ⟨hlen, hI⟩ := hI
  unfold Word.unite
  simp only
  by_cases hc : comp.getD P.1 0 = comp.getD Q.1 0
  · have hb : (comp.getD P.1 0 == comp.getD Q.1 0) = true := by simpa using hc
    rw [if_pos hb]
    refine ⟨hlen, fun i j => ?_⟩
    rw [hI]
    exact ⟨fun h => eqv_mono (fun a b hab => Or.inl hab) h,
      fun h => eqv_add ((hI P Q).1 hc) h⟩
  · have hb : ¬ (comp.getD P.1 0 == comp.getD Q.1 0) = true := by simpa using hc
    rw [if_neg hb]
    refine ⟨by simpa using hlen, fun i j => ?_⟩
    set ca := comp.getD P.1 0 with hca
    set cb := comp.getD Q.1 0 with hcb
    have hg : ∀ k : Fin m, (comp.map (fun c => if c == cb then ca else c)).getD k.1 0 =
        (if comp.getD k.1 0 = cb then ca else comp.getD k.1 0) := by
      intro k
      rw [getD_map_lt comp _ k.1 (by omega)]
      exact gval
    rw [hg, hg]
    constructor
    · intro hij
      by_cases h1 : comp.getD i.1 0 = cb <;> by_cases h2 : comp.getD j.1 0 = cb
      · have : comp.getD i.1 0 = comp.getD j.1 0 := by rw [h1, h2]
        exact eqv_mono (fun a b hab => Or.inl hab) ((hI i j).1 this)
      · -- i ∈ cb, j ∈ ca
        have h3 : comp.getD j.1 0 = ca := by
          rw [if_pos h1, if_neg h2] at hij
          exact hij.symm
        have e1 : Relation.EqvGen r i Q := (hI i Q).1 (by rw [h1])
        have e2 : Relation.EqvGen r P j := (hI P j).1 (by rw [← hca, h3])
        refine Relation.EqvGen.trans _ _ _ (eqv_mono (fun a b hab => Or.inl hab) e1)
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)))
            (eqv_mono (fun a b hab => Or.inl hab) e2))
      · have h3 : comp.getD i.1 0 = ca := by
          rw [if_neg h1, if_pos h2] at hij
          exact hij
        have e1 : Relation.EqvGen r i P := (hI i P).1 (by rw [h3])
        have e2 : Relation.EqvGen r Q j := (hI Q j).1 (by rw [h2])
        refine Relation.EqvGen.trans _ _ _ (eqv_mono (fun a b hab => Or.inl hab) e1)
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩))
            (eqv_mono (fun a b hab => Or.inl hab) e2))
      · have : comp.getD i.1 0 = comp.getD j.1 0 := by
          rw [if_neg h1, if_neg h2] at hij
          exact hij
        exact eqv_mono (fun a b hab => Or.inl hab) ((hI i j).1 this)
    · intro hij
      induction hij with
      | rel a b hab =>
        rcases hab with hab | ⟨rfl, rfl⟩
        · rw [(hI a b).2 (Relation.EqvGen.rel _ _ hab)]
        · have hne : ¬ ca = cb := hc
          change (if ca = cb then ca else ca) = if cb = cb then ca else cb
          rw [if_neg hne, if_pos rfl]
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem inv_foldl {m : ℕ} : ∀ (Ps : List (ℕ × ℕ)) (comp : List ℕ) (r : Fin m → Fin m → Prop),
    Inv m comp r → (∀ p ∈ Ps, p.1 < m ∧ p.2 < m) →
    Inv m (Ps.foldl Word.unite comp) (fun a b => r a b ∨ (a.1, b.1) ∈ Ps)
  | [], comp, r, hI, _ => inv_congr (fun a b => by simp) hI
  | p :: Ps, comp, r, hI, hb => by
      have hp := hb p (by simp)
      have h1 := inv_unite hI ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩
      have h2 := inv_foldl Ps _ _ h1 (fun q hq => hb q (by simp [hq]))
      refine inv_congr (fun a b => ?_) h2
      simp only [List.mem_cons, Fin.ext_iff, Prod.ext_iff]
      tauto

theorem reach_iff_eqv {m : ℕ} (r : Fin m → Fin m → Prop) (a b : Fin m) :
    (SimpleGraph.fromRel r).Reachable a b ↔ Relation.EqvGen r a b := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Relation.EqvGen.refl _
    | cons hadj _ ih =>
      obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hadj
      · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h) ih
      · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)) ih
  · intro h
    induction h with
    | rel a b hab => exact reach_of_rel hab
    | refl a => exact SimpleGraph.Reachable.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem card_cc_eq_eraseDups {m : ℕ} {comp : List ℕ} {r : Fin m → Fin m → Prop}
    (hI : Inv m comp r) :
    Nat.card (SimpleGraph.fromRel r).ConnectedComponent = comp.eraseDups.length := by
  obtain ⟨hlen, hI⟩ := hI
  let F : (SimpleGraph.fromRel r).ConnectedComponent → ℕ :=
    Quot.lift (fun a : Fin m => comp.getD a.1 0)
      (fun a b h => (hI a b).2 ((reach_iff_eqv r a b).1 h))
  have hinj : Function.Injective F := by
    intro c1 c2
    induction c1 using SimpleGraph.ConnectedComponent.ind with
    | h a =>
      induction c2 using SimpleGraph.ConnectedComponent.ind with
      | h b =>
        intro h
        exact SimpleGraph.ConnectedComponent.eq.2 ((reach_iff_eqv r a b).2 ((hI a b).1 h))
  have hrange : Set.range F = ((comp.eraseDups.toFinset : Finset ℕ) : Set ℕ) := by
    ext v
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset,
      List.mem_eraseDups]
    constructor
    · rintro ⟨c, rfl⟩
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h a =>
        change comp.getD a.1 0 ∈ comp
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
    · intro hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      refine ⟨(SimpleGraph.fromRel r).connectedComponentMk ⟨i, by omega⟩, ?_⟩
      change comp.getD i 0 = comp[i]
      rw [List.getD_eq_getElem _ _ hi]
  rw [← Nat.card_range_of_injective hinj, hrange]
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_eraseDups comp)]

end UF

/-! ### Lemas auxiliares: estados, pesos, rotación -/

section Aux

theorem sum_flat {K : Type*} [AddCommMonoid K] (f : List Bool → K) (l : List (List Bool)) :
    (List.map f (l.flatMap fun s => [true :: s, false :: s])).sum =
      (l.map fun s => f (true :: s) + f (false :: s)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih, add_assoc]

/-- La suma sobre `allStates n` es la suma sobre las funciones `Fin n → Bool`. -/
theorem sum_allStates {K : Type*} [AddCommMonoid K] (f : List Bool → K) :
    ∀ n : ℕ, ((Word.allStates n).map f).sum = ∑ b : Fin n → Bool, f (List.ofFn b)
  | 0 => by simp [Word.allStates]
  | k + 1 => by
    have ih := sum_allStates (fun s => f (true :: s) + f (false :: s)) k
    rw [← (Equiv.sum_comp (Fin.consEquiv (fun _ => Bool)) (fun b => f (List.ofFn b)))]
    rw [Fintype.sum_prod_type_right]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      Fintype.sum_bool]
    rw [Word.allStates, sum_flat, ih]

/-- El peso de un estado como producto sobre los cruces se reescribe con `count`. -/
theorem prod_ofFn {K : Type*} [Field K] (A : K) :
    ∀ (n : ℕ) (b : Fin n → Bool), (∏ k, if b k then A else A⁻¹) =
      A ^ (List.ofFn b).count true * A⁻¹ ^ (n - (List.ofFn b).count true)
  | 0, b => by simp
  | n + 1, b => by
    have ih := prod_ofFn A n (fun i => b i.succ)
    have hle : (List.ofFn fun i : Fin n => b i.succ).count true ≤ n := by
      simpa using (List.count_le_length (a := true) (l := List.ofFn fun i : Fin n => b i.succ))
    rw [Fin.prod_univ_succ, ih, List.ofFn_succ, List.count_cons]
    generalize (List.ofFn fun i : Fin n => b i.succ).count true = c at hle ⊢
    cases hb : b 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have : n + 1 - c = (n - c) + 1 := by omega
      simp [this, pow_succ]
      ring
    · simp only [↓reduceIte, beq_self_eq_true]
      have : n + 1 - (c + 1) = n - c := by omega
      simp [this, pow_succ]
      ring

theorem finRotate_symm_val {m : ℕ} (i : Fin m) :
    ((finRotate m).symm i).1 = (i.1 + m - 1) % m := by
  cases m with
  | zero => exact i.elim0
  | succ n =>
    have hi := i.2
    have hk : (i.1 + (n + 1) - 1) % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    have : (finRotate (n + 1)).symm i = ⟨(i.1 + (n + 1) - 1) % (n + 1), hk⟩ := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      rw [coe_finRotate]
      by_cases h0 : i.1 = 0
      · have hk0 : (i.1 + (n + 1) - 1) % (n + 1) = n := by
          have : i.1 + (n + 1) - 1 = n := by omega
          rw [this]; exact Nat.mod_eq_of_lt (by omega)
        have hl : (⟨(i.1 + (n + 1) - 1) % (n + 1), hk⟩ : Fin (n + 1)) = Fin.last n :=
          Fin.ext (by rw [Fin.val_last]; exact hk0)
        rw [if_pos hl]; omega
      · have hk1 : (i.1 + (n + 1) - 1) % (n + 1) = i.1 - 1 := by
          have : i.1 + (n + 1) - 1 = (i.1 - 1) + (n + 1) := by omega
          rw [this, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        have hl : ¬ (⟨(i.1 + (n + 1) - 1) % (n + 1), hk⟩ : Fin (n + 1)) = Fin.last n := by
          intro h
          have h2 := congrArg Fin.val h
          rw [Fin.val_last] at h2
          change (i.1 + (n + 1) - 1) % (n + 1) = n at h2
          omega
        rw [if_neg hl]
        change i.1 = (i.1 + (n + 1) - 1) % (n + 1) + 1
        omega
    rw [this]

theorem mem_zip_ofFn {L : List ℕ} {b : Fin L.length → Bool} {c : ℕ} {a : Bool} :
    (c, a) ∈ L.zip (List.ofFn b) ↔ ∃ k : Fin L.length, L[k.1] = c ∧ b k = a := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    have hi' : i < L.length := by simpa using hi
    refine ⟨⟨i, hi'⟩, ?_, ?_⟩
    · have := congrArg Prod.fst he
      simpa using this
    · have := congrArg Prod.snd he
      simpa using this
  · rintro ⟨k, hk, hb⟩
    refine ⟨k.1, by simp, ?_⟩
    simp [hk, hb]

end Aux

/-! ### Propiedades de los pasos superior e inferior -/

section Positions

variable {w : Word}

theorem mem_crossings (c : ℕ) :
    c ∈ Word.crossings w ↔ ∃ i : Fin w.length, w[i.1].over = true ∧ w[i.1].label = c := by
  unfold Word.crossings
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨l, ⟨hl, ho⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    exact ⟨⟨i, hi⟩, ho, rfl⟩
  · rintro ⟨i, ho, rfl⟩
    exact ⟨w[i.1], ⟨List.getElem_mem _, ho⟩, rfl⟩

theorem crossings_nodup (h : WfP w) : (Word.crossings w).Nodup := by
  have hpw : w.Pairwise (fun a b => ¬ (a.over = true ∧ b.over = true ∧ a.label = b.label)) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij ⟨ho1, ho2, hl⟩
    have := h.1 ⟨i, hi⟩ ⟨j, hj⟩ hl (by rw [ho1, ho2])
    have := congrArg Fin.val this
    simp at this
    omega
  unfold Word.crossings
  rw [List.Nodup, List.pairwise_map]
  refine (List.Pairwise.sublist List.filter_sublist hpw).imp_of_mem ?_
  intro a b ha hb hab hlab
  exact hab ⟨(List.mem_filter.1 ha).2, (List.mem_filter.1 hb).2, hlab⟩

theorem findIdx_eq_of (p : Letter → Bool) (j : Fin w.length) (hj : p w[j.1] = true)
    (hu : ∀ k : Fin w.length, p w[k.1] = true → k = j) : w.findIdx p = j.1 := by
  have hlt : w.findIdx p < w.length :=
    List.findIdx_lt_length_of_exists ⟨w[j.1], List.getElem_mem _, hj⟩
  have := hu ⟨w.findIdx p, hlt⟩ (List.findIdx_getElem (w := hlt))
  exact congrArg Fin.val this

theorem overPos_eq (h : WfP w) (x : Fin w.length) (hx : w[x.1].over = true) :
    Word.overPos w w[x.1].label = x.1 := by
  unfold Word.overPos
  apply findIdx_eq_of _ x (by simp [hx])
  intro k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  exact h.1 k x hk.1 (by rw [hk.2, hx])

theorem underPos_eq (h : WfP w) (x : Fin w.length) (hx : w[x.1].over = true) :
    Word.underPos w w[x.1].label = (partnerF w h x).1 := by
  unfold Word.underPos
  apply findIdx_eq_of _ (partnerF w h x)
  · have := partnerF_spec w h x
    simp [this.1, this.2, hx]
  · intro k hk
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hk
    exact partnerF_unique w h x k hk.1 (by simp [hk.2, hx])

theorem signOf_eq (h : WfP w) (x : Fin w.length) (hx : w[x.1].over = true) :
    Word.signOf w w[x.1].label = w[x.1].pos := by
  unfold Word.signOf
  cases hf : w.find? (fun l => l.label == w[x.1].label && l.over) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hf w[x.1] (List.getElem_mem _)
    simp [hx] at this
  | some y =>
    have hy := List.find?_some hf
    have hyw := List.mem_of_find?_eq_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hy
    simp [h.2.2 y hyw w[x.1] (List.getElem_mem _) hy.1]

end Positions

/-! ### Estados y parejas de aristas -/

section Bridge

variable {w : Word}

theorem prev_val (h : WfP w) (i : Fin w.length) :
    ((ofWordP w h).prev i).1 = (i.1 + w.length - 1) % w.length :=
  finRotate_symm_val i

/-- Índice del cruce dentro de `crossings w`. -/
def crossIdx (w : Word) (h : WfP w) (x : (ofWordP w h).Cross) : Fin (Word.crossings w).length :=
  ⟨(Word.crossings w).idxOf w[x.1.1].label,
    List.idxOf_lt_length_iff.2 ((mem_crossings _).2 ⟨x.1, x.2, rfl⟩)⟩

theorem crossIdx_bijective (h : WfP w) : Function.Bijective (crossIdx w h) := by
  constructor
  · intro x y hxy
    have h1 := congrArg (fun k : Fin (Word.crossings w).length =>
      (Word.crossings w)[k.1]'k.2) hxy
    simp only [crossIdx, List.getElem_idxOf] at h1
    exact Subtype.ext (h.1 x.1 y.1 h1 (x.2.trans y.2.symm))
  · intro k
    have hm : (Word.crossings w)[k.1] ∈ Word.crossings w := List.getElem_mem k.2
    obtain ⟨i, hi, hl⟩ := (mem_crossings _).1 hm
    refine ⟨⟨i, hi⟩, Fin.ext ?_⟩
    change (Word.crossings w).idxOf w[i.1].label = k.1
    rw [hl]
    exact List.Nodup.idxOf_getElem (crossings_nodup h) k.1 k.2

/-- Los cruces del diagrama se identifican, en orden, con las posiciones de `crossings w`. -/
noncomputable def crossEquiv (w : Word) (h : WfP w) :
    (ofWordP w h).Cross ≃ Fin (Word.crossings w).length :=
  Equiv.ofBijective (crossIdx w h) (crossIdx_bijective h)

theorem getElem_crossEquiv (h : WfP w) (x : (ofWordP w h).Cross) :
    (Word.crossings w)[(crossEquiv w h x).1]'(crossEquiv w h x).2 = w[x.1.1].label :=
  List.getElem_idxOf _

/-- Las parejas de la suavización coinciden con `smoothRel`. -/
theorem pairsAt_mem (h : WfP w) (x : Fin w.length) (hx : w[x.1].over = true) (s : Bool)
    (a c : Fin w.length) :
    (a.1, c.1) ∈ Word.pairsAt w w[x.1].label s ↔
      (ofWordP w h).smoothRel x (s == w[x.1].pos) a c := by
  have hm : 0 < w.length := x.pos
  unfold Word.pairsAt
  simp only
  rw [overPos_eq h x hx, underPos_eq h x hx, signOf_eq h x hx]
  have hpx : ((ofWordP w h).partner x).1 = (partnerF w h x).1 := rfl
  cases hs : (s == w[x.1].pos)
  ·     simp [GDiag.smoothRel, Fin.ext_iff, prev_val h, hpx]
  ·     simp [GDiag.smoothRel, Fin.ext_iff, prev_val h, hpx]

theorem pairsAt_lt (h : WfP w) (x : Fin w.length) (hx : w[x.1].over = true) (s : Bool)
    (p : ℕ × ℕ) (hp : p ∈ Word.pairsAt w w[x.1].label s) : p.1 < w.length ∧ p.2 < w.length := by
  have hm : 0 < w.length := x.pos
  unfold Word.pairsAt at hp
  simp only at hp
  rw [overPos_eq h x hx, underPos_eq h x hx, signOf_eq h x hx] at hp
  have h1 := x.2
  have h2 := (partnerF w h x).2
  have h3 : ∀ j : ℕ, (j + w.length - 1) % w.length < w.length := fun j => Nat.mod_lt _ hm
  split_ifs at hp <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl <;> exact ⟨by simp [h1, h3], by simp [h1, h3]⟩

/-- Parejas de aristas de un estado. -/
def pairsOf (w : Word) (st : List Bool) : List (ℕ × ℕ) :=
  ((Word.crossings w).zip st).flatMap (fun (c, a) => Word.pairsAt w c a)

theorem mem_pairsOf (h : WfP w) (b : Fin (Word.crossings w).length → Bool) (p : ℕ × ℕ) :
    p ∈ pairsOf w (List.ofFn b) ↔
      ∃ x : (ofWordP w h).Cross, p ∈ Word.pairsAt w w[x.1.1].label (b (crossEquiv w h x)) := by
  unfold pairsOf
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨c0, a0⟩, hz, hp⟩
    obtain ⟨k, hk1, hk2⟩ := mem_zip_ofFn.1 hz
    obtain ⟨x, rfl⟩ := (crossEquiv w h).surjective k
    subst hk1
    subst hk2
    rw [getElem_crossEquiv] at hp
    exact ⟨x, hp⟩
  · rintro ⟨x, hp⟩
    refine ⟨((Word.crossings w)[(crossEquiv w h x).1]'(crossEquiv w h x).2,
      b (crossEquiv w h x)), mem_zip_ofFn.2 ⟨crossEquiv w h x, rfl, rfl⟩, ?_⟩
    rw [getElem_crossEquiv]
    exact hp

theorem rel_iff (h : WfP w) (b : Fin (Word.crossings w).length → Bool) (a c : Fin w.length) :
    (ofWordP w h).rel (fun x => b (crossEquiv w h x)) a c ↔
      (a.1, c.1) ∈ pairsOf w (List.ofFn b) := by
  rw [mem_pairsOf h]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (pairsAt_mem h x.1 x.2 _ a c).2 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (pairsAt_mem h x.1 x.2 _ a c).1 hx⟩

/-- El número de lazos computable coincide con el abstracto. -/
theorem loops_eq (h : WfP w) (b : Fin (Word.crossings w).length → Bool) :
    Word.loops w (List.ofFn b) = (ofWordP w h).lazos (fun x => b (crossEquiv w h x)) := by
  by_cases hm : w.length = 0
  · have hE : IsEmpty (Fin w.length) := ⟨fun i => absurd i.2 (by omega)⟩
    have hcc : Nat.card ((ofWordP w h).graph (fun x => b (crossEquiv w h x))).ConnectedComponent
        = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun c => ?_⟩
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h a => exact hE.false a
    unfold Word.loops GDiag.lazos
    rw [if_pos hm, hcc]
    change 1 = 0 + (if w.length = 0 then 1 else 0)
    rw [if_pos hm]
  · have hbound : ∀ p ∈ pairsOf w (List.ofFn b), p.1 < w.length ∧ p.2 < w.length := by
      intro p hp
      obtain ⟨x, hx⟩ := (mem_pairsOf h b p).1 hp
      exact pairsAt_lt h x.1 x.2 _ p hx
    have hI := inv_foldl _ _ _ (inv_range w.length) hbound
    have hg : (ofWordP w h).graph (fun x => b (crossEquiv w h x)) =
        SimpleGraph.fromRel
          (fun a c : Fin w.length => False ∨ (a.1, c.1) ∈ pairsOf w (List.ofFn b)) := by
      unfold GDiag.graph
      congr 1
      funext a c
      exact propext (by rw [rel_iff h b a c]; simp)
    unfold Word.loops GDiag.lazos
    rw [if_neg hm, hg, card_cc_eq_eraseDups hI]
    change _ = _ + (if w.length = 0 then 1 else 0)
    rw [if_neg hm]
    rfl

/-- **Teorema puente** (versión con hipótesis en `Prop`). -/
theorem bracket_ofWordP (h : WfP w) {K : Type*} [Field K] (A : K) :
    (ofWordP w h).bracket A = Word.bracket A w := by
  let E : (Fin (Word.crossings w).length → Bool) ≃ ((ofWordP w h).Cross → Bool) :=
    { toFun := fun b x => b (crossEquiv w h x)
      invFun := fun σ k => σ ((crossEquiv w h).symm k)
      left_inv := by intro b; funext k; simp
      right_inv := by intro σ; funext x; simp }
  unfold GDiag.bracket Word.bracket Word.terms
  simp only [List.map_map]
  rw [sum_allStates]
  symm
  refine Fintype.sum_equiv E _ _ ?_
  intro b
  have hp : (∏ x : (ofWordP w h).Cross, if b (crossEquiv w h x) then A else A⁻¹) =
      A ^ (List.ofFn b).count true *
        A⁻¹ ^ ((Word.crossings w).length - (List.ofFn b).count true) := by
    rw [Fintype.prod_equiv (crossEquiv w h) _ (fun k => if b k then A else A⁻¹) (fun x => rfl)]
    exact prod_ofFn A _ b
  change A ^ (List.ofFn b).count true *
      A⁻¹ ^ ((Word.crossings w).length - (List.ofFn b).count true) *
      (-(A ^ 2) - A⁻¹ ^ 2) ^ (Word.loops w (List.ofFn b) - 1) =
    (∏ x : (ofWordP w h).Cross, if b (crossEquiv w h x) then A else A⁻¹) *
      (-(A ^ 2) - A⁻¹ ^ 2) ^ ((ofWordP w h).lazos (fun x => b (crossEquiv w h x)) - 1)
  rw [hp, loops_eq h b]

end Bridge

/-! ### Teorema puente y corolarios -/

/-- **Teorema puente.** El corchete abstracto del diagrama `ofWord w hw` coincide con el corchete
computable `Word.bracket` (en cualquier cuerpo y para todo `A`, sin necesidad de `A ≠ 0`). -/
theorem bracket_ofWord (w : Word) (hw : Word.wf w = true) {K : Type*} [Field K] (A : K) :
    (ofWord w hw).bracket A = Word.bracket A w :=
  bracket_ofWordP _ A

theorem wf_concat_trefoil : Word.wf (Word.concat trefoil trefoil) = true := by decide

theorem wf_concat_trefoil_swap :
    Word.wf (Word.concat trefoil (Word.swap trefoil)) = true := by decide

/-- Corchete del trébol derecho, trasladado al diagrama abstracto. -/
theorem bracket_ofWord_trefoil {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    (ofWord trefoil wf_trefoil).bracket A = A⁻¹ ^ 7 - A⁻¹ ^ 3 - A ^ 5 := by
  rw [bracket_ofWord]
  exact bracket_trefoil A hA

/-- Corchete del trébol izquierdo, trasladado al diagrama abstracto. -/
theorem bracket_ofWord_swap_trefoil {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    (ofWord (Word.swap trefoil) wf_swap_trefoil).bracket A = A ^ 7 - A ^ 3 - A⁻¹ ^ 5 := by
  rw [bracket_ofWord]
  exact bracket_swap_trefoil A hA

#print axioms bracket_ofWord
#print axioms bracket_ofWord_trefoil
#print axioms bracket_ofWord_swap_trefoil

end TMENudos.Puente
