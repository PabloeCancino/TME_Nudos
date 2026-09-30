import Mathlib

/-!
# Etapa 1 (spike M4): invariancia del corchete de Kauffman en diagramas de Gauss abstractos

Prueba de viabilidad. Los diagramas son estructuras sobre identificadores (sin índices de lista),
de modo que insertar letras no obliga a renumerar.
-/

namespace TMENudos.Invariancia

/-! ### Lemas generales sobre componentes conexas -/

section Graph

variable {α β : Type}

theorem reach_of_rel {r : α → α → Prop} {a b : α} (h : r a b) :
    (SimpleGraph.fromRel r).Reachable a b := by
  by_cases hab : a = b
  · subst hab
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj r _ _).2 ⟨hab, Or.inl h⟩)

theorem reach_map {G : SimpleGraph α} {G' : SimpleGraph β} (f : β → α)
    (hf : ∀ a b, G'.Adj a b → G.Reachable (f a) (f b)) {a b : β} (h : G'.Reachable a b) :
    G.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

theorem reach_eq {G : SimpleGraph β} {γ : Type} (F : β → γ)
    (h : ∀ a b, G.Adj a b → F a = F b) {a b : β} (hr : G.Reachable a b) : F a = F b := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- Dos grafos con aplicaciones cuasi-inversas tienen el mismo número de componentes. -/
theorem card_cc_eq {G : SimpleGraph α} {G' : SimpleGraph β} (f : β → α) (g : α → β)
    (hf : ∀ a b, G'.Adj a b → G.Reachable (f a) (f b))
    (hg : ∀ a b, G.Adj a b → G'.Reachable (g a) (g b))
    (hfg : ∀ a, G.Reachable (f (g a)) a) (hgf : ∀ b, G'.Reachable (g (f b)) b) :
    Nat.card G'.ConnectedComponent = Nat.card G.ConnectedComponent := by
  refine Nat.card_congr
    { toFun := Quot.lift (fun b => G.connectedComponentMk (f b)) ?_
      invFun := Quot.lift (fun a => G'.connectedComponentMk (g a)) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro a b h
    exact SimpleGraph.ConnectedComponent.eq.2 (reach_map f hf h)
  · intro a b h
    exact SimpleGraph.ConnectedComponent.eq.2 (reach_map g hg h)
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h b => exact SimpleGraph.ConnectedComponent.eq.2 (hgf b)
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h a => exact SimpleGraph.ConnectedComponent.eq.2 (hfg a)

/-- Como `card_cc_eq`, pero `G'` tiene además un vértice aislado `v0`, que aporta una componente. -/
theorem card_cc_succ [Finite α] {G : SimpleGraph α} {G' : SimpleGraph β} (v0 : β) (f : β → Option α)
    (g : α → β) (hv0 : f v0 = none) (hf0 : ∀ b, f b = none → b = v0)
    (hiso : ∀ b, ¬ G'.Adj v0 b)
    (hf : ∀ a b a' b', G'.Adj a b → f a = some a' → f b = some b' → G.Reachable a' b')
    (hg : ∀ a b, G.Adj a b → G'.Reachable (g a) (g b))
    (hfg : ∀ a, f (g a) = some a)
    (hgf : ∀ b a', f b = some a' → G'.Reachable (g a') b) :
    Nat.card G'.ConnectedComponent = Nat.card G.ConnectedComponent + 1 := by
  classical
  let F : β → Option G.ConnectedComponent := fun b =>
    (f b).map G.connectedComponentMk
  have hF : ∀ a b, G'.Adj a b → F a = F b := by
    intro a b h
    cases ha : f a with
    | none =>
      have : a = v0 := hf0 a ha
      subst this
      exact absurd h (hiso b)
    | some a' =>
      cases hb : f b with
      | none =>
        have : b = v0 := hf0 b hb
        subst this
        exact absurd h.symm (hiso a)
      | some b' =>
        simp only [F, ha, hb, Option.map_some]
        exact congrArg _ (SimpleGraph.ConnectedComponent.eq.2 (hf a b a' b' h ha hb))
  have hFr : ∀ {a b}, G'.Reachable a b → F a = F b := fun h => reach_eq F hF h
  have hginv : ∀ a b, G.Reachable a b →
      G'.connectedComponentMk (g a) = G'.connectedComponentMk (g b) := by
    intro a b h
    exact SimpleGraph.ConnectedComponent.eq.2 (reach_map g hg h)
  let T : G'.ConnectedComponent → Option G.ConnectedComponent := Quot.lift F (fun a b h => hFr h)
  let I : Option G.ConnectedComponent → G'.ConnectedComponent := fun c =>
    match c with
    | none => G'.connectedComponentMk v0
    | some c => Quot.lift (fun a => G'.connectedComponentMk (g a)) hginv c
  have hT : ∀ b, T (G'.connectedComponentMk b) = F b := fun _ => rfl
  have hI0 : I none = G'.connectedComponentMk v0 := rfl
  have hI1 : ∀ a, I (some (G.connectedComponentMk a)) = G'.connectedComponentMk (g a) :=
    fun _ => rfl
  have hcard : Nat.card G'.ConnectedComponent = Nat.card (Option G.ConnectedComponent) := by
    refine Nat.card_congr ⟨T, I, ?_, ?_⟩
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h b =>
        rw [hT]
        cases hb : f b with
        | none =>
          have : b = v0 := hf0 b hb
          rw [this]
          simp only [F, hv0, Option.map_none, hI0]
        | some a' =>
          simp only [F, hb, Option.map_some, hI1]
          exact SimpleGraph.ConnectedComponent.eq.2 (hgf b a' hb)
    · intro c
      cases c with
      | none => rw [hI0, hT]; simp only [F, hv0, Option.map_none]
      | some c =>
        induction c using SimpleGraph.ConnectedComponent.ind with
        | h a => rw [hI1, hT]; simp only [F, hfg, Option.map_some]
  rw [hcard]
  exact Finite.card_option

end Graph

/-! ### Diagramas de Gauss abstractos -/

/-- Diagrama de Gauss con signos sobre identificadores. La arista `i` va de la letra `i` a
`next i`. `partner` es el otro paso por el mismo cruce. `free` cuenta circunferencias sin cruces. -/
structure GDiag (ι : Type) [DecidableEq ι] [Fintype ι] where
  next : Equiv.Perm ι
  partner : ι → ι
  ovr : ι → Bool
  sign : ι → Bool
  partner_partner : ∀ i, partner (partner i) = i
  partner_ne : ∀ i, partner i ≠ i
  ovr_partner : ∀ i, ovr (partner i) = !ovr i
  sign_partner : ∀ i, sign (partner i) = sign i
  free : ℕ

namespace GDiag

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Arista que llega a la letra `i`. -/
def prev (i : ι) : ι := D.next.symm i

/-- Los cruces, representados por su letra superior. -/
abbrev Cross : Type := {x : ι // D.ovr x = true}

/-- Aristas que une la suavización del cruce con letra superior `x`; `ori = true` es la
suavización orientada. -/
def smoothRel (x : ι) (ori : Bool) (a b : ι) : Prop :=
  (ori = true ∧ ((a = D.prev x ∧ b = D.partner x) ∨ (a = D.prev (D.partner x) ∧ b = x))) ∨
  (ori = false ∧ ((a = D.prev x ∧ b = D.prev (D.partner x)) ∨ (a = x ∧ b = D.partner x)))

/-- Un estado `σ` (`true` = suavización A). La suavización es orientada cuando `σ x = sign x`. -/
def rel (σ : D.Cross → Bool) (a b : ι) : Prop :=
  ∃ x : D.Cross, D.smoothRel x.1 (σ x == D.sign x.1) a b

/-- El grafo del estado `σ`: vértices = aristas del diagrama. -/
def graph (σ : D.Cross → Bool) : SimpleGraph ι := SimpleGraph.fromRel (D.rel σ)

/-- Número de lazos del estado: componentes conexas más circunferencias libres. -/
noncomputable def lazos (σ : D.Cross → Bool) : ℕ :=
  Nat.card (D.graph σ).ConnectedComponent + D.free

/-- Corchete de Kauffman normalizado (`⟨círculo⟩ = 1`) por suma de estados, con `B = A⁻¹` y
`d = -A² - A⁻²`. El peso `A^#A * B^#B` se escribe como producto sobre los cruces. -/
noncomputable def bracket {K : Type*} [Field K] (A : K) : K :=
  ∑ σ : D.Cross → Bool, (∏ x : D.Cross, if σ x then A else A⁻¹) *
    (-(A ^ 2) - A⁻¹ ^ 2) ^ (D.lazos σ - 1)

end GDiag

/-! ### Invariancia por isomorfismo -/

namespace GDiag

variable {ι ι' : Type} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']

/-- Transporte de un diagrama por una biyección de identificadores. -/
def map (D : GDiag ι) (e : ι ≃ ι') : GDiag ι' where
  next := e.permCongr D.next
  partner j := e (D.partner (e.symm j))
  ovr j := D.ovr (e.symm j)
  sign j := D.sign (e.symm j)
  partner_partner j := by simp [D.partner_partner]
  partner_ne j := by
    intro h
    apply D.partner_ne (e.symm j)
    have := congrArg e.symm h
    simpa using this
  ovr_partner j := by simp [D.ovr_partner]
  sign_partner j := by simp [D.sign_partner]
  free := D.free

@[simp] theorem partner_map (D : GDiag ι) (e : ι ≃ ι') (j : ι') :
    (D.map e).partner j = e (D.partner (e.symm j)) := rfl

theorem prev_map (D : GDiag ι) (e : ι ≃ ι') (j : ι') :
    (D.map e).prev j = e (D.prev (e.symm j)) := by
  simp only [prev]
  rw [Equiv.symm_apply_eq]
  simp [map, Equiv.permCongr_apply]

theorem smoothRel_map (D : GDiag ι) (e : ι ≃ ι') (x : ι') (ori : Bool) (a b : ι') :
    (D.map e).smoothRel x ori a b ↔ D.smoothRel (e.symm x) ori (e.symm a) (e.symm b) := by
  simp [smoothRel, prev_map, partner_map, Equiv.symm_apply_eq]

/-- Los cruces se corresponden. -/
def crossEquiv (D : GDiag ι) (e : ι ≃ ι') : (D.map e).Cross ≃ D.Cross :=
  e.symm.subtypeEquiv (fun _ => Iff.rfl)

theorem rel_map (D : GDiag ι) (e : ι ≃ ι') (σ' : (D.map e).Cross → Bool) (σ : D.Cross → Bool)
    (hσ : ∀ x, σ' x = σ (crossEquiv D e x)) (a b : ι') :
    (D.map e).rel σ' a b ↔ D.rel σ (e.symm a) (e.symm b) := by
  constructor
  · rintro ⟨x, h⟩
    refine ⟨crossEquiv D e x, ?_⟩
    rw [hσ x] at h
    exact (smoothRel_map D e _ _ _ _).1 h
  · rintro ⟨x, h⟩
    refine ⟨(crossEquiv D e).symm x, ?_⟩
    rw [hσ, Equiv.apply_symm_apply]
    have h1 : e.symm ((crossEquiv D e).symm x).1 = x.1 := by simp [crossEquiv]
    have h2 : (D.map e).sign ((crossEquiv D e).symm x).1 = D.sign x.1 := by
      change D.sign (e.symm _) = _
      rw [h1]
    rw [h2, smoothRel_map, h1]
    exact h

theorem lazos_map (D : GDiag ι) (e : ι ≃ ι') (σ' : (D.map e).Cross → Bool) (σ : D.Cross → Bool)
    (hσ : ∀ x, σ' x = σ (crossEquiv D e x)) :
    (D.map e).lazos σ' = D.lazos σ := by
  have key : Nat.card ((D.map e).graph σ').ConnectedComponent =
      Nat.card (D.graph σ).ConnectedComponent := by
    refine card_cc_eq e.symm e ?_ ?_ ?_ ?_
    · intro a b h
      obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
      · exact reach_of_rel ((rel_map D e σ' σ hσ a b).1 h)
      · exact (reach_of_rel ((rel_map D e σ' σ hσ b a).1 h)).symm
    · intro a b h
      obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
      · exact reach_of_rel ((rel_map D e σ' σ hσ _ _).2 (by simpa using h))
      · exact (reach_of_rel ((rel_map D e σ' σ hσ _ _).2 (by simpa using h))).symm
    · intro a
      simp
    · intro b
      simp
  unfold lazos
  rw [key]
  rfl

/-- **Invariancia por isomorfismo.** -/
theorem bracket_map {K : Type*} [Field K] (A : K) (D : GDiag ι) (e : ι ≃ ι') :
    (D.map e).bracket A = D.bracket A := by
  unfold bracket
  refine Fintype.sum_equiv ((crossEquiv D e).arrowCongr (Equiv.refl Bool)) _ _ ?_
  intro σ'
  have hσ : ∀ x, σ' x = ((crossEquiv D e).arrowCongr (Equiv.refl Bool) σ') (crossEquiv D e x) := by
    intro x
    simp
  rw [lazos_map D e σ' _ hσ]
  congr 1
  refine Fintype.prod_equiv (crossEquiv D e) _ _ ?_
  intro x
  rw [hσ x]

end GDiag

/-! ### R1: lemas puros sobre componentes

`ι ⊕ Bool`: la letra `inl i` es la letra `i`; `inr false` = x y `inr true` = y son las dos letras
nuevas. La arista `e` se parte en `e`, `x`, `y`. -/

section PureR1

variable {ι : Type} (e : ι)

/-- Aplicación que manda `x` e `y` a `e`. -/
def fe : ι ⊕ Bool → ι
  | .inl i => i
  | .inr _ => e

@[simp] theorem fe_inl (i : ι) : fe e (.inl i) = i := rfl

/-- Como `fe`, pero `x` va a `none` (es la arista aislada del caso orientado). -/
def fo : ι ⊕ Bool → Option ι
  | .inl i => some i
  | .inr false => none
  | .inr true => some e

theorem fo_eq_some {b : ι ⊕ Bool} {a' : ι} (h : fo e b = some a') : fe e b = a' := by
  rcases b with i | _ | _ <;> simp_all [fo, fe]

/-- Caso no orientado: el grafo nuevo tiene las mismas componentes. -/
theorem card_unori (r : ι → ι → Prop) (old new : ι ⊕ Bool → ι ⊕ Bool → Prop)
    (O1 : ∀ a c, old a c → r (fe e a) (fe e c))
    (O2 : ∀ a' c', r a' c' → ∃ a c, old a c ∧ (a = .inl a' ∨ (a = .inr true ∧ a' = e)) ∧
      (c = .inl c' ∨ (c = .inr true ∧ c' = e)))
    (N1 : ∀ a c, new a c → fe e a = e ∧ fe e c = e)
    (N2 : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl e) (.inr false) ∧
      (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inr false) (.inr true)) :
    Nat.card (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel r).ConnectedComponent := by
  have hey : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl e) (.inr true) :=
    N2.1.trans N2.2
  refine card_cc_eq (fe e) Sum.inl ?_ ?_ ?_ ?_
  · intro a c h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · exact reach_of_rel (O1 a c h)
      · rw [(N1 a c h).1, (N1 a c h).2]
    · rcases h with h | h
      · exact (reach_of_rel (O1 c a h)).symm
      · rw [(N1 c a h).1, (N1 c a h).2]
  · intro a c h
    have key : ∀ a' c', r a' c' →
        (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl a') (.inl c') := by
      intro a' c' h'
      obtain ⟨a₁, c₁, ho, ha, hc⟩ := O2 a' c' h'
      have h1 : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl a') a₁ := by
        rcases ha with rfl | ⟨rfl, rfl⟩
        · exact SimpleGraph.Reachable.refl _
        · exact hey
      have h2 : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl c') c₁ := by
        rcases hc with rfl | ⟨rfl, rfl⟩
        · exact SimpleGraph.Reachable.refl _
        · exact hey
      exact h1.trans ((reach_of_rel (r := fun a c => old a c ∨ new a c) (Or.inl ho)).trans h2.symm)
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · exact key a c h
    · exact (key c a h).symm
  · intro a
    exact SimpleGraph.Reachable.refl _
  · intro b
    rcases b with i | _ | _
    · exact SimpleGraph.Reachable.refl _
    · exact N2.1
    · exact hey

/-- Caso orientado: la arista `x` queda aislada y aporta una componente más. -/
theorem card_ori [Finite ι] (r : ι → ι → Prop) (old new : ι ⊕ Bool → ι ⊕ Bool → Prop)
    (O1 : ∀ a c, old a c → r (fe e a) (fe e c))
    (O2 : ∀ a' c', r a' c' → ∃ a c, old a c ∧ (a = .inl a' ∨ (a = .inr true ∧ a' = e)) ∧
      (c = .inl c' ∨ (c = .inr true ∧ c' = e)))
    (O3 : ∀ a c, old a c → a ≠ .inr false ∧ c ≠ .inr false)
    (N1 : ∀ a c, new a c → (a = .inl e ∧ c = .inr true) ∨ (a = .inr false ∧ c = .inr false))
    (N2 : new (.inl e) (.inr true)) :
    Nat.card (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel r).ConnectedComponent + 1 := by
  have hey : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl e) (.inr true) :=
    reach_of_rel (Or.inr N2)
  refine card_cc_succ (.inr false) (fo e) Sum.inl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rcases b with i | _ | _ <;> simp_all [fo]
  · intro b h
    obtain ⟨hne, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · exact (O3 _ _ h).1 rfl
      · rcases N1 _ _ h with ⟨h1, -⟩ | ⟨-, rfl⟩
        · exact absurd h1 (by simp)
        · exact hne rfl
    · rcases h with h | h
      · exact (O3 _ _ h).2 rfl
      · rcases N1 _ _ h with ⟨-, h2⟩ | ⟨rfl, -⟩
        · exact absurd h2 (by simp)
        · exact hne rfl
  · have key : ∀ a c a' c', (old a c ∨ new a c) → fo e a = some a' → fo e c = some c' →
        (SimpleGraph.fromRel r).Reachable a' c' := by
      intro a c a' c' h ha hc
      rcases h with h | h
      · rw [← fo_eq_some e ha, ← fo_eq_some e hc]
        exact reach_of_rel (O1 a c h)
      · rcases N1 _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [fo, Option.some.injEq] at ha hc
          rw [← ha, ← hc]
        · simp [fo] at ha
    intro a c a' c' h ha hc
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · exact key a c a' c' h ha hc
    · exact (key c a c' a' h hc ha).symm
  · intro a c h
    have key : ∀ a' c', r a' c' →
        (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl a') (.inl c') := by
      intro a' c' h'
      obtain ⟨a₁, c₁, ho, ha, hc⟩ := O2 a' c' h'
      have h1 : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl a') a₁ := by
        rcases ha with rfl | ⟨rfl, rfl⟩
        · exact SimpleGraph.Reachable.refl _
        · exact hey
      have h2 : (SimpleGraph.fromRel (fun a c => old a c ∨ new a c)).Reachable (.inl c') c₁ := by
        rcases hc with rfl | ⟨rfl, rfl⟩
        · exact SimpleGraph.Reachable.refl _
        · exact hey
      exact h1.trans ((reach_of_rel (r := fun a c => old a c ∨ new a c) (Or.inl ho)).trans h2.symm)
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · exact key a c h
    · exact (key c a h).symm
  · intro a
    rfl
  · intro b a' h
    rcases b with i | _ | _
    · simp only [fo, Option.some.injEq] at h
      rw [h]
    · simp [fo] at h
    · simp only [fo, Option.some.injEq] at h
      rw [← h]
      exact hey

end PureR1

/-! ### Grafos que son unión disjunta (para R1 sobre una circunferencia libre) -/

section SumGraph

variable {α κ : Type}

/-- Las componentes de un grafo sin aristas entre `α` y `κ` son las de cada parte. -/
theorem card_cc_sum [Finite α] [Finite κ] {G : SimpleGraph α} {H : SimpleGraph κ}
    {G' : SimpleGraph (α ⊕ κ)}
    (h1 : ∀ a c, G'.Adj (.inl a) (.inl c) ↔ G.Adj a c)
    (h2 : ∀ a c, G'.Adj (.inr a) (.inr c) ↔ H.Adj a c)
    (h3 : ∀ a c, ¬ G'.Adj (.inl a) (.inr c)) :
    Nat.card G'.ConnectedComponent =
      Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
  let F : α ⊕ κ → G.ConnectedComponent ⊕ H.ConnectedComponent :=
    Sum.map G.connectedComponentMk H.connectedComponentMk
  have hF : ∀ a c, G'.Adj a c → F a = F c := by
    intro a c h
    rcases a with a | a <;> rcases c with c | c
    · exact congrArg Sum.inl (SimpleGraph.ConnectedComponent.eq.2 (((h1 a c).1 h).reachable))
    · exact absurd h (h3 a c)
    · exact absurd h.symm (h3 c a)
    · exact congrArg Sum.inr (SimpleGraph.ConnectedComponent.eq.2 (((h2 a c).1 h).reachable))
  have hFr : ∀ {a c}, G'.Reachable a c → F a = F c := fun h => reach_eq F hF h
  have hI1 : ∀ a c, G.Reachable a c →
      G'.connectedComponentMk (.inl a) = G'.connectedComponentMk (.inl c) := by
    intro a c h
    refine SimpleGraph.ConnectedComponent.eq.2 (reach_map (G := G') (G' := G) Sum.inl ?_ h)
    intro a c h
    exact ((h1 a c).2 h).reachable
  have hI2 : ∀ a c, H.Reachable a c →
      G'.connectedComponentMk (.inr a) = G'.connectedComponentMk (.inr c) := by
    intro a c h
    refine SimpleGraph.ConnectedComponent.eq.2 (reach_map (G := G') (G' := H) Sum.inr ?_ h)
    intro a c h
    exact ((h2 a c).2 h).reachable
  let T : G'.ConnectedComponent → G.ConnectedComponent ⊕ H.ConnectedComponent :=
    Quot.lift F (fun a c h => hFr h)
  let I : G.ConnectedComponent ⊕ H.ConnectedComponent → G'.ConnectedComponent :=
    Sum.elim (Quot.lift (fun a => G'.connectedComponentMk (.inl a)) hI1)
      (Quot.lift (fun a => G'.connectedComponentMk (.inr a)) hI2)
  have hT : ∀ v, T (G'.connectedComponentMk v) = F v := fun _ => rfl
  have hcard : Nat.card G'.ConnectedComponent =
      Nat.card (G.ConnectedComponent ⊕ H.ConnectedComponent) := by
    refine Nat.card_congr ⟨T, I, ?_, ?_⟩
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h v =>
        rw [hT]
        rcases v with a | a <;> rfl
    · intro c
      rcases c with c | c
      · induction c using SimpleGraph.ConnectedComponent.ind with
        | h a => rw [show I (.inl (G.connectedComponentMk a)) =
              G'.connectedComponentMk (.inl a) from rfl, hT]; rfl
      · induction c using SimpleGraph.ConnectedComponent.ind with
        | h a => rw [show I (.inr (H.connectedComponentMk a)) =
              G'.connectedComponentMk (.inr a) from rfl, hT]; rfl
  rw [hcard]
  exact Nat.card_sum

theorem card_cc_bot_bool : Nat.card (⊥ : SimpleGraph Bool).ConnectedComponent = 2 := by
  have : Nat.card Bool = Nat.card (⊥ : SimpleGraph Bool).ConnectedComponent := by
    refine Nat.card_congr
      (Equiv.ofBijective (fun k => (⊥ : SimpleGraph Bool).connectedComponentMk k)
      ⟨?_, ?_⟩)
    · intro a c h
      exact SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.eq.1 h)
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h v => exact ⟨v, rfl⟩
  rw [← this]
  simp

theorem card_cc_top_bool : Nat.card (⊤ : SimpleGraph Bool).ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨SimpleGraph.Preconnected.subsingleton_connectedComponent ?_, ?_⟩
  · exact SimpleGraph.preconnected_top
  · exact ⟨(⊤ : SimpleGraph Bool).connectedComponentMk true⟩

end SumGraph

/-! ### Álgebra del factor del rizo -/

section Alg

variable {K : Type*} [Field K]

/-- `A·d + A⁻¹ = -A³` con `d = -A² - A⁻²`. -/
theorem factor_pos (A : K) (hA : A ≠ 0) : A * (-(A ^ 2) - A⁻¹ ^ 2) + A⁻¹ = -A ^ 3 := by
  field_simp
  ring

/-- `A + A⁻¹·d = -A⁻³`. -/
theorem factor_neg (A : K) (hA : A ≠ 0) : A + A⁻¹ * (-(A ^ 2) - A⁻¹ ^ 2) = -A⁻¹ ^ 3 := by
  field_simp
  ring

/-- La suma sobre el estado del cruce nuevo. `W` es el peso de los demás cruces y `l + 1` el
número de lazos del estado sin el cruce nuevo. -/
theorem sum_new_crossing (A : K) (hA : A ≠ 0) (s : Bool) (W : K) (l : ℕ) :
    W * (if true then A else A⁻¹) *
        (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 + (if (true == s) = true then 1 else 0) - 1) +
      W * (if false then A else A⁻¹) *
        (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 + (if (false == s) = true then 1 else 0) - 1) =
    (if s then -A ^ 3 else -A⁻¹ ^ 3) * (W * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 - 1)) := by
  cases s
  · change W * A * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 + 0 - 1) +
      W * A⁻¹ * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 + 1 - 1) =
        -A⁻¹ ^ 3 * (W * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 - 1))
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    linear_combination (W * (-(A ^ 2) - A⁻¹ ^ 2) ^ l) * factor_neg A hA
  · change W * A * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 + 1 - 1) +
      W * A⁻¹ * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 + 0 - 1) =
        -A ^ 3 * (W * (-(A ^ 2) - A⁻¹ ^ 2) ^ (l + 1 - 1))
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    linear_combination (W * (-(A ^ 2) - A⁻¹ ^ 2) ^ l) * factor_pos A hA

end Alg

/-! ### R1 sobre una arista existente -/

namespace GDiag

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Sucesor cíclico tras insertar `x → y` justo después de `e`:
`e → x → y → next e`. -/
def r1Next (D : GDiag ι) (e : ι) : Equiv.Perm (ι ⊕ Bool) where
  toFun
    | .inl i => if i = e then .inr false else .inl (D.next i)
    | .inr false => .inr true
    | .inr true => .inl (D.next e)
  invFun
    | .inl i => if i = D.next e then .inr true else .inl (D.next.symm i)
    | .inr false => .inl e
    | .inr true => .inr false
  left_inv := by
    intro z
    rcases z with i | _ | _
    · by_cases h : i = e
      · simp [h]
      · simp [h]
    · rfl
    · simp
  right_inv := by
    intro z
    rcases z with i | _ | _
    · by_cases h : i = D.next e
      · simp [h]
      · have h' : ¬ D.next.symm i = e := by
          rw [Equiv.symm_apply_eq]
          exact h
        simp [h, h']
    · simp
    · simp

/-- El diagrama tras un rizo (R1) insertado en la arista `e`. La letra `x = inr false` tiene
`ovr = o1`, la `y = inr true` tiene `ovr = !o1`; ambas con signo `s`. -/
def r1 (D : GDiag ι) (e : ι) (o1 s : Bool) : GDiag (ι ⊕ Bool) where
  next := r1Next D e
  partner
    | .inl i => .inl (D.partner i)
    | .inr b => .inr (!b)
  ovr
    | .inl i => D.ovr i
    | .inr b => xor o1 b
  sign
    | .inl i => D.sign i
    | .inr _ => s
  partner_partner := by
    rintro (i | b)
    · simp [D.partner_partner]
    · simp
  partner_ne := by
    rintro (i | b)
    · simp [D.partner_ne]
    · cases b <;> simp
  ovr_partner := by
    rintro (i | b)
    · simpa using D.ovr_partner i
    · cases o1 <;> cases b <;> rfl
  sign_partner := by
    rintro (i | b)
    · simpa using D.sign_partner i
    · rfl
  free := D.free

variable (D : GDiag ι) (e : ι) (o1 s : Bool)
theorem prev_next (i : ι) : D.prev (D.next i) = i := by simp [prev]

theorem r1_prev_inl (i : ι) : (r1 D e o1 s).prev (.inl i) =
    if i = D.next e then .inr true else .inl (D.prev i) := rfl

@[simp] theorem r1_prev_inl_next : (r1 D e o1 s).prev (.inl (D.next e)) = .inr true := by
  rw [r1_prev_inl, if_pos rfl]

theorem r1_prev_inl_of_ne {i : ι} (h : i ≠ D.next e) :
    (r1 D e o1 s).prev (.inl i) = .inl (D.prev i) := by
  rw [r1_prev_inl, if_neg h]

@[simp] theorem r1_prev_x : (r1 D e o1 s).prev (.inr false) = .inl e := rfl

@[simp] theorem r1_prev_y : (r1 D e o1 s).prev (.inr true) = .inr false := rfl

@[simp] theorem r1_partner_inl (i : ι) : (r1 D e o1 s).partner (.inl i) = .inl (D.partner i) := rfl

@[simp] theorem r1_partner_inr (b : Bool) : (r1 D e o1 s).partner (.inr b) = .inr (!b) := rfl

@[simp] theorem r1_sign_inl (i : ι) : (r1 D e o1 s).sign (.inl i) = D.sign i := rfl

@[simp] theorem r1_sign_inr (b : Bool) : (r1 D e o1 s).sign (.inr b) = s := rfl

@[simp] theorem r1_ovr_inl (i : ι) : (r1 D e o1 s).ovr (.inl i) = D.ovr i := rfl

@[simp] theorem r1_ovr_inr (b : Bool) : (r1 D e o1 s).ovr (.inr b) = xor o1 b := rfl

/-- `fe` manda la arista anterior a `z` en `D'` a la arista anterior a `z` en `D`. -/
theorem fe_prev (z : ι) : fe e ((r1 D e o1 s).prev (.inl z)) = D.prev z := by
  by_cases h : z = D.next e
  · subst h
    simp [fe, prev_next]
  · rw [r1_prev_inl_of_ne D e o1 s h]
    rfl

theorem prev_ne_x (z : ι) : (r1 D e o1 s).prev (.inl z) ≠ .inr false := by
  by_cases h : z = D.next e
  · subst h
    simp
  · rw [r1_prev_inl_of_ne D e o1 s h]
    simp

/-- Las aristas `prev' z` y `prev z` están en la misma posición salvo `e`/`y`. -/
theorem prev_cases (z : ι) :
    (r1 D e o1 s).prev (.inl z) = .inl (D.prev z) ∨
      ((r1 D e o1 s).prev (.inl z) = .inr true ∧ D.prev z = e) := by
  by_cases h : z = D.next e
  · subst h
    right
    simp [prev_next]
  · left
    exact r1_prev_inl_of_ne D e o1 s h

/-- Los cruces de `D'` son los de `D` más el nuevo, cuya letra superior es `inr (!o1)`. -/
def r1Cross : (r1 D e o1 s).Cross ≃ D.Cross ⊕ Unit where
  toFun z :=
    match z with
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr _, _⟩ => .inr ()
  invFun w :=
    match w with
    | .inl x => ⟨.inl x.1, x.2⟩
    | .inr _ => ⟨.inr (!o1), by cases o1 <;> rfl⟩
  left_inv := by
    rintro ⟨z, h⟩
    rcases z with i | b
    · rfl
    · have hb : b = !o1 := by
        simp only [r1_ovr_inr] at h
        cases o1 <;> cases b <;> simp_all
      subst hb
      rfl
  right_inv := by
    rintro (x | u)
    · rfl
    · rfl

/-- Los estados de `D'` son los de `D` junto con el estado del cruce nuevo. -/
def r1State : ((r1 D e o1 s).Cross → Bool) ≃ (D.Cross → Bool) × Bool where
  toFun σ' := (fun x => σ' ((r1Cross D e o1 s).symm (.inl x)),
    σ' ((r1Cross D e o1 s).symm (.inr ())))
  invFun p := fun z => Sum.elim p.1 (fun _ => p.2) (r1Cross D e o1 s z)
  left_inv := by
    intro σ'
    funext z
    rcases h : r1Cross D e o1 s z with x | u
    · have hz : (r1Cross D e o1 s).symm (.inl x) = z := (Equiv.symm_apply_eq _).2 h.symm
      simp only [h, Sum.elim_inl, hz]
    · have hz : (r1Cross D e o1 s).symm (.inr ()) = z := by
        rw [Equiv.symm_apply_eq, h]
      simp only [h, Sum.elim_inr, hz]
  right_inv := by
    rintro ⟨σ, b⟩
    refine Prod.ext (funext fun x => ?_) ?_
    · simp
    · simp

theorem r1State_symm_inl (σ : D.Cross → Bool) (b : Bool) (x : D.Cross) :
    (r1State D e o1 s).symm (σ, b) ((r1Cross D e o1 s).symm (.inl x)) = σ x := by
  simp [r1State]

theorem r1State_symm_inr (σ : D.Cross → Bool) (b : Bool) :
    (r1State D e o1 s).symm (σ, b) ((r1Cross D e o1 s).symm (.inr ())) = b := by
  simp [r1State]

theorem r1_rel_iff (σ : D.Cross → Bool) (b : Bool) (a c : ι ⊕ Bool) :
    (r1 D e o1 s).rel ((r1State D e o1 s).symm (σ, b)) a c ↔
      (∃ x : D.Cross, (r1 D e o1 s).smoothRel (.inl x.1) (σ x == D.sign x.1) a c) ∨
        (r1 D e o1 s).smoothRel (.inr (!o1)) (b == s) a c := by
  unfold rel
  refine (Equiv.exists_congr_left (r1Cross D e o1 s)).trans ?_
  rw [Sum.exists]
  apply or_congr
  · apply exists_congr
    intro x
    rw [r1State_symm_inl]
    rfl
  · constructor
    · rintro ⟨u, h⟩
      cases u
      rw [r1State_symm_inr] at h
      exact h
    · intro h
      exact ⟨(), by rw [r1State_symm_inr]; exact h⟩

/-- Parte del grafo `G'_σ` que viene de los cruces viejos. -/
def r1Old (σ : D.Cross → Bool) (a c : ι ⊕ Bool) : Prop :=
  ∃ x : D.Cross, (r1 D e o1 s).smoothRel (.inl x.1) (σ x == D.sign x.1) a c

/-- Parte del grafo `G'_σ` que viene del cruce nuevo. -/
def r1New (b : Bool) (a c : ι ⊕ Bool) : Prop :=
  (r1 D e o1 s).smoothRel (.inr (!o1)) (b == s) a c

theorem r1Old_fe (σ : D.Cross → Bool) (a c : ι ⊕ Bool) (h : r1Old D e o1 s σ a c) :
    D.rel σ (fe e a) (fe e c) := by
  obtain ⟨x, h⟩ := h
  refine ⟨x, ?_⟩
  rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    simp [smoothRel, ho, fe_prev, fe_inl]

theorem r1Old_ne_x (σ : D.Cross → Bool) (a c : ι ⊕ Bool) (h : r1Old D e o1 s σ a c) :
    a ≠ .inr false ∧ c ≠ .inr false := by
  obtain ⟨x, h⟩ := h
  rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    simp [prev_ne_x]

theorem r1Old_lift (σ : D.Cross → Bool) (a' c' : ι) (h : D.rel σ a' c') :
    ∃ a c, r1Old D e o1 s σ a c ∧ (a = .inl a' ∨ (a = .inr true ∧ a' = e)) ∧
      (c = .inl c' ∨ (c = .inr true ∧ c' = e)) := by
  obtain ⟨x, h⟩ := h
  have hp := fun z => prev_cases D e o1 s z
  rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, ⟨x, Or.inl ⟨ho, Or.inl ⟨rfl, rfl⟩⟩⟩, hp _, Or.inl rfl⟩
  · exact ⟨_, _, ⟨x, Or.inl ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩, hp _, Or.inl rfl⟩
  · exact ⟨_, _, ⟨x, Or.inr ⟨ho, Or.inl ⟨rfl, rfl⟩⟩⟩, hp _, hp _⟩
  · exact ⟨_, _, ⟨x, Or.inr ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩, Or.inl rfl, Or.inl rfl⟩

theorem r1New_ori (b : Bool) (hb : (b == s) = true) (a c : ι ⊕ Bool) :
    r1New D e o1 s b a c ↔ (a = .inl e ∧ c = .inr true) ∨ (a = .inr false ∧ c = .inr false) := by
  cases o1 <;> simp [r1New, smoothRel, hb, or_comm]

theorem r1New_unori (b : Bool) (hb : (b == s) = false) (a c : ι ⊕ Bool) :
    r1New D e o1 s b a c → fe e a = e ∧ fe e c = e := by
  intro h
  cases o1 <;> simp only [r1New, smoothRel, hb, Bool.false_eq_true, Bool.not_false,
    Bool.not_true, r1_prev_y, r1_partner_inr, r1_prev_x, false_and, true_and, false_or] at h <;>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [fe]

theorem r1New_unori_reach (b : Bool) (hb : (b == s) = false) :
    (r1New D e o1 s b (.inl e) (.inr false) ∨ r1New D e o1 s b (.inr false) (.inl e)) ∧
      (r1New D e o1 s b (.inr false) (.inr true) ∨ r1New D e o1 s b (.inr true) (.inr false)) := by
  cases o1 <;> simp [r1New, smoothRel, hb]

theorem r1_graph_eq (σ : D.Cross → Bool) (b : Bool) :
    (r1 D e o1 s).graph ((r1State D e o1 s).symm (σ, b)) =
      SimpleGraph.fromRel (fun a c => r1Old D e o1 s σ a c ∨ r1New D e o1 s b a c) := by
  unfold graph
  congr 1
  funext a c
  exact propext (r1_rel_iff D e o1 s σ b a c)

/-- **Lema de componentes.** Con la suavización orientada del cruce nuevo, hay una componente
más; con la no orientada, las mismas. -/
theorem r1_card (σ : D.Cross → Bool) (b : Bool) :
    Nat.card ((r1 D e o1 s).graph ((r1State D e o1 s).symm (σ, b))).ConnectedComponent =
      Nat.card (D.graph σ).ConnectedComponent + (if b == s then 1 else 0) := by
  rw [r1_graph_eq]
  by_cases hb : (b == s) = true
  · rw [if_pos hb]
    refine card_ori e (D.rel σ) (r1Old D e o1 s σ) (r1New D e o1 s b)
      (r1Old_fe D e o1 s σ) (r1Old_lift D e o1 s σ) (r1Old_ne_x D e o1 s σ) ?_ ?_
    · intro a c h
      exact (r1New_ori D e o1 s b hb a c).1 h
    · exact (r1New_ori D e o1 s b hb _ _).2 (Or.inl ⟨rfl, rfl⟩)
  · have hb' : (b == s) = false := by simpa using hb
    rw [if_neg hb, add_zero]
    obtain ⟨h1, h2⟩ := r1New_unori_reach D e o1 s b hb'
    have hR : ∀ a c, r1New D e o1 s b a c → (SimpleGraph.fromRel (fun a c =>
        r1Old D e o1 s σ a c ∨ r1New D e o1 s b a c)).Reachable a c :=
      fun a c h => reach_of_rel (Or.inr h)
    refine card_unori e (D.rel σ) (r1Old D e o1 s σ) (r1New D e o1 s b)
      (r1Old_fe D e o1 s σ) (r1Old_lift D e o1 s σ) (r1New_unori D e o1 s b hb') ⟨?_, ?_⟩
    · rcases h1 with h | h
      · exact hR _ _ h
      · exact (hR _ _ h).symm
    · rcases h2 with h | h
      · exact hR _ _ h
      · exact (hR _ _ h).symm

theorem r1_lazos (σ : D.Cross → Bool) (b : Bool) :
    (r1 D e o1 s).lazos ((r1State D e o1 s).symm (σ, b)) =
      D.lazos σ + (if b == s then 1 else 0) := by
  unfold lazos
  rw [r1_card]
  change _ + D.free = _
  ring

theorem r1_weight {K : Type*} [Field K] (A : K) (σ : D.Cross → Bool) (b : Bool) :
    (∏ z : (r1 D e o1 s).Cross, if (r1State D e o1 s).symm (σ, b) z then A else A⁻¹) =
      (∏ x : D.Cross, if σ x then A else A⁻¹) * (if b then A else A⁻¹) := by
  rw [Fintype.prod_equiv (r1Cross D e o1 s) _
    (fun w => if (r1State D e o1 s).symm (σ, b) ((r1Cross D e o1 s).symm w) then A else A⁻¹)
    (by intro z; simp)]
  rw [Fintype.prod_sum_type]
  simp [r1State_symm_inl, r1State_symm_inr]

theorem lazos_pos [Nonempty ι] (σ : D.Cross → Bool) : 1 ≤ D.lazos σ := by
  unfold lazos
  haveI : Nonempty (D.graph σ).ConnectedComponent :=
    ⟨(D.graph σ).connectedComponentMk (Classical.arbitrary ι)⟩
  have : 0 < Nat.card (D.graph σ).ConnectedComponent := Nat.card_pos
  omega

/-- **R1 sobre una arista existente.** Insertar un rizo de signo `s` multiplica el corchete por
`-A³` (si `s = true`) o por `-A⁻³` (si `s = false`). -/
theorem bracket_r1 {K : Type*} [Field K] (A : K) (hA : A ≠ 0) [Nonempty ι] :
    (r1 D e o1 s).bracket A = (if s then -A ^ 3 else -A⁻¹ ^ 3) * D.bracket A := by
  unfold bracket
  rw [← (r1State D e o1 s).symm.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_bool]
  simp only [r1_weight, r1_lazos]
  obtain ⟨l, hl⟩ : ∃ l, D.lazos σ = l + 1 := ⟨D.lazos σ - 1, by have := lazos_pos D σ; omega⟩
  rw [hl]
  exact sum_new_crossing A hA s _ l

end GDiag

/-! ### R1 sobre una circunferencia libre -/

namespace GDiag

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι) (o1 s : Bool)

/-- Rizo sobre una circunferencia libre: dos letras nuevas `x → y → x` que forman su propio
ciclo, y una circunferencia libre menos. -/
def r1F : GDiag (ι ⊕ Bool) where
  next :=
    { toFun := Sum.map D.next not
      invFun := Sum.map D.next.symm not
      left_inv := by rintro (i | b) <;> simp
      right_inv := by rintro (i | b) <;> simp }
  partner
    | .inl i => .inl (D.partner i)
    | .inr b => .inr (!b)
  ovr
    | .inl i => D.ovr i
    | .inr b => xor o1 b
  sign
    | .inl i => D.sign i
    | .inr _ => s
  partner_partner := by
    rintro (i | b)
    · simp [D.partner_partner]
    · simp
  partner_ne := by
    rintro (i | b)
    · simp [D.partner_ne]
    · cases b <;> simp
  ovr_partner := by
    rintro (i | b)
    · simpa using D.ovr_partner i
    · cases o1 <;> cases b <;> rfl
  sign_partner := by
    rintro (i | b)
    · simpa using D.sign_partner i
    · rfl
  free := D.free - 1

@[simp] theorem r1F_prev_inl (i : ι) : (r1F D o1 s).prev (.inl i) = .inl (D.prev i) := rfl

@[simp] theorem r1F_prev_inr (b : Bool) : (r1F D o1 s).prev (.inr b) = .inr (!b) := rfl

@[simp] theorem r1F_partner_inl (i : ι) :
    (r1F D o1 s).partner (.inl i) = .inl (D.partner i) := rfl

@[simp] theorem r1F_partner_inr (b : Bool) : (r1F D o1 s).partner (.inr b) = .inr (!b) := rfl

@[simp] theorem r1F_sign_inl (i : ι) : (r1F D o1 s).sign (.inl i) = D.sign i := rfl

@[simp] theorem r1F_sign_inr (b : Bool) : (r1F D o1 s).sign (.inr b) = s := rfl

@[simp] theorem r1F_ovr_inl (i : ι) : (r1F D o1 s).ovr (.inl i) = D.ovr i := rfl

@[simp] theorem r1F_ovr_inr (b : Bool) : (r1F D o1 s).ovr (.inr b) = xor o1 b := rfl

/-- Los cruces de `D'` son los de `D` más el nuevo. -/
def r1FCross : (r1F D o1 s).Cross ≃ D.Cross ⊕ Unit where
  toFun z :=
    match z with
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr _, _⟩ => .inr ()
  invFun w :=
    match w with
    | .inl x => ⟨.inl x.1, x.2⟩
    | .inr _ => ⟨.inr (!o1), by cases o1 <;> rfl⟩
  left_inv := by
    rintro ⟨z, h⟩
    rcases z with i | b
    · rfl
    · have hb : b = !o1 := by
        simp only [r1F_ovr_inr] at h
        cases o1 <;> cases b <;> simp_all
      subst hb
      rfl
  right_inv := by
    rintro (x | u)
    · rfl
    · rfl

/-- Los estados de `D'` son los de `D` junto con el estado del cruce nuevo. -/
def r1FState : ((r1F D o1 s).Cross → Bool) ≃ (D.Cross → Bool) × Bool where
  toFun σ' := (fun x => σ' ((r1FCross D o1 s).symm (.inl x)),
    σ' ((r1FCross D o1 s).symm (.inr ())))
  invFun p := fun z => Sum.elim p.1 (fun _ => p.2) (r1FCross D o1 s z)
  left_inv := by
    intro σ'
    funext z
    rcases h : r1FCross D o1 s z with x | u
    · have hz : (r1FCross D o1 s).symm (.inl x) = z := (Equiv.symm_apply_eq _).2 h.symm
      simp only [h, Sum.elim_inl, hz]
    · have hz : (r1FCross D o1 s).symm (.inr ()) = z := by
        rw [Equiv.symm_apply_eq, h]
      simp only [h, Sum.elim_inr, hz]
  right_inv := by
    rintro ⟨σ, b⟩
    refine Prod.ext (funext fun x => ?_) ?_
    · simp
    · simp

theorem r1FState_symm_inl (σ : D.Cross → Bool) (b : Bool) (x : D.Cross) :
    (r1FState D o1 s).symm (σ, b) ((r1FCross D o1 s).symm (.inl x)) = σ x := by
  simp [r1FState]

theorem r1FState_symm_inr (σ : D.Cross → Bool) (b : Bool) :
    (r1FState D o1 s).symm (σ, b) ((r1FCross D o1 s).symm (.inr ())) = b := by
  simp [r1FState]

/-- Parte del grafo que viene de los cruces viejos. -/
def r1FOld (σ : D.Cross → Bool) (a c : ι ⊕ Bool) : Prop :=
  ∃ x : D.Cross, (r1F D o1 s).smoothRel (.inl x.1) (σ x == D.sign x.1) a c

/-- Parte del grafo que viene del cruce nuevo. -/
def r1FNew (b : Bool) (a c : ι ⊕ Bool) : Prop :=
  (r1F D o1 s).smoothRel (.inr (!o1)) (b == s) a c

theorem r1F_rel_iff (σ : D.Cross → Bool) (b : Bool) (a c : ι ⊕ Bool) :
    (r1F D o1 s).rel ((r1FState D o1 s).symm (σ, b)) a c ↔
      r1FOld D o1 s σ a c ∨ r1FNew D o1 s b a c := by
  unfold rel r1FOld r1FNew
  refine (Equiv.exists_congr_left (r1FCross D o1 s)).trans ?_
  rw [Sum.exists]
  apply or_congr
  · apply exists_congr
    intro x
    rw [r1FState_symm_inl]
    rfl
  · constructor
    · rintro ⟨u, h⟩
      cases u
      rw [r1FState_symm_inr] at h
      exact h
    · intro h
      exact ⟨(), by rw [r1FState_symm_inr]; exact h⟩

theorem r1FOld_iff (σ : D.Cross → Bool) (a c : ι ⊕ Bool) :
    r1FOld D o1 s σ a c ↔ ∃ a' c', a = .inl a' ∧ c = .inl c' ∧ D.rel σ a' c' := by
  constructor
  · rintro ⟨x, h⟩
    rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, rfl, rfl, x, Or.inl ⟨ho, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨_, _, rfl, rfl, x, Or.inl ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact ⟨_, _, rfl, rfl, x, Or.inr ⟨ho, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨_, _, rfl, rfl, x, Or.inr ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro ⟨a', c', rfl, rfl, x, h⟩
    refine ⟨x, ?_⟩
    rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨ho, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨ho, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨ho, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨ho, Or.inr ⟨rfl, rfl⟩⟩

theorem r1FNew_ori (b : Bool) (hb : (b == s) = true) (a c : ι ⊕ Bool) :
    r1FNew D o1 s b a c ↔ (a = .inr false ∧ c = .inr false) ∨ (a = .inr true ∧ c = .inr true) := by
  cases o1 <;> simp [r1FNew, smoothRel, hb, or_comm]

theorem r1FNew_unori (b : Bool) (hb : (b == s) = false) (a c : ι ⊕ Bool) :
    r1FNew D o1 s b a c ↔ (a = .inr false ∧ c = .inr true) ∨ (a = .inr true ∧ c = .inr false) := by
  cases o1 <;> simp [r1FNew, smoothRel, hb, or_comm]

theorem r1FNew_inr (b : Bool) (a c : ι ⊕ Bool) (h : r1FNew D o1 s b a c) :
    (∃ u, a = .inr u) ∧ ∃ v, c = .inr v := by
  by_cases hb : (b == s) = true
  · rcases (r1FNew_ori D o1 s b hb a c).1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨⟨_, rfl⟩, _, rfl⟩
  · have hb' : (b == s) = false := by simpa using hb
    rcases (r1FNew_unori D o1 s b hb' a c).1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨⟨_, rfl⟩, _, rfl⟩

theorem r1F_graph_eq (σ : D.Cross → Bool) (b : Bool) :
    (r1F D o1 s).graph ((r1FState D o1 s).symm (σ, b)) =
      SimpleGraph.fromRel (fun a c => r1FOld D o1 s σ a c ∨ r1FNew D o1 s b a c) := by
  unfold graph
  congr 1
  funext a c
  exact propext (r1F_rel_iff D o1 s σ b a c)

theorem r1F_card (σ : D.Cross → Bool) (b : Bool) :
    Nat.card ((r1F D o1 s).graph ((r1FState D o1 s).symm (σ, b))).ConnectedComponent =
      Nat.card (D.graph σ).ConnectedComponent + (if b == s then 2 else 1) := by
  rw [r1F_graph_eq]
  set R : ι ⊕ Bool → ι ⊕ Bool → Prop := fun a c => r1FOld D o1 s σ a c ∨ r1FNew D o1 s b a c
    with hR
  have hinl : ∀ a c, R (.inl a) (.inl c) ↔ D.rel σ a c := by
    intro a c
    constructor
    · rintro (h | h)
      · obtain ⟨a', c', h1, h2, h3⟩ := (r1FOld_iff D o1 s σ _ _).1 h
        cases h1
        cases h2
        exact h3
      · obtain ⟨⟨u, hu⟩, -⟩ := r1FNew_inr D o1 s b _ _ h
        cases hu
    · intro h
      exact Or.inl ((r1FOld_iff D o1 s σ _ _).2 ⟨a, c, rfl, rfl, h⟩)
  have hmix : ∀ a c, ¬ R (.inl a) (.inr c) := by
    rintro a c (h | h)
    · obtain ⟨a', c', -, h2, -⟩ := (r1FOld_iff D o1 s σ _ _).1 h
      cases h2
    · obtain ⟨⟨u, hu⟩, -⟩ := r1FNew_inr D o1 s b _ _ h
      cases hu
  have hmix' : ∀ a c, ¬ R (.inr a) (.inl c) := by
    rintro a c (h | h)
    · obtain ⟨a', c', h1, -, -⟩ := (r1FOld_iff D o1 s σ _ _).1 h
      cases h1
    · obtain ⟨-, ⟨u, hu⟩⟩ := r1FNew_inr D o1 s b _ _ h
      cases hu
  have h1 : ∀ a c, (SimpleGraph.fromRel R).Adj (.inl a) (.inl c) ↔ (D.graph σ).Adj a c := by
    intro a c
    unfold graph
    rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj, hinl, hinl]
    simp
  have h3 : ∀ a c, ¬ (SimpleGraph.fromRel R).Adj (.inl a) (.inr c) := by
    intro a c h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · exact hmix a c h
    · exact hmix' c a h
  have hold : ∀ a c, ¬ r1FOld D o1 s σ (.inr a) (.inr c) := by
    intro a c h
    obtain ⟨a', c', h1, -, -⟩ := (r1FOld_iff D o1 s σ _ _).1 h
    cases h1
  by_cases hb : (b == s) = true
  · rw [if_pos hb]
    have hori : ∀ a c, R (.inr a) (.inr c) → a = c := by
      rintro a c (h | h)
      · exact absurd h (hold a c)
      · rcases (r1FNew_ori D o1 s b hb _ _).1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (Sum.inr.inj h1).trans (Sum.inr.inj h2).symm
        · exact (Sum.inr.inj h1).trans (Sum.inr.inj h2).symm
    have h2 : ∀ a c, (SimpleGraph.fromRel R).Adj (.inr a) (.inr c) ↔
        (⊥ : SimpleGraph Bool).Adj a c := by
      intro a c
      rw [SimpleGraph.fromRel_adj, SimpleGraph.bot_adj]
      constructor
      · rintro ⟨hne, h | h⟩
        · exact absurd (congrArg Sum.inr (hori _ _ h)) hne
        · exact absurd (congrArg Sum.inr (hori _ _ h).symm) hne
      · intro h
        exact h.elim
    rw [card_cc_sum h1 h2 h3, card_cc_bot_bool]
  · have hb' : (b == s) = false := by simpa using hb
    rw [if_neg hb]
    have h2 : ∀ a c, (SimpleGraph.fromRel R).Adj (.inr a) (.inr c) ↔
        (⊤ : SimpleGraph Bool).Adj a c := by
      intro a c
      rw [SimpleGraph.fromRel_adj, SimpleGraph.top_adj]
      constructor
      · rintro ⟨hne, -⟩ h
        exact hne (congrArg Sum.inr h)
      · intro h
        refine ⟨fun h' => h (Sum.inr.inj h'), ?_⟩
        cases a <;> cases c
        · exact absurd rfl h
        · exact Or.inl (Or.inr ((r1FNew_unori D o1 s b hb' _ _).2 (Or.inl ⟨rfl, rfl⟩)))
        · exact Or.inl (Or.inr ((r1FNew_unori D o1 s b hb' _ _).2 (Or.inr ⟨rfl, rfl⟩)))
        · exact absurd rfl h
    rw [card_cc_sum h1 h2 h3, card_cc_top_bool]

theorem r1F_lazos (hfree : 1 ≤ D.free) (σ : D.Cross → Bool) (b : Bool) :
    (r1F D o1 s).lazos ((r1FState D o1 s).symm (σ, b)) =
      D.lazos σ + (if b == s then 1 else 0) := by
  unfold lazos
  rw [r1F_card]
  change _ + (D.free - 1) = _
  split_ifs <;> omega

theorem r1F_weight {K : Type*} [Field K] (A : K) (σ : D.Cross → Bool) (b : Bool) :
    (∏ z : (r1F D o1 s).Cross, if (r1FState D o1 s).symm (σ, b) z then A else A⁻¹) =
      (∏ x : D.Cross, if σ x then A else A⁻¹) * (if b then A else A⁻¹) := by
  rw [Fintype.prod_equiv (r1FCross D o1 s) _
    (fun w => if (r1FState D o1 s).symm (σ, b) ((r1FCross D o1 s).symm w) then A else A⁻¹)
    (by intro z; simp)]
  rw [Fintype.prod_sum_type]
  simp [r1FState_symm_inl, r1FState_symm_inr]

/-- **R1 sobre una circunferencia libre**: de `D` con `free ≥ 1` a `D'` con una circunferencia
libre menos y un rizo aislado. Mismo factor que en `bracket_r1`. -/
theorem bracket_r1_free {K : Type*} [Field K] (A : K) (hA : A ≠ 0) (hfree : 1 ≤ D.free) :
    (r1F D o1 s).bracket A = (if s then -A ^ 3 else -A⁻¹ ^ 3) * D.bracket A := by
  unfold bracket
  rw [← (r1FState D o1 s).symm.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_bool]
  simp only [r1F_weight, r1F_lazos D o1 s hfree]
  have hpos : 1 ≤ D.lazos σ := by
    unfold lazos
    omega
  obtain ⟨l, hl⟩ : ∃ l, D.lazos σ = l + 1 := ⟨D.lazos σ - 1, by omega⟩
  rw [hl]
  exact sum_new_crossing A hA s _ l

end GDiag

/-! ### Ejemplo mínimo y forma con contadores -/

namespace GDiag

/-- La circunferencia sin cruces (una componente libre). -/
def emptyCircle : GDiag Empty where
  next := Equiv.refl _
  partner := fun i => i
  ovr := fun _ => false
  sign := fun _ => false
  partner_partner := fun _ => rfl
  partner_ne := fun i => i.elim
  ovr_partner := fun i => i.elim
  sign_partner := fun _ => rfl
  free := 1

/-- Normalización: `⟨círculo⟩ = 1`. -/
theorem bracket_emptyCircle {K : Type*} [Field K] (A : K) : emptyCircle.bracket A = 1 := by
  haveI : IsEmpty emptyCircle.Cross := ⟨fun x => x.1.elim⟩
  unfold bracket
  rw [Fintype.sum_unique]
  have hE : ∀ σ : emptyCircle.Cross → Bool,
      IsEmpty (emptyCircle.graph σ).ConnectedComponent := fun σ =>
    ⟨fun c => by
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h v => exact v.elim⟩
  have hl : ∀ σ : emptyCircle.Cross → Bool, emptyCircle.lazos σ = 1 := by
    intro σ
    haveI := hE σ
    unfold lazos
    rw [Nat.card_of_isEmpty]
    rfl
  simp [hl]

/-- Un rizo aislado (dos letras, un cruce) de signo `s`, obtenido por R1 sobre la circunferencia
libre. -/
def kink (s : Bool) : GDiag (Empty ⊕ Bool) := r1F emptyCircle true s

/-- El corchete del rizo aislado es `-A³` o `-A⁻³`. -/
theorem bracket_kink {K : Type*} [Field K] (A : K) (hA : A ≠ 0) (s : Bool) :
    (kink s).bracket A = if s then -A ^ 3 else -A⁻¹ ^ 3 := by
  unfold kink
  rw [bracket_r1_free emptyCircle true s A hA (by decide), bracket_emptyCircle, mul_one]

/-- El peso `∏ (A o B)` es `A^#A * B^#B`, con `B = A⁻¹`. -/
theorem weight_eq_pow {ι : Type} [DecidableEq ι] [Fintype ι] {K : Type*} [Field K] (A : K)
    (D : GDiag ι) (σ : D.Cross → Bool) :
    (∏ x : D.Cross, if σ x then A else A⁻¹) =
      A ^ (Finset.univ.filter fun x => σ x = true).card *
        A⁻¹ ^ (Finset.univ.filter fun x => ¬ σ x = true).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]

end GDiag

#print axioms GDiag.bracket_map
#print axioms GDiag.bracket_r1
#print axioms GDiag.bracket_r1_free
#print axioms GDiag.bracket_kink
#print axioms GDiag.bracket_emptyCircle

end TMENudos.Invariancia
