import TMENudos.Etapa1_Invariancia

/-!
# Etapa 1 (spike M4, R2): invariancia del corchete de Kauffman bajo el movimiento R2

Archivo NUEVO; no forma parte de `TMENudos.lean`. Sigue la técnica de `Etapa1_Invariancia.lean`
(R1): diagramas de Gauss abstractos `GDiag`, estados
`D'.Cross → Bool ≃ (D.Cross → Bool) × Bool × Bool` y conteo de componentes con
`card_cc_eq` / `card_cc_succ'`.

## El movimiento
Dadas dos aristas distintas `e ≠ f`, `ov` (la hebra de `e` pasa por encima), `par` (las dos hebras
van en el mismo sentido) y `s` (signo del cruce `a`; el `b` tiene signo `!s`), se insertan en `e`
las letras `a₁, b₁` (con `ovr = ov`) y en `f` las letras `a₂, b₂` (`ovr = !ov`), en ese orden si
`par`, en el orden `b₂, a₂` si no. Los tipos: `ι ⊕ (Bool × Bool)` con `inr (c, k)`, `c` = cruce
(`false` = a, `true` = b) y `k` = hebra (`false` = la de `e`, `true` = la de `f`).

## PASO 0: comprobación numérica previa (versión de listas de `Etapa1_GaussWord`)
Se construyó `r2w w i j ov par s` con `List.zipIdx`, insertando tras la posición `i` las letras
`⟨la, ov, s⟩, ⟨lb, ov, !s⟩` y tras la `j` las `⟨la, !ov, s⟩, ⟨lb, !ov, !s⟩` (en el orden `a₂ b₂` si
`par`, `b₂ a₂` si no), con etiquetas frescas `la = fresh w`, `lb = la + 1`. Se evaluó
`Word.bracket` en `ℚ` con `A = 2` y `A = 3`, para TODAS las parejas de posiciones `i ≠ j`:

| conjunto de palabras                                   | pares (i,j) | fallos por combinación |
|--------------------------------------------------------|-------------|------------------------|
| todas las palabras bien formadas de 1 cruce (con signos)| 8           | 0                      |
| todas las palabras bien formadas de 2 cruces            | 576         | 0                      |
| trébol y su espejo                                      | 60          | 0                      |
| 26 palabras de 3 cruces (una de cada 37, no planares incluidas) | 780 | 0                      |

y esto para cada una de las 8 combinaciones `(ov, par, s) ∈ Bool³`, con `A = 2` y `A = 3`:

| ov    | par   | s     | invariante |
|-------|-------|-------|------------|
| true  | true  | true  | sí         |
| true  | true  | false | sí         |
| true  | false | true  | sí         |
| true  | false | false | sí         |
| false | true  | true  | sí         |
| false | true  | false | sí         |
| false | false | true  | sí         |
| false | false | false | sí         |

Control negativo: con la regla de signos equivocada (los dos cruces con el MISMO signo) las 8
combinaciones fallan en TODAS las palabras probadas (8/8, 576/576, 60/60, 780/780), así que la
prueba tiene poder discriminante. Conclusión: la regla `(s, !s)` es la correcta y las 8
combinaciones son R2 válidos; el teorema se demuestra para las 8 (para cualquier `ov par s`).
Observación: no hace falta exigir que `e` y `f` estén en una misma cara: el corchete de un código de
Gauss abstracto es un invariante de nudos virtuales, para los que R2 es válido entre aristas
cualesquiera.
-/


namespace TMENudos.Invariancia

/-! ### Lemas genéricos de conteo de componentes -/

section GraphR2

variable {α β : Type}

theorem reach_of_or_left {r s : α → α → Prop} {a b : α} (h : r a b) :
    (SimpleGraph.fromRel fun x y => r x y ∨ s x y).Reachable a b :=
  reach_of_rel (Or.inl h)

theorem reach_of_or_right {r s : α → α → Prop} {a b : α} (h : s a b) :
    (SimpleGraph.fromRel fun x y => r x y ∨ s x y).Reachable a b :=
  reach_of_rel (Or.inr h)

/-- Como `card_cc_succ`, pero la parte que se pierde (`f b = none`) puede tener varios vértices,
con tal de ser conexa y cerrada (sin aristas hacia el resto). -/
theorem card_cc_succ' [Finite α] {G : SimpleGraph α} {G' : SimpleGraph β} (v0 : β)
    (f : β → Option α) (g : α → β) (hv0 : f v0 = none)
    (hcl : ∀ a b, G'.Adj a b → (f a = none ↔ f b = none))
    (hconn : ∀ a b, f a = none → f b = none → G'.Reachable a b)
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
      have hb : f b = none := (hcl a b h).1 ha
      simp only [F, ha, hb, Option.map_none]
    | some a' =>
      cases hb : f b with
      | none => exact absurd ((hcl a b h).2 hb) (by simp [ha])
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
          simp only [F, hb, Option.map_none, hI0]
          exact SimpleGraph.ConnectedComponent.eq.2 (hconn v0 b hv0 hb)
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

/-- Cambio de grafo por retracción: `π : α → β` incluye, `ρ : β → α` retrae, con
relaciones "viejas" `O` que se corresponden y relaciones "nuevas" `N` locales. -/
theorem card_local_eq (π : α → β) (ρ : β → α) (hρπ : ∀ x, ρ (π x) = x)
    (Oβ Nβ : β → β → Prop) (Oα Nα : α → α → Prop)
    (hO1 : ∀ a c, Oβ a c → ∃ x y, a = π x ∧ c = π y ∧ Oα x y)
    (hO2 : ∀ x y, Oα x y → Oβ (π x) (π y))
    (hN1 : ∀ a c, Nβ a c →
      (SimpleGraph.fromRel fun x y => Oα x y ∨ Nα x y).Reachable (ρ a) (ρ c))
    (hN2 : ∀ x y, Nα x y →
      (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).Reachable (π x) (π y))
    (hmid : ∀ b, (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).Reachable (π (ρ b)) b) :
    Nat.card (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y => Oα x y ∨ Nα x y).ConnectedComponent := by
  refine card_cc_eq ρ π ?_ ?_ ?_ ?_
  · intro a c h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · obtain ⟨x, y, rfl, rfl, hxy⟩ := hO1 a c h
        rw [hρπ, hρπ]
        exact reach_of_or_left hxy
      · exact hN1 a c h
    · rcases h with h | h
      · obtain ⟨x, y, rfl, rfl, hxy⟩ := hO1 c a h
        rw [hρπ, hρπ]
        exact (reach_of_or_left hxy).symm
      · exact (hN1 c a h).symm
  · intro x y h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · exact reach_of_or_left (hO2 x y h)
      · exact hN2 x y h
    · rcases h with h | h
      · exact (reach_of_or_left (hO2 y x h)).symm
      · exact (hN2 y x h).symm
  · intro x
    rw [hρπ]
  · exact hmid

/-- Como `card_local_eq`, pero las aristas intermedias (`ρ b = none`) forman una componente
propia, que aporta una componente más. -/
theorem card_local_circ [Finite α] (π : α → β) (ρ : β → Option α) (v0 : β) (hv0 : ρ v0 = none)
    (hρπ : ∀ x, ρ (π x) = some x)
    (Oβ Nβ : β → β → Prop) (Oα Nα : α → α → Prop)
    (hO1 : ∀ a c, Oβ a c → ∃ x y, a = π x ∧ c = π y ∧ Oα x y)
    (hO2 : ∀ x y, Oα x y → Oβ (π x) (π y))
    (hN1 : ∀ a c x y, Nβ a c → ρ a = some x → ρ c = some y →
      (SimpleGraph.fromRel fun x y => Oα x y ∨ Nα x y).Reachable x y)
    (hN2 : ∀ x y, Nα x y →
      (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).Reachable (π x) (π y))
    (hcl : ∀ a c, Nβ a c → (ρ a = none ↔ ρ c = none))
    (hconn : ∀ a c, ρ a = none → ρ c = none →
      (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).Reachable a c)
    (hmid : ∀ b x, ρ b = some x →
      (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).Reachable (π x) b) :
    Nat.card (SimpleGraph.fromRel fun a c => Oβ a c ∨ Nβ a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y => Oα x y ∨ Nα x y).ConnectedComponent + 1 := by
  refine card_cc_succ' v0 ρ π hv0 ?_ hconn ?_ ?_ hρπ hmid
  · intro a c h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · obtain ⟨x, y, rfl, rfl, -⟩ := hO1 a c h
        simp [hρπ]
      · exact hcl a c h
    · rcases h with h | h
      · obtain ⟨x, y, rfl, rfl, -⟩ := hO1 c a h
        simp [hρπ]
      · exact (hcl c a h).symm
  · intro a c x y h ha hc
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · obtain ⟨x', y', rfl, rfl, hxy⟩ := hO1 a c h
        rw [hρπ] at ha hc
        cases ha
        cases hc
        exact reach_of_or_left hxy
      · exact hN1 a c x y h ha hc
    · rcases h with h | h
      · obtain ⟨x', y', rfl, rfl, hxy⟩ := hO1 c a h
        rw [hρπ] at ha hc
        cases ha
        cases hc
        exact (reach_of_or_left hxy).symm
      · exact (hN1 c a y x h hc ha).symm
  · intro x y h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · exact reach_of_or_left (hO2 x y h)
      · exact hN2 x y h
    · rcases h with h | h
      · exact (reach_of_or_left (hO2 y x h)).symm
      · exact (hN2 y x h).symm

end GraphR2

namespace GDiag

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Sucesor cíclico tras un R2: en la arista `e` se insertan `a₁ → b₁` (`e → a₁ → b₁ → next e`)
y en la arista `f` las letras `a₂, b₂` (en ese orden si `par`, al revés si no).
Las letras nuevas son `inr (c, k)`: `c = false` es el cruce `a`, `c = true` el cruce `b`;
`k = false` es la hebra de `e` y `k = true` la de `f`. -/
def r2Next (D : GDiag ι) (e f : ι) (hef : e ≠ f) (par : Bool) :
    Equiv.Perm (ι ⊕ (Bool × Bool)) where
  toFun
    | .inl i => if i = e then .inr (false, false) else if i = f then .inr (!par, true)
        else .inl (D.next i)
    | .inr (c, false) => if c then .inl (D.next e) else .inr (true, false)
    | .inr (c, true) => if c = par then .inl (D.next f) else .inr (par, true)
  invFun
    | .inl i => if i = D.next e then .inr (true, false) else if i = D.next f then .inr (par, true)
        else .inl (D.next.symm i)
    | .inr (c, false) => if c then .inr (false, false) else .inl e
    | .inr (c, true) => if c = par then .inr (!par, true) else .inl f
  left_inv := by
    have h5 : D.next f ≠ D.next e := fun h => hef (D.next.injective h).symm
    rintro (i | ⟨c, k⟩)
    · by_cases h1 : i = e
      · simp [h1]
      · by_cases h2 : i = f
        · subst h2
          cases par <;> simp [h1]
        · have h3 : D.next i ≠ D.next e := fun h => h1 (D.next.injective h)
          have h4 : D.next i ≠ D.next f := fun h => h2 (D.next.injective h)
          simp [h1, h2, h3, h4]
    · cases k <;> cases c <;> cases par <;> simp [h5]
  right_inv := by
    have h5 : D.next.symm e ≠ D.next.symm f := fun h => hef (D.next.symm.injective h)
    rintro (i | ⟨c, k⟩)
    · by_cases h1 : i = D.next e
      · subst h1
        simp
      · by_cases h2 : i = D.next f
        · subst h2
          cases par <;> simp [h1]
        · have h3 : D.next.symm i ≠ e := by
            rw [Ne, Equiv.symm_apply_eq]
            exact h1
          have h4 : D.next.symm i ≠ f := by
            rw [Ne, Equiv.symm_apply_eq]
            exact h2
          simp [h1, h2, h3, h4]
    · cases k <;> cases c <;> cases par <;> simp [hef.symm]

/-- El diagrama tras un R2 entre las aristas distintas `e` y `f`. La hebra de `e` pasa por encima
si `ov`; `par` indica que las dos hebras van en el mismo sentido; el cruce `a` tiene signo `s` y el
`b` signo `!s`. -/
def r2 (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool) : GDiag (ι ⊕ (Bool × Bool)) where
  next := r2Next D e f hef par
  partner
    | .inl i => .inl (D.partner i)
    | .inr (c, k) => .inr (c, !k)
  ovr
    | .inl i => D.ovr i
    | .inr (_, k) => xor ov k
  sign
    | .inl i => D.sign i
    | .inr (c, _) => xor s c
  partner_partner := by
    rintro (i | ⟨c, k⟩)
    · simp [D.partner_partner]
    · simp
  partner_ne := by
    rintro (i | ⟨c, k⟩)
    · simp [D.partner_ne]
    · cases k <;> simp
  ovr_partner := by
    rintro (i | ⟨c, k⟩)
    · simpa using D.ovr_partner i
    · cases ov <;> cases k <;> rfl
  sign_partner := by
    rintro (i | ⟨c, k⟩)
    · simpa using D.sign_partner i
    · rfl
  free := D.free

section Local

variable (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool)

theorem r2_prev_inl (z : ι) : (r2 D e f hef ov par s).prev (.inl z) =
    if z = D.next e then .inr (true, false) else if z = D.next f then .inr (par, true)
      else .inl (D.prev z) := rfl

theorem r2_prev_inl_next_e :
    (r2 D e f hef ov par s).prev (.inl (D.next e)) = .inr (true, false) := by
  rw [r2_prev_inl, if_pos rfl]

theorem r2_prev_inl_next_f : (r2 D e f hef ov par s).prev (.inl (D.next f)) = .inr (par, true) := by
  have h5 : D.next f ≠ D.next e := fun h => hef (D.next.injective h).symm
  rw [r2_prev_inl, if_neg h5, if_pos rfl]

theorem r2_prev_inl_of_ne {z : ι} (h1 : z ≠ D.next e) (h2 : z ≠ D.next f) :
    (r2 D e f hef ov par s).prev (.inl z) = .inl (D.prev z) := by
  rw [r2_prev_inl, if_neg h1, if_neg h2]

@[simp] theorem r2_prev_a1 : (r2 D e f hef ov par s).prev (.inr (false, false)) = .inl e := rfl

@[simp] theorem r2_prev_b1 : (r2 D e f hef ov par s).prev (.inr (true, false)) =
    .inr (false, false) := rfl

theorem r2_prev_f1 : (r2 D e f hef ov par s).prev (.inr (!par, true)) = .inl f := by
  cases par <;> rfl

theorem r2_prev_f2 : (r2 D e f hef ov par s).prev (.inr (par, true)) = .inr (!par, true) := by
  cases par <;> rfl

@[simp] theorem r2_partner_inl (i : ι) :
    (r2 D e f hef ov par s).partner (.inl i) = .inl (D.partner i) := rfl

@[simp] theorem r2_partner_inr (c k : Bool) :
    (r2 D e f hef ov par s).partner (.inr (c, k)) = .inr (c, !k) := rfl

@[simp] theorem r2_sign_inl (i : ι) : (r2 D e f hef ov par s).sign (.inl i) = D.sign i := rfl

@[simp] theorem r2_sign_inr (c k : Bool) : (r2 D e f hef ov par s).sign (.inr (c, k)) = xor s c :=
  rfl

@[simp] theorem r2_ovr_inl (i : ι) : (r2 D e f hef ov par s).ovr (.inl i) = D.ovr i := rfl

@[simp] theorem r2_ovr_inr (c k : Bool) : (r2 D e f hef ov par s).ovr (.inr (c, k)) = xor ov k :=
  rfl

end Local

/-! ### Estados: (estados de `D`) × (estado del cruce `a`) × (estado del cruce `b`) -/

section States

variable (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool)

/-- Los cruces de `D'` son los de `D` más los dos nuevos (`a` y `b`); la letra superior del
cruce nuevo `c` es `inr (c, !ov)`. -/
def r2Cross : (r2 D e f hef ov par s).Cross ≃ D.Cross ⊕ Bool where
  toFun z :=
    match z with
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr (c, _), _⟩ => .inr c
  invFun w :=
    match w with
    | .inl x => ⟨.inl x.1, x.2⟩
    | .inr c => ⟨.inr (c, !ov), by cases ov <;> rfl⟩
  left_inv := by
    rintro ⟨z, h⟩
    rcases z with i | ⟨c, k⟩
    · rfl
    · have hb : k = !ov := by
        simp only [r2_ovr_inr] at h
        cases ov <;> cases k <;> simp_all
      subst hb
      rfl
  right_inv := by
    rintro (x | c) <;> rfl

/-- Los estados de `D'` son los de `D` junto con los estados de los dos cruces nuevos. -/
def r2State : ((r2 D e f hef ov par s).Cross → Bool) ≃ (D.Cross → Bool) × Bool × Bool where
  toFun σ' := (fun x => σ' ((r2Cross D e f hef ov par s).symm (.inl x)),
    σ' ((r2Cross D e f hef ov par s).symm (.inr false)),
    σ' ((r2Cross D e f hef ov par s).symm (.inr true)))
  invFun p := fun z => Sum.elim p.1 (fun c => if c then p.2.2 else p.2.1)
    (r2Cross D e f hef ov par s z)
  left_inv := by
    intro σ'
    funext z
    rcases h : r2Cross D e f hef ov par s z with x | c
    · have hz : (r2Cross D e f hef ov par s).symm (.inl x) = z := (Equiv.symm_apply_eq _).2 h.symm
      simp only [h, Sum.elim_inl, hz]
    · have hz : (r2Cross D e f hef ov par s).symm (.inr c) = z := (Equiv.symm_apply_eq _).2 h.symm
      cases c <;> simp only [h, Sum.elim_inr, hz] <;> rfl
  right_inv := by
    rintro ⟨σ, ba, bb⟩
    refine Prod.ext (funext fun x => ?_) (Prod.ext ?_ ?_)
    · simp
    · simp
    · simp

theorem r2State_symm_inl (σ : D.Cross → Bool) (ba bb : Bool) (x : D.Cross) :
    (r2State D e f hef ov par s).symm (σ, ba, bb)
      ((r2Cross D e f hef ov par s).symm (.inl x)) = σ x := by
  simp [r2State]

theorem r2State_symm_a (σ : D.Cross → Bool) (ba bb : Bool) :
    (r2State D e f hef ov par s).symm (σ, ba, bb)
      ((r2Cross D e f hef ov par s).symm (.inr false)) = ba := by
  simp [r2State]

theorem r2State_symm_b (σ : D.Cross → Bool) (ba bb : Bool) :
    (r2State D e f hef ov par s).symm (σ, ba, bb)
      ((r2Cross D e f hef ov par s).symm (.inr true)) = bb := by
  simp [r2State]

theorem r2_rel_iff (σ : D.Cross → Bool) (ba bb : Bool) (a c : ι ⊕ (Bool × Bool)) :
    (r2 D e f hef ov par s).rel ((r2State D e f hef ov par s).symm (σ, ba, bb)) a c ↔
      (∃ x : D.Cross, (r2 D e f hef ov par s).smoothRel (.inl x.1) (σ x == D.sign x.1) a c) ∨
        (r2 D e f hef ov par s).smoothRel (.inr (false, !ov)) (ba == s) a c ∨
        (r2 D e f hef ov par s).smoothRel (.inr (true, !ov)) (bb == !s) a c := by
  unfold rel
  refine (Equiv.exists_congr_left (r2Cross D e f hef ov par s)).trans ?_
  rw [Sum.exists, Bool.exists_bool]
  apply or_congr
  · apply exists_congr
    intro x
    rw [r2State_symm_inl]
    rfl
  · apply or_congr
    · rw [r2State_symm_a]
      cases s <;> exact Iff.rfl
    · rw [r2State_symm_b]
      cases s <;> exact Iff.rfl

theorem r2_weight {K : Type*} [Field K] (A : K) (σ : D.Cross → Bool) (ba bb : Bool) :
    (∏ z : (r2 D e f hef ov par s).Cross,
        if (r2State D e f hef ov par s).symm (σ, ba, bb) z then A else A⁻¹) =
      (∏ x : D.Cross, if σ x then A else A⁻¹) *
        ((if ba then A else A⁻¹) * (if bb then A else A⁻¹)) := by
  rw [Fintype.prod_equiv (r2Cross D e f hef ov par s) _
    (fun w => if (r2State D e f hef ov par s).symm (σ, ba, bb)
      ((r2Cross D e f hef ov par s).symm w) then A else A⁻¹)
    (by intro z; simp)]
  rw [Fintype.prod_sum_type, Fintype.prod_bool]
  simp only [r2State_symm_inl, r2State_symm_a, r2State_symm_b]
  congr 1
  exact mul_comm _ _

end States

/-! ### La parte "vieja" del grafo de estados -/

section Old

/-- Colapso: las aristas nuevas de la hebra de `e` (resp. `f`) van a `e` (resp. `f`). -/
def fe2 (e f : ι) : ι ⊕ (Bool × Bool) → ι
  | .inl i => i
  | .inr (_, false) => e
  | .inr (_, true) => f

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem fe2_inl (e f i : ι) : fe2 e f (.inl i) = i := rfl

/-- Inclusión de las aristas "no intermedias": `inr true` es la última arista de la hebra `e`
(la que llega a `next e`) y `inr false` la última de la hebra `f`. -/
def pi2 (par : Bool) : ι ⊕ Bool → ι ⊕ (Bool × Bool)
  | .inl i => .inl i
  | .inr true => .inr (true, false)
  | .inr false => .inr (par, true)

variable (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool)

/-- Parte del grafo `G'_σ` que viene de los cruces viejos. -/
def r2Old (σ : D.Cross → Bool) (a c : ι ⊕ (Bool × Bool)) : Prop :=
  ∃ x : D.Cross, (r2 D e f hef ov par s).smoothRel (.inl x.1) (σ x == D.sign x.1) a c

theorem fe2_prev (z : ι) : fe2 e f ((r2 D e f hef ov par s).prev (.inl z)) = D.prev z := by
  by_cases h1 : z = D.next e
  · subst h1
    rw [r2_prev_inl_next_e]
    simp [fe2, prev]
  · by_cases h2 : z = D.next f
    · subst h2
      rw [r2_prev_inl_next_f]
      simp [fe2, prev]
    · rw [r2_prev_inl_of_ne D e f hef ov par s h1 h2]
      rfl

theorem prev_pi (z : ι) : ∃ u : ι ⊕ Bool,
    (r2 D e f hef ov par s).prev (.inl z) = pi2 par u ∧
      (u = .inl (D.prev z) ∨ (u = .inr true ∧ D.prev z = e) ∨ (u = .inr false ∧ D.prev z = f)) := by
  by_cases h1 : z = D.next e
  · subst h1
    refine ⟨.inr true, r2_prev_inl_next_e D e f hef ov par s, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    simp [prev]
  · by_cases h2 : z = D.next f
    · subst h2
      refine ⟨.inr false, r2_prev_inl_next_f D e f hef ov par s, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      simp [prev]
    · exact ⟨.inl (D.prev z), r2_prev_inl_of_ne D e f hef ov par s h1 h2, Or.inl rfl⟩

theorem r2Old_fe (σ : D.Cross → Bool) (a c : ι ⊕ (Bool × Bool))
    (h : r2Old D e f hef ov par s σ a c) : D.rel σ (fe2 e f a) (fe2 e f c) := by
  obtain ⟨x, h⟩ := h
  refine ⟨x, ?_⟩
  rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    simp [smoothRel, ho, fe2_prev D e f hef ov par s]

theorem r2Old_pi (σ : D.Cross → Bool) (a c : ι ⊕ (Bool × Bool))
    (h : r2Old D e f hef ov par s σ a c) :
    (∃ x, a = pi2 par x) ∧ ∃ y, c = pi2 par y := by
  obtain ⟨x, h⟩ := h
  obtain ⟨u1, hu1, -⟩ := prev_pi D e f hef ov par s x.1
  obtain ⟨u2, hu2, -⟩ := prev_pi D e f hef ov par s (D.partner x.1)
  rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨⟨u1, hu1⟩, .inl (D.partner x.1), rfl⟩
  · exact ⟨⟨u2, hu2⟩, .inl x.1, rfl⟩
  · exact ⟨⟨u1, hu1⟩, u2, hu2⟩
  · exact ⟨⟨.inl x.1, rfl⟩, .inl (D.partner x.1), rfl⟩

theorem r2Old_lift (σ : D.Cross → Bool) (a' c' : ι) (h : D.rel σ a' c') :
    ∃ x y : ι ⊕ Bool, r2Old D e f hef ov par s σ (pi2 par x) (pi2 par y) ∧
      (x = .inl a' ∨ (x = .inr true ∧ a' = e) ∨ (x = .inr false ∧ a' = f)) ∧
      (y = .inl c' ∨ (y = .inr true ∧ c' = e) ∨ (y = .inr false ∧ c' = f)) := by
  obtain ⟨x, h⟩ := h
  obtain ⟨u1, hu1, hu1'⟩ := prev_pi D e f hef ov par s x.1
  obtain ⟨u2, hu2, hu2'⟩ := prev_pi D e f hef ov par s (D.partner x.1)
  rcases h with ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨u1, .inl (D.partner x.1), ⟨x, Or.inl ⟨ho, Or.inl ⟨hu1.symm, rfl⟩⟩⟩, hu1', Or.inl rfl⟩
  · exact ⟨u2, .inl x.1, ⟨x, Or.inl ⟨ho, Or.inr ⟨hu2.symm, rfl⟩⟩⟩, hu2', Or.inl rfl⟩
  · exact ⟨u1, u2, ⟨x, Or.inr ⟨ho, Or.inl ⟨hu1.symm, hu2.symm⟩⟩⟩, hu1', hu2'⟩
  · exact ⟨.inl x.1, .inl (D.partner x.1), ⟨x, Or.inr ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩, Or.inl rfl,
      Or.inl rfl⟩

end Old

/-! ### La parte "nueva": los dos cruces insertados -/

section New

/-- La suavización de un cruce, simetrizada, no depende de cuál de sus dos letras se use. -/
theorem smooth_symm (D : GDiag ι) (x : ι) (ori : Bool) (a c : ι) :
    (D.smoothRel x ori a c ∨ D.smoothRel x ori c a) ↔
      (D.smoothRel (D.partner x) ori a c ∨ D.smoothRel (D.partner x) ori c a) := by
  unfold smoothRel
  rw [D.partner_partner]
  generalize D.prev x = px
  generalize D.prev (D.partner x) = pp
  generalize D.partner x = p
  cases ori <;> simp only [Bool.false_eq_true, false_and, true_and, false_or] <;> tauto

/-- Las aristas que unen los dos cruces nuevos, según el modo `par` de las hebras y la
orientación `oa`, `ob` de las suavizaciones de `a` y `b`. Aquí `E0 = inl e`, `E1 = a₁`,
`E2 = b₁` son las tres aristas de la hebra `e`; `F0 = inl f`, `F1`, `F2` las de la hebra `f`. -/
def Nloc (e f : ι) (par oa ob : Bool) (a c : ι ⊕ (Bool × Bool)) : Prop :=
  match par, oa, ob with
  | true, true, true =>
    (a = .inl e ∧ c = .inr (false, true)) ∨ (a = .inl f ∧ c = .inr (false, false)) ∨
    (a = .inr (false, false) ∧ c = .inr (true, true)) ∨
    (a = .inr (false, true) ∧ c = .inr (true, false))
  | true, false, false =>
    (a = .inl e ∧ c = .inl f) ∨ (a = .inr (false, false) ∧ c = .inr (false, true)) ∨
    (a = .inr (true, false) ∧ c = .inr (true, true))
  | true, true, false =>
    (a = .inl e ∧ c = .inr (false, true)) ∨ (a = .inl f ∧ c = .inr (false, false)) ∨
    (a = .inr (false, false) ∧ c = .inr (false, true)) ∨
    (a = .inr (true, false) ∧ c = .inr (true, true))
  | true, false, true =>
    (a = .inl e ∧ c = .inl f) ∨ (a = .inr (false, false) ∧ c = .inr (false, true)) ∨
    (a = .inr (false, false) ∧ c = .inr (true, true)) ∨
    (a = .inr (false, true) ∧ c = .inr (true, false))
  | false, true, true =>
    (a = .inl e ∧ c = .inr (false, true)) ∨ (a = .inr (false, false) ∧ c = .inr (true, true)) ∨
    (a = .inr (true, false) ∧ c = .inl f)
  | false, false, false =>
    (a = .inl e ∧ c = .inr (true, true)) ∨ (a = .inr (false, false) ∧ c = .inr (false, true)) ∨
    (a = .inr (false, false) ∧ c = .inl f) ∨ (a = .inr (true, false) ∧ c = .inr (true, true))
  | false, true, false =>
    (a = .inl e ∧ c = .inr (false, true)) ∨ (a = .inr (true, true) ∧ c = .inr (false, false)) ∨
    (a = .inr (false, false) ∧ c = .inl f) ∨ (a = .inr (true, false) ∧ c = .inr (true, true))
  | false, false, true =>
    (a = .inl e ∧ c = .inr (true, true)) ∨ (a = .inr (false, false) ∧ c = .inr (false, true)) ∨
    (a = .inr (false, false) ∧ c = .inr (true, true)) ∨ (a = .inl f ∧ c = .inr (true, false))

variable (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool)

theorem r2_prev_inr_true (c : Bool) : (r2 D e f hef ov par s).prev (.inr (c, true)) =
    if c = par then .inr (!par, true) else .inl f := rfl

theorem r2_newE_sym (oa ob : Bool) (a c : ι ⊕ (Bool × Bool)) :
    (((r2 D e f hef ov par s).smoothRel (.inr (false, false)) oa a c ∨
        (r2 D e f hef ov par s).smoothRel (.inr (true, false)) ob a c) ∨
      ((r2 D e f hef ov par s).smoothRel (.inr (false, false)) oa c a ∨
        (r2 D e f hef ov par s).smoothRel (.inr (true, false)) ob c a)) ↔
    (Nloc e f par oa ob a c ∨ Nloc e f par oa ob c a) := by
  cases par <;> cases oa <;> cases ob <;>
    simp [smoothRel, Nloc, r2_prev_inr_true] <;> aesop

theorem r2_new_sym (ba bb : Bool) (a c : ι ⊕ (Bool × Bool)) :
    (((r2 D e f hef ov par s).smoothRel (.inr (false, !ov)) (ba == s) a c ∨
        (r2 D e f hef ov par s).smoothRel (.inr (true, !ov)) (bb == !s) a c) ∨
      ((r2 D e f hef ov par s).smoothRel (.inr (false, !ov)) (ba == s) c a ∨
        (r2 D e f hef ov par s).smoothRel (.inr (true, !ov)) (bb == !s) c a)) ↔
    (Nloc e f par (ba == s) (bb == !s) a c ∨ Nloc e f par (ba == s) (bb == !s) c a) := by
  rw [← r2_newE_sym D e f hef ov par s (ba == s) (bb == !s) a c]
  have h1 := smooth_symm (r2 D e f hef ov par s) (.inr (false, false)) (ba == s) a c
  have h2 := smooth_symm (r2 D e f hef ov par s) (.inr (true, false)) (bb == !s) a c
  cases ov
  · simp only [r2_partner_inr, Bool.not_false] at h1 h2 ⊢
    tauto
  · simp only [Bool.not_true]

theorem r2_graph_eq (σ : D.Cross → Bool) (ba bb : Bool) :
    (r2 D e f hef ov par s).graph ((r2State D e f hef ov par s).symm (σ, ba, bb)) =
      SimpleGraph.fromRel
        (fun a c => r2Old D e f hef ov par s σ a c ∨ Nloc e f par (ba == s) (bb == !s) a c) := by
  ext a c
  unfold graph
  rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  apply and_congr_right
  intro _
  have h := r2_new_sym D e f hef ov par s ba bb a c
  rw [r2_rel_iff, r2_rel_iff]
  unfold r2Old
  tauto

end New

/-! ### Conteo de componentes por patrón local -/

section Counts

theorem reach_N {α : Type} {r s : α → α → Prop} {a b : α} (h : s a b ∨ s b a) :
    (SimpleGraph.fromRel fun x y => r x y ∨ s x y).Reachable a b := by
  rcases h with h | h
  · exact reach_of_or_right h
  · exact (reach_of_or_right h).symm

theorem reach_N2 {α : Type} {r s : α → α → Prop} {a b c : α} (h1 : s a b ∨ s b a)
    (h2 : s b c ∨ s c b) : (SimpleGraph.fromRel fun x y => r x y ∨ s x y).Reachable a c :=
  (reach_N h1).trans (reach_N h2)

theorem reach_N3 {α : Type} {r s : α → α → Prop} {a b c d : α} (h1 : s a b ∨ s b a)
    (h2 : s b c ∨ s c b) (h3 : s c d ∨ s d c) :
    (SimpleGraph.fromRel fun x y => r x y ∨ s x y).Reachable a d :=
  (reach_N2 h1 h2).trans (reach_N h3)

/-- Aristas del grafo reducido al identificar cada hebra con su arista final. -/
def Oa (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool) (σ : D.Cross → Bool)
    (x y : ι ⊕ Bool) : Prop :=
  r2Old D e f hef ov par s σ (pi2 par x) (pi2 par y)

/-- Patrón "identidad": `e` con su arista final, `f` con la suya. -/
def NI (e f : ι) (x y : ι ⊕ Bool) : Prop :=
  (x = .inl e ∧ y = .inr true) ∨ (x = .inl f ∧ y = .inr false)

/-- Patrón "reconectado". -/
def NR (e f : ι) (par : Bool) (x y : ι ⊕ Bool) : Prop :=
  match par with
  | true => (x = .inl e ∧ y = .inl f) ∨ (x = .inr true ∧ y = .inr false)
  | false => (x = .inl e ∧ y = .inr false) ∨ (x = .inr true ∧ y = .inl f)

/-- Retracción de las aristas intermedias a las representantes `r₁` (para `a₁`) y `r₂`
(para la primera arista de la hebra `f`). -/
def rho2 (par : Bool) (r₁ r₂ : ι ⊕ Bool) : ι ⊕ (Bool × Bool) → ι ⊕ Bool
  | .inl i => .inl i
  | .inr (c, false) => if c then .inr true else r₁
  | .inr (c, true) => if c = par then .inr false else r₂

/-- Como `rho2`, pero las aristas intermedias van a `none`. -/
def rho2o (par : Bool) : ι ⊕ (Bool × Bool) → Option (ι ⊕ Bool)
  | .inl i => some (.inl i)
  | .inr (c, false) => if c then some (.inr true) else none
  | .inr (c, true) => if c = par then some (.inr false) else none

omit [DecidableEq ι] [Fintype ι] in
theorem rho2_pi (par : Bool) (r₁ r₂ x : ι ⊕ Bool) : rho2 par r₁ r₂ (pi2 par x) = x := by
  rcases x with i | _ | _ <;> simp [rho2, pi2]

omit [DecidableEq ι] [Fintype ι] in
theorem rho2o_pi (par : Bool) (x : ι ⊕ Bool) : rho2o par (pi2 par x) = some x := by
  rcases x with i | _ | _ <;> simp [rho2o, pi2]

omit [DecidableEq ι] [Fintype ι] in
theorem rho2o_none (par : Bool) (b : ι ⊕ (Bool × Bool)) :
    rho2o par b = none ↔ (b = .inr (false, false) ∨ b = .inr (!par, true)) := by
  rcases b with i | ⟨c, k⟩
  · simp [rho2o]
  · cases k <;> cases c <;> cases par <;> simp [rho2o]

omit [DecidableEq ι] [Fintype ι] in
theorem rho2o_some (par : Bool) {b : ι ⊕ (Bool × Bool)} {x : ι ⊕ Bool}
    (h : rho2o par b = some x) : b = pi2 par x := by
  rcases b with i | ⟨c, k⟩
  · simp only [rho2o, Option.some.injEq] at h
    subst h
    rfl
  · cases k <;> cases c <;> cases par <;>
      simp only [rho2o, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
        Option.some.injEq] at h <;> subst h <;> rfl

local macro "reach_auto" : tactic => `(tactic| first
  | exact SimpleGraph.Reachable.refl _
  | (refine reach_N ?_; simp [Nloc, NI, NR, pi2]; done)
  | (refine reach_N2 (b := .inr (false, false)) ?_ ?_ <;> (simp [Nloc, pi2]; done))
  | (refine reach_N2 (b := .inr (false, true)) ?_ ?_ <;> (simp [Nloc, pi2]; done))
  | (refine reach_N2 (b := .inr (true, true)) ?_ ?_ <;> (simp [Nloc, pi2]; done))
  | (refine reach_N2 (b := .inr (true, false)) ?_ ?_ <;> (simp [Nloc, pi2]; done)))

variable (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov s : Bool) (σ : D.Cross → Bool)

theorem r2_hO1 (par : Bool) (a c : ι ⊕ (Bool × Bool)) (h : r2Old D e f hef ov par s σ a c) :
    ∃ x y, a = pi2 par x ∧ c = pi2 par y ∧ Oa D e f hef ov par s σ x y := by
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := r2Old_pi D e f hef ov par s σ a c h
  exact ⟨x, y, rfl, rfl, h⟩

/-- `par`, `a` orientada, `b` orientada: el patrón es la identidad. -/
theorem card_ID_tt :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov true s σ a c ∨ Nloc e f true true true a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov true s σ x y ∨ NI e f x y).ConnectedComponent := by
  refine card_local_eq (pi2 true) (rho2 true (.inl f) (.inl e)) (rho2_pi true _ _) _ _ _ _
    (r2_hO1 D e f hef ov s σ true) (fun x y h => h) ?_ ?_ ?_
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [rho2] <;>
      reach_auto
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N2 (b := .inr (false, true)) (by simp [Nloc, pi2]) (by simp [Nloc, pi2])
    · exact reach_N2 (b := .inr (false, false)) (by simp [Nloc, pi2]) (by simp [Nloc, pi2])
  · intro b
    rcases b with i | ⟨c, k⟩
    · exact SimpleGraph.Reachable.refl _
    · cases k <;> cases c <;> simp only [rho2, pi2] <;> reach_auto

/-- `par = false`, `a` y `b` no orientadas: el patrón es la identidad. -/
theorem card_ID_ff :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov false s σ a c ∨ Nloc e f false false false a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov false s σ x y ∨ NI e f x y).ConnectedComponent := by
  refine card_local_eq (pi2 false) (rho2 false (.inl f) (.inl e)) (rho2_pi false _ _) _ _ _ _
    (r2_hO1 D e f hef ov s σ false) (fun x y h => h) ?_ ?_ ?_
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [rho2] <;>
      reach_auto
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N2 (b := .inr (true, true)) (by simp [Nloc, pi2]) (by simp [Nloc, pi2])
    · exact reach_N2 (b := .inr (false, false)) (by simp [Nloc, pi2]) (by simp [Nloc, pi2])
  · intro b
    rcases b with i | ⟨c, k⟩
    · exact SimpleGraph.Reachable.refl _
    · cases k <;> cases c <;> simp only [rho2, pi2] <;> reach_auto

/-- Patrón reconectado, `par`, `a` orientada, `b` no. -/
theorem card_X_t :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov true s σ a c ∨ Nloc e f true true false a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov true s σ x y ∨ NR e f true x y).ConnectedComponent := by
  refine card_local_eq (pi2 true) (rho2 true (.inl e) (.inl e)) (rho2_pi true _ _) _ _ _ _
    (r2_hO1 D e f hef ov s σ true) (fun x y h => h) ?_ ?_ ?_
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [rho2] <;>
      reach_auto
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N3 (b := .inr (false, true)) (c := .inr (false, false))
        (by simp [Nloc, pi2]) (by simp [Nloc]) (by simp [Nloc, pi2])
    · exact reach_N (by simp [Nloc, pi2])
  · intro b
    rcases b with i | ⟨c, k⟩
    · exact SimpleGraph.Reachable.refl _
    · cases k <;> cases c <;> simp only [rho2, pi2] <;> reach_auto

/-- Patrón reconectado, `par`, `a` no orientada, `b` orientada. -/
theorem card_Y_t :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov true s σ a c ∨ Nloc e f true false true a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov true s σ x y ∨ NR e f true x y).ConnectedComponent := by
  refine card_local_eq (pi2 true) (rho2 true (.inr true) (.inr true)) (rho2_pi true _ _) _ _ _ _
    (r2_hO1 D e f hef ov s σ true) (fun x y h => h) ?_ ?_ ?_
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [rho2] <;>
      reach_auto
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N (by simp [Nloc, pi2])
    · exact reach_N3 (b := .inr (false, true)) (c := .inr (false, false))
        (by simp [Nloc, pi2]) (by simp [Nloc]) (by simp [Nloc, pi2])
  · intro b
    rcases b with i | ⟨c, k⟩
    · exact SimpleGraph.Reachable.refl _
    · cases k <;> cases c <;> simp only [rho2, pi2] <;> reach_auto

/-- Patrón reconectado, `par = false`, `a` orientada, `b` no. -/
theorem card_X_f :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov false s σ a c ∨ Nloc e f false true false a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov false s σ x y ∨ NR e f false x y).ConnectedComponent := by
  refine card_local_eq (pi2 false) (rho2 false (.inl f) (.inl f)) (rho2_pi false _ _) _ _ _ _
    (r2_hO1 D e f hef ov s σ false) (fun x y h => h) ?_ ?_ ?_
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [rho2] <;>
      reach_auto
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N (by simp [Nloc, pi2])
    · exact reach_N3 (b := .inr (true, true)) (c := .inr (false, false))
        (by simp [Nloc, pi2]) (by simp [Nloc]) (by simp [Nloc, pi2])
  · intro b
    rcases b with i | ⟨c, k⟩
    · exact SimpleGraph.Reachable.refl _
    · cases k <;> cases c <;> simp only [rho2, pi2] <;> reach_auto

/-- Patrón reconectado, `par = false`, `a` no orientada, `b` orientada. -/
theorem card_Y_f :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov false s σ a c ∨ Nloc e f false false true a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov false s σ x y ∨ NR e f false x y).ConnectedComponent := by
  refine card_local_eq (pi2 false) (rho2 false (.inl e) (.inl e)) (rho2_pi false _ _) _ _ _ _
    (r2_hO1 D e f hef ov s σ false) (fun x y h => h) ?_ ?_ ?_
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [rho2] <;>
      reach_auto
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N3 (b := .inr (true, true)) (c := .inr (false, false))
        (by simp [Nloc, pi2]) (by simp [Nloc]) (by simp [Nloc, pi2])
    · exact reach_N (by simp [Nloc, pi2])
  · intro b
    rcases b with i | ⟨c, k⟩
    · exact SimpleGraph.Reachable.refl _
    · cases k <;> cases c <;> simp only [rho2, pi2] <;> reach_auto

/-- Patrón "reconectado con lazo aislado" (`par`, ni `a` ni `b` orientadas): una componente más. -/
theorem card_C_t :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov true s σ a c ∨ Nloc e f true false false a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov true s σ x y ∨ NR e f true x y).ConnectedComponent + 1 := by
  refine card_local_circ (pi2 true) (rho2o true) (.inr (false, false)) rfl (rho2o_pi true)
    _ _ _ _ (r2_hO1 D e f hef ov s σ true) (fun x y h => h) ?_ ?_ ?_ ?_ ?_
  · intro a c x y h ha hc
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [rho2o, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.some.injEq]
        at ha hc <;>
      (subst ha; subst hc; reach_auto)
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N (by simp [Nloc, pi2])
    · exact reach_N (by simp [Nloc, pi2])
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [rho2o]
  · intro a c ha hc
    rcases (rho2o_none _ _).1 ha with rfl | rfl <;> rcases (rho2o_none _ _).1 hc with rfl | rfl <;>
      reach_auto
  · intro b x hb
    rw [rho2o_some _ hb]

/-- Como `card_C_t`, con `par = false` (`a` y `b` orientadas). -/
theorem card_C_f :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov false s σ a c ∨ Nloc e f false true true a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov false s σ x y ∨ NR e f false x y).ConnectedComponent + 1 := by
  refine card_local_circ (pi2 false) (rho2o false) (.inr (false, false)) rfl (rho2o_pi false)
    _ _ _ _ (r2_hO1 D e f hef ov s σ false) (fun x y h => h) ?_ ?_ ?_ ?_ ?_
  · intro a c x y h ha hc
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [rho2o, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.some.injEq]
        at ha hc <;>
      (subst ha; subst hc; reach_auto)
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reach_N (by simp [Nloc, pi2])
    · exact reach_N (by simp [Nloc, pi2])
  · intro a c h
    simp only [Nloc] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [rho2o]
  · intro a c ha hc
    rcases (rho2o_none _ _).1 ha with rfl | rfl <;> rcases (rho2o_none _ _).1 hc with rfl | rfl <;>
      reach_auto
  · intro b x hb
    rw [rho2o_some _ hb]

end Counts


/-! ### Número de lazos de cada estado y teorema principal -/

section Main

/-- Colapso de `ι ⊕ Bool` sobre `ι`: `inr true` va a `e` e `inr false` a `f`. -/
def colr (e f : ι) : ι ⊕ Bool → ι
  | .inl i => i
  | .inr true => e
  | .inr false => f

omit [DecidableEq ι] [Fintype ι] in
theorem fe2_pi2 (e f : ι) (par : Bool) (x : ι ⊕ Bool) : fe2 e f (pi2 par x) = colr e f x := by
  rcases x with i | _ | _ <;> rfl

variable (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov s : Bool) (σ : D.Cross → Bool)

/-- El patrón identidad da las mismas componentes que `D`. -/
theorem card_NI (par : Bool) :
    Nat.card (SimpleGraph.fromRel fun x y =>
        Oa D e f hef ov par s σ x y ∨ NI e f x y).ConnectedComponent =
      Nat.card (D.graph σ).ConnectedComponent := by
  have hlift : ∀ (x : ι ⊕ Bool) (a' : ι),
      (x = .inl a' ∨ (x = .inr true ∧ a' = e) ∨ (x = .inr false ∧ a' = f)) →
      (SimpleGraph.fromRel fun x y => Oa D e f hef ov par s σ x y ∨ NI e f x y).Reachable
        (.inl a') x := by
    rintro x a' (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact SimpleGraph.Reachable.refl _
    · exact reach_N (by simp [NI])
    · exact reach_N (by simp [NI])
  have hfe : ∀ x y, Oa D e f hef ov par s σ x y → D.rel σ (colr e f x) (colr e f y) := by
    intro x y h
    have := r2Old_fe D e f hef ov par s σ _ _ h
    rwa [fe2_pi2, fe2_pi2] at this
  refine card_cc_eq (colr e f) Sum.inl ?_ ?_ ?_ ?_
  · intro a c h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · rcases h with h | h
      · exact reach_of_rel (hfe a c h)
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact SimpleGraph.Reachable.refl _
    · rcases h with h | h
      · exact (reach_of_rel (hfe c a h)).symm
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact SimpleGraph.Reachable.refl _
  · have key : ∀ a' c', D.rel σ a' c' →
        (SimpleGraph.fromRel fun x y => Oa D e f hef ov par s σ x y ∨ NI e f x y).Reachable
          (.inl a') (.inl c') := by
      intro a' c' h
      obtain ⟨x, y, ho, hx, hy⟩ := r2Old_lift D e f hef ov par s σ a' c' h
      exact (hlift x a' hx).trans ((reach_of_or_left (r := Oa D e f hef ov par s σ) ho).trans
        (hlift y c' hy).symm)
    intro a c h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
    · exact key a c h
    · exact (key c a h).symm
  · intro a
    exact SimpleGraph.Reachable.refl _
  · intro b
    rcases b with i | _ | _
    · exact SimpleGraph.Reachable.refl _
    · exact hlift _ f (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact hlift _ e (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- Número de lazos según el patrón local: `oa`, `ob` son las orientaciones de las
suavizaciones de los cruces `a` y `b`; `L` son los lazos del estado de `D` y `m` los del estado
reconectado. -/
def lz (par oa ob : Bool) (L m : ℕ) : ℕ :=
  if oa == ob then (if oa == par then L else m + 1) else m

/-- Lazos del estado "reconectado". -/
noncomputable def Mcc (par : Bool) : ℕ :=
  Nat.card (SimpleGraph.fromRel fun x y =>
    Oa D e f hef ov par s σ x y ∨ NR e f par x y).ConnectedComponent + D.free

theorem r2_lazos_aux (par oa ob : Bool) :
    Nat.card (SimpleGraph.fromRel fun a c =>
        r2Old D e f hef ov par s σ a c ∨ Nloc e f par oa ob a c).ConnectedComponent + D.free =
      lz par oa ob (D.lazos σ) (Mcc D e f hef ov s σ par) := by
  cases par <;> cases oa <;> cases ob
  · rw [card_ID_ff D e f hef ov s σ, card_NI D e f hef ov s σ false]
    simp [lz, GDiag.lazos]
  · rw [card_Y_f D e f hef ov s σ]
    simp [lz, Mcc]
  · rw [card_X_f D e f hef ov s σ]
    simp [lz, Mcc]
  · rw [card_C_f D e f hef ov s σ]
    simp [lz, Mcc]
    omega
  · rw [card_C_t D e f hef ov s σ]
    simp [lz, Mcc]
    omega
  · rw [card_Y_t D e f hef ov s σ]
    simp [lz, Mcc]
  · rw [card_X_t D e f hef ov s σ]
    simp [lz, Mcc]
  · rw [card_ID_tt D e f hef ov s σ, card_NI D e f hef ov s σ true]
    simp [lz, GDiag.lazos]

/-- **Lema de lazos.** Los lazos del estado `(σ, ba, bb)` de `D'`. -/
theorem r2_lazos (par : Bool) (ba bb : Bool) :
    (r2 D e f hef ov par s).lazos ((r2State D e f hef ov par s).symm (σ, ba, bb)) =
      lz par (ba == s) (bb == !s) (D.lazos σ) (Mcc D e f hef ov s σ par) := by
  unfold lazos
  rw [r2_graph_eq]
  exact r2_lazos_aux D e f hef ov s σ par _ _

theorem Mcc_pos (par : Bool) : 1 ≤ Mcc D e f hef ov s σ par := by
  unfold Mcc
  haveI : Nonempty (SimpleGraph.fromRel fun x y =>
      Oa D e f hef ov par s σ x y ∨ NR e f par x y).ConnectedComponent :=
    ⟨(SimpleGraph.fromRel fun x y =>
      Oa D e f hef ov par s σ x y ∨ NR e f par x y).connectedComponentMk (.inl e)⟩
  have := Nat.card_pos (α := (SimpleGraph.fromRel fun x y =>
      Oa D e f hef ov par s σ x y ∨ NR e f par x y).ConnectedComponent)
  omega

/-- Álgebra final: `A·A⁻¹ = 1` y `A² + A⁻² + d = 0`. -/
theorem r2_alg {K : Type*} [Field K] (A : K) (hA : A ≠ 0) (s par : Bool) (W : K) (k l : ℕ) :
    (∑ ba : Bool, ∑ bb : Bool, W * ((if ba then A else A⁻¹) * (if bb then A else A⁻¹)) *
      (-(A ^ 2) - A⁻¹ ^ 2) ^ (lz par (ba == s) (bb == !s) (k + 1) (l + 1) - 1)) =
      W * (-(A ^ 2) - A⁻¹ ^ 2) ^ (k + 1 - 1) := by
  cases s <;> cases par <;> simp [lz] <;>
    simp only [mul_inv_cancel₀ hA, inv_mul_cancel₀ hA, mul_one] <;> ring

/-- **Invariancia del corchete de Kauffman bajo R2.** Para dos aristas distintas `e ≠ f` y
cualesquiera `ov`, `par`, `s`, insertar los dos cruces del movimiento R2 no cambia el corchete. -/
theorem bracket_r2 {K : Type*} [Field K] (A : K) (hA : A ≠ 0) (par : Bool) :
    (r2 D e f hef ov par s).bracket A = D.bracket A := by
  haveI : Nonempty ι := ⟨e⟩
  unfold bracket
  rw [← (r2State D e f hef ov par s).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [r2_weight, r2_lazos]
  obtain ⟨k, hk⟩ : ∃ k, D.lazos σ = k + 1 := ⟨D.lazos σ - 1, by have := lazos_pos D σ; omega⟩
  obtain ⟨l, hl⟩ : ∃ l, Mcc D e f hef ov s σ par = l + 1 :=
    ⟨Mcc D e f hef ov s σ par - 1, by have := Mcc_pos D e f hef ov s σ par; omega⟩
  rw [hk, hl]
  exact r2_alg A hA s par _ k l

end Main

end GDiag

#print axioms GDiag.bracket_r2
#print axioms GDiag.r2_lazos
#print axioms GDiag.r2_graph_eq
#print axioms GDiag.card_ID_tt
#print axioms GDiag.card_C_t
#print axioms GDiag.card_X_t

end TMENudos.Invariancia
