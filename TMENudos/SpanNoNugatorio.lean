import Mathlib
import TMENudos.SpanAdecuado
import TMENudos.SpanPuente
import TMENudos.SpanGenero

/-!
# Adecuacion desde la igualdad de genero y la ausencia de cruces de corte (etapa S5c)

Idea: la adecuacion sale, sin geometria, de (i) `s_A + s_B = c + 2` y (ii) que el cruce `x` no
sea "de corte" (nugatorio).  Desacoplar `x` (usar en `x` el emparejamiento B tambien en el
`a`) da una terna de involuciones `(eps, a_x, b)` con `a_x * b` involucion con exactamente 4
puntos fijos (los extremos de `x`).  Un `L2` refinado que cuenta los puntos fijos mejora la
cota en 1.
-/

open SpanGenero

namespace SpanNoNug

section Abstracto

variable {X : Type*}

/-- Una involucion tiene `2 cyc >= |X| + #puntos fijos` (de hecho hay igualdad). -/
theorem card_add_fixed_le_two_cyc [Fintype X] (x : Equiv.Perm X) (hx : ∀ y, x (x y) = y) :
    Fintype.card X + Nat.card {y // x y = y} ≤ 2 * cyc x := by
  classical
  let o : X → X := fun y => (Quotient.mk (cycSetoid x) y).out
  have hA : ∀ y, o y = y ∨ o y = x y := fun y =>
    cyc_invol x hx ((cycSetoid x).symm (Quotient.mk_out (s := cycSetoid x) y))
  have hcls : ∀ y z, Quotient.mk (cycSetoid x) y = Quotient.mk (cycSetoid x) z → o y = o z :=
    fun y z h => by simp only [o, h]
  have hfix : ∀ y z, x z = z → Quotient.mk (cycSetoid x) y = Quotient.mk (cycSetoid x) z →
      y = z := by
    intro y z hz h
    rcases cyc_invol x hx ((cycSetoid x).symm (Quotient.exact h)) with h1 | h1
    · exact h1
    · rw [hz] at h1; exact h1
  let F : X ⊕ {y // x y = y} → Quotient (cycSetoid x) × Bool := fun s =>
    match s with
    | Sum.inl y => (Quotient.mk _ y, decide (y ≠ o y))
    | Sum.inr y => (Quotient.mk _ y.1, true)
  have hmix : ∀ (z : X) (y : {y // x y = y}), F (Sum.inl z) = F (Sum.inr y) → False := by
    intro z y h
    simp only [F, Prod.mk.injEq, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hz : z = y.1 := hfix _ _ y.2 h1
    have hoo := hcls _ _ h1
    have hoz : o y.1 = y.1 := by
      rcases hA y.1 with e | e
      · exact e
      · rw [y.2] at e; exact e
    exact h2 (hz.trans (hoz.symm.trans hoo.symm))
  have hinj : Function.Injective F := by
    rintro (y | y) (z | z) h
    · simp only [F, Prod.mk.injEq, decide_eq_decide] at h
      obtain ⟨h1, h2⟩ := h
      have hoo := hcls _ _ h1
      by_cases hy : y = o y
      · have hz : z = o z := by
          by_contra hz; exact (h2.2 hz) hy
        exact congrArg Sum.inl (hy.trans (hoo.trans hz.symm))
      · have hz : z ≠ o z := h2.1 hy
        rcases hA y with e1 | e1
        · exact absurd e1.symm hy
        rcases hA z with e2 | e2
        · exact absurd e2.symm hz
        have : x y = x z := by rw [← e1, ← e2, hoo]
        exact congrArg Sum.inl (x.injective this)
    · exact (hmix _ _ h).elim
    · exact (hmix _ _ h.symm).elim
    · simp only [F, Prod.mk.injEq] at h
      exact congrArg Sum.inr (Subtype.ext (hfix _ _ y.2 h.1.symm).symm)
  have := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Nat.card_eq_fintype_card (α := X)] at this
  simp only [Fintype.card_bool] at this
  unfold cyc ncs
  omega

end Abstracto

/-! ### (1) L2 refinado -/

section Refinado

variable {X : Type*} [Fintype X]

/-- **L2 refinado**: como `L2`, contando ademas los puntos fijos `f` de la involucion `a * b`:
`2 (cyc (eps a) + cyc (eps b)) + f <= |X| + 8 orb <eps, a, b>`. -/
theorem L2_refinado (ε a b : Equiv.Perm X) (hε : ε * ε = 1) (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) :
    2 * (cyc (ε * a) + cyc (ε * b)) + Nat.card {y // (a * b) y = y} ≤
      Fintype.card X + 8 * orb {ε, a, b} := by
  have hprod : (ε * a) * (a * b) * (b * ε) = 1 := by
    calc (ε * a) * (a * b) * (b * ε) = ε * (a * a) * (b * b) * ε := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, mul_one, mul_one, hε]
  have hq : b * ε = (ε * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right hε]
  have h1 := L1 (ε * a) (a * b) (b * ε) hprod
  have h2 := orb_le_two_mul ε a b (ε * a) (a * b) (b * ε) (pt_of_mul_self ε hε)
    (pt_of_mul_self a ha) (pt_of_mul_self b hb) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have h3 := card_add_fixed_le_two_cyc (a * b) (pt_of_mul_self _ hab)
  have hc : cyc (b * ε) = cyc (ε * b) := by rw [hq, cyc_inv]
  rw [hc] at h1
  omega

end Refinado

end SpanNoNug

/-! ### (2) Estado desacoplado -/

open TMENudos.Invariancia SpanPuente

namespace TMENudos.Invariancia.GDiag

section Desacoplado

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Orientacion del estado todo-A cambiada en el cruce `x` (sus dos letras). -/
def oriAX (x : D.Cross) (j : ι) : Bool :=
  if j = x.1 ∨ j = D.partner x.1 then !D.sign j else D.sign j

/-- Orientacion del estado todo-B cambiada en el cruce `x`. -/
def oriBX (x : D.Cross) (j : ι) : Bool :=
  if j = x.1 ∨ j = D.partner x.1 then D.sign j else !D.sign j

theorem pair_partner (x : D.Cross) (j : ι) :
    (D.partner j = x.1 ∨ D.partner j = D.partner x.1) ↔ (j = x.1 ∨ j = D.partner x.1) := by
  constructor
  · rintro (h | h)
    · right; rw [← h, D.partner_partner]
    · left
      have := congrArg D.partner h
      rwa [D.partner_partner, D.partner_partner] at this
  · rintro (h | h)
    · right; rw [h]
    · left; rw [h, D.partner_partner]

theorem oriAX_partner (x : D.Cross) (j : ι) : D.oriAX x (D.partner j) = D.oriAX x j := by
  unfold oriAX
  simp only [D.pair_partner x j, D.sign_partner]

theorem oriBX_partner (x : D.Cross) (j : ι) : D.oriBX x (D.partner j) = D.oriBX x j := by
  unfold oriBX
  simp only [D.pair_partner x j, D.sign_partner]

/-- Emparejamiento `a` con el B-emparejamiento en el cruce `x`. -/
def aX (x : D.Cross) : Equiv.Perm (ι × Bool) := D.sm (D.oriAX x) (D.oriAX_partner x)

/-- Emparejamiento `b` con el A-emparejamiento en el cruce `x`. -/
def bX (x : D.Cross) : Equiv.Perm (ι × Bool) := D.sm (D.oriBX x) (D.oriBX_partner x)

theorem aX_mul_aX (x : D.Cross) : D.aX x * D.aX x = 1 := D.sm_mul_sm _ _

theorem bX_mul_bX (x : D.Cross) : D.bX x * D.bX x = 1 := D.sm_mul_sm _ _

theorem aX_ne (x : D.Cross) (y : ι × Bool) : D.aX x y ≠ y := D.sm_ne _ _ y

theorem bX_ne (x : D.Cross) (y : ι × Bool) : D.bX x y ≠ y := D.sm_ne _ _ y

/-- Producto de dos emparejamientos: gira el segundo componente segun `o1 xor o2`. -/
theorem sm_mul_sm_apply' (o1 o2 : ι → Bool) (h1 : ∀ j, o1 (D.partner j) = o1 j)
    (h2 : ∀ j, o2 (D.partner j) = o2 j) (y : ι × Bool) :
    (D.sm o1 h1 * D.sm o2 h2) y = (y.1, xor y.2 (xor (o1 y.1) (o2 y.1))) := by
  obtain ⟨j, s⟩ := y
  simp only [Equiv.Perm.mul_apply, sm_apply, D.partner_partner, h1]
  cases s <;> cases o1 j <;> cases o2 j <;> rfl

theorem sm_mul_sm_invol (o1 o2 : ι → Bool) (h1 : ∀ j, o1 (D.partner j) = o1 j)
    (h2 : ∀ j, o2 (D.partner j) = o2 j) :
    (D.sm o1 h1 * D.sm o2 h2) * (D.sm o1 h1 * D.sm o2 h2) = 1 := by
  refine Equiv.ext fun y => ?_
  change (D.sm o1 h1 * D.sm o2 h2) ((D.sm o1 h1 * D.sm o2 h2) y) = y
  rw [sm_mul_sm_apply', sm_mul_sm_apply']
  obtain ⟨j, s⟩ := y
  cases s <;> cases o1 j <;> cases o2 j <;> rfl

/-- Los puntos fijos del producto son exactamente los cuatro extremos del cruce `x` cuando
`o1 xor o2` se anula solo en las dos letras de `x`. -/
theorem card_fixed_sm (o1 o2 : ι → Bool) (h1 : ∀ j, o1 (D.partner j) = o1 j)
    (h2 : ∀ j, o2 (D.partner j) = o2 j) (x : D.Cross)
    (hx : ∀ j, xor (o1 j) (o2 j) = false ↔ (j = x.1 ∨ j = D.partner x.1)) :
    Nat.card {y // (D.sm o1 h1 * D.sm o2 h2) y = y} = 4 := by
  classical
  have hfix : ∀ y : ι × Bool, (D.sm o1 h1 * D.sm o2 h2) y = y ↔
      (y.1 = x.1 ∨ y.1 = D.partner x.1) := by
    intro y
    rw [sm_mul_sm_apply', ← hx]
    obtain ⟨j, s⟩ := y
    simp only [Prod.mk.injEq, true_and]
    cases s <;> cases (xor (o1 j) (o2 j)) <;> simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter fun y : ι × Bool => (D.sm o1 h1 * D.sm o2 h2) y = y) =
      {(x.1, false), (x.1, true), (D.partner x.1, false), (D.partner x.1, true)} := by
    ext y
    rw [Finset.mem_filter, hfix]
    obtain ⟨j, s⟩ := y
    simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    cases s <;> simp
  rw [this]
  have hp := D.partner_ne x.1
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  all_goals simp [hp.symm]

/-- Un cruce `c` distinto de `x` no es ni `x` ni su pareja (las letras de `Cross` son las
superiores). -/
theorem cross_ne_pair (x c : D.Cross) (hc : c ≠ x) :
    ¬ (c.1 = x.1 ∨ c.1 = D.partner x.1) := by
  rintro (h | h)
  · exact hc (Subtype.ext h)
  · have h1 := c.2
    have h2 := D.ovr_partner x.1
    rw [x.2, ← h, h1] at h2
    simp at h2

theorem hori_AX (x : D.Cross) (c : D.Cross) :
    ((Function.update D.allA x false) c == D.sign c.1) = D.oriAX x c.1 := by
  by_cases hc : c = x
  · subst hc
    simp [oriAX]
  · have := D.cross_ne_pair x c hc
    simp [oriAX, this, Function.update_of_ne hc, allA]

theorem hori_BX (x : D.Cross) (c : D.Cross) :
    ((Function.update D.allB x true) c == D.sign c.1) = D.oriBX x c.1 := by
  by_cases hc : c = x
  · subst hc
    simp [oriBX]
  · have := D.cross_ne_pair x c hc
    simp [oriBX, this, Function.update_of_ne hc, allB]

/-- Lazos del estado todo-A cambiado en `x` = orbitas de `<eps, a_x>`. -/
theorem lazos_update_allA_eq (hfree : D.free = 0) (x : D.Cross) :
    D.lazos (Function.update D.allA x false) = orb {D.eps, D.aX x} := by
  rw [lazos_eq, hfree, add_zero]
  exact (D.orb_sm _ (D.oriAX x) (D.oriAX_partner x) (D.hori_AX x)).symm

/-- Lazos del estado todo-B cambiado en `x` = orbitas de `<eps, b_x>`. -/
theorem lazos_update_allB_eq (hfree : D.free = 0) (x : D.Cross) :
    D.lazos (Function.update D.allB x true) = orb {D.eps, D.bX x} := by
  rw [lazos_eq, hfree, add_zero]
  exact (D.orb_sm _ (D.oriBX x) (D.oriBX_partner x) (D.hori_BX x)).symm

theorem aX_b_invol (x : D.Cross) : (D.aX x * D.b) * (D.aX x * D.b) = 1 :=
  D.sm_mul_sm_invol _ _ _ _

theorem a_bX_invol (x : D.Cross) : (D.a * D.bX x) * (D.a * D.bX x) = 1 :=
  D.sm_mul_sm_invol _ _ _ _

/-- Los puntos fijos de `a_x * b` son los 4 extremos del cruce `x`. -/
theorem card_fixed_aX_b (x : D.Cross) : Nat.card {y // (D.aX x * D.b) y = y} = 4 := by
  refine D.card_fixed_sm (D.oriAX x) (fun i => !D.sign i) (D.oriAX_partner x)
    D.notSign_partner x fun j => ?_
  unfold oriAX
  split_ifs <;> cases hs : D.sign j <;> simp_all

/-- Los puntos fijos de `a * b_x` son los 4 extremos del cruce `x`. -/
theorem card_fixed_a_bX (x : D.Cross) : Nat.card {y // (D.a * D.bX x) y = y} = 4 := by
  refine D.card_fixed_sm D.sign (D.oriBX x) D.sign_partner (D.oriBX_partner x) x fun j => ?_
  unfold oriBX
  split_ifs <;> cases hs : D.sign j <;> simp_all

/-- Puntos fijos de `a_x * b`, descritos explicitamente. -/
theorem aX_b_apply (x : D.Cross) (y : ι × Bool) :
    (D.aX x * D.b) y =
      (y.1, xor y.2 (if y.1 = x.1 ∨ y.1 = D.partner x.1 then false else true)) := by
  rw [aX, b, D.sm_mul_sm_apply']
  obtain ⟨j, s⟩ := y
  simp only [oriAX]
  split_ifs <;> cases hs : D.sign j <;> cases s <;> simp_all

end Desacoplado

/-! ### (3) Adecuacion en un cruce -/

section Adecuacion

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- **Adecuacion A en un cruce**: si `s_A + s_B = c + 2` y el cruce `x` no es de corte
(`<eps, a_x, b>` transitivo), cambiar la suavizacion en `x` desde todo-A baja los lazos. -/
theorem lazos_update_allA_lt (hfree : D.free = 0) (x : D.Cross)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2)
    (hconn : orb {D.eps, D.aX x, D.b} = 1) :
    D.lazos (Function.update D.allA x false) < D.lazos D.allA := by
  rw [lazos_allA_eq D hfree, lazos_allB_eq D hfree] at hgen
  rw [lazos_update_allA_eq D hfree x, lazos_allA_eq D hfree]
  have h1 := two_orb_le_cyc D.eps (D.aX x) D.eps_mul_eps (D.aX_mul_aX x) D.eps_ne (D.aX_ne x)
  have h2 := two_orb_le_cyc D.eps D.b D.eps_mul_eps (D.sm_mul_sm _ _) D.eps_ne (D.sm_ne _ _)
  have hL := SpanNoNug.L2_refinado D.eps (D.aX x) D.b D.eps_mul_eps (D.aX_mul_aX x)
    (D.sm_mul_sm _ _) (D.aX_b_invol x)
  rw [hconn, D.card_fixed_aX_b x, D.card_modelo] at hL
  omega

/-- **Adecuacion B en un cruce**. -/
theorem lazos_update_allB_lt (hfree : D.free = 0) (x : D.Cross)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2)
    (hconn : orb {D.eps, D.a, D.bX x} = 1) :
    D.lazos (Function.update D.allB x true) < D.lazos D.allB := by
  rw [lazos_allA_eq D hfree, lazos_allB_eq D hfree] at hgen
  rw [lazos_update_allB_eq D hfree x, lazos_allB_eq D hfree]
  have h1 := two_orb_le_cyc D.eps D.a D.eps_mul_eps (D.sm_mul_sm _ _) D.eps_ne (D.sm_ne _ _)
  have h2 := two_orb_le_cyc D.eps (D.bX x) D.eps_mul_eps (D.bX_mul_bX x) D.eps_ne (D.bX_ne x)
  have hL := SpanNoNug.L2_refinado D.eps D.a (D.bX x) D.eps_mul_eps (D.sm_mul_sm _ _)
    (D.bX_mul_bX x) (D.a_bX_invol x)
  rw [hconn, D.card_fixed_a_bX x, D.card_modelo] at hL
  omega

end Adecuacion

end TMENudos.Invariancia.GDiag

/-! ### (4) Definicion y teoremas generales -/

namespace TMENudos.Invariancia.GDiag

section NoNugatorio

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- **No nugatorio**: ningun cruce es "de corte", en el sentido combinatorio de que desacoplar
cualquier cruce (en el `a` o en el `b`) deja el grupo `<eps, a_x, b>` (resp. `<eps, a, b_x>`)
transitivo en los extremos de letras. -/
def NonNugatory (D : GDiag ι) : Prop :=
  ∀ x : D.Cross, orb {D.eps, D.aX x, D.b} = 1 ∧ orb {D.eps, D.a, D.bX x} = 1

end NoNugatorio

end TMENudos.Invariancia.GDiag

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.SpanLaurent TMENudos.Nudos

section General

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Con `s_A + s_B = c + 2` y sin cruces de corte, el diagrama es A-adecuado. -/
theorem aAdequate_of_nonNugatory (D : GDiag ι) (hfree : D.free = 0)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2)
    (hN : D.NonNugatory) : AAdequate D :=
  fun x => D.lazos_update_allA_lt hfree x hgen (hN x).1

/-- Con `s_A + s_B = c + 2` y sin cruces de corte, el diagrama es B-adecuado. -/
theorem bAdequate_of_nonNugatory (D : GDiag ι) (hfree : D.free = 0)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2)
    (hN : D.NonNugatory) : BAdequate D :=
  fun x => D.lazos_update_allB_lt hfree x hgen (hN x).2

/-- **Adecuacion sin geometria**: `s_A + s_B = c + 2` y no nugatorio dan A- y B-adecuacion. -/
theorem adequate_of_nonNugatory (D : GDiag ι) (hfree : D.free = 0)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2)
    (hN : D.NonNugatory) : AAdequate D ∧ BAdequate D :=
  ⟨aAdequate_of_nonNugatory D hfree hgen hN, bAdequate_of_nonNugatory D hfree hgen hN⟩

/-- **Span exacto**: `span <bracket> = 4 c`. -/
theorem span_eq_four_mul_of_nonNugatory (D : GDiag ι) (hfree : D.free = 0)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2)
    (hN : D.NonNugatory) (hne : Nonempty D.Cross) :
    span (bracketL D) = 4 * Fintype.card D.Cross :=
  span_bracketL_eq_four_mul D (aAdequate_of_nonNugatory D hfree hgen hN)
    (bAdequate_of_nonNugatory D hfree hgen hN) hne hgen

/-- **Minimalidad general**: si `d` cumple `s_A + s_B = c + 2`, es no nugatorio, sin libres y con
algun cruce, todo `d'` de una curva sin libres con `GRel d d'` tiene al menos tantos cruces. -/
theorem minimal_of_nonNugatory (d d' : Diag) (h : GRel d d') (hf : d.D.free = 0)
    (hgen : d.D.lazos d.D.allA + d.D.lazos d.D.allB = Fintype.card d.D.Cross + 2)
    (hN : d.D.NonNugatory) (hne : Nonempty d.D.Cross) (hf' : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) :
    Fintype.card d.D.Cross ≤ Fintype.card d'.D.Cross := by
  have hspan : span (bracketL d'.D) = 4 * Fintype.card d.D.Cross := by
    rw [← span_bracketL_rel h]
    exact span_eq_four_mul_of_nonNugatory d.D hf hgen hN hne
  have hpos : 0 < Fintype.card d.D.Cross := Fintype.card_pos_iff.2 hne
  by_cases hne' : Nonempty d'.D.Cross
  · have h1 := span_bracketL_le_of_nonempty d'.D hne'
    have h2 := GDiag.lazos_allA_add_allB_le d'.D hf' hc hne'
    omega
  · rw [not_nonempty_iff] at hne'
    have := span_bracketL_of_isEmpty d'.D hne' hf'
    omega

end General

end TMENudos.Puente

/-! ### (5) Sanidad: el trebol es no nugatorio -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.Nudos

/-- Caminos (generadores `0 = eps`, `1 = a_x`, `2 = b`) desde el extremo `(0, true)`, indexados por
la letra superior `x` del cruce (`0, 2, 4`) y por el extremo `2 * j + s`; generados por BFS. -/
def tblA : List (List (List (Fin 3))) :=
  [[[1, 0, 1, 0, 1, 0], [], [0], [2, 1, 0], [2, 0, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1, 0], [1],
    [2, 0], [1, 0], [0, 1, 0], [2, 1, 0, 1, 0]], [],
   [[2, 1], [], [0], [2, 1, 0], [1, 0, 1, 0], [0, 1], [1], [2], [2, 0], [1, 0], [0, 1, 0],
    [1, 0, 1]], [],
   [[2, 1], [], [0], [1, 0, 1, 0, 1], [2, 1, 0, 1], [0, 1], [1], [2], [1, 0], [0, 1, 0, 1],
    [1, 0, 1], [2, 0, 1]], []]

/-- Analogo para `(eps, a, b_x)`. -/
def tblB : List (List (List (Fin 3))) :=
  [[[1, 0, 2, 0], [], [0], [2, 1, 0], [2, 0, 1, 0], [0, 1], [1], [0, 2, 0], [2, 0], [1, 0],
    [0, 1, 0], [2, 0, 1]], [],
   [[2, 1], [], [0], [2, 1, 0], [0, 2, 1, 0], [0, 1], [1], [2], [2, 0], [1, 0], [0, 1, 0],
    [0, 2, 1]], [],
   [[2, 1], [], [0], [1, 0, 2], [2, 0, 1, 0], [0, 1], [1], [2], [0, 2], [1, 0], [0, 1, 0],
    [2, 0, 1]], []]

def pathOf (t : List (List (List (Fin 3)))) (i : Nat) (y : Fin trefoil.length × Bool) :
    List (Fin 3) :=
  ((t.getD i []).getD (2 * y.1.val + if y.2 then 1 else 0) [])

theorem hendA : ∀ x : (ofWord trefoil wf_trefoil).Cross, ∀ y,
    (pathOf tblA x.1.val y).foldr
      (fun i z => (![(ofWord trefoil wf_trefoil).eps, (ofWord trefoil wf_trefoil).aX x,
        (ofWord trefoil wf_trefoil).b] i) z) (⟨0, by decide⟩, true) = y := by
  decide +kernel

theorem hendB : ∀ x : (ofWord trefoil wf_trefoil).Cross, ∀ y,
    (pathOf tblB x.1.val y).foldr
      (fun i z => (![(ofWord trefoil wf_trefoil).eps, (ofWord trefoil wf_trefoil).a,
        (ofWord trefoil wf_trefoil).bX x] i) z) (⟨0, by decide⟩, true) = y := by
  decide +kernel

/-- El trebol es no nugatorio. -/
theorem trefoil_nonNugatory : (ofWord trefoil wf_trefoil).NonNugatory := fun x =>
  ⟨SpanGenero.orb_eq_one_of_path _ _ _ _ _ (hendA x),
   SpanGenero.orb_eq_one_of_path _ _ _ _ _ (hendB x)⟩

/-- Sanidad: el teorema general reproduce `span = 12` del trebol, sin el calculo por estados
de `trefoil_AAdequate` / `trefoil_BAdequate`. -/
theorem span_trefoil_eq_of_nonNugatory :
    SpanLaurent.span (SpanLaurent.bracketL (ofWord trefoil wf_trefoil)) = 12 := by
  obtain ⟨h1, h2, h3⟩ := sanidad_trefoil
  have hne : Nonempty (ofWord trefoil wf_trefoil).Cross := by
    rw [← Fintype.card_pos_iff, h1]; norm_num
  have hf : (ofWord trefoil wf_trefoil).free = 0 := by
    have : trefoil.length ≠ 0 := by decide +kernel
    change (if trefoil.length = 0 then 1 else 0) = 0
    simp [this]
  have := span_eq_four_mul_of_nonNugatory _ hf (by rw [h1, h2, h3]) trefoil_nonNugatory hne
  rw [this, h1]

/-- El trebol: la minimalidad general reproduce `trefoil_minimal`. -/
theorem trefoil_minimal_nonNugatory (d' : Diag)
    (h : GRel (Diag.mk _ (ofWord trefoil wf_trefoil)) d') (hf : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) : 3 ≤ Fintype.card d'.D.Cross := by
  obtain ⟨h1, h2, h3⟩ := sanidad_trefoil
  have hne : Nonempty (ofWord trefoil wf_trefoil).Cross := by
    rw [← Fintype.card_pos_iff, h1]; norm_num
  have hf0 : (ofWord trefoil wf_trefoil).free = 0 := by
    have : trefoil.length ≠ 0 := by decide +kernel
    change (if trefoil.length = 0 then 1 else 0) = 0
    simp [this]
  have := minimal_of_nonNugatory (Diag.mk _ (ofWord trefoil wf_trefoil)) d' h hf0
    (by change _ + _ = Fintype.card (ofWord trefoil wf_trefoil).Cross + 2
        rw [h1, h2, h3]) trefoil_nonNugatory hne hf hc
  change Fintype.card (ofWord trefoil wf_trefoil).Cross ≤ _ at this
  omega

end TMENudos.Puente

#print axioms SpanNoNug.card_add_fixed_le_two_cyc
#print axioms SpanNoNug.L2_refinado
#print axioms TMENudos.Invariancia.GDiag.card_fixed_aX_b
#print axioms TMENudos.Invariancia.GDiag.card_fixed_a_bX
#print axioms TMENudos.Invariancia.GDiag.lazos_update_allA_lt
#print axioms TMENudos.Invariancia.GDiag.lazos_update_allB_lt
#print axioms TMENudos.Puente.adequate_of_nonNugatory
#print axioms TMENudos.Puente.span_eq_four_mul_of_nonNugatory
#print axioms TMENudos.Puente.minimal_of_nonNugatory
#print axioms TMENudos.Puente.trefoil_nonNugatory
#print axioms TMENudos.Puente.span_trefoil_eq_of_nonNugatory
#print axioms TMENudos.Puente.trefoil_minimal_nonNugatory
