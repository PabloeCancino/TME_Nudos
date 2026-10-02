import Mathlib
import TMENudos.SpanGenero
import TMENudos.SpanEstados

/-!
# Puente entre estados y permutaciones (etapa S4)

Desigualdad de genero `s_A + s_B <= c + 2` de un diagrama de una sola curva.

Modelo: `X = iota x Bool` (extremos de letras).  `(j, false)` es el extremo de ENTRADA de la
letra `j` (donde llega la arista `prev j`) y `(j, true)` el de SALIDA (donde nace la arista
`j`).  `eps` une `(j, true)` con `(next j, false)` (los dos extremos de la arista `j`);
`sm ori` une `(j, s)` con `(partner j, s xor ori j)`.
-/

open SpanGenero Relation

namespace SpanPuente

/-! ### (A) Lema abstracto: dos ciclos por orbita -/

section Abstracto

variable {X : Type*}

/-- Las palabras `eps * (eps * a)^n` no tienen puntos fijos. -/
theorem word_fpf (ε a : Equiv.Perm X) (hε : ε * ε = 1) (ha : a * a = 1)
    (hε' : ∀ x, ε x ≠ x) (ha' : ∀ x, a x ≠ x) :
    ∀ n : ℕ, ∀ x, (ε * (ε * a) ^ n) x ≠ x := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro x; simpa using hε' x
  | one =>
    intro x
    have : ε * (ε * a) ^ 1 = a := by rw [pow_one, ← mul_assoc, hε, one_mul]
    rw [this]; exact ha' x
  | more n ih _ =>
    intro x hx
    have key : ε * (ε * a) ^ (n + 2) = (a * ε) * (ε * (ε * a) ^ n) * (ε * a) := by
      have e1 : (a * ε) * (ε * (ε * a) ^ n) * (ε * a) =
          a * (ε * ε) * (ε * a) ^ n * (ε * a) := by simp only [mul_assoc]
      rw [e1, hε, mul_one]
      have e2 : a = ε * (ε * a) := by rw [← mul_assoc, hε, one_mul]
      calc ε * (ε * a) ^ (n + 2) = ε * ((ε * a) * (ε * a) ^ n * (ε * a)) := by
            rw [pow_succ, pow_succ', mul_assoc]
        _ = (ε * (ε * a)) * (ε * a) ^ n * (ε * a) := by simp only [mul_assoc]
        _ = a * (ε * a) ^ n * (ε * a) := by rw [← e2]
    rw [key] at hx
    have h3 : (a * ε) ((ε * (ε * a) ^ n) ((ε * a) x)) = x := by
      simpa [Equiv.Perm.mul_apply] using hx
    have h4 := congrArg (ε * a) h3
    have h5 : (ε * a) * (a * ε) = 1 := by
      calc (ε * a) * (a * ε) = ε * (a * a) * ε := by simp only [mul_assoc]
        _ = 1 := by rw [ha, mul_one, hε]
    rw [← Equiv.Perm.mul_apply, h5, Equiv.Perm.one_apply] at h4
    exact ih _ h4

/-- `x` y `eps x` no estan en el mismo ciclo de `eps * a`. -/
theorem not_cyc_eps (ε a : Equiv.Perm X) (hε : ε * ε = 1) (ha : a * a = 1)
    (hε' : ∀ x, ε x ≠ x) (ha' : ∀ x, a x ≠ x) (x : X) : ¬ (cycSetoid (ε * a)) x (ε x) := by
  intro h
  obtain ⟨i, hi⟩ := cycSetoid_le_sameCycle _ h
  have hee : ∀ y, ε (ε y) = y := pt_of_mul_self ε hε
  rcases i with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast] at hi
    apply word_fpf ε a hε ha hε' ha' n x
    rw [Equiv.Perm.mul_apply, hi, hee]
  · rw [zpow_negSucc, Equiv.Perm.inv_eq_iff_eq] at hi
    apply word_fpf ε a hε ha hε' ha' (n + 1) (ε x)
    rw [Equiv.Perm.mul_apply, ← hi]

/-- Cada orbita de `<eps, a>` contiene al menos dos ciclos de `eps * a`. -/
theorem two_orb_le_cyc [Finite X] (ε a : Equiv.Perm X) (hε : ε * ε = 1) (ha : a * a = 1)
    (hε' : ∀ x, ε x ≠ x) (ha' : ∀ x, a x ≠ x) : 2 * orb {ε, a} ≤ cyc (ε * a) := by
  have hee : ∀ y, ε (ε y) = y := pt_of_mul_self ε hε
  have hCO : ∀ x y, (cycSetoid (ε * a)) x y → (orbSetoid {ε, a}) x y := by
    intro x y h
    refine eqvGen_le (s := orbSetoid {ε, a}) ?_ h
    rintro u v rfl
    exact (orbSetoid {ε, a}).trans (orb_step (S := {ε, a}) (g := a) (by simp) u)
      (orb_step (S := {ε, a}) (g := ε) (by simp) (a u))
  let rep : Quotient (orbSetoid {ε, a}) → Bool → X := fun o b => if b then ε o.out else o.out
  have hrep : ∀ o b, (orbSetoid {ε, a}) (rep o b) o.out := by
    intro o b
    cases b
    · exact (orbSetoid {ε, a}).refl _
    · exact (orbSetoid {ε, a}).symm (orb_step (g := ε) (by simp) o.out)
  let F : Quotient (orbSetoid {ε, a}) × Bool → Quotient (cycSetoid (ε * a)) :=
    fun p => Quotient.mk _ (rep p.1 p.2)
  have hinj : Function.Injective F := by
    rintro ⟨o, b⟩ ⟨o', b'⟩ h
    have h1 := hCO _ _ (Quotient.exact h)
    have h2 : (orbSetoid {ε, a}) o.out o'.out :=
      (orbSetoid {ε, a}).trans ((orbSetoid {ε, a}).symm (hrep o b))
        ((orbSetoid {ε, a}).trans h1 (hrep o' b'))
    have h3 : o = o' := by
      rw [← Quotient.out_eq o, ← Quotient.out_eq o']
      exact Quotient.sound h2
    subst h3
    have h4 := Quotient.exact h
    cases b <;> cases b'
    · rfl
    · exact absurd h4 (not_cyc_eps ε a hε ha hε' ha' _)
    · refine absurd ((cycSetoid (ε * a)).symm h4) ?_
      have := not_cyc_eps ε a hε ha hε' ha' o.out
      exact this
    · rfl
  have := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  unfold orb cyc ncs
  omega

end Abstracto

/-! ### (C0) Lema general de cocientes -/

section Cocientes

variable {X ι : Type*}

/-- Si `phi` es sobreyectiva y `S x y <-> T (phi x) (phi y)`, hay el mismo numero de clases. -/
theorem ncs_eq_of_fiber (S : Setoid X) (T : Setoid ι) (φ : X → ι) (hsurj : Function.Surjective φ)
    (h : ∀ x y, S x y ↔ T (φ x) (φ y)) : ncs S = ncs T := by
  let f : Quotient S → Quotient T := Quotient.map φ (fun x y hxy => (h x y).1 hxy)
  have hinj : Function.Injective f := by
    intro p q
    induction p using Quotient.inductionOn with
    | _ x =>
      induction q using Quotient.inductionOn with
      | _ y => exact fun hpq => Quotient.sound ((h x y).2 (Quotient.exact hpq))
  have hs : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ u =>
      obtain ⟨x, rfl⟩ := hsurj u
      exact ⟨Quotient.mk _ x, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hs⟩)

/-- Las orbitas de `<eps, s>` corresponden a las componentes de `r` cuando `phi` identifica
exactamente los extremos de `eps` y `r` viene de `s`. -/
theorem orb_eq_ncs (ε s : Equiv.Perm X) (φ : X → ι) (r : ι → ι → Prop)
    (hsurj : Function.Surjective φ) (hεφ : ∀ x, φ (ε x) = φ x)
    (hfib : ∀ x y, φ x = φ y → y = x ∨ y = ε x)
    (hfwd : ∀ x, EqvGen r (φ x) (φ (s x)))
    (hbwd : ∀ u v, r u v → ∃ x, φ x = u ∧ φ (s x) = v) :
    orb {ε, s} = ncs (EqvGen.setoid r) := by
  have hS : ∀ x y, φ x = φ y → (orbSetoid {ε, s}) x y := by
    intro x y hxy
    rcases hfib x y hxy with rfl | rfl
    · exact (orbSetoid {ε, s}).refl _
    · exact orb_step (g := ε) (by simp) x
  refine ncs_eq_of_fiber _ _ φ hsurj (fun x y => ⟨?_, ?_⟩)
  · intro hxy
    refine orbSetoid_le (t := Setoid.comap φ (EqvGen.setoid r)) ?_ x y hxy
    intro g hg z
    rcases hg with rfl | rfl
    · change EqvGen r (φ z) (φ (g z))
      rw [hεφ]; exact EqvGen.refl _
    · exact hfwd z
  · intro hxy
    have key : ∀ u v, EqvGen r u v → ∀ x y, φ x = u → φ y = v → (orbSetoid {ε, s}) x y := by
      intro u v huv
      induction huv with
      | rel u v huv =>
        intro x y hx hy
        obtain ⟨x0, hx0, hy0⟩ := hbwd u v huv
        have e1 := hS x x0 (hx.trans hx0.symm)
        have e2 := hS (s x0) y (hy0.trans hy.symm)
        exact (orbSetoid {ε, s}).trans e1
          ((orbSetoid {ε, s}).trans (orb_step (g := s) (by simp) x0) e2)
      | refl u =>
        intro x y hx hy
        exact hS x y (hx.trans hy.symm)
      | symm u v _ ih =>
        intro x y hx hy
        exact (orbSetoid {ε, s}).symm (ih y x hy hx)
      | trans u v w _ _ ih1 ih2 =>
        intro x y hx hy
        obtain ⟨z, hz⟩ := hsurj v
        exact (orbSetoid {ε, s}).trans (ih1 x z hx hz) (ih2 z y hz hy)
    exact key _ _ hxy x y rfl rfl

end Cocientes

/-! ### (B) El modelo `iota x Bool` -/

end SpanPuente

open SpanPuente

namespace TMENudos.Invariancia.GDiag

section Modelo

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Las dos puntas de cada arista: `(j, true)` (salida de `j`) con `(next j, false)`. -/
def epsFun : ι × Bool → ι × Bool
  | (j, true) => (D.next j, false)
  | (j, false) => (D.prev j, true)

theorem epsFun_invol (x : ι × Bool) : D.epsFun (D.epsFun x) = x := by
  obtain ⟨j, _ | _⟩ := x <;> simp [epsFun, prev]

/-- La involucion `eps`. -/
def eps : Equiv.Perm (ι × Bool) := Function.Involutive.toPerm D.epsFun D.epsFun_invol

theorem eps_true (j : ι) : D.eps (j, true) = (D.next j, false) := rfl

theorem eps_false (j : ι) : D.eps (j, false) = (D.prev j, true) := rfl

theorem eps_eps (x : ι × Bool) : D.eps (D.eps x) = x := D.epsFun_invol x

theorem eps_mul_eps : D.eps * D.eps = 1 := by
  exact Equiv.ext fun x => D.eps_eps x

theorem eps_ne (x : ι × Bool) : D.eps x ≠ x := by
  obtain ⟨j, _ | _⟩ := x <;> simp [eps_true, eps_false]

/-- Emparejamiento generico: `(j, s) <-> (partner j, s xor ori j)`. -/
def smFun (ori : ι → Bool) (x : ι × Bool) : ι × Bool := (D.partner x.1, xor x.2 (ori x.1))

theorem smFun_invol (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j)
    (x : ι × Bool) : D.smFun ori (D.smFun ori x) = x := by
  obtain ⟨j, s⟩ := x
  simp [smFun, hpar, D.partner_partner]

/-- Permutacion asociada a un emparejamiento. -/
def sm (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j) : Equiv.Perm (ι × Bool) :=
  Function.Involutive.toPerm (D.smFun ori) (D.smFun_invol ori hpar)

theorem sm_apply (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j) (j : ι) (s : Bool) :
    D.sm ori hpar (j, s) = (D.partner j, xor s (ori j)) := rfl

theorem sm_sm (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j) (x : ι × Bool) :
    D.sm ori hpar (D.sm ori hpar x) = x := D.smFun_invol ori hpar x

theorem sm_mul_sm (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j) :
    D.sm ori hpar * D.sm ori hpar = 1 := by
  exact Equiv.ext fun x => D.sm_sm ori hpar x

theorem sm_ne (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j) (x : ι × Bool) :
    D.sm ori hpar x ≠ x := by
  obtain ⟨j, s⟩ := x
  intro h
  rw [sm_apply] at h
  exact D.partner_ne j (congrArg Prod.fst h)

/-- Emparejamiento del estado todo-A: orientado en los cruces de signo `true`. -/
def a : Equiv.Perm (ι × Bool) := D.sm D.sign D.sign_partner

theorem notSign_partner (j : ι) : (fun i => !D.sign i) (D.partner j) = (fun i => !D.sign i) j := by
  simp [D.sign_partner]

/-- Emparejamiento del estado todo-B. -/
def b : Equiv.Perm (ι × Bool) := D.sm (fun i => !D.sign i) D.notSign_partner

theorem a_apply (j : ι) (s : Bool) : D.a (j, s) = (D.partner j, xor s (D.sign j)) := rfl

theorem b_apply (j : ι) (s : Bool) : D.b (j, s) = (D.partner j, xor s (!D.sign j)) := rfl

theorem ab_apply (x : ι × Bool) : (D.a * D.b) x = (x.1, !x.2) := by
  obtain ⟨j, s⟩ := x
  simp [Equiv.Perm.mul_apply, a_apply, b_apply, D.partner_partner, D.sign_partner]

theorem ab_mul_ab : (D.a * D.b) * (D.a * D.b) = 1 := by
  refine Equiv.ext fun x => ?_
  change (D.a * D.b) ((D.a * D.b) x) = x
  rw [ab_apply, ab_apply]
  simp

end Modelo

/-! ### (C) Lazos = orbitas -/

section Lazos

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- La arista a la que pertenece un extremo. -/
def phi : ι × Bool → ι
  | (j, true) => j
  | (j, false) => D.prev j

theorem phi_surj : Function.Surjective D.phi := fun j => ⟨(j, true), rfl⟩

theorem phi_eps (x : ι × Bool) : D.phi (D.eps x) = D.phi x := by
  obtain ⟨j, _ | _⟩ := x <;> simp [eps_true, eps_false, phi, prev]

theorem phi_fib (x y : ι × Bool) (h : D.phi x = D.phi y) : y = x ∨ y = D.eps x := by
  obtain ⟨j, _ | _⟩ := x <;> obtain ⟨k, _ | _⟩ := y <;>
    simp only [phi, prev, eps_true, eps_false] at *
  · left; simp [D.next.symm.injective h]
  · right; simp [h]
  · right; simp [h]
  · left; simp [h]

theorem smooth_swap_true (j u v : ι) :
    D.smoothRel (D.partner j) true u v ↔ D.smoothRel j true u v := by
  rw [smoothRel_true, smoothRel_true, D.partner_partner]; tauto

theorem smooth_swap_false (j u v : ι) :
    D.smoothRel (D.partner j) false u v ↔ D.smoothRel j false v u := by
  rw [smoothRel_false, smoothRel_false, D.partner_partner]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> subst h1 h2 <;> tauto

/-- Una suavizacion en cualquiera de las dos letras del cruce es una arista del grafo. -/
theorem eqv_of_smooth (σ : D.Cross → Bool) (ori : ι → Bool)
    (hpar : ∀ j, ori (D.partner j) = ori j)
    (hori : ∀ c : D.Cross, (σ c == D.sign c.1) = ori c.1) (j u v : ι)
    (h : D.smoothRel j (ori j) u v) : EqvGen (D.rel σ) u v := by
  by_cases hj : D.ovr j = true
  · exact EqvGen.rel _ _ ⟨⟨j, hj⟩, by rw [hori]; exact h⟩
  · have hp : D.ovr (D.partner j) = true := by
      rw [D.ovr_partner]; simpa using hj
    have h' : D.smoothRel (D.partner j) (ori j) u v ∨ D.smoothRel (D.partner j) (ori j) v u := by
      cases hoj : ori j
      · rw [hoj] at h
        right; rw [smooth_swap_false]; exact h
      · rw [hoj] at h
        left; rw [smooth_swap_true]; exact h
    have hr : ∀ a b, D.smoothRel (D.partner j) (ori j) a b → D.rel σ a b := fun a b hab =>
      ⟨⟨D.partner j, hp⟩, by rw [hori]; simpa [hpar] using hab⟩
    rcases h' with h' | h'
    · exact EqvGen.rel _ _ (hr _ _ h')
    · exact EqvGen.symm _ _ (EqvGen.rel _ _ (hr _ _ h'))

theorem orb_sm (σ : D.Cross → Bool) (ori : ι → Bool) (hpar : ∀ j, ori (D.partner j) = ori j)
    (hori : ∀ c : D.Cross, (σ c == D.sign c.1) = ori c.1) :
    orb {D.eps, D.sm ori hpar} = ncs (EqvGen.setoid (D.rel σ)) := by
  refine orb_eq_ncs D.eps (D.sm ori hpar) D.phi (D.rel σ) D.phi_surj D.phi_eps D.phi_fib ?_ ?_
  · rintro ⟨j, _ | _⟩
    · rw [sm_apply]
      cases hoj : ori j
      · refine D.eqv_of_smooth σ ori hpar hori j _ _ ?_
        rw [hoj, smoothRel_false]
        left; simp [phi]
      · refine D.eqv_of_smooth σ ori hpar hori j _ _ ?_
        rw [hoj, smoothRel_true]
        left; simp [phi]
    · rw [sm_apply]
      cases hoj : ori j
      · refine D.eqv_of_smooth σ ori hpar hori j _ _ ?_
        rw [hoj, smoothRel_false]
        right; simp [phi]
      · refine EqvGen.symm _ _ (D.eqv_of_smooth σ ori hpar hori j _ _ ?_)
        rw [hoj, smoothRel_true]
        right; simp [phi]
  · rintro u v ⟨c, hc⟩
    rw [hori] at hc
    cases hoc : ori c.1 <;> rw [hoc] at hc
    · rw [smoothRel_false] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(c.1, false), rfl, by simp [sm_apply, phi, hoc]⟩
      · exact ⟨(c.1, true), rfl, by simp [sm_apply, phi, hoc]⟩
    · rw [smoothRel_true] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(c.1, false), rfl, by simp [sm_apply, phi, hoc]⟩
      · refine ⟨(D.partner c.1, false), rfl, ?_⟩
        simp [sm_apply, phi, hpar, hoc, D.partner_partner]

end Lazos

section Lazos2

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Lazos del estado todo-A = orbitas de `<eps, a>` (sin circunferencias libres). -/
theorem lazos_allA_eq (hfree : D.free = 0) : D.lazos D.allA = orb {D.eps, D.a} := by
  rw [lazos_eq, hfree, add_zero]
  exact (D.orb_sm D.allA D.sign D.sign_partner (fun c => by simp [allA])).symm

/-- Lazos del estado todo-B = orbitas de `<eps, b>` (sin circunferencias libres). -/
theorem lazos_allB_eq (hfree : D.free = 0) : D.lazos D.allB = orb {D.eps, D.b} := by
  rw [lazos_eq, hfree, add_zero]
  exact (D.orb_sm D.allB (fun i => !D.sign i) D.notSign_partner
    (fun c => by simp [allB])).symm

end Lazos2

/-! ### (D) Cardinales -/

section Cardinal

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

theorem card_letras : Fintype.card ι = 2 * Fintype.card D.Cross := by
  have h1 : Fintype.card D.Cross = (Finset.univ.filter fun x => D.ovr x = true).card := by
    rw [Fintype.card_subtype]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun x => D.ovr x = true)
  have h3 : (Finset.univ.filter fun x => ¬ D.ovr x = true).card =
      (Finset.univ.filter fun x => D.ovr x = true).card := by
    refine Finset.card_nbij' D.partner D.partner ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Bool.not_eq_true] at hx ⊢
      rw [D.ovr_partner, hx.2]; exact ⟨Finset.mem_univ _, rfl⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Bool.not_eq_true] at hx ⊢
      rw [D.ovr_partner, hx.2]; exact ⟨Finset.mem_univ _, rfl⟩
    · intro x _; exact D.partner_partner x
    · intro x _; exact D.partner_partner x
  rw [Finset.card_univ] at h2
  omega

theorem card_modelo : Fintype.card (ι × Bool) = 4 * Fintype.card D.Cross := by
  rw [Fintype.card_prod, Fintype.card_bool, D.card_letras]; ring

end Cardinal

/-! ### (E) Conexion -/

section Conexion

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

theorem orb_eq_one (hcurve : ∀ i j : ι, D.next.SameCycle i j) (hne : Nonempty ι) :
    orb {D.eps, D.a, D.b} = 1 := by
  have hS : ∀ {g : Equiv.Perm (ι × Bool)}, g ∈ ({D.eps, D.a, D.b} : Set _) → ∀ x,
      (orbSetoid {D.eps, D.a, D.b}) x (g x) := fun hg x => orb_step hg x
  have h1 : ∀ j, (orbSetoid {D.eps, D.a, D.b}) (j, false) (j, true) := by
    intro j
    have e := (orbSetoid {D.eps, D.a, D.b}).trans (hS (g := D.b) (by simp) (j, false))
      (hS (g := D.a) (by simp) (D.b (j, false)))
    have : D.a (D.b (j, false)) = (j, true) := by
      simpa using D.ab_apply (j, false)
    rwa [this] at e
  have h2 : ∀ j, (orbSetoid {D.eps, D.a, D.b}) (j, true) (D.next j, true) := by
    intro j
    have e := hS (g := D.eps) (by simp) (j, true)
    rw [eps_true] at e
    exact (orbSetoid {D.eps, D.a, D.b}).trans e (h1 _)
  have h3 : ∀ (n : ℕ) j, (orbSetoid {D.eps, D.a, D.b}) (j, true) (((D.next ^ n) j), true) := by
    intro n
    induction n with
    | zero => intro j; exact (orbSetoid _).refl _
    | succ n ih =>
      intro j
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (orbSetoid _).trans (h2 j) (ih (D.next j))
  have h4 : ∀ i j, (orbSetoid {D.eps, D.a, D.b}) (i, true) (j, true) := by
    intro i j
    obtain ⟨n, hn⟩ := (hcurve i j).exists_nat_pow_eq
    rw [← hn]; exact h3 n i
  obtain ⟨i0⟩ := hne
  have hall : ∀ x y, (orbSetoid {D.eps, D.a, D.b}) x y := by
    have h5 : ∀ x : ι × Bool, (orbSetoid {D.eps, D.a, D.b}) x (i0, true) := by
      rintro ⟨j, _ | _⟩
      · exact (orbSetoid _).trans (h1 j) (h4 j i0)
      · exact h4 j i0
    intro x y
    exact (orbSetoid _).trans (h5 x) ((orbSetoid _).symm (h5 y))
  unfold orb ncs
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun p q => ?_⟩, ⟨Quotient.mk _ (i0, true)⟩⟩
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y => exact Quotient.sound (hall x y)

end Conexion

/-! ### (F) Desigualdad de genero -/

section Final

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- **Desigualdad de genero** `s_A + s_B <= c + 2` para un diagrama de una sola curva sin
circunferencias libres. -/
theorem lazos_allA_add_allB_le (D : GDiag ι) (hfree : D.free = 0)
    (hcurve : ∀ i j : ι, D.next.SameCycle i j) (hne : Nonempty D.Cross) :
    D.lazos D.allA + D.lazos D.allB ≤ Fintype.card D.Cross + 2 := by
  have hι : Nonempty ι := ⟨hne.some.1⟩
  rw [lazos_allA_eq D hfree, lazos_allB_eq D hfree]
  have hA := two_orb_le_cyc D.eps D.a D.eps_mul_eps (D.sm_mul_sm _ _) D.eps_ne
    (D.sm_ne _ _)
  have hB := two_orb_le_cyc D.eps D.b D.eps_mul_eps (D.sm_mul_sm _ _) D.eps_ne
    (D.sm_ne _ _)
  have hL := L2 D.eps D.a D.b D.eps_mul_eps (D.sm_mul_sm _ _) (D.sm_mul_sm _ _) D.ab_mul_ab
  rw [D.orb_eq_one hcurve hι, D.card_modelo] at hL
  omega

end Final

end TMENudos.Invariancia.GDiag

/-! ### (G) Sanidad: el trebol -/

theorem sameCycle_finRotate (n : ℕ) (i j : Fin n) : (finRotate n).SameCycle i j := by
  rcases n with _ | _ | n
  · exact i.elim0
  · rw [Fin.ext (by omega : i.1 = j.1)]
  · refine isCycle_finRotate.sameCycle ?_ ?_ <;>
      (rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia

/-- El trebol cumple las hipotesis: una curva, sin circunferencias libres, con cruces, y la
desigualdad de genero `s_A + s_B <= c + 2` (aqui `2 + 3 <= 3 + 2`, con igualdad). -/
theorem genero_trefoil :
    (ofWord trefoil wf_trefoil).lazos (ofWord trefoil wf_trefoil).allA +
      (ofWord trefoil wf_trefoil).lazos (ofWord trefoil wf_trefoil).allB ≤
      Fintype.card (ofWord trefoil wf_trefoil).Cross + 2 := by
  obtain ⟨hc, -, -⟩ := sanidad_trefoil
  refine GDiag.lazos_allA_add_allB_le _ ?_ (fun i j => sameCycle_finRotate _ i j) ?_
  · have : trefoil.length ≠ 0 := by decide +kernel
    change (if trefoil.length = 0 then 1 else 0) = 0
    simp [this]
  · exact Fintype.card_pos_iff.1 (by omega)

end TMENudos.Puente

#print axioms SpanPuente.two_orb_le_cyc
#print axioms SpanPuente.orb_eq_ncs
#print axioms TMENudos.Invariancia.GDiag.lazos_allA_eq
#print axioms TMENudos.Invariancia.GDiag.lazos_allB_eq
#print axioms TMENudos.Invariancia.GDiag.card_modelo
#print axioms TMENudos.Invariancia.GDiag.orb_eq_one
#print axioms TMENudos.Invariancia.GDiag.lazos_allA_add_allB_le
#print axioms TMENudos.Puente.genero_trefoil
