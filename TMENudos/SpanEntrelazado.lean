import Mathlib
import TMENudos.SpanFinal

/-!
# Etapa S5e: cuerdas entrelazadas implican no nugatorio

Para un diagrama `D` de una curva, un cruce `x` (letras `i`, `k = partner i`) divide la curva en
dos arcos abiertos: `A` (de `i` a `k` siguiendo `next`) y `B` (de `k` a `i`).  Otro cruce `y`
esta *entrelazado* con `x` si una letra de `y` cae en `A` y la otra en `B` (exactamente un
extremo de `y` entre los de `x`: la nocion `interlaced` de la sonda 28).

Resultado: si cada cruce esta entrelazado con algun otro, `D` es `NonNugatory`.

Idea de la prueba: en la estructura desacoplada en `x`, recorrer un arco (por `eps` y por el
paso `(j, s) ↦ (j, !s)` de los cruces intermedios) conecta todos los extremos del arco con
`(i, true)` (arco `A`) o con `(k, true)` (arco `B`); el cruce entrelazado `y` une un extremo de
`A` con uno de `B`; asi todo queda en una orbita.
-/

open SpanGenero TMENudos.Invariancia SpanPuente

namespace TMENudos.Invariancia.GDiag

section Arcos

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Arco abierto de `p` a `q`: letras `next^t p` con `t > 0` alcanzadas antes de volver a `p` o
tocar `q` (en una curva, son las letras estrictamente entre `p` y `q`). -/
def Arc (p q j : ι) : Prop :=
  ∃ t : ℕ, 0 < t ∧ (D.next ^ t) p = j ∧
    ∀ u : ℕ, 0 < u → u ≤ t → (D.next ^ u) p ≠ p ∧ (D.next ^ u) p ≠ q

/-- El cruce `y` esta entrelazado con `x`: una de sus letras cae en el arco `i → k` y la otra
en el arco `k → i`. -/
def Entrelazado (x y : D.Cross) : Prop :=
  (D.Arc x.1 (D.partner x.1) y.1 ∧ D.Arc (D.partner x.1) x.1 (D.partner y.1)) ∨
  (D.Arc x.1 (D.partner x.1) (D.partner y.1) ∧ D.Arc (D.partner x.1) x.1 y.1)

/-- Toda cuerda esta entrelazada con otra. -/
def TodaEntrelazada : Prop := ∀ x : D.Cross, ∃ y : D.Cross, y ≠ x ∧ D.Entrelazado x y

variable {D}

theorem Arc.ne {p q j : ι} (h : D.Arc p q j) : j ≠ p ∧ j ≠ q := by
  obtain ⟨t, ht, rfl, hu⟩ := h
  exact hu t ht le_rfl

theorem pow_apply_add (n u : ℕ) (p : ι) :
    (D.next ^ n) ((D.next ^ u) p) = (D.next ^ (n + u)) p := by
  rw [pow_add, Equiv.Perm.mul_apply]

theorem pow_mul_apply_of_eq {u : ℕ} {p : ι} (h : (D.next ^ u) p = p) (r : ℕ) :
    (D.next ^ (u * r)) p = p := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ, ← pow_apply_add, h, ih]

/-- Primer instante positivo en que `p` toca `{p, q}`, si `q` es alcanzable y distinto de `p`:
es un golpe a `q`. -/
theorem exists_first_hit {p q : ι} (hpq : p ≠ q) (hr : ∃ n : ℕ, (D.next ^ n) p = q) :
    ∃ m : ℕ, 0 < m ∧ (D.next ^ m) p = q ∧
      ∀ u : ℕ, 0 < u → u < m → (D.next ^ u) p ≠ p ∧ (D.next ^ u) p ≠ q := by
  classical
  obtain ⟨n, hn⟩ := hr
  have hex : ∃ u : ℕ, 0 < u ∧ ((D.next ^ u) p = p ∨ (D.next ^ u) p = q) := by
    refine ⟨n, ?_, Or.inr hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by simpa using hn) hpq
    · exact h
  have hspec := Nat.find_spec hex
  have hmin : ∀ v, v < Nat.find hex → ¬ (0 < v ∧ ((D.next ^ v) p = p ∨ (D.next ^ v) p = q)) :=
    fun v hv => Nat.find_min hex hv
  refine ⟨Nat.find hex, hspec.1, ?_, fun u hu hlt => ?_⟩
  · rcases hspec.2 with h | h
    · exfalso
      have hq : (D.next ^ (n % Nat.find hex)) p = q := by
        calc (D.next ^ (n % Nat.find hex)) p
            = (D.next ^ (n % Nat.find hex))
                ((D.next ^ (Nat.find hex * (n / Nat.find hex))) p) := by
              rw [pow_mul_apply_of_eq h]
          _ = (D.next ^ (n % Nat.find hex + Nat.find hex * (n / Nat.find hex))) p :=
              pow_apply_add _ _ _
          _ = q := by rw [Nat.mod_add_div]; exact hn
      have hr0 : 0 < n % Nat.find hex := by
        rcases Nat.eq_zero_or_pos (n % Nat.find hex) with h0 | h0
        · rw [h0] at hq; exact absurd (by simpa using hq) hpq
        · exact h0
      exact hmin _ (Nat.mod_lt _ hspec.1) ⟨hr0, Or.inr hq⟩
    · exact h
  · have := hmin u hlt
    exact ⟨fun h => this ⟨hu, Or.inl h⟩, fun h => this ⟨hu, Or.inr h⟩⟩

/-- Recubrimiento: toda letra alcanzable desde `p` y distinta de `p, q` esta en uno de los dos
arcos. -/
theorem arc_cover (n : ℕ) : ∀ (p q j : ι), (D.next ^ n) p = j → j ≠ p → j ≠ q →
    D.Arc p q j ∨ D.Arc q p j := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q j hn hjp hjq
    by_cases hall : ∀ u : ℕ, 0 < u → u ≤ n → (D.next ^ u) p ≠ p ∧ (D.next ^ u) p ≠ q
    · left
      refine ⟨n, ?_, hn, hall⟩
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (by simpa using hn.symm) hjp
      · exact h
    · have hex : ∃ u : ℕ, 0 < u ∧ u ≤ n ∧ ((D.next ^ u) p = p ∨ (D.next ^ u) p = q) := by
        by_contra hne
        apply hall
        intro u hu hun
        exact ⟨fun h => hne ⟨u, hu, hun, Or.inl h⟩, fun h => hne ⟨u, hu, hun, Or.inr h⟩⟩
      obtain ⟨u, hu, hun, hpq⟩ := hex
      have hsub : (D.next ^ (n - u)) ((D.next ^ u) p) = j := by
        rw [pow_apply_add, Nat.sub_add_cancel hun]; exact hn
      have hlt : n - u < n := Nat.sub_lt (lt_of_lt_of_le hu hun) hu
      rcases hpq with h | h
      · rw [h] at hsub
        exact ih _ hlt p q j hsub hjp hjq
      · rw [h] at hsub
        exact (ih _ hlt q p j hsub hjq hjp).symm

end Arcos

/-! ### Recorrido de un arco -/

section Recorrido

variable {ι : Type} [DecidableEq ι] [Fintype ι] {D : GDiag ι}

/-- Recorrer el arco: `(p, true)` queda relacionado con `(next^(t+1) p, false)`. -/
theorem walk (R : Setoid (ι × Bool)) (p q : ι)
    (H1 : ∀ j, R (j, true) (D.next j, false))
    (H2 : ∀ j, j ≠ p → j ≠ q → ∀ s, R (j, s) (j, !s)) :
    ∀ t : ℕ, (∀ u : ℕ, 0 < u → u ≤ t → (D.next ^ u) p ≠ p ∧ (D.next ^ u) p ≠ q) →
      R (p, true) ((D.next ^ (t + 1)) p, false) := by
  intro t
  induction t with
  | zero => intro _; simpa using H1 p
  | succ t ih =>
    intro hu
    have h1 := ih (fun u h1 h2 => hu u h1 (by omega))
    have hl := hu (t + 1) (by omega) le_rfl
    have h2 := H2 _ hl.1 hl.2 false
    have h3 := H1 ((D.next ^ (t + 1)) p)
    have e : (D.next ^ (t + 1 + 1)) p = D.next ((D.next ^ (t + 1)) p) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [e]
    exact R.trans h1 (R.trans h2 h3)

/-- Los dos extremos de toda letra de un arco quedan relacionados con `(p, true)`. -/
theorem arc_reach (R : Setoid (ι × Bool)) (p q j : ι)
    (H1 : ∀ j, R (j, true) (D.next j, false))
    (H2 : ∀ j, j ≠ p → j ≠ q → ∀ s, R (j, s) (j, !s)) (h : D.Arc p q j) (s : Bool) :
    R (p, true) (j, s) := by
  obtain ⟨t, ht, rfl, hu⟩ := h
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have h1 := walk R p q H1 H2 t (fun u h1 h2 => hu u h1 (by omega))
  have hl := hu (t + 1) (by omega) le_rfl
  cases s
  · exact h1
  · exact R.trans h1 (H2 _ hl.1 hl.2 false)

/-- El arco termina en `(q, false)`. -/
theorem hit_reach (R : Setoid (ι × Bool)) (p q : ι)
    (H1 : ∀ j, R (j, true) (D.next j, false))
    (H2 : ∀ j, j ≠ p → j ≠ q → ∀ s, R (j, s) (j, !s)) (m : ℕ) (hm : 0 < m)
    (hq : (D.next ^ m) p = q)
    (hu : ∀ u : ℕ, 0 < u → u < m → (D.next ^ u) p ≠ p ∧ (D.next ^ u) p ≠ q) :
    R (p, true) (q, false) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have := walk R p q H1 H2 m (fun u h1 h2 => hu u h1 (by omega))
  rwa [hq] at this

/-- **Conectividad**: si la letra `j` esta en el arco `i → k` y su pareja en el arco `k → i`,
y la relacion `R` pasa por `eps`, por el giro `(j, s) ↦ (j, !s)` en las letras ajenas a `x` y
por algun emparejamiento en cada letra ajena a `x`, entonces `R` es total. -/
theorem rel_all (hcurve : ∀ i j : ι, D.next.SameCycle i j) (i : ι) (R : Setoid (ι × Bool))
    (hE : ∃ j, D.Arc i (D.partner i) j ∧ D.Arc (D.partner i) i (D.partner j))
    (H1 : ∀ j, R (j, true) (D.next j, false))
    (H2 : ∀ j, j ≠ i → j ≠ D.partner i → ∀ s, R (j, s) (j, !s))
    (H3 : ∀ j, j ≠ i → j ≠ D.partner i → ∃ s, R (j, true) (D.partner j, s)) :
    ∀ z, R (i, true) z := by
  have hik : i ≠ D.partner i := (D.partner_ne i).symm
  have hki : D.partner i ≠ i := D.partner_ne i
  obtain ⟨m, hm0, hmk, hmu⟩ := exists_first_hit (D := D) hik (hcurve i _).exists_nat_pow_eq
  obtain ⟨m', hm0', hmi, hmu'⟩ := exists_first_hit (D := D) hki (hcurve _ i).exists_nat_pow_eq
  have H2' : ∀ j, j ≠ D.partner i → j ≠ i → ∀ s, R (j, s) (j, !s) := fun j a b s => H2 j b a s
  have P := hit_reach R i _ H1 H2 m hm0 hmk hmu
  have Q := hit_reach R (D.partner i) i H1 H2' m' hm0' hmi hmu'
  obtain ⟨j, hjA, hjB⟩ := hE
  have hj := hjA.ne
  obtain ⟨s, hs⟩ := H3 j hj.1 hj.2
  have hik' : R (i, true) (D.partner i, true) :=
    R.trans (arc_reach R i _ j H1 H2 hjA true)
      (R.trans hs (R.symm (arc_reach R (D.partner i) i _ H1 H2' hjB s)))
  rintro ⟨l, s⟩
  by_cases hli : l = i
  · rw [hli]
    cases s
    · exact R.trans hik' Q
    · exact R.refl _
  by_cases hlk : l = D.partner i
  · rw [hlk]
    cases s
    · exact P
    · exact hik'
  obtain ⟨n, hn⟩ := (hcurve i l).exists_nat_pow_eq
  rcases arc_cover n i _ l hn hli hlk with h | h
  · exact arc_reach R i _ l H1 H2 h s
  · exact R.trans hik' (arc_reach R (D.partner i) i l H1 H2' h s)

end Recorrido

/-! ### Los dos grupos desacoplados -/

section Grupos

variable {ι : Type} [DecidableEq ι] [Fintype ι] {D : GDiag ι}

theorem orb_eq_one_of_rel {X : Type*} [Finite X] (S : Set (Equiv.Perm X)) (x0 : X)
    (hall : ∀ y, (orbSetoid S) x0 y) : orb S = 1 := by
  have hsub : Subsingleton (Quotient (orbSetoid S)) := by
    constructor
    intro p q
    induction p using Quotient.inductionOn with
    | _ y =>
      induction q using Quotient.inductionOn with
      | _ z =>
        exact Quotient.sound ((orbSetoid S).trans ((orbSetoid S).symm (hall y)) (hall z))
  haveI : Nonempty (Quotient (orbSetoid S)) := ⟨Quotient.mk _ x0⟩
  have hpos : 0 < ncs (orbSetoid S) := Nat.card_pos
  have hle : ncs (orbSetoid S) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  unfold orb
  omega

theorem entrelazado_arcs {x y : D.Cross} (hy : D.Entrelazado x y) :
    ∃ j, D.Arc x.1 (D.partner x.1) j ∧ D.Arc (D.partner x.1) x.1 (D.partner j) := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨y.1, h1, h2⟩
  · exact ⟨D.partner y.1, h1, by rwa [D.partner_partner]⟩

theorem a_bX_apply (x : D.Cross) (y : ι × Bool) :
    (D.a * D.bX x) y =
      (y.1, xor y.2 (if y.1 = x.1 ∨ y.1 = D.partner x.1 then false else true)) := by
  rw [a, bX, D.sm_mul_sm_apply']
  obtain ⟨j, s⟩ := y
  simp only [oriBX]
  split_ifs <;> cases hs : D.sign j <;> cases s <;> simp_all

/-- El grupo `<eps, a_x, b>` es transitivo si `x` tiene una cuerda entrelazada. -/
theorem orb_aX_b_eq_one (hcurve : ∀ i j : ι, D.next.SameCycle i j) (x y : D.Cross)
    (hy : D.Entrelazado x y) : orb {D.eps, D.aX x, D.b} = 1 := by
  have hall := rel_all hcurve x.1 (orbSetoid {D.eps, D.aX x, D.b}) (entrelazado_arcs hy)
    (fun j => by
      have := orb_step (S := {D.eps, D.aX x, D.b}) (g := D.eps) (by simp) (j, true)
      rwa [D.eps_true] at this)
    (fun j hj1 hj2 s => by
      have h1 := orb_step (S := {D.eps, D.aX x, D.b}) (g := D.b) (by simp) (j, s)
      have h2 := orb_step (S := {D.eps, D.aX x, D.b}) (g := D.aX x) (by simp) (D.b (j, s))
      have e : D.aX x (D.b (j, s)) = (j, !s) := by
        have := D.aX_b_apply x (j, s)
        rw [Equiv.Perm.mul_apply] at this
        rw [this]
        simp [hj1, hj2]
      rw [e] at h2
      exact (orbSetoid _).trans h1 h2)
    (fun j _ _ => ⟨_, by
      have := orb_step (S := {D.eps, D.aX x, D.b}) (g := D.b) (by simp) (j, true)
      rwa [D.b_apply] at this⟩)
  exact orb_eq_one_of_rel _ (x.1, true) hall

/-- El grupo `<eps, a, b_x>` es transitivo si `x` tiene una cuerda entrelazada. -/
theorem orb_a_bX_eq_one (hcurve : ∀ i j : ι, D.next.SameCycle i j) (x y : D.Cross)
    (hy : D.Entrelazado x y) : orb {D.eps, D.a, D.bX x} = 1 := by
  have hall := rel_all hcurve x.1 (orbSetoid {D.eps, D.a, D.bX x}) (entrelazado_arcs hy)
    (fun j => by
      have := orb_step (S := {D.eps, D.a, D.bX x}) (g := D.eps) (by simp) (j, true)
      rwa [D.eps_true] at this)
    (fun j hj1 hj2 s => by
      have h1 := orb_step (S := {D.eps, D.a, D.bX x}) (g := D.bX x) (by simp) (j, s)
      have h2 := orb_step (S := {D.eps, D.a, D.bX x}) (g := D.a) (by simp) (D.bX x (j, s))
      have e : D.a (D.bX x (j, s)) = (j, !s) := by
        have := a_bX_apply x (j, s)
        rw [Equiv.Perm.mul_apply] at this
        rw [this]
        simp [hj1, hj2]
      rw [e] at h2
      exact (orbSetoid _).trans h1 h2)
    (fun j _ _ => ⟨_, by
      have := orb_step (S := {D.eps, D.a, D.bX x}) (g := D.a) (by simp) (j, true)
      rwa [D.a_apply] at this⟩)
  exact orb_eq_one_of_rel _ (x.1, true) hall

/-- **Teorema central (S5e)**: si toda cuerda esta entrelazada con otra, el diagrama de una
curva es no nugatorio. -/
theorem nonNugatory_of_entrelazada (D : GDiag ι) (hcurve : ∀ i j : ι, D.next.SameCycle i j)
    (h : D.TodaEntrelazada) : D.NonNugatory := fun x => by
  obtain ⟨y, -, hy⟩ := h x
  exact ⟨orb_aX_b_eq_one hcurve x y hy, orb_a_bX_eq_one hcurve x y hy⟩

end Grupos

end TMENudos.Invariancia.GDiag

/-! ### Corolario final -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.Nudos

/-- **Minimalidad de cruces para diagramas alternantes planares con toda cuerda entrelazada.** -/
theorem minimal_alternante_planar_entrelazada (d d' : Diag) (h : GRel d d')
    (hf : d.D.free = 0) (hcurve : ∀ i j, d.D.next.SameCycle i j) (halt : d.D.Alt)
    (hpl : d.D.PlanarD) (hent : d.D.TodaEntrelazada) (hne : Nonempty d.D.Cross)
    (hf' : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    Fintype.card d.D.Cross ≤ Fintype.card d'.D.Cross :=
  minimal_alternante_planar d d' h hf halt hpl
    (GDiag.nonNugatory_of_entrelazada d.D hcurve hent) hne hf' hc

end TMENudos.Puente


/-! ### Sanidad: el trebol tiene toda cuerda entrelazada -/

namespace TMENudos.Invariancia.GDiag

section Decidible

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Version acotada y decidible de `Arc` (tiempos `< N`). -/
def ArcD (N : ℕ) (p q j : ι) : Prop :=
  ∃ t ∈ Finset.range N, 0 < t ∧ (D.next ^ t) p = j ∧
    ∀ u ∈ Finset.range N, 0 < u → u ≤ t → (D.next ^ u) p ≠ p ∧ (D.next ^ u) p ≠ q

instance (N : ℕ) (p q j : ι) : Decidable (D.ArcD N p q j) := by
  unfold ArcD; infer_instance

theorem ArcD.arc {N : ℕ} {p q j : ι} (h : D.ArcD N p q j) : D.Arc p q j := by
  obtain ⟨t, htN, ht, hj, hu⟩ := h
  refine ⟨t, ht, hj, fun u hu0 hut => hu u ?_ hu0 hut⟩
  exact Finset.mem_range.2 (lt_of_le_of_lt hut (Finset.mem_range.1 htN))

/-- Version decidible de `Entrelazado`. -/
def EntrelazadoD (N : ℕ) (x y : D.Cross) : Prop :=
  (D.ArcD N x.1 (D.partner x.1) y.1 ∧ D.ArcD N (D.partner x.1) x.1 (D.partner y.1)) ∨
  (D.ArcD N x.1 (D.partner x.1) (D.partner y.1) ∧ D.ArcD N (D.partner x.1) x.1 y.1)

instance (N : ℕ) (x y : D.Cross) : Decidable (D.EntrelazadoD N x y) := by
  unfold EntrelazadoD; infer_instance

theorem EntrelazadoD.entrelazado {N : ℕ} {x y : D.Cross} (h : D.EntrelazadoD N x y) :
    D.Entrelazado x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.arc, h2.arc⟩
  · exact Or.inr ⟨h1.arc, h2.arc⟩

end Decidible

end TMENudos.Invariancia.GDiag

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.Nudos

/-- Sanidad: en el trebol toda cuerda esta entrelazada con otra (las tres, dos a dos). -/
theorem trefoil_todaEntrelazada : (ofWord trefoil wf_trefoil).TodaEntrelazada := by
  have h : ∀ x : (ofWord trefoil wf_trefoil).Cross, ∃ y : (ofWord trefoil wf_trefoil).Cross,
      y ≠ x ∧ (ofWord trefoil wf_trefoil).EntrelazadoD 7 x y := by
    decide +kernel
  intro x
  obtain ⟨y, hne, hy⟩ := h x
  exact ⟨y, hne, hy.entrelazado⟩

/-- El trebol es una sola curva. -/
theorem trefoil_curve : ∀ i j, (ofWord trefoil wf_trefoil).next.SameCycle i j := by
  decide +kernel

/-- El trebol es no nugatorio tambien por la ruta general (S5e), sin tablas de caminos. -/
theorem trefoil_nonNugatory_entrelazado : (ofWord trefoil wf_trefoil).NonNugatory :=
  GDiag.nonNugatory_of_entrelazada _ trefoil_curve trefoil_todaEntrelazada

end TMENudos.Puente

#print axioms TMENudos.Puente.trefoil_todaEntrelazada
#print axioms TMENudos.Puente.trefoil_nonNugatory_entrelazado

#print axioms TMENudos.Invariancia.GDiag.arc_cover
#print axioms TMENudos.Invariancia.GDiag.rel_all
#print axioms TMENudos.Invariancia.GDiag.nonNugatory_of_entrelazada
#print axioms TMENudos.Puente.minimal_alternante_planar_entrelazada
