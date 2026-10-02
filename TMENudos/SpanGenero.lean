import Mathlib

/-!
# Desigualdad de genero (etapa S3)

Resultado combinatorio sobre permutaciones de un tipo finito `X`:

* `cyc` : numero de ciclos (con puntos fijos) de una permutacion;
* `orb` : numero de orbitas del grupo generado por un conjunto de permutaciones;
* `L1` : si `sigma * tau * rho = 1` entonces `cyc sigma + cyc tau + cyc rho <= |X| + 2 * orb`.
-/

open Relation


namespace SpanGenero

section Conteo

variable {X : Type*}

/-- Numero de clases de un setoid. -/
noncomputable def ncs (s : Setoid X) : ℕ := Nat.card (Quotient s)

theorem eqvGen_le {E : X → X → Prop} {s : Setoid X} (h : ∀ x y, E x y → s x y) :
    ∀ {x y}, EqvGen E x y → s x y := by
  intro x y hxy
  induction hxy with
  | rel x y h' => exact h x y h'
  | refl x => exact s.refl x
  | symm x y _ ih => exact s.symm ih
  | trans x y z _ _ ih1 ih2 => exact s.trans ih1 ih2

/-- Setoid obtenido anadiendo una arista `a — b`. -/
def join1 (s : Setoid X) (a b : X) : Setoid X :=
  EqvGen.setoid (fun x y => s x y ∨ (x = a ∧ y = b))

theorem le_join1 (s : Setoid X) (a b : X) : ∀ x y, s x y → (join1 s a b) x y :=
  fun x y h => EqvGen.rel x y (Or.inl h)

theorem join1_edge (s : Setoid X) (a b : X) : (join1 s a b) a b :=
  EqvGen.rel a b (Or.inr ⟨rfl, rfl⟩)

variable [Finite X]

theorem ncs_le_card (s : Setoid X) : ncs s ≤ Nat.card X :=
  Nat.card_le_card_of_surjective _ (Quotient.mk_surjective (s := s))

/-- Un setoid mas grueso tiene menos clases. -/
theorem ncs_le_of_le {s s' : Setoid X} (h : ∀ x y, s x y → s' x y) : ncs s' ≤ ncs s := by
  have hf : Function.Surjective
      (Quotient.map (sa := s) (sb := s') id (fun x y hxy => h x y hxy)) := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact ⟨Quotient.mk _ x, rfl⟩
  exact Nat.card_le_card_of_surjective _ hf

/-- Si ademas se identifican dos puntos antes distintos, baja al menos en 1. -/
theorem ncs_lt_of_lt {s s' : Setoid X} (h : ∀ x y, s x y → s' x y)
    (x y : X) (hs' : s' x y) (hs : ¬ s x y) : ncs s' + 1 ≤ ncs s := by
  have hf : Function.Surjective
      (Quotient.map (sa := s) (sb := s') id (fun x y hxy => h x y hxy)) := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact ⟨Quotient.mk _ x, rfl⟩
  have hle := ncs_le_of_le h
  by_contra hcon
  have hcard : Nat.card (Quotient s) ≤ Nat.card (Quotient s') := by
    unfold ncs at hle hcon
    omega
  have hbij := hf.bijective_of_nat_card_le hcard
  have : Quotient.mk s x = Quotient.mk s y := by
    apply hbij.1
    exact Quotient.sound hs'
  exact hs (Quotient.exact this)

/-- Anadir una arista baja el numero de clases a lo sumo en 1. -/
theorem ncs_le_join1 (s : Setoid X) (a b : X) : ncs s ≤ ncs (join1 s a b) + 1 := by
  classical
  -- caracterizacion de la relacion ampliada
  have hchar : ∀ x y, (join1 s a b) x y →
      Quotient.mk s x = Quotient.mk s y ∨
      (Quotient.mk s x = Quotient.mk s a ∧ Quotient.mk s y = Quotient.mk s b) ∨
      (Quotient.mk s x = Quotient.mk s b ∧ Quotient.mk s y = Quotient.mk s a) := by
    intro x y hxy
    induction hxy with
    | rel x y h =>
      rcases h with h | ⟨rfl, rfl⟩
      · exact Or.inl (Quotient.sound h)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | refl x => exact Or.inl rfl
    | symm x y _ ih => grind
    | trans x y z _ _ ih1 ih2 => grind
  -- aplicacion inyectiva de las clases distintas de `[b]`
  have hf : Function.Injective (fun c : Quotient s =>
      (if c = Quotient.mk s b then none else
        some (Quotient.map (sa := s) (sb := join1 s a b) id
          (fun x y hxy => le_join1 s a b x y hxy) c) :
        Option (Quotient (join1 s a b)))) := by
    intro c d hcd
    induction c using Quotient.inductionOn with
    | _ x =>
    induction d using Quotient.inductionOn with
    | _ y =>
    by_cases hx : Quotient.mk s x = Quotient.mk s b <;>
      by_cases hy : Quotient.mk s y = Quotient.mk s b
    · rw [hx, hy]
    · dsimp only at hcd
      rw [if_pos hx, if_neg hy] at hcd
      cases hcd
    · dsimp only at hcd
      rw [if_neg hx, if_pos hy] at hcd
      cases hcd
    · dsimp only at hcd
      rw [if_neg hx, if_neg hy, Option.some.injEq] at hcd
      have h2 : (join1 s a b) x y := Quotient.exact hcd
      rcases hchar x y h2 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h
      · exact absurd h2 hy
      · exact absurd h1 hx
  have := Nat.card_le_card_of_injective _ hf
  rw [Finite.card_option] at this
  exact this

end Conteo

section Ciclos

variable {X : Type*}

/-- "Mismo ciclo": cierre de equivalencia de `x ↦ π x`. -/
def cycSetoid (π : Equiv.Perm X) : Setoid X := EqvGen.setoid (fun x y => π x = y)

/-- Numero de ciclos de `π`, incluyendo los puntos fijos. -/
noncomputable def cyc (π : Equiv.Perm X) : ℕ := ncs (cycSetoid π)

theorem cyc_step (π : Equiv.Perm X) (x : X) : (cycSetoid π) x (π x) :=
  EqvGen.rel x (π x) rfl

theorem cyc_pow (π : Equiv.Perm X) (a : X) (n : ℕ) : (cycSetoid π) a ((π ^ n) a) := by
  induction n with
  | zero => exact (cycSetoid π).refl a
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (cycSetoid π).trans ih (cyc_step π _)

theorem cyc_le_card [Fintype X] (π : Equiv.Perm X) : cyc π ≤ Fintype.card X := by
  have := ncs_le_card (cycSetoid π)
  rwa [Nat.card_eq_fintype_card] at this

theorem cycSetoid_le_sameCycle (π : Equiv.Perm X) {x y : X} (h : (cycSetoid π) x y) :
    π.SameCycle x y := by
  refine eqvGen_le (s := Equiv.Perm.SameCycle.setoid π) ?_ h
  intro u v huv
  subst huv
  exact ⟨1, by simp⟩

theorem sameCycle_le_cycSetoid [Finite X] (π : Equiv.Perm X) {x y : X} (h : π.SameCycle x y) :
    (cycSetoid π) x y := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact cyc_pow π x i

theorem cycSetoid_iff [Finite X] (π : Equiv.Perm X) {x y : X} :
    (cycSetoid π) x y ↔ π.SameCycle x y :=
  ⟨cycSetoid_le_sameCycle π, sameCycle_le_cycSetoid π⟩

theorem cyc_inv [Finite X] (π : Equiv.Perm X) : cyc π⁻¹ = cyc π := by
  have : cycSetoid π⁻¹ = cycSetoid π := by
    ext x y
    rw [cycSetoid_iff, cycSetoid_iff, Equiv.Perm.sameCycle_inv]
  unfold cyc
  rw [this]

/-- Una transposicion cuyos extremos estan relacionados mueve cada punto a un relacionado. -/
theorem rel_swap [DecidableEq X] {t : Setoid X} {a b : X} (h : t a b) (z : X) :
    t z (Equiv.swap a b z) := by
  by_cases hza : z = a
  · subst hza
    simpa using h
  · by_cases hzb : z = b
    · subst hzb
      simpa using t.symm h
    · rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

/-- Multiplicar por una transposicion cambia `cyc` en a lo sumo 1 (cota inferior). -/
theorem cyc_le_swap_mul [Finite X] [DecidableEq X] (π : Equiv.Perm X) (a b : X) :
    cyc π ≤ cyc (Equiv.swap a b * π) + 1 := by
  have h1 : ∀ x y, (cycSetoid (Equiv.swap a b * π)) x y → (join1 (cycSetoid π) a b) x y := by
    refine fun x y h => eqvGen_le (s := join1 (cycSetoid π) a b) ?_ h
    intro u v huv
    subst huv
    rw [Equiv.Perm.mul_apply]
    exact (join1 _ a b).trans (le_join1 _ a b _ _ (cyc_step π u))
      (rel_swap (join1_edge _ a b) _)
  have h2 := ncs_le_of_le h1
  have h3 := ncs_le_join1 (cycSetoid π) a b
  unfold cyc
  omega

theorem cyc_swap_mul_le [Finite X] [DecidableEq X] (π : Equiv.Perm X) (a b : X) :
    cyc (Equiv.swap a b * π) ≤ cyc π + 1 := by
  have := cyc_le_swap_mul (Equiv.swap a b * π) a b
  rwa [← mul_assoc, Equiv.swap_mul_self, one_mul] at this

/-- Potencia periodica: si `f^m a = a` entonces `f^(m*q + r) a = f^r a`. -/
theorem pow_period (f : Equiv.Perm X) (a : X) (m : ℕ) (h : (f ^ m) a = a) (q r : ℕ) :
    (f ^ (m * q + r)) a = (f ^ r) a := by
  have hq : ∀ q : ℕ, (f ^ (m * q)) a = a := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, h, ih]
  rw [add_comm, pow_add, Equiv.Perm.mul_apply, hq]

/-- Primer retorno a `{a, b}` bajo `π`. -/
theorem exists_first (π : Equiv.Perm X) (a b : X)
    (h : ∃ k, 0 < k ∧ ((π ^ k) a = a ∨ (π ^ k) a = b)) :
    ∃ m, 0 < m ∧ ((π ^ m) a = a ∨ (π ^ m) a = b) ∧
      ∀ j, 0 < j → j < m → (π ^ j) a ≠ a ∧ (π ^ j) a ≠ b := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, fun j hj hjm => ?_⟩
  have := Nat.find_min h hjm
  simp only [not_and, not_or] at this
  exact this hj

/-- Las iteradas de `swap a b * π` desde `a` siguen a `π` hasta el primer retorno. -/
theorem iter_swap_mul [DecidableEq X] (π : Equiv.Perm X) (a b : X) (m : ℕ) (hm : 0 < m)
    (hmin : ∀ j, 0 < j → j < m → (π ^ j) a ≠ a ∧ (π ^ j) a ≠ b) :
    (∀ i, i < m → ((Equiv.swap a b * π) ^ i) a = (π ^ i) a) ∧
      ((Equiv.swap a b * π) ^ m) a = Equiv.swap a b ((π ^ m) a) := by
  have e : ∀ n, (π ^ (n + 1)) a = π ((π ^ n) a) := fun n => by
    rw [pow_succ', Equiv.Perm.mul_apply]
  have key : ∀ i, i < m → ((Equiv.swap a b * π) ^ i) a = (π ^ i) a := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), Equiv.Perm.mul_apply, ← e i]
      have := hmin (i + 1) (by omega) hi
      rw [Equiv.swap_apply_of_ne_of_ne this.1 this.2]
  refine ⟨key, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ', Equiv.Perm.mul_apply, key i (by omega), Equiv.Perm.mul_apply, ← e i]

/-- Fusion: si `a` y `b` estan en ciclos distintos de `π`, quedan en el mismo ciclo de
`swap a b * π`. -/
theorem cyc_swap_connect [Finite X] [DecidableEq X] (π : Equiv.Perm X) (a b : X)
    (h : ¬ (cycSetoid π) a b) :
    (cycSetoid (Equiv.swap a b * π)) a b := by
  obtain ⟨m, hm, hmem, hmin⟩ := exists_first π a b
    ⟨orderOf π, orderOf_pos π, Or.inl (by rw [pow_orderOf_eq_one]; rfl)⟩
  have hma : (π ^ m) a = a := by
    rcases hmem with h' | h'
    · exact h'
    · exact absurd (h' ▸ cyc_pow π a m) h
  have := (iter_swap_mul π a b m hm hmin).2
  rw [hma, Equiv.swap_apply_left] at this
  have h2 := cyc_pow (Equiv.swap a b * π) a m
  rwa [this] at h2

theorem pow_mod_apply (f : Equiv.Perm X) (a : X) (m : ℕ) (h : (f ^ m) a = a) (k : ℕ) :
    (f ^ k) a = (f ^ (k % m)) a := by
  have := pow_period f a m h (k / m) (k % m)
  rwa [Nat.div_add_mod] at this

/-- Corte: si `a ≠ b` estan en el mismo ciclo de `π`, quedan en ciclos distintos de
`swap a b * π`. -/
theorem not_cyc_swap_of_cyc [Finite X] [DecidableEq X] (π : Equiv.Perm X) (a b : X) (hab : a ≠ b)
    (h : (cycSetoid π) a b) : ¬ (cycSetoid (Equiv.swap a b * π)) a b := by
  obtain ⟨k, hk⟩ := (cycSetoid_le_sameCycle π h).exists_nat_pow_eq
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      exact absurd (by simpa using hk) hab
    · exact h0
  obtain ⟨m, hm, hmem, hmin⟩ := exists_first π a b ⟨k, hk0, Or.inr hk⟩
  have hnb : ∀ r, r < m → (π ^ r) a = b → False := by
    intro r hr hrb
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exact hab (by simpa using hrb)
    · exact (hmin r h0 hr).2 hrb
  have hmb : (π ^ m) a = b := by
    rcases hmem with h' | h'
    · exfalso
      have := pow_mod_apply π a m h' k
      exact hnb (k % m) (Nat.mod_lt _ hm) (this ▸ hk)
    · exact h'
  obtain ⟨hit, hlast⟩ := iter_swap_mul π a b m hm hmin
  have hper : ((Equiv.swap a b * π) ^ m) a = a := by
    rw [hlast, hmb, Equiv.swap_apply_right]
  intro hc
  obtain ⟨i, hi⟩ := (cycSetoid_le_sameCycle _ hc).exists_nat_pow_eq
  rw [pow_mod_apply _ a m hper i, hit _ (Nat.mod_lt _ hm)] at hi
  exact hnb _ (Nat.mod_lt _ hm) hi

/-- Cota inferior de la division: si `a ≠ b` estan en el mismo ciclo, `cyc` sube en 1. -/
theorem cyc_lt_swap_mul [Finite X] [DecidableEq X] (π : Equiv.Perm X) (a b : X) (hab : a ≠ b)
    (h : (cycSetoid π) a b) : cyc π + 1 ≤ cyc (Equiv.swap a b * π) := by
  have h1 : ∀ x y, (cycSetoid (Equiv.swap a b * π)) x y → (cycSetoid π) x y := by
    refine fun x y h' => eqvGen_le (s := cycSetoid π) ?_ h'
    intro u v huv
    subst huv
    rw [Equiv.Perm.mul_apply]
    exact (cycSetoid π).trans (cyc_step π u) (rel_swap h _)
  exact ncs_lt_of_lt h1 a b h (not_cyc_swap_of_cyc π a b hab h)

end Ciclos

section Orbitas

variable {X : Type*}

/-- Aristas `x — g x` para `g ∈ S`. -/
def edges (S : Set (Equiv.Perm X)) : X → X → Prop := fun x y => ∃ g ∈ S, g x = y

/-- Relacion "misma orbita" del grupo generado por `S`. -/
def orbSetoid (S : Set (Equiv.Perm X)) : Setoid X := EqvGen.setoid (edges S)

/-- Numero de orbitas del subgrupo generado por `S` actuando sobre `X`. -/
noncomputable def orb (S : Set (Equiv.Perm X)) : ℕ := ncs (orbSetoid S)

theorem orb_step {S : Set (Equiv.Perm X)} {g : Equiv.Perm X} (hg : g ∈ S) (x : X) :
    (orbSetoid S) x (g x) :=
  EqvGen.rel x (g x) ⟨g, hg, rfl⟩

theorem orbSetoid_le {S : Set (Equiv.Perm X)} {t : Setoid X}
    (h : ∀ g ∈ S, ∀ x, t x (g x)) : ∀ x y, (orbSetoid S) x y → t x y := by
  intro x y hxy
  refine eqvGen_le ?_ hxy
  rintro u v ⟨g, hg, rfl⟩
  exact h g hg u

/-- Comparacion de orbitas tras multiplicar por una transposicion. -/
theorem orb_cmp [DecidableEq X] {σ τ ρ σ' τ' : Equiv.Perm X} {a b : X} {T : Setoid X}
    (hG' : ∀ x y, (orbSetoid {σ', τ', ρ}) x y → T x y)
    (hst : ∀ z, T z (Equiv.swap a b z))
    (hσ : ∀ x, σ x = σ' (Equiv.swap a b x)) (hτ : ∀ x, τ x = Equiv.swap a b (τ' x)) :
    ∀ x y, (orbSetoid {σ, τ, ρ}) x y → T x y := by
  apply orbSetoid_le
  intro g hg u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [hσ u]
    exact T.trans (hst u) (hG' _ _ (orb_step (by simp) _))
  · rw [hτ u]
    exact T.trans (hG' _ _ (orb_step (by simp) u)) (hst _)
  · exact hG' _ _ (orb_step (by simp) u)

theorem orb_le_split [Finite X] [DecidableEq X] {σ τ ρ σ' τ' : Equiv.Perm X} {a b : X}
    (hσ : ∀ x, σ x = σ' (Equiv.swap a b x)) (hτ : ∀ x, τ x = Equiv.swap a b (τ' x)) :
    orb {σ', τ', ρ} ≤ orb {σ, τ, ρ} + 1 := by
  have h1 := orb_cmp (T := join1 (orbSetoid {σ', τ', ρ}) a b)
    (le_join1 _ a b) (fun z => rel_swap (join1_edge _ a b) z) hσ hτ
  have h2 := ncs_le_of_le h1
  have h3 := ncs_le_join1 (orbSetoid {σ', τ', ρ}) a b
  unfold orb
  omega

theorem orb_le_merge [Finite X] [DecidableEq X] {σ τ ρ σ' τ' : Equiv.Perm X} {a b : X}
    (hab : (orbSetoid {σ', τ', ρ}) a b)
    (hσ : ∀ x, σ x = σ' (Equiv.swap a b x)) (hτ : ∀ x, τ x = Equiv.swap a b (τ' x)) :
    orb {σ', τ', ρ} ≤ orb {σ, τ, ρ} := by
  have h1 := orb_cmp (T := orbSetoid {σ', τ', ρ}) (fun x y h => h)
    (fun z => rel_swap hab z) hσ hτ
  exact ncs_le_of_le h1

theorem orb_le_card [Fintype X] (S : Set (Equiv.Perm X)) : orb S ≤ Fintype.card X := by
  have := ncs_le_card (orbSetoid S)
  rwa [Nat.card_eq_fintype_card] at this

/-- Caso base `σ = 1`. -/
theorem L1_base [Fintype X] (τ : Equiv.Perm X) :
    cyc (1 : Equiv.Perm X) + cyc τ + cyc τ⁻¹ ≤ Fintype.card X + 2 * orb {1, τ, τ⁻¹} := by
  have h1 : ∀ x y, (orbSetoid {1, τ, τ⁻¹}) x y → (cycSetoid τ) x y := by
    apply orbSetoid_le
    intro g hg u
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h <;> rw [h]
    · simp
    · exact cyc_step τ u
    · have h := cyc_step τ (τ⁻¹ u)
      have e : τ (τ⁻¹ u) = u := by simp
      rw [e] at h
      exact (cycSetoid τ).symm h
  have h2 := ncs_le_of_le h1
  have h3 := cyc_le_card (1 : Equiv.Perm X)
  rw [cyc_inv]
  unfold orb
  unfold cyc at *
  omega

/-- Caso `σ = 1` de L1. -/
theorem L1_of_fixed [Fintype X] (σ τ ρ : Equiv.Perm X) (h : ∀ x, σ x = x) (hprod : σ * τ * ρ = 1) :
    cyc σ + cyc τ + cyc ρ ≤ Fintype.card X + 2 * orb {σ, τ, ρ} := by
  have hσ : σ = 1 := Equiv.ext h
  subst hσ
  rw [one_mul] at hprod
  have hρ := eq_inv_of_mul_eq_one_right hprod
  subst hρ
  exact L1_base τ

/-- Lema L1 (tipo Riemann–Hurwitz), por induccion sobre `|X| - cyc σ`. -/
theorem L1_aux [Fintype X] (n : ℕ) : ∀ σ τ ρ : Equiv.Perm X, Fintype.card X - cyc σ ≤ n →
    σ * τ * ρ = 1 →
    cyc σ + cyc τ + cyc ρ ≤ Fintype.card X + 2 * orb {σ, τ, ρ} := by
  classical
  induction n with
  | zero =>
    intro σ τ ρ hn hprod
    by_cases h : ∃ x0, σ x0 ≠ x0
    · exfalso
      obtain ⟨x0, hx⟩ := h
      have h1 := cyc_lt_swap_mul σ x0 (σ x0) hx.symm (cyc_step σ x0)
      have h2 := cyc_le_card (Equiv.swap x0 (σ x0) * σ)
      omega
    · push Not at h
      exact L1_of_fixed σ τ ρ h hprod
  | succ n ih =>
    intro σ τ ρ hn hprod
    by_cases h : ∃ x0, σ x0 ≠ x0
    · obtain ⟨x0, hx⟩ := h
      obtain ⟨w, hw⟩ : ∃ w, w = σ⁻¹ x0 := ⟨_, rfl⟩
      have hσw : σ w = x0 := by simp [hw]
      have hwx : w ≠ x0 := by
        intro h'
        rw [h'] at hσw
        exact hx hσw
      obtain ⟨σ', hσ'⟩ : ∃ σ', σ' = Equiv.swap x0 (σ x0) * σ := ⟨_, rfl⟩
      obtain ⟨τ', hτ'⟩ : ∃ τ', τ' = Equiv.swap w x0 * τ := ⟨_, rfl⟩
      have hσt : ∀ y, σ (Equiv.swap w x0 y) = Equiv.swap x0 (σ x0) (σ y) := by
        intro y
        have := Equiv.mul_swap_eq_swap_mul σ w x0
        rw [hσw] at this
        exact DFunLike.congr_fun this y
      have hσ : ∀ x, σ x = σ' (Equiv.swap w x0 x) := by
        intro x
        rw [hσ', Equiv.Perm.mul_apply, hσt, Equiv.swap_apply_self]
      have hτ : ∀ x, τ x = Equiv.swap w x0 (τ' x) := by
        intro x
        rw [hτ', Equiv.Perm.mul_apply, Equiv.swap_apply_self]
      have hprod' : σ' * τ' * ρ = 1 := by
        rw [← hprod]
        congr 1
        ext x
        rw [hσ', hτ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply, hσt, Equiv.swap_apply_self]
      have h1 : cyc σ + 1 ≤ cyc σ' := by
        rw [hσ']
        exact cyc_lt_swap_mul σ x0 (σ x0) hx.symm (cyc_step σ x0)
      have h1' := cyc_le_card σ'
      have hih := ih σ' τ' ρ (by omega) hprod'
      by_cases hc : (cycSetoid τ) w x0
      · have h2 : cyc τ + 1 ≤ cyc τ' := by
          rw [hτ']
          exact cyc_lt_swap_mul τ w x0 hwx hc
        have h3 := orb_le_split (ρ := ρ) hσ hτ
        omega
      · have h2 : cyc τ ≤ cyc τ' + 1 := by
          rw [hτ']
          exact cyc_le_swap_mul τ w x0
        have h4 : (cycSetoid τ') w x0 := by
          rw [hτ']
          exact cyc_swap_connect τ w x0 hc
        have h5 : (orbSetoid {σ', τ', ρ}) w x0 := by
          refine eqvGen_le (s := orbSetoid {σ', τ', ρ}) ?_ h4
          intro u v huv
          subst huv
          exact orb_step (by simp) u
        have h3 := orb_le_merge (ρ := ρ) h5 hσ hτ
        omega
    · push Not at h
      exact L1_of_fixed σ τ ρ h hprod

/-- **Lema L1** (desigualdad de genero, tipo Riemann–Hurwitz): si `σ * τ * ρ = 1`, entonces
`cyc σ + cyc τ + cyc ρ ≤ |X| + 2 · (numero de orbitas de ⟨σ, τ, ρ⟩)`. -/
theorem L1 [Fintype X] (σ τ ρ : Equiv.Perm X) (h : σ * τ * ρ = 1) :
    cyc σ + cyc τ + cyc ρ ≤ Fintype.card X + 2 * orb {σ, τ, ρ} :=
  L1_aux _ σ τ ρ le_rfl h

/-- En el ciclo de una involucion `x`, los puntos son `z` o `x z`. -/
theorem cyc_invol (x : Equiv.Perm X) (hx : ∀ y, x (x y) = y) {z y : X}
    (h : (cycSetoid x) z y) : y = z ∨ y = x z := by
  induction h with
  | rel u v h => exact Or.inr h.symm
  | refl u => exact Or.inl rfl
  | symm u v _ ih =>
    rcases ih with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, hx])
  | trans u v w _ _ ih1 ih2 =>
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · exact Or.inl (h2.trans h1)
    · exact Or.inr (by rw [h2, h1])
    · exact Or.inr (h2.trans h1)
    · exact Or.inl (by rw [h2, h1, hx])

/-- Una involucion tiene al menos `|X| / 2` ciclos. -/
theorem card_le_two_cyc [Fintype X] (x : Equiv.Perm X) (hx : ∀ y, x (x y) = y) :
    Fintype.card X ≤ 2 * cyc x := by
  let F : Quotient (cycSetoid x) × Bool → X := fun cb =>
    if cb.2 then x cb.1.out else cb.1.out
  have hF : Function.Surjective F := by
    intro y
    have h := Quotient.mk_out (s := cycSetoid x) y
    rcases cyc_invol x hx ((cycSetoid x).symm h) with h' | h'
    · exact ⟨(Quotient.mk _ y, false), by simp [F, h']⟩
    · exact ⟨(Quotient.mk _ y, true), by simp [F, h', hx]⟩
  have := Nat.card_le_card_of_surjective _ hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Nat.card_eq_fintype_card (α := X)]
    at this
  unfold cyc ncs
  simp at this
  omega

/-- Cada orbita de `⟨ε, a, b⟩` se parte en a lo sumo dos de `⟨p, x, q⟩`. -/
theorem orb_le_two_mul [Finite X] (ε a b p x q : Equiv.Perm X) (hε : ∀ y, ε (ε y) = y)
    (ha : ∀ y, a (a y) = y) (hb : ∀ y, b (b y) = y) (hp : ∀ y, p y = ε (a y))
    (hx : ∀ y, x y = a (b y)) (hq : ∀ y, q y = b (ε y)) :
    orb {p, x, q} ≤ 2 * orb {ε, a, b} := by
  set H' := orbSetoid {p, x, q} with hH'
  have stp : ∀ u, H' u (p u) := fun u => orb_step (by simp) u
  have stx : ∀ u, H' u (x u) := fun u => orb_step (by simp) u
  have stq : ∀ u, H' u (q u) := fun u => orb_step (by simp) u
  -- invariancia bajo ε
  have hC : ∀ y z, H' y z →
      H' (ε y) (ε z) := by
    let T : Setoid X := ⟨fun y z => H' (ε y) (ε z),
      ⟨fun _ => H'.refl _, fun h => H'.symm h, fun h1 h2 => H'.trans h1 h2⟩⟩
    have key : ∀ y z, H' y z → T y z := by
      apply orbSetoid_le
      intro g hg u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h | h <;> rw [h]
      · -- g = p
        have e1 : ε (p u) = a u := by rw [hp, hε]
        have e2 : p (a u) = ε u := by rw [hp, ha]
        change H' (ε u) (ε (p u))
        rw [e1]
        have := stp (a u)
        rw [e2] at this
        exact H'.symm this
      · -- g = x
        change H' (ε u) (ε (x u))
        have e1 : q (ε u) = b u := by rw [hq, hε]
        have e2 : p (b u) = ε (x u) := by rw [hp, hx]
        have s1 := stq (ε u)
        have s2 := stp (b u)
        rw [e1] at s1
        rw [e2] at s2
        exact H'.trans s1 s2
      · -- g = q
        change H' (ε u) (ε (q u))
        have e : q (ε (q u)) = ε u := by rw [hq, hε, hq, hb]
        have := stq (ε (q u))
        rw [e] at this
        exact H'.symm this
    exact key
  -- fibras de tamano a lo sumo 2
  have hB : ∀ y z, (orbSetoid {ε, a, b}) y z →
      H' z y ∨ H' z (ε y) := by
    let R : Setoid X := ⟨fun y z => H' z y ∨ H' z (ε y),
      ⟨fun y => Or.inl (H'.refl _), ?_, ?_⟩⟩
    · exact orbSetoid_le (t := R) (by
        intro g hg u
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with h | h | h <;> rw [h]
        · exact Or.inr (H'.refl _)
        · have e : p (a u) = ε u := by rw [hp, ha]
          have := stp (a u)
          rw [e] at this
          exact Or.inr this
        · have e : q (ε u) = b u := by rw [hq, hε]
          have := stq (ε u)
          rw [e] at this
          exact Or.inr (H'.symm this))
    · intro y z h
      rcases h with h | h
      · exact Or.inl (H'.symm h)
      · refine Or.inr ?_
        have := hC _ _ h
        rw [hε] at this
        exact H'.symm this
    · intro y z w h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact Or.inl (H'.trans h2 h1)
      · exact Or.inr (by
          have := hC _ _ h1
          exact H'.trans h2 this)
      · exact Or.inr (H'.trans h2 h1)
      · exact Or.inl (by
          have := hC _ _ h1
          rw [hε] at this
          exact H'.trans h2 this)
  let F : Quotient (orbSetoid {ε, a, b}) × Bool → Quotient H' :=
    fun cb => Quotient.mk _ (if cb.2 then ε cb.1.out else cb.1.out)
  have hF : Function.Surjective F := by
    intro c
    induction c using Quotient.inductionOn with
    | _ z =>
      have h := Quotient.mk_out (s := orbSetoid {ε, a, b}) z
      rcases hB _ _ h with h' | h'
      · exact ⟨(Quotient.mk _ z, false), (Quotient.sound h').symm⟩
      · exact ⟨(Quotient.mk _ z, true), (Quotient.sound h').symm⟩
  have := Nat.card_le_card_of_surjective _ hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool)] at this
  simp only [Fintype.card_bool] at this
  have e : orb {p, x, q} = Nat.card (Quotient H') := rfl
  have e2 : orb {ε, a, b} = Nat.card (Quotient (orbSetoid {ε, a, b})) := rfl
  omega

theorem pt_of_mul_self (f : Equiv.Perm X) (h : f * f = 1) (y : X) : f (f y) = y := by
  simpa using DFunLike.congr_fun h y

/-- **Lema L2**: tres involuciones `ε, a, b` con `a ∘ b` involucion.  Con `p = ε a` y
`q = ε b`: `2 (cyc p + cyc q) ≤ |X| + 8 · orb ⟨ε, a, b⟩`.  (No hacen falta las hipotesis de
ausencia de puntos fijos de `ε`, `a`, `b`, ni de `a b`.) -/
theorem L2 [Fintype X] (ε a b : Equiv.Perm X) (hε : ε * ε = 1) (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) :
    2 * (cyc (ε * a) + cyc (ε * b)) ≤ Fintype.card X + 8 * orb {ε, a, b} := by
  have hprod : (ε * a) * (a * b) * (b * ε) = 1 := by
    calc (ε * a) * (a * b) * (b * ε) = ε * (a * a) * (b * b) * ε := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, mul_one, mul_one, hε]
  have hq : b * ε = (ε * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right hε]
  have h1 := L1 (ε * a) (a * b) (b * ε) hprod
  have h2 := orb_le_two_mul ε a b (ε * a) (a * b) (b * ε) (pt_of_mul_self ε hε)
    (pt_of_mul_self a ha) (pt_of_mul_self b hb) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have h3 := card_le_two_cyc (a * b) (pt_of_mul_self _ hab)
  have hc : cyc (b * ε) = cyc (ε * b) := by rw [hq, cyc_inv]
  rw [hc] at h1
  omega

/-- Version con las hipotesis completas del enunciado (involuciones sin puntos fijos). -/
theorem L2_fpf [Fintype X] (ε a b : Equiv.Perm X) (hε : ε * ε = 1) (_hε' : ∀ x, ε x ≠ x)
    (ha : a * a = 1) (_ha' : ∀ x, a x ≠ x) (hb : b * b = 1) (_hb' : ∀ x, b x ≠ x)
    (hab : (a * b) * (a * b) = 1) (_hab' : ∀ x, (a * b) x ≠ x) :
    2 * (cyc (ε * a) + cyc (ε * b)) ≤ Fintype.card X + 8 * orb {ε, a, b} :=
  L2 ε a b hε ha hb hab

/-- Corolario: si `⟨ε, a, b⟩` es transitivo, `cyc p + cyc q ≤ |X| / 2 + 4`. -/
theorem L2_conexo [Fintype X] (ε a b : Equiv.Perm X) (hε : ε * ε = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) * (a * b) = 1) (hk : orb {ε, a, b} = 1) :
    cyc (ε * a) + cyc (ε * b) ≤ Fintype.card X / 2 + 4 := by
  have := L2 ε a b hε ha hb hab
  rw [hk] at this
  omega

end Orbitas

section Puente

variable {X : Type*}

/-- Las orbitas de `orbSetoid S` son las del subgrupo generado por `S`. -/
theorem orbSetoid_eq (S : Set (Equiv.Perm X)) :
    orbSetoid S = MulAction.orbitRel (Subgroup.closure S) X := by
  ext x y
  constructor
  · intro h
    refine eqvGen_le (s := MulAction.orbitRel (Subgroup.closure S) X) ?_ h
    rintro u v ⟨g, hg, rfl⟩
    rw [MulAction.orbitRel_apply]
    exact ⟨⟨g⁻¹, inv_mem (Subgroup.subset_closure hg)⟩, by simp⟩
  · intro h
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨⟨g, hg⟩, hgy⟩ := h
    have key : ∀ g ∈ Subgroup.closure S, ∀ y, (orbSetoid S) y (g y) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg => exact fun y => orb_step hg y
      | one => exact fun y => (orbSetoid S).refl y
      | mul g h _ _ ihg ihh => exact fun y => (orbSetoid S).trans (ihh y) (ihg (h y))
      | inv g _ ih =>
        intro y
        have := ih (g⁻¹ y)
        rw [show g (g⁻¹ y) = y by simp] at this
        exact (orbSetoid S).symm this
    have := key g hg y
    have e : g y = x := by simpa using hgy
    rw [e] at this
    exact (orbSetoid S).symm this

/-- `orb S` es el cardinal del cociente `X / ⟨S⟩` de Mathlib. -/
theorem orb_eq_card_orbitRel (S : Set (Equiv.Perm X)) :
    orb S = Nat.card (MulAction.orbitRel.Quotient (Subgroup.closure S) X) := by
  unfold orb ncs
  rw [orbSetoid_eq]

theorem cycSetoid_eq_orbSetoid (π : Equiv.Perm X) : cycSetoid π = orbSetoid {π} := by
  have : (fun x y => π x = y) = edges {π} := by
    ext x y
    simp [edges]
  unfold cycSetoid orbSetoid
  rw [this]

/-- `cyc π = orb {π}`. -/
theorem cyc_eq_orb (π : Equiv.Perm X) : cyc π = orb {π} := by
  unfold cyc orb
  rw [cycSetoid_eq_orbSetoid]

/-- `cyc π` es el numero de orbitas de `zpowers π`, incluyendo puntos fijos. -/
theorem cyc_eq_card_zpowers (π : Equiv.Perm X) :
    cyc π = Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers π) X) := by
  rw [cyc_eq_orb, orb_eq_card_orbitRel, Subgroup.zpowers_eq_closure]

end Puente

section Computable

variable {X : Type*} [Fintype X] [LinearOrder X]

/-- Conteo computable de ciclos: un representante (el minimo) por ciclo. -/
def cycC (π : Equiv.Perm X) : ℕ :=
  (Finset.univ.filter (fun x => ∀ y, π.SameCycle y x → x ≤ y)).card

theorem cyc_eq_cycC (π : Equiv.Perm X) : cyc π = cycC π := by
  let M := {x : X // ∀ y, π.SameCycle y x → x ≤ y}
  let f : M → Quotient (cycSetoid π) := fun x => Quotient.mk _ x.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      have h1 : (cycSetoid π) x y := Quotient.exact h
      have h2 := (cycSetoid_iff π).1 h1
      have := le_antisymm (hx y h2.symm) (hy x h2)
      exact Subtype.ext this
    · intro c
      induction c using Quotient.inductionOn with
      | _ z =>
        let T := Finset.univ.filter (fun w => π.SameCycle w z)
        have hT : T.Nonempty := ⟨z, by simpa [T] using Equiv.Perm.SameCycle.refl π z⟩
        refine ⟨⟨T.min' hT, ?_⟩, ?_⟩
        · intro w hw
          apply Finset.min'_le
          have hy : π.SameCycle (T.min' hT) z := by
            have := T.min'_mem hT
            simpa [T] using this
          simpa [T] using hw.trans hy
        · apply Quotient.sound
          have hy : π.SameCycle (T.min' hT) z := by
            have := T.min'_mem hT
            simpa [T] using this
          exact (cycSetoid_iff π).2 hy
  have := Nat.card_eq_of_bijective f hf
  unfold cyc ncs cycC
  rw [← this, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [Fintype X] [LinearOrder X] in
/-- Certificado de transitividad: si cada `y` se alcanza desde `x0` por un camino de
generadores (`0 ↦ ε`, `1 ↦ a`, `2 ↦ b`), el grupo `⟨ε, a, b⟩` tiene una sola orbita. -/
theorem orb_eq_one_of_path [Finite X] (ε a b : Equiv.Perm X) (x0 : X)
    (path : X → List (Fin 3))
    (hend : ∀ y, (path y).foldr (fun i z => (![ε, a, b] i) z) x0 = y) :
    orb {ε, a, b} = 1 := by
  have key : ∀ l : List (Fin 3), ∀ z,
      (orbSetoid {ε, a, b}) z (l.foldr (fun i z => (![ε, a, b] i) z) z) := by
    intro l
    induction l with
    | nil => exact fun z => (orbSetoid {ε, a, b}).refl z
    | cons i l ih =>
      intro z
      have hg : (![ε, a, b] i) ∈ ({ε, a, b} : Set (Equiv.Perm X)) := by
        fin_cases i <;> simp
      have h1 := ih z
      have h2 := orb_step hg (l.foldr (fun i z => (![ε, a, b] i) z) z)
      exact (orbSetoid {ε, a, b}).trans h1 h2
  have hall : ∀ y, (orbSetoid {ε, a, b}) x0 y := by
    intro y
    have := key (path y) x0
    rwa [hend y] at this
  have hsub : Subsingleton (Quotient (orbSetoid {ε, a, b})) := by
    constructor
    intro p q
    induction p using Quotient.inductionOn with
    | _ y =>
      induction q using Quotient.inductionOn with
      | _ z =>
        exact Quotient.sound ((orbSetoid {ε, a, b}).trans ((orbSetoid {ε, a, b}).symm (hall y))
          (hall z))
  haveI : Nonempty (Quotient (orbSetoid {ε, a, b})) := ⟨Quotient.mk _ x0⟩
  have hpos : 0 < ncs (orbSetoid {ε, a, b}) := Nat.card_pos
  have hle : ncs (orbSetoid {ε, a, b}) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  unfold orb
  omega

end Computable

section Sanidad

open Equiv

/-- Dos cruces: `ε` empareja los extremos de las aristas, `a` y `b` son las suavizaciones. -/
def exEps : Perm (Fin 8) := swap 0 1 * swap 2 4 * swap 3 5 * swap 6 7
def exA : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
def exB : Perm (Fin 8) := swap 1 2 * swap 3 0 * swap 5 6 * swap 7 4

example : exEps * exEps = 1 := by decide
example : exA * exA = 1 := by decide
example : exB * exB = 1 := by decide
example : (exA * exB) * (exA * exB) = 1 := by decide
example : ∀ x, exEps x ≠ x := by decide
example : ∀ x, exA x ≠ x := by decide
example : ∀ x, exB x ≠ x := by decide
example : ∀ x, (exA * exB) x ≠ x := by decide

theorem ex_orb : orb {exEps, exA, exB} = 1 :=
  orb_eq_one_of_path exEps exA exB 0
    ![[], [0], [2, 0], [2], [0, 2, 0], [0, 2], [2, 0, 2], [2, 0, 2, 0]] (by decide)

theorem ex_cyc : cyc (exEps * exA) + cyc (exEps * exB) = 8 := by
  rw [cyc_eq_cycC, cyc_eq_cycC]
  decide

/-- Instancia concreta de L2 (y es justa: se da la igualdad). -/
example : 2 * (cyc (exEps * exA) + cyc (exEps * exB)) ≤
    Fintype.card (Fin 8) + 8 * orb {exEps, exA, exB} :=
  L2_fpf exEps exA exB (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : 2 * (cyc (exEps * exA) + cyc (exEps * exB)) =
    Fintype.card (Fin 8) + 8 * orb {exEps, exA, exB} := by
  rw [ex_orb, ex_cyc]
  decide

example : cyc (exEps * exA) + cyc (exEps * exB) ≤ Fintype.card (Fin 8) / 2 + 4 :=
  L2_conexo exEps exA exB (by decide) (by decide) (by decide) (by decide) ex_orb

/-- Instancia de L1 en `Fin 4` (genero 0: igualdad). -/
def exS : Perm (Fin 4) := swap 0 1 * swap 1 2 * swap 2 3
def exT : Perm (Fin 4) := swap 1 3 * swap 3 2
def exR : Perm (Fin 4) := swap 0 1

example : exS * exT * exR = 1 := by decide

theorem ex1_orb : orb {exS, exT, exR} = 1 :=
  orb_eq_one_of_path exS exT exR 0 ![[], [0], [0, 0], [1, 0]] (by decide)

example : cyc exS + cyc exT + cyc exR ≤ Fintype.card (Fin 4) + 2 * orb {exS, exT, exR} :=
  L1 exS exT exR (by decide)

example : cyc exS + cyc exT + cyc exR = Fintype.card (Fin 4) + 2 * orb {exS, exT, exR} := by
  rw [ex1_orb, cyc_eq_cycC, cyc_eq_cycC, cyc_eq_cycC]
  decide

end Sanidad

end SpanGenero
