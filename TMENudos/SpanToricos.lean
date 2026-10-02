import Mathlib
import TMENudos.SpanEntrelazado

/-!
# Etapa S7: minimalidad de los diagramas estandar de los nudos toricos `T(2,n)`, `n` impar

El diagrama es el de `n` diametros `(j, j + n)` de la circunferencia de `2n` puntos
(`ZMod (2n)`), alternando superior/inferior, con todos los signos `true`.
Se prueban las hipotesis de `minimal_alternante_planar_entrelazada` para todo `n` impar `>= 3`:
una curva, alternante, toda cuerda entrelazada y planar
(`orb {eps, a} = 2`, `orb {eps, b} = n`, suma `n + 2`).
-/

open SpanGenero TMENudos.Invariancia SpanPuente

namespace SpanToricos

variable {n : ℕ}

/-! ### Aritmetica en `ZMod (2n)` -/

instance [NeZero n] : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩

theorem natCast_inj {a b : ℕ} (ha : a < 2 * n) (hb : b < 2 * n) :
    ((a : ℕ) : ZMod (2 * n)) = (b : ZMod (2 * n)) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem val_natCast_lt {a : ℕ} (ha : a < 2 * n) : ((a : ZMod (2 * n))).val = a := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]

theorem val_add_par [NeZero n] (x y : ZMod (2 * n)) : (x + y).val % 2 = (x.val + y.val) % 2 := by
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 n)]

theorem val_one [NeZero n] (h : 2 ≤ n) : (1 : ZMod (2 * n)).val = 1 := by
  have := val_natCast_lt (n := n) (a := 1) (by omega)
  simpa using this

theorem val_n [NeZero n] (h : 1 ≤ n) : (n : ZMod (2 * n)).val = n := val_natCast_lt (by omega)

theorem two_n : (2 * n : ZMod (2 * n)) = 0 := by
  exact_mod_cast ZMod.natCast_self (2 * n)

theorem add_n_n (j : ZMod (2 * n)) : j + (n : ZMod (2 * n)) + (n : ZMod (2 * n)) = j := by
  rw [add_assoc, ← two_mul, two_n, add_zero]


/-! ### El diagrama -/

theorem ovr_add_n [NeZero n] (hn : Odd n) (j : ZMod (2 * n)) :
    decide ((j + (n : ZMod (2 * n))).val % 2 = 0) = !decide (j.val % 2 = 0) := by
  have h1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [val_add_par, val_n h1]
  obtain ⟨k, hk⟩ := hn
  by_cases h : j.val % 2 = 0 <;> simp [h] <;> omega

theorem ovr_add_one [NeZero n] (h2 : 2 ≤ n) (j : ZMod (2 * n)) :
    decide ((j + 1).val % 2 = 0) = !decide (j.val % 2 = 0) := by
  rw [val_add_par, val_one h2]
  by_cases h : j.val % 2 = 0 <;> simp [h] <;> omega

/-- El diagrama estandar de `T(2,n)`: `n` diametros `(j, j + n)` de `ZMod (2n)`. -/
def toroD (n : ℕ) [NeZero n] (hn : Odd n) : GDiag (ZMod (2 * n)) where
  next := Equiv.addRight 1
  partner j := j + (n : ZMod (2 * n))
  ovr j := decide (j.val % 2 = 0)
  sign _ := true
  partner_partner j := add_n_n j
  partner_ne j h := by
    have h1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    have h0 : (n : ZMod (2 * n)) = 0 := by simpa using h
    have := val_n h1
    rw [h0, ZMod.val_zero] at this
    omega
  ovr_partner j := ovr_add_n hn j
  sign_partner _ := rfl
  free := 0

variable [NeZero n] (hn : Odd n)

theorem toroD_next (j : ZMod (2 * n)) : (toroD n hn).next j = j + 1 := rfl

theorem toroD_partner (j : ZMod (2 * n)) : (toroD n hn).partner j = j + (n : ZMod (2 * n)) := rfl

theorem toroD_next_pow (t : ℕ) (p : ZMod (2 * n)) :
    ((toroD n hn).next ^ t) p = p + (t : ZMod (2 * n)) := by
  induction t generalizing p with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih p, toroD_next]
    push_cast; ring

theorem toroD_curve : ∀ i j : ZMod (2 * n), (toroD n hn).next.SameCycle i j := by
  intro i j
  refine ⟨((j - i).val : ℤ), ?_⟩
  rw [zpow_natCast, toroD_next_pow]
  simp

theorem toroD_alt (h2 : 2 ≤ n) : (toroD n hn).Alt := fun j => ovr_add_one h2 j

theorem toroD_nonempty : Nonempty (toroD n hn).Cross :=
  ⟨⟨0, by simp [toroD]⟩⟩

theorem toroD_card : Fintype.card (toroD n hn).Cross = n := by
  have h := (toroD n hn).card_letras
  rw [ZMod.card] at h
  omega


/-! ### Toda cuerda entrelazada -/

theorem toroD_ovr (j : ZMod (2 * n)) : (toroD n hn).ovr j = decide (j.val % 2 = 0) := rfl

/-- Arco de longitud 2 de `p` a `p + 2`, si `q` no es `p + 1` ni `p + 2`. -/
theorem arc_two (p q : ZMod (2 * n)) (h2 : 2 ≤ n) (h1 : p + (1 : ℕ) ≠ q)
    (h2' : p + (2 : ℕ) ≠ q) : (toroD n hn).Arc p q (p + (2 : ℕ)) := by
  refine ⟨2, by norm_num, toroD_next_pow hn 2 p, fun u hu hu2 => ?_⟩
  rw [toroD_next_pow]
  have hz : ∀ m : ℕ, 0 < m → m < 2 * n → p + (m : ZMod (2 * n)) ≠ p := by
    intro m hm hm2 h
    have : ((m : ℕ) : ZMod (2 * n)) = ((0 : ℕ) : ZMod (2 * n)) := by simpa using h
    have := (natCast_inj hm2 (by omega)).1 this
    omega
  interval_cases u
  · exact ⟨hz 1 (by omega) (by omega), h1⟩
  · exact ⟨hz 2 (by omega) (by omega), h2'⟩

theorem toroD_ovr_add_two (h2 : 2 ≤ n) (j : ZMod (2 * n)) :
    (toroD n hn).ovr (j + (2 : ℕ)) = (toroD n hn).ovr j := by
  have : j + (2 : ℕ) = j + 1 + 1 := by push_cast; ring
  rw [this, toroD_ovr, toroD_ovr, ovr_add_one h2, ovr_add_one h2]
  simp

theorem toroD_entrelazada (h3 : 3 ≤ n) : (toroD n hn).TodaEntrelazada := by
  intro x
  have hy : (toroD n hn).ovr (x.1 + (2 : ℕ)) = true := by
    rw [toroD_ovr_add_two hn (by omega)]; exact x.2
  refine ⟨⟨x.1 + (2 : ℕ), hy⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
  · intro h
    have h' : x.1 + (2 : ℕ) = x.1 := congrArg Subtype.val h
    have : ((2 : ℕ) : ZMod (2 * n)) = ((0 : ℕ) : ZMod (2 * n)) := by simpa using h'
    have := (natCast_inj (by omega) (by omega)).1 this
    omega
  · rw [toroD_partner]
    refine arc_two hn _ _ (by omega) ?_ ?_ <;> intro h
    · have h' : ((1 : ℕ) : ZMod (2 * n)) = (n : ZMod (2 * n)) := add_left_cancel h
      have := (natCast_inj (by omega) (by omega)).1 h'
      omega
    · have h' : ((2 : ℕ) : ZMod (2 * n)) = (n : ZMod (2 * n)) := add_left_cancel h
      have := (natCast_inj (by omega) (by omega)).1 h'
      omega
  · change (toroD n hn).Arc ((toroD n hn).partner x.1) x.1
      ((toroD n hn).partner (x.1 + (2 : ℕ)))
    rw [toroD_partner, toroD_partner]
    have e : x.1 + (2 : ℕ) + (n : ZMod (2 * n)) = (x.1 + (n : ZMod (2 * n))) + (2 : ℕ) := by
      ring
    rw [e]
    refine arc_two hn _ _ (by omega) ?_ ?_ <;> intro h
    · have h' : ((n + 1 : ℕ) : ZMod (2 * n)) = ((0 : ℕ) : ZMod (2 * n)) := by
        have : x.1 + (n : ZMod (2 * n)) + (1 : ℕ) = x.1 := h
        have h3 : x.1 + ((n + 1 : ℕ) : ZMod (2 * n)) = x.1 + 0 := by
          push_cast; rw [← add_assoc]; simpa using this
        simpa using add_left_cancel h3
      have := (natCast_inj (by omega) (by omega)).1 h'
      omega
    · have h' : ((n + 2 : ℕ) : ZMod (2 * n)) = ((0 : ℕ) : ZMod (2 * n)) := by
        have : x.1 + (n : ZMod (2 * n)) + (2 : ℕ) = x.1 := h
        have h3 : x.1 + ((n + 2 : ℕ) : ZMod (2 * n)) = x.1 + 0 := by
          push_cast; rw [← add_assoc]; simpa using this
        simpa using add_left_cancel h3
      have := (natCast_inj (by omega) (by omega)).1 h'
      omega


/-! ### Planaridad: conteo de orbitas -/

section Orbitas

/-- Si `f` es invariante, tiene una seccion `rep` y cada punto esta en la orbita de
`rep (f x)`, el numero de orbitas es el cardinal del codominio. -/
theorem orb_eq_card {X K : Type*} [Fintype K] (S : Set (Equiv.Perm X)) (f : X → K) (rep : K → X)
    (hf : ∀ g ∈ S, ∀ x, f (g x) = f x) (hr : ∀ k, f (rep k) = k)
    (hc : ∀ x, (orbSetoid S) x (rep (f x))) : orb S = Fintype.card K := by
  have hres : ∀ x y, (orbSetoid S) x y → f x = f y := fun x y h =>
    orbSetoid_le (t := Setoid.ker f) (fun g hg z => (hf g hg z).symm) x y h
  let e : Quotient (orbSetoid S) ≃ K :=
    { toFun := Quotient.lift f hres
      invFun := fun k => Quotient.mk _ (rep k)
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ x => exact (Quotient.sound ((orbSetoid S).symm (hc x)))
      right_inv := hr }
  unfold orb ncs
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]

theorem eps_inv_of_true (D : GDiag (ZMod (2 * n))) {K : Type*} (f : ZMod (2 * n) × Bool → K)
    (h : ∀ j, f (D.eps (j, true)) = f (j, true)) : ∀ x, f (D.eps x) = f x := by
  rintro ⟨j, s⟩
  cases s
  · rw [D.eps_false]
    have := h (D.prev j)
    rw [D.eps_true] at this
    have e : D.next (D.prev j) = j := by simp [GDiag.prev]
    rw [e] at this
    exact this.symm
  · exact h j

/-- Todo punto es equivalente por `eps` a uno con `s = true` con el mismo valor de `f`. -/
theorem exists_true (D : GDiag (ZMod (2 * n))) {K : Type*} (f : ZMod (2 * n) × Bool → K)
    (h : ∀ x, f (D.eps x) = f x) (x : ZMod (2 * n) × Bool) :
    ∃ k, (orbSetoid {D.eps, D.a}) x (k, true) ∧ (orbSetoid {D.eps, D.b}) x (k, true) ∧
      f x = f (k, true) := by
  obtain ⟨j, s⟩ := x
  cases s
  · refine ⟨D.prev j, ?_, ?_, ?_⟩
    · have := orb_step (S := {D.eps, D.a}) (g := D.eps) (by simp) (j, false)
      rwa [D.eps_false] at this
    · have := orb_step (S := {D.eps, D.b}) (g := D.eps) (by simp) (j, false)
      rwa [D.eps_false] at this
    · have := h (j, false)
      rw [D.eps_false] at this
      exact this.symm
  · exact ⟨j, (orbSetoid _).refl _, (orbSetoid _).refl _, rfl⟩

end Orbitas


theorem par_add_one (h2 : 2 ≤ n) (j : ZMod (2 * n)) : (j + 1).val % 2 = (j.val + 1) % 2 := by
  rw [val_add_par, val_one h2]

theorem par_add_n (j : ZMod (2 * n)) : (j + (n : ZMod (2 * n))).val % 2 = (j.val + n) % 2 := by
  have h1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [val_add_par, val_n h1]

/-- Invariante de `<eps, a>`: paridad de la letra, ajustada por el signo. -/
def fA (x : ZMod (2 * n) × Bool) : Bool := xor (decide (x.1.val % 2 = 1)) x.2

theorem fA_eps_true (h2 : 2 ≤ n) (j : ZMod (2 * n)) :
    fA ((toroD n hn).eps (j, true)) = fA (j, true) := by
  rw [(toroD n hn).eps_true, toroD_next]
  have := par_add_one h2 j
  unfold fA
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp [h] <;> omega

theorem fA_a (j : ZMod (2 * n)) (s : Bool) :
    fA ((toroD n hn).a (j, s)) = fA (j, s) := by
  rw [(toroD n hn).a_apply]
  have := par_add_n j
  unfold fA
  simp only [toroD_partner]
  have hn' := hn
  obtain ⟨k, hk⟩ := hn'
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> cases s <;>
    simp [toroD, h] <;> omega

theorem stepA (k : ZMod (2 * n)) :
    (orbSetoid {(toroD n hn).eps, (toroD n hn).a}) (k, true)
      (k + 1 + (n : ZMod (2 * n)), true) := by
  have h1 := orb_step (S := {(toroD n hn).eps, (toroD n hn).a}) (g := (toroD n hn).eps)
    (by simp) (k, true)
  have h2 := orb_step (S := {(toroD n hn).eps, (toroD n hn).a}) (g := (toroD n hn).a)
    (by simp) (k + 1, false)
  rw [(toroD n hn).eps_true, toroD_next] at h1
  rw [(toroD n hn).a_apply, toroD_partner] at h2
  exact (orbSetoid _).trans h1 h2

theorem stepA2 (k : ZMod (2 * n)) :
    (orbSetoid {(toroD n hn).eps, (toroD n hn).a}) (k, true) (k + 2, true) := by
  have h := (orbSetoid _).trans (stepA hn k) (stepA hn (k + 1 + n))
  have e : k + 1 + (n : ZMod (2 * n)) + 1 + (n : ZMod (2 * n)) = k + 2 := by
    have := two_n (n := n)
    linear_combination this
  rwa [e] at h


theorem stepA_m (k : ZMod (2 * n)) (m : ℕ) :
    (orbSetoid {(toroD n hn).eps, (toroD n hn).a}) (k, true)
      (k + 2 * (m : ZMod (2 * n)), true) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := (orbSetoid _).trans ih (stepA2 hn (k + 2 * (m : ZMod (2 * n))))
    have e : k + 2 * (m : ZMod (2 * n)) + 2 = k + 2 * ((m + 1 : ℕ) : ZMod (2 * n)) := by
      push_cast; ring
    rwa [e] at h

/-- Las orbitas de `<eps, a>` son exactamente 2. -/
theorem orb_A (h3 : 3 ≤ n) : orb {(toroD n hn).eps, (toroD n hn).a} = 2 := by
  have h2 : 2 ≤ n := by omega
  have hf : ∀ g ∈ ({(toroD n hn).eps, (toroD n hn).a} :
      Set (Equiv.Perm (ZMod (2 * n) × Bool))),
      ∀ x, fA (g x) = fA x := by
    intro g hg x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact eps_inv_of_true _ _ (fA_eps_true hn h2) x
    · exact fA_a hn x.1 x.2
  have key := orb_eq_card (K := Bool) {(toroD n hn).eps, (toroD n hn).a} fA
    (fun b => (if b then 0 else 1, true)) hf ?_ ?_
  · simpa using key
  · intro b
    cases b
    · simp [fA, val_one h2]
    · simp [fA]
  · intro x
    obtain ⟨k, hk, -, hfk⟩ :=
      exists_true (toroD n hn) fA (eps_inv_of_true _ _ (fA_eps_true hn h2)) x
    rw [hfk]
    refine (orbSetoid _).trans hk ?_
    have hk' : k = ((k.val % 2 : ℕ) : ZMod (2 * n)) + 2 * ((k.val / 2 : ℕ) : ZMod (2 * n)) := by
      have hv : (k.val : ZMod (2 * n)) = ((k.val % 2 + 2 * (k.val / 2) : ℕ) : ZMod (2 * n)) :=
        congrArg _ (Nat.mod_add_div k.val 2).symm
      rw [ZMod.natCast_zmod_val] at hv
      refine hv.trans ?_
      push_cast
      ring
    have hm := stepA_m hn ((k.val % 2 : ℕ) : ZMod (2 * n)) (k.val / 2)
    rw [← hk'] at hm
    refine (orbSetoid _).trans ((orbSetoid _).symm hm) ?_
    rcases Nat.mod_two_eq_zero_or_one k.val with h | h
    · simp [fA, h]
    · simp [fA, h]


/-- Reduccion modulo `n`. -/
def red (n : ℕ) : ZMod (2 * n) →+* ZMod n := ZMod.castHom (dvd_mul_left n 2) (ZMod n)

/-- Invariante de `<eps, b>`: clase modulo `n` de la letra, ajustada por el signo. -/
def fB (x : ZMod (2 * n) × Bool) : ZMod n := red n x.1 - (if x.2 then 0 else 1)

theorem fB_eps_true (hn : Odd n) (j : ZMod (2 * n)) :
    fB ((toroD n hn).eps (j, true)) = fB (j, true) := by
  rw [(toroD n hn).eps_true, toroD_next]
  simp [fB]

theorem fB_b (hn : Odd n) (j : ZMod (2 * n)) (s : Bool) :
    fB ((toroD n hn).b (j, s)) = fB (j, s) := by
  rw [(toroD n hn).b_apply, toroD_partner]
  cases s <;> simp [fB, toroD]

theorem stepB (hn : Odd n) (c : ZMod (2 * n)) :
    (orbSetoid {(toroD n hn).eps, (toroD n hn).b}) (c, true) (c + (n : ZMod (2 * n)), true) := by
  have h := orb_step (S := {(toroD n hn).eps, (toroD n hn).b}) (g := (toroD n hn).b)
    (by simp) (c, true)
  rw [(toroD n hn).b_apply, toroD_partner] at h
  simpa [toroD] using h

/-- Las orbitas de `<eps, b>` son exactamente `n`. -/
theorem orb_B (hn : Odd n) : orb {(toroD n hn).eps, (toroD n hn).b} = n := by
  have hf : ∀ g ∈ ({(toroD n hn).eps, (toroD n hn).b} :
      Set (Equiv.Perm (ZMod (2 * n) × Bool))),
      ∀ x, fB (g x) = fB x := by
    intro g hg x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact eps_inv_of_true _ _ (fB_eps_true hn) x
    · exact fB_b hn x.1 x.2
  have key := orb_eq_card (K := ZMod n) {(toroD n hn).eps, (toroD n hn).b} fB
    (fun k => (((k.val : ℕ) : ZMod (2 * n)), true)) hf ?_ ?_
  · simpa [ZMod.card] using key
  · intro k
    simp [fB, red]
  · intro x
    obtain ⟨k, -, hk, hfk⟩ :=
      exists_true (toroD n hn) fB (eps_inv_of_true _ _ (fB_eps_true hn)) x
    rw [hfk]
    refine (orbSetoid _).trans hk ?_
    -- (k, true) y su representante difieren en 0 o en n
    set c : ZMod (2 * n) := (((fB (k, true)).val : ℕ) : ZMod (2 * n)) with hc
    have hfk' : fB (k, true) = red n k := by simp [fB]
    have hm : red n k = ((k.val : ℕ) : ZMod n) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val k]
      rw [map_natCast]
    have hvl : k.val < 2 * n := ZMod.val_lt k
    have hcv : (fB (k, true)).val = k.val % n := by
      rw [hfk', hm, ZMod.val_natCast]
    by_cases hlt : k.val < n
    · have : c = k := by
        rw [hc, hcv, Nat.mod_eq_of_lt hlt, ZMod.natCast_zmod_val]
      change (orbSetoid _) (k, true) (c, true)
      rw [this]
    · have hkn : k = c + (n : ZMod (2 * n)) := by
        have e1 : k.val % n = k.val - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hc, hcv, e1]
        have : (k.val : ZMod (2 * n)) =
            ((k.val - n : ℕ) : ZMod (2 * n)) + (n : ZMod (2 * n)) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
        rw [ZMod.natCast_zmod_val] at this
        exact this
      have h := stepB hn c
      rw [← hkn] at h
      exact (orbSetoid _).symm h


/-- **Planaridad** del diagrama toroidal: caras `= n + 2` (`orb = 2` y `orb = n`). -/
theorem toroD_planar (h3 : 3 ≤ n) : (toroD n hn).PlanarD := by
  unfold GDiag.PlanarD
  rw [GDiag.caras_eq_of_alternante _ rfl (toroD_alt hn (by omega)),
    GDiag.lazos_allA_eq _ rfl, GDiag.lazos_allB_eq _ rfl, orb_A hn h3, orb_B hn, toroD_card]
  ring

end SpanToricos

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.Nudos SpanToricos

/-- **Minimalidad del diagrama estandar de `T(2,n)`**, `n` impar `>= 3`: cualquier diagrama
de una curva sin libres, `GRel`-equivalente, tiene al menos `n` cruces. -/
theorem toro_minimal (n : ℕ) [NeZero n] (hn : Odd n) (h3 : 3 ≤ n) (d' : Diag)
    (h : GRel (Diag.mk _ (toroD n hn)) d') (hf' : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) : n ≤ Fintype.card d'.D.Cross := by
  have := minimal_alternante_planar_entrelazada (Diag.mk _ (toroD n hn)) d' h rfl
    (toroD_curve hn) (toroD_alt hn (by omega)) (toroD_planar hn h3) (toroD_entrelazada hn h3)
    (toroD_nonempty hn) hf' hc
  rwa [show Fintype.card (Diag.mk _ (toroD n hn)).D.Cross = n from toroD_card hn] at this

end TMENudos.Puente

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.Nudos SpanToricos

/-- Sanidad `n = 3`: las cuerdas son `(0,3), (2,5), (4,1)` como en el trebol, 3 cruces. -/
theorem toroD3_cuerdas :
    (toroD 3 (by decide)).partner 0 = 3 ∧ (toroD 3 (by decide)).partner 2 = 5 ∧
      (toroD 3 (by decide)).partner 4 = 1 := by
  decide +kernel

/-- Minimalidad del trebol (`T(2,3)`) como caso `n = 3` de la familia. -/
theorem toro3_minimal (d' : Diag) (h : GRel (Diag.mk _ (toroD 3 (by decide))) d')
    (hf' : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    3 ≤ Fintype.card d'.D.Cross :=
  toro_minimal 3 (by decide) le_rfl d' h hf' hc

/-- Minimalidad de `5_1` (`T(2,5)`): caso `n = 5` de la familia. -/
theorem toro5_minimal (d' : Diag) (h : GRel (Diag.mk _ (toroD 5 (by decide))) d')
    (hf' : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    5 ≤ Fintype.card d'.D.Cross :=
  toro_minimal 5 (by decide) (by norm_num) d' h hf' hc

end TMENudos.Puente

#print axioms SpanToricos.toroD_curve
#print axioms SpanToricos.toroD_alt
#print axioms SpanToricos.toroD_card
#print axioms SpanToricos.toroD_entrelazada
#print axioms SpanToricos.orb_A
#print axioms SpanToricos.orb_B
#print axioms SpanToricos.toroD_planar
#print axioms TMENudos.Puente.toro_minimal
#print axioms TMENudos.Puente.toro3_minimal
#print axioms TMENudos.Puente.toro5_minimal
