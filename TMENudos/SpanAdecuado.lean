import Mathlib
import TMENudos.SpanLaurent
import TMENudos.SpanPuente

/-!
# Diagramas A- y B-adecuados y span exacto (etapa S5a)

Algebra y combinatoria generales sobre `GDiag`: si el diagrama es A-adecuado, el exponente
maximo del corchete se alcanza solo en el estado todo-A (coeficiente `(-1)^(s_A-1)`); analogo con
B-adecuado y el exponente minimo. De ahi el span exacto y el piloto del trebol.
-/

open LaurentPolynomial

namespace TMENudos.SpanLaurent

open TMENudos.Invariancia TMENudos.Nudos

section Defs

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Cambiar UNA suavizacion desde todo-A baja los lazos. -/
def AAdequate (D : GDiag ι) : Prop :=
  ∀ x : D.Cross, D.lazos (Function.update D.allA x false) < D.lazos D.allA

/-- Cambiar UNA suavizacion desde todo-B baja los lazos. -/
def BAdequate (D : GDiag ι) : Prop :=
  ∀ x : D.Cross, D.lazos (Function.update D.allB x true) < D.lazos D.allB

variable (D : GDiag ι)

theorem nB_update_true (σ : D.Cross → Bool) (x : D.Cross) (hx : σ x = false) :
    D.nB (Function.update σ x true) + 1 = D.nB σ := by
  unfold GDiag.nB
  have : (Finset.univ.filter fun y => Function.update σ x true y = false) =
      (Finset.univ.filter fun y => σ y = false).erase x := by
    ext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  rw [this]
  exact Finset.card_erase_add_one (by simpa using hx)

theorem nA_update_false (σ : D.Cross → Bool) (x : D.Cross) (hx : σ x = true) :
    D.nA (Function.update σ x false) + 1 = D.nA σ := by
  have h1 := D.nA_add_nB σ
  have h2 := D.nA_add_nB (Function.update σ x false)
  have h3 : D.nB (Function.update σ x false) = D.nB σ + 1 := by
    unfold GDiag.nB
    have : (Finset.univ.filter fun y => Function.update σ x false y = false) =
        insert x (Finset.univ.filter fun y => σ y = false) := by
      ext y
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy]
    rw [this, Finset.card_insert_of_notMem (by simp [hx])]
  omega

/-- Cota estricta para estados no extremos (desde todo-A). -/
theorem lazos_lt_of_AAdequate (hA : AAdequate D) :
    ∀ (n : ℕ) (σ : D.Cross → Bool), D.nB σ = n → 1 ≤ n →
      D.lazos σ + 1 ≤ D.lazos D.allA + D.nB σ := by
  intro n
  induction n with
  | zero => intro σ _ h; omega
  | succ n ih =>
    intro σ hn _
    have hex : ∃ x, σ x = false := by
      by_contra hcon
      have hc : ∀ x, σ x = true := fun x => by
        cases h : σ x
        · exact absurd ⟨x, h⟩ hcon
        · rfl
      have : D.nB σ = 0 := by
        unfold GDiag.nB
        simp [hc]
      omega
    obtain ⟨x, hx⟩ := hex
    have hd := nB_update_true D σ x hx
    have hs := D.lazos_le_succ (σ := σ) (σ' := Function.update σ x true) (x := x)
      (fun y hy => by simp [Function.update_of_ne hy])
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hone : D.nB (Function.update σ x true) = 0 := by omega
      have hσ : Function.update σ x true = D.allA := by
        funext y
        by_contra hy
        have hyf : Function.update σ x true y = false := by
          simpa [GDiag.allA] using hy
        have : 0 < D.nB (Function.update σ x true) :=
          Finset.card_pos.2 ⟨y, by simpa using hyf⟩
        omega
      have hσ2 : σ = Function.update D.allA x false := by
        funext y
        by_cases hy : y = x
        · subst hy; simp [hx]
        · have := congrFun hσ y
          simp only [Function.update_of_ne hy] at this
          simp [Function.update_of_ne hy, this]
      have := hA x
      rw [← hσ2] at this
      omega
    · have := ih (Function.update σ x true) (by omega) hpos
      omega

theorem lazos_lt_of_AAdequate' (hA : AAdequate D) (σ : D.Cross → Bool) (h : 1 ≤ D.nB σ) :
    D.lazos σ + 1 ≤ D.lazos D.allA + D.nB σ :=
  lazos_lt_of_AAdequate D hA _ σ rfl h

/-- Analogo para B-adecuado. -/
theorem lazos_lt_of_BAdequate (hB : BAdequate D) :
    ∀ (n : ℕ) (σ : D.Cross → Bool), D.nA σ = n → 1 ≤ n →
      D.lazos σ + 1 ≤ D.lazos D.allB + D.nA σ := by
  intro n
  induction n with
  | zero => intro σ _ h; omega
  | succ n ih =>
    intro σ hn _
    have hex : ∃ x, σ x = true := by
      by_contra hcon
      have hc : ∀ x, σ x = false := fun x => by
        cases h : σ x
        · rfl
        · exact absurd ⟨x, h⟩ hcon
      have : D.nA σ = 0 := by
        rw [D.nA_eq]
        simp [hc]
      omega
    obtain ⟨x, hx⟩ := hex
    have hd := nA_update_false D σ x hx
    have hs := D.lazos_le_succ (σ := σ) (σ' := Function.update σ x false) (x := x)
      (fun y hy => by simp [Function.update_of_ne hy])
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hone : D.nA (Function.update σ x false) = 0 := by omega
      have hσ : Function.update σ x false = D.allB := by
        funext y
        by_contra hy
        have hyf : Function.update σ x false y = true := by
          simpa [GDiag.allB] using hy
        have : 0 < D.nA (Function.update σ x false) := by
          rw [D.nA_eq]
          exact Finset.card_pos.2 ⟨y, by simpa using hyf⟩
        omega
      have hσ2 : σ = Function.update D.allB x true := by
        funext y
        by_cases hy : y = x
        · subst hy; simp [hx]
        · have := congrFun hσ y
          simp only [Function.update_of_ne hy] at this
          simp [Function.update_of_ne hy, this]
      have := hB x
      rw [← hσ2] at this
      omega
    · have := ih (Function.update σ x false) (by omega) hpos
      omega

theorem lazos_lt_of_BAdequate' (hB : BAdequate D) (σ : D.Cross → Bool) (h : 1 ≤ D.nA σ) :
    D.lazos σ + 1 ≤ D.lazos D.allB + D.nA σ :=
  lazos_lt_of_BAdequate D hB _ σ rfl h

end Defs

/-! ### Coeficientes extremos de `dL ^ m` -/

theorem coeff_mul_T (k : ℤ) (p : LaurentPolynomial ℤ) (n : ℤ) :
    (p * (T k : LaurentPolynomial ℤ)) n = p (n - k) := by
  rw [mul_comm]; exact coeff_T_mul k p n

theorem coeff_sub (p q : LaurentPolynomial ℤ) (n : ℤ) : (p - q) n = p n - q n :=
  Finsupp.sub_apply p q n

theorem coeff_add (p q : LaurentPolynomial ℤ) (n : ℤ) : (p + q) n = p n + q n :=
  Finsupp.add_apply p q n

theorem coeff_neg (p : LaurentPolynomial ℤ) (n : ℤ) : (-p) n = -p n :=
  Finsupp.neg_apply p n

theorem coeff_of_inBox {p : LaurentPolynomial ℤ} {lo hi : ℤ} (h : InBox p lo hi) {n : ℤ}
    (hn : n < lo ∨ hi < n) : p n = 0 := by
  by_contra hne
  have := h n (Finsupp.mem_support_iff.2 hne)
  omega

theorem coeff_dL_pow_top (m : ℕ) : ((dL ^ m : LaurentPolynomial ℤ)) (2 * m) = (-1) ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    rw [AddMonoidAlgebra.one_def]
    exact Finsupp.single_eq_same
  | succ m ih =>
    have e : (dL ^ (m + 1) : LaurentPolynomial ℤ) =
        -(dL ^ m * T 2) - dL ^ m * T (-2) := by
      rw [pow_succ]; unfold dL; ring
    rw [e]
    have h1 := coeff_mul_T 2 (dL ^ m) (2 * ((m + 1 : ℕ) : ℤ))
    have h2 := coeff_mul_T (-2) (dL ^ m) (2 * ((m + 1 : ℕ) : ℤ))
    have h3 : (dL ^ m : LaurentPolynomial ℤ) (2 * ((m + 1 : ℕ) : ℤ) - -2) = 0 :=
      coeff_of_inBox (inBox_dL_pow m) (Or.inr (by push_cast; omega))
    have h4 : 2 * ((m + 1 : ℕ) : ℤ) - 2 = 2 * (m : ℤ) := by push_cast; ring
    rw [h4] at h1
    rw [h3] at h2
    rw [coeff_sub, coeff_neg]
    rw [h1, h2, ih]
    ring

theorem coeff_dL_pow_bot (m : ℕ) : ((dL ^ m : LaurentPolynomial ℤ)) (-2 * m) = (-1) ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    rw [AddMonoidAlgebra.one_def]
    exact Finsupp.single_eq_same
  | succ m ih =>
    have e : (dL ^ (m + 1) : LaurentPolynomial ℤ) =
        -(dL ^ m * T 2) - dL ^ m * T (-2) := by
      rw [pow_succ]; unfold dL; ring
    rw [e]
    have h1 := coeff_mul_T 2 (dL ^ m) (-2 * ((m + 1 : ℕ) : ℤ))
    have h2 := coeff_mul_T (-2) (dL ^ m) (-2 * ((m + 1 : ℕ) : ℤ))
    have h3 : (dL ^ m : LaurentPolynomial ℤ) (-2 * ((m + 1 : ℕ) : ℤ) - 2) = 0 :=
      coeff_of_inBox (inBox_dL_pow m) (Or.inl (by push_cast; omega))
    have h4 : -2 * ((m + 1 : ℕ) : ℤ) - -2 = -2 * (m : ℤ) := by push_cast; ring
    rw [h4] at h2
    rw [h3] at h1
    rw [coeff_sub, coeff_neg]
    rw [h1, h2, ih]
    ring


/-! ### Exponente maximo y minimo -/

section Extremos

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

theorem eq_allA_of_nB_zero (σ : D.Cross → Bool) (h : D.nB σ = 0) : σ = D.allA := by
  funext y
  by_contra hy
  have hyf : σ y = false := by simpa [GDiag.allA] using hy
  have : 0 < D.nB σ := Finset.card_pos.2 ⟨y, by simpa using hyf⟩
  omega

theorem eq_allB_of_nA_zero (σ : D.Cross → Bool) (h : D.nA σ = 0) : σ = D.allB := by
  funext y
  by_contra hy
  have hyf : σ y = true := by simpa [GDiag.allB] using hy
  have : 0 < D.nA σ := by
    rw [D.nA_eq]
    exact Finset.card_pos.2 ⟨y, by simpa using hyf⟩
  omega

/-- Caja del termino del estado `σ`, con `expo` y `lazos` explicitos. -/
theorem inBox_term' (σ : D.Cross → Bool) (h : 1 ≤ D.lazos σ) :
    InBox ((∏ x : D.Cross, if σ x then (T 1 : LaurentPolynomial ℤ) else T (-1)) *
        dL ^ (D.lazos σ - 1))
      (D.expo σ - 2 * ((D.lazos σ : ℤ) - 1)) (D.expo σ + 2 * ((D.lazos σ : ℤ) - 1)) := by
  rw [prod_ite_T]
  have hm : (((D.lazos σ - 1 : ℕ)) : ℤ) = (D.lazos σ : ℤ) - 1 := by omega
  have h1 := (InBox.T (D.expo σ)).mul (inBox_dL_pow (D.lazos σ - 1))
  rw [hm] at h1
  exact h1.mono (by linarith) (by linarith)

/-- Coeficiente en el exponente maximo, para un diagrama A-adecuado. -/
theorem coeff_top (hA : AAdequate D) (hne : Nonempty D.Cross) :
    bracketL D ((Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2) =
      (-1) ^ (D.lazos D.allA - 1) := by
  have h1 := one_le_lazos D hne
  have hsplit : bracketL D = (∏ x : D.Cross, if D.allA x then (T 1 : LaurentPolynomial ℤ)
        else T (-1)) * dL ^ (D.lazos D.allA - 1) +
      ∑ σ ∈ Finset.univ.erase D.allA, (∏ x : D.Cross, if σ x then (T 1 : LaurentPolynomial ℤ)
        else T (-1)) * dL ^ (D.lazos σ - 1) := by
    unfold bracketL
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ D.allA)).symm
  have hrest : InBox (∑ σ ∈ Finset.univ.erase D.allA, (∏ x : D.Cross,
      if σ x then (T 1 : LaurentPolynomial ℤ) else T (-1)) * dL ^ (D.lazos σ - 1))
      (-(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2)
      ((Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 4) := by
    refine InBox.sum _ _ fun σ hσ => ?_
    have hσ' : σ ≠ D.allA := (Finset.mem_erase.1 hσ).1
    have hnB : 1 ≤ D.nB σ := by
      by_contra hc
      exact hσ' (eq_allA_of_nB_zero D σ (by omega))
    have hl := lazos_lt_of_AAdequate' D hA σ hnB
    have h2 := D.nA_add_nB σ
    have h3 := GDiag.expo_lower D σ
    have hσl := one_le_lazos D hne σ
    refine (inBox_term' D σ hσl).mono (by linarith) ?_
    unfold GDiag.expo
    omega
  have hz := coeff_of_inBox hrest (n := (Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2)
    (Or.inr (by omega))
  rw [hsplit, coeff_add, hz, add_zero,
    prod_ite_T, GDiag.expo_allA, coeff_T_mul]
  have hA1 := h1 D.allA
  have : (Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2 - (Fintype.card D.Cross : ℤ)
      = 2 * ((D.lazos D.allA - 1 : ℕ) : ℤ) := by omega
  rw [this, coeff_dL_pow_top]

/-- Coeficiente en el exponente minimo, para un diagrama B-adecuado. -/
theorem coeff_bot (hB : BAdequate D) (hne : Nonempty D.Cross) :
    bracketL D (-(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2) =
      (-1) ^ (D.lazos D.allB - 1) := by
  have h1 := one_le_lazos D hne
  have hsplit : bracketL D = (∏ x : D.Cross, if D.allB x then (T 1 : LaurentPolynomial ℤ)
        else T (-1)) * dL ^ (D.lazos D.allB - 1) +
      ∑ σ ∈ Finset.univ.erase D.allB, (∏ x : D.Cross, if σ x then (T 1 : LaurentPolynomial ℤ)
        else T (-1)) * dL ^ (D.lazos σ - 1) := by
    unfold bracketL
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ D.allB)).symm
  have hrest : InBox (∑ σ ∈ Finset.univ.erase D.allB, (∏ x : D.Cross,
      if σ x then (T 1 : LaurentPolynomial ℤ) else T (-1)) * dL ^ (D.lazos σ - 1))
      (-(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 4)
      ((Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2) := by
    refine InBox.sum _ _ fun σ hσ => ?_
    have hσ' : σ ≠ D.allB := (Finset.mem_erase.1 hσ).1
    have hnA : 1 ≤ D.nA σ := by
      by_contra hc
      exact hσ' (eq_allB_of_nA_zero D σ (by omega))
    have hl := lazos_lt_of_BAdequate' D hB σ hnA
    have h2 := D.nA_add_nB σ
    have h3 := GDiag.expo_upper D σ
    have hσl := one_le_lazos D hne σ
    refine (inBox_term' D σ hσl).mono ?_ (by linarith)
    unfold GDiag.expo
    omega
  have hz := coeff_of_inBox hrest
    (n := -(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2) (Or.inl (by omega))
  rw [hsplit, coeff_add, hz, add_zero,
    prod_ite_T, GDiag.expo_allB, coeff_T_mul]
  have hB1 := h1 D.allB
  have : -(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2 -
      (-(Fintype.card D.Cross : ℤ)) = -2 * ((D.lazos D.allB - 1 : ℕ) : ℤ) := by omega
  rw [this, coeff_dL_pow_bot]

end Extremos

theorem maxExp_eq {p : LaurentPolynomial ℤ} {lo N : ℤ} (hbox : InBox p lo N) (hc : p N ≠ 0) :
    maxExp p = N := by
  have hmem : N ∈ p.support := Finsupp.mem_support_iff.2 hc
  have hp : p.support.Nonempty := ⟨N, hmem⟩
  unfold maxExp
  rw [dif_pos hp]
  exact le_antisymm (Finset.max'_le _ _ _ fun n hn => (hbox n hn).2) (Finset.le_max' _ _ hmem)

theorem minExp_eq {p : LaurentPolynomial ℤ} {M hi : ℤ} (hbox : InBox p M hi) (hc : p M ≠ 0) :
    minExp p = M := by
  have hmem : M ∈ p.support := Finsupp.mem_support_iff.2 hc
  have hp : p.support.Nonempty := ⟨M, hmem⟩
  unfold minExp
  rw [dif_pos hp]
  exact le_antisymm (Finset.min'_le _ _ hmem) (Finset.le_min' _ _ _ fun n hn => (hbox n hn).1)

theorem neg_one_pow_ne_zero (n : ℕ) : ((-1 : ℤ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)

section Final

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Exponente maximo exacto de un diagrama A-adecuado. -/
theorem maxExp_bracketL (hA : AAdequate D) (hne : Nonempty D.Cross) :
    maxExp (bracketL D) = (Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2 :=
  maxExp_eq (lo := -(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2)
    (inBox_bracketL D (one_le_lazos D hne))
    (by rw [coeff_top D hA hne]; exact neg_one_pow_ne_zero _)

/-- Exponente minimo exacto de un diagrama B-adecuado. -/
theorem minExp_bracketL (hB : BAdequate D) (hne : Nonempty D.Cross) :
    minExp (bracketL D) = -(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2 :=
  minExp_eq (hi := (Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2)
    (inBox_bracketL D (one_le_lazos D hne))
    (by rw [coeff_bot D hB hne]; exact neg_one_pow_ne_zero _)

/-- **Span exacto** de un diagrama A- y B-adecuado con algun cruce. -/
theorem span_bracketL_eq (hA : AAdequate D) (hB : BAdequate D) (hne : Nonempty D.Cross) :
    (span (bracketL D) : ℤ) =
      2 * (Fintype.card D.Cross : ℤ) + 2 * ((D.lazos D.allA : ℤ) + D.lazos D.allB) - 4 := by
  have h1 := maxExp_bracketL D hA hne
  have h2 := minExp_bracketL D hB hne
  have hA1 := one_le_lazos D hne D.allA
  have hB1 := one_le_lazos D hne D.allB
  have hc : 0 < Fintype.card D.Cross := Fintype.card_pos_iff.2 hne
  unfold span
  rw [h1, h2, Int.toNat_of_nonneg (by omega)]
  ring

/-- Corolario con la igualdad de genero `s_A + s_B = c + 2`: `span = 4c`. -/
theorem span_bracketL_eq_four_mul (hA : AAdequate D) (hB : BAdequate D)
    (hne : Nonempty D.Cross)
    (hgen : D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2) :
    span (bracketL D) = 4 * Fintype.card D.Cross := by
  have := span_bracketL_eq D hA hB hne
  omega

end Final

end TMENudos.SpanLaurent

/-! ### Caso sin cruces -/

namespace TMENudos.SpanLaurent

open TMENudos.Invariancia

theorem span_le_of_inBox {p : LaurentPolynomial ℤ} {lo hi : ℤ} (hlh : lo ≤ hi)
    (h : InBox p lo hi) : (span p : ℤ) ≤ hi - lo := by
  unfold span maxExp minExp
  by_cases hp : p.support.Nonempty
  · rw [dif_pos hp, dif_pos hp]
    have h1 := h _ (Finset.max'_mem _ hp)
    have h2 := h _ (Finset.min'_mem _ hp)
    omega
  · rw [dif_neg hp, dif_neg hp]
    simp only [sub_self, Int.toNat_zero, Nat.cast_zero]
    omega

section Vacio

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Sin cruces no hay letras. -/
theorem isEmpty_of_isEmpty_cross (D : GDiag ι) (h : IsEmpty D.Cross) : IsEmpty ι := by
  refine ⟨fun i => ?_⟩
  cases hi : D.ovr i
  · have := D.ovr_partner i
    rw [hi] at this
    exact h.false ⟨D.partner i, by simpa using this⟩
  · exact h.false ⟨i, hi⟩

/-- Sin cruces y sin circunferencias libres, el corchete vale `1`. -/
theorem bracketL_of_isEmpty (D : GDiag ι) (h : IsEmpty D.Cross) (hf : D.free = 0) :
    bracketL D = 1 := by
  haveI := isEmpty_of_isEmpty_cross D h
  haveI : Unique (D.Cross → Bool) := Pi.uniqueOfIsEmpty _
  have hl : ∀ σ : D.Cross → Bool, D.lazos σ = 0 := by
    intro σ
    unfold GDiag.lazos
    rw [hf]
    haveI : IsEmpty (D.graph σ).ConnectedComponent :=
      ⟨fun c => c.ind (fun v => isEmptyElim v)⟩
    simp
  unfold bracketL
  simp [hl]

/-- Sin cruces, el span del corchete es `0`. -/
theorem span_bracketL_of_isEmpty (D : GDiag ι) (h : IsEmpty D.Cross) (hf : D.free = 0) :
    span (bracketL D) = 0 := by
  rw [bracketL_of_isEmpty D h hf]
  have h1 : InBox (1 : LaurentPolynomial ℤ) 0 0 := by
    have := InBox.T 0
    rwa [T_zero] at this
  have := span_le_of_inBox le_rfl h1
  omega

end Vacio

end TMENudos.SpanLaurent

/-! ### Piloto: el trebol -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.SpanLaurent

theorem trefoil_A_single :
    ∀ i : Fin (Word.crossings trefoil).length,
      Word.loops trefoil (List.ofFn (Function.update (fun _ => true) i false)) < 2 := by
  decide +kernel

theorem trefoil_B_single :
    ∀ i : Fin (Word.crossings trefoil).length,
      Word.loops trefoil (List.ofFn (Function.update (fun _ => false) i true)) < 3 := by
  decide +kernel

theorem trefoil_AAdequate : AAdequate (ofWord trefoil wf_trefoil) := by
  have hw := wfP_of_wf trefoil wf_trefoil
  change AAdequate (ofWordP trefoil hw)
  intro x
  obtain ⟨-, h2, -⟩ := sanidad_trefoil
  have hk := trefoil_A_single (crossEquiv trefoil hw x)
  rw [loops_eq hw] at hk
  have hfun : (fun y => Function.update (fun _ => true) (crossEquiv trefoil hw x) false
      (crossEquiv trefoil hw y)) = Function.update (ofWordP trefoil hw).allA x false := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · have : crossEquiv trefoil hw y ≠ crossEquiv trefoil hw x :=
        fun h => hy ((crossEquiv trefoil hw).injective h)
      simp [Function.update_of_ne hy, Function.update_of_ne this, GDiag.allA]
  rw [hfun] at hk
  change (ofWordP trefoil hw).lazos (ofWordP trefoil hw).allA = 2 at h2
  omega

theorem trefoil_BAdequate : BAdequate (ofWord trefoil wf_trefoil) := by
  have hw := wfP_of_wf trefoil wf_trefoil
  change BAdequate (ofWordP trefoil hw)
  intro x
  obtain ⟨-, -, h3⟩ := sanidad_trefoil
  have hk := trefoil_B_single (crossEquiv trefoil hw x)
  rw [loops_eq hw] at hk
  have hfun : (fun y => Function.update (fun _ => false) (crossEquiv trefoil hw x) true
      (crossEquiv trefoil hw y)) = Function.update (ofWordP trefoil hw).allB x true := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · have : crossEquiv trefoil hw y ≠ crossEquiv trefoil hw x :=
        fun h => hy ((crossEquiv trefoil hw).injective h)
      simp [Function.update_of_ne hy, Function.update_of_ne this, GDiag.allB]
  rw [hfun] at hk
  change (ofWordP trefoil hw).lazos (ofWordP trefoil hw).allB = 3 at h3
  omega

/-- **Span del trebol**: `span ⟨trebol⟩ = 12`. -/
theorem span_trefoil_eq :
    span (bracketL (ofWord trefoil wf_trefoil)) = 12 := by
  obtain ⟨h1, h2, h3⟩ := sanidad_trefoil
  have hne : Nonempty (ofWord trefoil wf_trefoil).Cross := by
    rw [← Fintype.card_pos_iff, h1]; norm_num
  have := span_bracketL_eq _ trefoil_AAdequate trefoil_BAdequate hne
  rw [h1, h2, h3] at this
  omega

end TMENudos.Puente

#print axioms TMENudos.SpanLaurent.span_bracketL_of_isEmpty
#print axioms TMENudos.Puente.trefoil_AAdequate
#print axioms TMENudos.Puente.trefoil_BAdequate
#print axioms TMENudos.Puente.span_trefoil_eq

/-! ### Minimalidad del trebol (version condicionada a la desigualdad de genero) -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.SpanLaurent TMENudos.Nudos

/-- Todo diagrama sin circunferencias libres equivalente por `GRel` al trebol y que cumple la
desigualdad de genero `s_A + s_B <= c + 2` tiene al menos 3 cruces. -/
theorem trefoil_minimal_of_genero (d' : Diag)
    (h : GRel (Diag.mk _ (ofWord trefoil wf_trefoil)) d') (hf : d'.D.free = 0)
    (hgen : d'.D.lazos d'.D.allA + d'.D.lazos d'.D.allB ≤ Fintype.card d'.D.Cross + 2) :
    3 ≤ Fintype.card d'.D.Cross := by
  have h12 : span (bracketL d'.D) = 12 := by
    rw [← span_bracketL_rel h]; exact span_trefoil_eq
  by_cases hne : Nonempty d'.D.Cross
  · have := span_bracketL_le_of_nonempty d'.D hne
    omega
  · rw [not_nonempty_iff] at hne
    have := span_bracketL_of_isEmpty d'.D hne hf
    omega

/-- **Teorema piloto de minimalidad**: todo diagrama de UNA curva, sin circunferencias libres,
equivalente por `GRel` al trebol, tiene al menos 3 cruces (el numero de cruces del trebol es 3).
La cota inferior sale del span del corchete: `span = 12` (invariante por `GRel`, `span_trefoil_eq`)
y `span <= 4 c'` (`span_bracketL_le_of_nonempty` mas la desigualdad de genero de `SpanPuente`). -/
theorem trefoil_minimal (d' : Diag)
    (h : GRel (Diag.mk _ (ofWord trefoil wf_trefoil)) d') (hf : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) : 3 ≤ Fintype.card d'.D.Cross := by
  have h12 : span (bracketL d'.D) = 12 := by
    rw [← span_bracketL_rel h]; exact span_trefoil_eq
  by_cases hne : Nonempty d'.D.Cross
  · exact trefoil_minimal_of_genero d' h hf (GDiag.lazos_allA_add_allB_le d'.D hf hc hne)
  · rw [not_nonempty_iff] at hne
    have := span_bracketL_of_isEmpty d'.D hne hf
    omega

end TMENudos.Puente

#print axioms TMENudos.Puente.trefoil_minimal_of_genero
#print axioms TMENudos.Puente.trefoil_minimal
