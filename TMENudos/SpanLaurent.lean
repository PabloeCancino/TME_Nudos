import Mathlib
import TMENudos.SpanEstados
import TMENudos.Etapa1_Nudos

/-!
# Corchete como polinomio de Laurent y span (etapa S1)

`bracketL D : ℤ[T;T⁻¹]` es la suma de estados con `A = T`. Se evalua en cuerpos con
`LaurentPolynomial.eval₂`, y la evaluacion en todos los racionales no nulos determina el
polinomio. De ahi: el Jones polinomial es invariante por `GRel`, y el `span` del corchete tambien.
-/

open LaurentPolynomial

namespace TMENudos.SpanLaurent

open TMENudos.Invariancia TMENudos.Nudos

section Defs

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- El valor `d = -A² - A⁻²` como polinomio de Laurent. -/
noncomputable def dL : LaurentPolynomial ℤ := -(T 2) - T (-2)

/-- Corchete de Kauffman como polinomio de Laurent (`A = T`). -/
noncomputable def bracketL (D : GDiag ι) : LaurentPolynomial ℤ :=
  ∑ σ : D.Cross → Bool, (∏ x : D.Cross, if σ x then (T 1 : LaurentPolynomial ℤ) else T (-1)) *
    dL ^ (D.lazos σ - 1)

/-- Jones como polinomio de Laurent: `(-1)^|w| · T^(-3w) · ⟨D⟩`. -/
noncomputable def jonesL (D : GDiag ι) : LaurentPolynomial ℤ :=
  (-1) ^ D.writhe.natAbs * T (-3 * D.writhe) * bracketL D

/-- Evaluacion `T ↦ a`. -/
noncomputable def evalL {K : Type*} [Field K] (a : Kˣ) : LaurentPolynomial ℤ →+* K :=
  LaurentPolynomial.eval₂ (Int.castRingHom K) a

variable {K : Type*} [Field K]

theorem evalL_T (a : Kˣ) (n : ℤ) : evalL a (T n) = (a : K) ^ n := by
  simp [evalL]

theorem evalL_dL (a : Kˣ) : evalL a dL = -((a : K) ^ 2) - (a : K)⁻¹ ^ 2 := by
  simp [dL, evalL_T, zpow_neg, inv_pow, zpow_ofNat]

theorem evalL_bracketL (a : Kˣ) {D : GDiag ι} : evalL a (bracketL D) = D.bracket (a : K) := by
  unfold bracketL GDiag.bracket
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_prod, map_pow, evalL_dL]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs <;> simp [evalL_T, zpow_neg]

theorem neg_pow_zpow_aux (x : K) (w : ℤ) :
    (-(x ^ 3)) ^ (-w) = (-1) ^ w.natAbs * x ^ (-3 * w) := by
  have key : ∀ n : ℕ, (-(x ^ 3)) ^ n = (-1) ^ n * x ^ (3 * (n : ℤ)) := by
    intro n
    rw [neg_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]
    simp [mul_comm]
  have hu : ∀ n : ℕ, ((-1 : K) ^ n)⁻¹ = (-1) ^ n := by
    intro n
    rcases neg_one_pow_eq_or K n with h | h <;> simp [h]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rw [zpow_neg, zpow_natCast, key, mul_inv, hu]
    simp [← zpow_neg, neg_mul]
  · rw [neg_neg, zpow_natCast, key]
    simp

theorem evalL_jonesL (a : Kˣ) {D : GDiag ι} : evalL a (jonesL D) = D.jones (a : K) := by
  unfold jonesL GDiag.jones
  rw [map_mul, map_mul, map_pow, map_neg, map_one, evalL_T, evalL_bracketL,
    neg_pow_zpow_aux (a : K), mul_assoc]

end Defs

/-! ### Inyectividad de la evaluacion en los racionales -/

/-- Un polinomio de Laurent entero que se anula en todos los racionales no nulos es cero. -/
theorem eq_zero_of_evalL (p : LaurentPolynomial ℤ)
    (h : ∀ a : ℚˣ, evalL a p = 0) : p = 0 := by
  obtain ⟨n, f, hf⟩ := p.exists_T_pow
  have hf0 : f = 0 := by
    have hz : (f.map (Int.castRingHom ℚ)) = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
      have hsub : {x : ℚ | x ≠ 0} ⊆ {x : ℚ | (f.map (Int.castRingHom ℚ)).IsRoot x} := by
        intro x hx
        have h1 := h (Units.mk0 x hx)
        have h2 : evalL (Units.mk0 x hx) (f.toLaurent) = 0 := by
          rw [hf, map_mul, h1, zero_mul]
        simp only [evalL, eval₂_toLaurent] at h2
        simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_map]
        simpa using h2
      refine Set.Infinite.mono hsub ?_
      have : {x : ℚ | x ≠ 0} = {0}ᶜ := by ext; simp
      rw [this]
      exact (Set.finite_singleton (0 : ℚ)).infinite_compl
    exact Polynomial.map_injective _ (RingHom.injective_int _) (by simpa using hz)
  rw [hf0, map_zero] at hf
  exact (isUnit_T (n : ℤ)).mul_left_eq_zero.1 hf.symm

theorem evalL_injective {p q : LaurentPolynomial ℤ}
    (h : ∀ a : ℚˣ, evalL a p = evalL a q) : p = q :=
  sub_eq_zero.1 (eq_zero_of_evalL _ fun a => by rw [map_sub, h a, sub_self])

/-! ### Invariancia polinomial -/

section Invariancia

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- El Jones polinomial es invariante por `GRel`. -/
theorem jonesL_rel {d d' : Diag} (h : GRel d d') : jonesL d.D = jonesL d'.D := by
  refine evalL_injective fun a => ?_
  rw [evalL_jonesL, evalL_jonesL]
  exact jones_rel (K := ℚ) (A := (a : ℚ)) a.ne_zero h

theorem bracketL_eq_jonesL (D : GDiag ι) :
    bracketL D = (-1) ^ D.writhe.natAbs * T (3 * D.writhe) * jonesL D := by
  unfold jonesL
  have h1 : ((-1 : LaurentPolynomial ℤ) ^ D.writhe.natAbs) * (-1) ^ D.writhe.natAbs = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have h2 : (T (3 * D.writhe) : LaurentPolynomial ℤ) * T (-3 * D.writhe) = 1 := by
    rw [← T_add]; simp
  calc bracketL D = ((-1) ^ D.writhe.natAbs * (-1) ^ D.writhe.natAbs) *
        (T (3 * D.writhe) * T (-3 * D.writhe)) * bracketL D := by rw [h1, h2]; simp
    _ = _ := by ring

theorem neg_one_pow_or (n : ℕ) :
    (-1 : LaurentPolynomial ℤ) ^ n = 1 ∨ (-1 : LaurentPolynomial ℤ) ^ n = -1 :=
  neg_one_pow_eq_or _ n

/-- Dos diagramas relacionados tienen corchetes que difieren en `± T^k`. -/
theorem bracketL_rel {d d' : Diag} (h : GRel d d') :
    ∃ (s : LaurentPolynomial ℤ) (k : ℤ), (s = 1 ∨ s = -1) ∧
      bracketL d'.D = s * T k * bracketL d.D := by
  have hj := jonesL_rel h
  refine ⟨(-1) ^ d'.D.writhe.natAbs * (-1) ^ d.D.writhe.natAbs, 3 * d'.D.writhe - 3 * d.D.writhe,
    ?_, ?_⟩
  · rcases neg_one_pow_or d'.D.writhe.natAbs with h1 | h1 <;>
      rcases neg_one_pow_or d.D.writhe.natAbs with h2 | h2 <;> simp [h1, h2]
  · rw [bracketL_eq_jonesL d'.D, ← hj]
    unfold jonesL
    rw [T_sub, show -3 * d.D.writhe = -(3 * d.D.writhe) by ring]
    ring

end Invariancia

/-! ### Span -/

section Span

/-- Mayor exponente del soporte (`0` si el polinomio es nulo). -/
noncomputable def maxExp (p : LaurentPolynomial ℤ) : ℤ :=
  if h : p.support.Nonempty then p.support.max' h else 0

/-- Menor exponente del soporte (`0` si el polinomio es nulo). -/
noncomputable def minExp (p : LaurentPolynomial ℤ) : ℤ :=
  if h : p.support.Nonempty then p.support.min' h else 0

/-- Span: diferencia entre el mayor y el menor exponente (`0` si `p = 0`). -/
noncomputable def span (p : LaurentPolynomial ℤ) : ℕ := (maxExp p - minExp p).toNat

theorem span_zero : span 0 = 0 := by
  have h : (0 : LaurentPolynomial ℤ).support = ∅ := rfl
  simp [span, maxExp, minExp, h]

theorem coeff_T_mul (k : ℤ) (p : LaurentPolynomial ℤ) (n : ℤ) :
    ((T k : LaurentPolynomial ℤ) * p) n = p (n - k) := by
  have : (T k : LaurentPolynomial ℤ) = AddMonoidAlgebra.single k 1 := rfl
  rw [this, AddMonoidAlgebra.single_mul_apply]
  simp [sub_eq_add_neg, add_comm]

theorem support_T_mul (k : ℤ) (p : LaurentPolynomial ℤ) :
    (T k * p).support = p.support.image (· + k) := by
  ext n
  simp only [Finsupp.mem_support_iff, Finset.mem_image]
  rw [coeff_T_mul]
  constructor
  · intro h; exact ⟨n - k, h, by ring⟩
  · rintro ⟨m, hm, rfl⟩; simpa using hm

theorem support_neg' (p : LaurentPolynomial ℤ) : (-p).support = p.support := by
  ext n; simp [Finsupp.mem_support_iff]

theorem span_T_mul (k : ℤ) (p : LaurentPolynomial ℤ) : span (T k * p) = span p := by
  by_cases hp : p.support.Nonempty
  · have hq : (T k * p).support.Nonempty := by
      rw [support_T_mul]; exact hp.image _
    unfold span maxExp minExp
    rw [dif_pos hp, dif_pos hp, dif_pos hq, dif_pos hq]
    simp only [support_T_mul]
    rw [Finset.max'_image (f := (· + k)) (fun a b h => by simpa using h),
      Finset.min'_image (f := (· + k)) (fun a b h => by simpa using h)]
    congr 1; ring
  · have : p.support = ∅ := Finset.not_nonempty_iff_eq_empty.1 hp
    have hp0 : p = 0 := Finsupp.support_eq_empty.1 this
    subst hp0; simp [span_zero]

theorem span_neg (q : LaurentPolynomial ℤ) : span (-q) = span q := by
  unfold span maxExp minExp
  simp only [support_neg']

theorem span_unit_mul (s : LaurentPolynomial ℤ) (hs : s = 1 ∨ s = -1) (k : ℤ)
    (p : LaurentPolynomial ℤ) : span (s * T k * p) = span p := by
  rcases hs with rfl | rfl
  · rw [one_mul, span_T_mul]
  · have : -1 * T k * p = -(T k * p) := by ring
    rw [this, span_neg, span_T_mul]

/-- El span del corchete es invariante por `GRel`. -/
theorem span_bracketL_rel {d d' : Diag} (h : GRel d d') :
    span (bracketL d.D) = span (bracketL d'.D) := by
  obtain ⟨s, k, hs, he⟩ := bracketL_rel h
  rw [he, span_unit_mul s hs k]

end Span

/-! ### Cota por estados en el polinomio -/

section Cota

/-- Todos los exponentes del soporte de `p` estan en `[lo, hi]`. -/
def InBox (p : LaurentPolynomial ℤ) (lo hi : ℤ) : Prop := ∀ n ∈ p.support, lo ≤ n ∧ n ≤ hi

theorem InBox.zero (lo hi : ℤ) : InBox 0 lo hi := by
  intro n hn
  have h : (0 : LaurentPolynomial ℤ).support = ∅ := rfl
  rw [h] at hn; simp at hn

theorem InBox.add {p q : LaurentPolynomial ℤ} {lo hi : ℤ} (hp : InBox p lo hi)
    (hq : InBox q lo hi) : InBox (p + q) lo hi := by
  intro n hn
  have := Finsupp.support_add hn
  rcases Finset.mem_union.1 this with h | h
  · exact hp n h
  · exact hq n h

theorem InBox.sum {α : Type*} (s : Finset α) (f : α → LaurentPolynomial ℤ) {lo hi : ℤ}
    (h : ∀ a ∈ s, InBox (f a) lo hi) : InBox (∑ a ∈ s, f a) lo hi := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InBox.zero lo hi
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem InBox.neg {p : LaurentPolynomial ℤ} {lo hi : ℤ} (hp : InBox p lo hi) :
    InBox (-p) lo hi := by
  intro n hn; rw [support_neg'] at hn; exact hp n hn

theorem InBox.sub {p q : LaurentPolynomial ℤ} {lo hi : ℤ} (hp : InBox p lo hi)
    (hq : InBox q lo hi) : InBox (p - q) lo hi := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem InBox.mul {p q : LaurentPolynomial ℤ} {a b c d : ℤ} (hp : InBox p a b)
    (hq : InBox q c d) : InBox (p * q) (a + c) (b + d) := by
  classical
  intro n hn
  have := AddMonoidAlgebra.support_mul p q hn
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 this
  have h1 := hp x hx
  have h2 := hq y hy
  constructor <;> omega

theorem InBox.T (n : ℤ) : InBox (T n : LaurentPolynomial ℤ) n n := by
  intro m hm
  have : m = n := by
    have := Finsupp.support_single_subset hm
    simpa using this
  omega

theorem InBox.mono {p : LaurentPolynomial ℤ} {lo hi lo' hi' : ℤ} (hp : InBox p lo hi)
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : InBox p lo' hi' := fun n hn => by
  have := hp n hn; constructor <;> omega

theorem inBox_dL : InBox dL (-2) 2 := by
  have h1 : InBox (T 2 : LaurentPolynomial ℤ) (-2) 2 := (InBox.T 2).mono (by norm_num) le_rfl
  have h2 : InBox (T (-2) : LaurentPolynomial ℤ) (-2) 2 :=
    (InBox.T (-2)).mono le_rfl (by norm_num)
  exact h1.neg.sub h2


theorem inBox_dL_pow (m : ℕ) : InBox (dL ^ m) (-2 * m) (2 * m) := by
  induction m with
  | zero => simpa using InBox.T 0
  | succ m ih =>
    rw [pow_succ]
    have := ih.mul inBox_dL
    push_cast
    exact this.mono (by linarith) (by linarith)

section Estados

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

theorem prod_T {α : Type*} (s : Finset α) (f : α → ℤ) :
    ∏ x ∈ s, (T (f x) : LaurentPolynomial ℤ) = T (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, T_add]

theorem sum_sign_eq_expo (σ : D.Cross → Bool) :
    ∑ x : D.Cross, (if σ x then (1 : ℤ) else -1) = D.expo σ := by
  rw [Finset.sum_ite]
  have h := D.nA_eq σ
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have h2 : (Finset.univ.filter fun x => ¬ σ x = true) =
      Finset.univ.filter fun x => σ x = false := by simp
  rw [h2]
  unfold GDiag.expo
  rw [h]
  rfl

theorem prod_ite_T (σ : D.Cross → Bool) :
    (∏ x : D.Cross, if σ x then (T 1 : LaurentPolynomial ℤ) else T (-1)) = T (D.expo σ) := by
  rw [← sum_sign_eq_expo, ← prod_T]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs <;> rfl

end Estados

end Cota

/-! ### Cota de exponentes y de span -/

section CotaFinal

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Si hay algun cruce, todo estado tiene al menos un lazo. -/
theorem one_le_lazos (hne : Nonempty D.Cross) (σ : D.Cross → Bool) : 1 ≤ D.lazos σ := by
  unfold GDiag.lazos
  have : Nonempty (D.graph σ).ConnectedComponent := by
    obtain ⟨x⟩ := hne
    exact ⟨(D.graph σ).connectedComponentMk x.1⟩
  have := Nat.card_pos (α := (D.graph σ).ConnectedComponent)
  omega

/-- El termino del estado `σ` tiene sus exponentes en `[expo - 2(l-1), expo + 2(l-1)]`. -/
theorem inBox_term (σ : D.Cross → Bool) (h : 1 ≤ D.lazos σ) :
    InBox ((∏ x : D.Cross, if σ x then (T 1 : LaurentPolynomial ℤ) else T (-1)) *
        dL ^ (D.lazos σ - 1))
      (-(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2)
      ((Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2) := by
  rw [prod_ite_T]
  have hm : (((D.lazos σ - 1 : ℕ)) : ℤ) = (D.lazos σ : ℤ) - 1 := by omega
  have h1 := (InBox.T (D.expo σ)).mul (inBox_dL_pow (D.lazos σ - 1))
  rw [hm] at h1
  have h2 := GDiag.expo_upper D σ
  have h3 := GDiag.expo_lower D σ
  exact h1.mono (by linarith) (by linarith)

/-- **Cota de exponentes.** Si todo estado tiene al menos un lazo (p. ej. si hay algun cruce),
los exponentes del corchete estan en `[-c - 2 s_B + 2, c + 2 s_A - 2]`. -/
theorem inBox_bracketL (h : ∀ σ : D.Cross → Bool, 1 ≤ D.lazos σ) :
    InBox (bracketL D)
      (-(Fintype.card D.Cross : ℤ) - 2 * (D.lazos D.allB : ℤ) + 2)
      ((Fintype.card D.Cross : ℤ) + 2 * (D.lazos D.allA : ℤ) - 2) :=
  InBox.sum _ _ fun σ _ => inBox_term D σ (h σ)

/-- Cota del span: `span ≤ 2c + 2(s_A + s_B) - 4`. -/
theorem span_bracketL_le (h : ∀ σ : D.Cross → Bool, 1 ≤ D.lazos σ) :
    (span (bracketL D) : ℤ) ≤
      2 * (Fintype.card D.Cross : ℤ) + 2 * ((D.lazos D.allA : ℤ) + D.lazos D.allB) - 4 := by
  have hb := inBox_bracketL D h
  have hA := h D.allA
  have hB := h D.allB
  unfold span maxExp minExp
  by_cases hp : (bracketL D).support.Nonempty
  · rw [dif_pos hp, dif_pos hp]
    have h1 := hb _ (Finset.max'_mem _ hp)
    have h2 := hb _ (Finset.min'_mem _ hp)
    omega
  · rw [dif_neg hp, dif_neg hp]
    simp only [sub_self, Int.toNat_zero, Nat.cast_zero]
    omega

/-- Caso con algun cruce: no hace falta hipotesis sobre los lazos. -/
theorem span_bracketL_le_of_nonempty (hne : Nonempty D.Cross) :
    (span (bracketL D) : ℤ) ≤
      2 * (Fintype.card D.Cross : ℤ) + 2 * ((D.lazos D.allA : ℤ) + D.lazos D.allB) - 4 :=
  span_bracketL_le D (one_le_lazos D hne)

end CotaFinal

/-! ### Sanidad con el trebol

`bracketL` es noncomputable (los lazos usan `Nat.card`), asi que `decide` no sirve. Pero la cota
general con los datos de `sanidad_trefoil` (`c = 3`, `s_A = 2`, `s_B = 3`) da `span ≤ 12 = 4·3`. -/

open TMENudos.Puente in
theorem span_trefoil_le :
    span (bracketL (ofWord TMENudos.Gauss.trefoil wf_trefoil)) ≤ 12 := by
  obtain ⟨h1, h2, h3⟩ := sanidad_trefoil
  have hne : Nonempty (ofWord TMENudos.Gauss.trefoil wf_trefoil).Cross := by
    rw [← Fintype.card_pos_iff, h1]; norm_num
  have := span_bracketL_le_of_nonempty _ hne
  rw [h1, h2, h3] at this
  omega

end TMENudos.SpanLaurent

#print axioms TMENudos.SpanLaurent.evalL_bracketL
#print axioms TMENudos.SpanLaurent.evalL_jonesL
#print axioms TMENudos.SpanLaurent.evalL_injective
#print axioms TMENudos.SpanLaurent.jonesL_rel
#print axioms TMENudos.SpanLaurent.bracketL_rel
#print axioms TMENudos.SpanLaurent.span_unit_mul
#print axioms TMENudos.SpanLaurent.span_bracketL_rel
#print axioms TMENudos.SpanLaurent.inBox_bracketL
#print axioms TMENudos.SpanLaurent.span_bracketL_le
#print axioms TMENudos.SpanLaurent.span_trefoil_le
