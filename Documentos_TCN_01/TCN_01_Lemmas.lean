-- TCN_01_Lemmas.lean
-- Lemas auxiliares y ejemplo de implementación de mirror
-- Para usar en TCN_01_Fundamentos.lean

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace KnotTheory

/-! ## Lemas Auxiliares sobre Listas -/

/-- La longitud de una lista mapeada es igual a la longitud original -/
lemma map_length {α β : Type*} (f : α → β) (l : List α) :
  (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [List.map, ih]

/-- Acceso a elemento mapeado -/
lemma getElem_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) 
  (h : i < l.length) :
  (l.map f).get ⟨i, by rw [map_length]; exact h⟩ = f (l.get ⟨i, h⟩) := by
  induction l generalizing i with
  | nil => contradiction
  | cons head tail ih =>
    cases i with
    | zero => rfl
    | succ i' => 
      simp [List.map, List.get]
      exact ih f i' _

/-! ## Lemas Aritméticos para ℤ -/

/-- Descomposición fundamental: n = |n| * sgn(n) para n ≠ 0 -/
lemma int_abs_sign_decomp (n : ℤ) (hn : n ≠ 0) :
  n = (Int.natAbs n : ℤ) * Int.sign n := by
  rcases Int.sign_eq_one_or_neg_one_of_ne_zero hn with h | h
  · -- sign n = 1, entonces n > 0
    rw [h, mul_one]
    have hp : 0 < n := Int.sign_eq_one_iff.mp h
    exact (Int.natAbs_of_nonneg hp.le).symm
  · -- sign n = -1, entonces n < 0
    rw [h, mul_neg, mul_one]
    have hn_neg : n < 0 := Int.sign_eq_neg_one_iff.mp h
    conv_lhs => rw [← Int.neg_neg n]
    congr 1
    exact Int.natAbs_of_nonneg (Int.neg_nonneg.mpr hn_neg.le)

/-- Valor absoluto de un número no nulo es al menos 1 -/
lemma natAbs_pos_of_nonzero (n : ℤ) (hn : n ≠ 0) :
  Int.natAbs n ≥ 1 := by
  have : Int.natAbs n ≠ 0 := Int.natAbs_ne_zero.mpr hn
  omega

/-- Cota superior del valor absoluto -/
lemma natAbs_le_of_bounded (n : ℤ) (m : ℕ) (h : -↑m ≤ n ∧ n ≤ ↑m) :
  Int.natAbs n ≤ m := by
  rcases h with ⟨h_lower, h_upper⟩
  cases' Int.natAbs_eq n with hp hn
  · -- n ≥ 0
    rw [hp]
    exact Int.ofNat_le.mp h_upper
  · -- n < 0
    rw [hn]
    have : -n ≤ ↑m := by
      calc -n = -n := rfl
           _ = -(n) := rfl
           _ ≤ -(-↑m) := by exact Int.neg_le_neg h_lower
           _ = ↑m := by simp
    exact Int.ofNat_le.mp this

/-- Valor absoluto de negación -/
lemma natAbs_neg (n : ℤ) : Int.natAbs (-n) = Int.natAbs n := by
  exact Int.natAbs_neg n

/-! ## Lemas sobre adjustDelta -/

/-- adjustDelta de pairDelta nunca es cero (porque los elementos son distintos) -/
lemma adjustDelta_nonzero_of_distinct {a b : ZMod 6} (h : a ≠ b) :
  adjustDelta ((b.val : ℤ) - (a.val : ℤ)) ≠ 0 := by
  unfold adjustDelta
  split_ifs with h1 h2
  · -- δ > 3, entonces δ - 6 ≠ 0
    omega
  · -- δ < -3, entonces δ + 6 ≠ 0
    omega
  · -- -3 ≤ δ ≤ 3
    by_contra h_zero
    -- Si adjustDelta δ = 0, entonces δ = 0
    -- Pero δ = b.val - a.val ≠ 0 mod 6 (porque a ≠ b)
    have : (b.val : ℤ) - (a.val : ℤ) = 0 := h_zero
    have : b.val = a.val := by omega
    have : b = a := ZMod.val_injective 6 this
    contradiction

/-- adjustDelta mantiene valores en [-3, 3] -/
lemma adjustDelta_bounded (δ : ℤ) :
  -3 ≤ adjustDelta δ ∧ adjustDelta δ ≤ 3 := by
  unfold adjustDelta
  split_ifs with h1 h2
  · -- δ > 3, entonces -3 ≤ δ - 6 ≤ 3
    constructor <;> omega
  · -- δ < -3, entonces -3 ≤ δ + 6 ≤ 3
    constructor <;> omega
  · -- Ya está en rango
    constructor <;> omega

/-- adjustDelta conmuta con negación -/
lemma adjustDelta_neg (δ : ℤ) :
  adjustDelta (-δ) = -adjustDelta δ := by
  unfold adjustDelta
  split_ifs with h1 h2 h3 h4
  · -- -δ > 3, entonces δ < -3
    -- adjustDelta(-δ) = -δ - 6
    -- adjustDelta(δ) = δ + 6 (porque δ < -3)
    omega
  · -- -δ > 3 y -δ ≥ -3 (contradicción si -δ > 3)
    omega
  · -- -δ > 3 y no (-δ ≥ -3) y no (-δ < -3) (imposible)
    omega
  · -- -δ ≤ 3 y -δ < -3, entonces δ > 3
    -- adjustDelta(-δ) = -δ + 6
    -- adjustDelta(δ) = δ - 6 (porque δ > 3)
    omega
  · -- -δ ≤ 3, -δ ≥ -3 (es decir, -3 ≤ -δ ≤ 3)
    -- entonces -3 ≤ δ ≤ 3
    omega
  · -- Caso: -δ ≤ 3, no (-δ ≥ -3), no (-δ < -3)
    -- Esto significa -δ < -3 pero también ¬(-δ < -3), contradicción
    omega
  all_goals omega

/-! ## Lemas sobre pairDelta -/

/-- pairDelta de par invertido es negación -/
lemma pairDelta_reverse (p : OrderedPair) :
  pairDelta p.reverse = -pairDelta p := by
  unfold pairDelta OrderedPair.reverse
  simp
  ring

/-! ## Lemas sobre sum de listas -/

/-- Suma de lista con cota inferior -/
lemma sum_list_ge (l : List ℕ) (n m : ℕ) 
  (hlen : l.length = n) 
  (hbound : ∀ x ∈ l, x ≥ m) :
  l.foldl (· + ·) 0 ≥ n * m := by
  -- Estrategia: inducción sobre la lista
  -- Caso base: lista vacía → 0 ≥ 0 * m (trivial)
  -- Paso inductivo: si x :: tail con x ≥ m y sum(tail) ≥ n' * m
  --                 entonces sum(x :: tail) ≥ (n'+1) * m
  subst hlen
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl]
    have hh : h ≥ m := hbound h (List.mem_cons_self h t)
    have ih' : t.foldl (· + ·) 0 ≥ t.length * m := by
      apply ih
      intro x hx
      exact hbound x (List.mem_cons_of_mem h hx)
    omega

/-- Suma de lista con cota superior -/
lemma sum_list_le (l : List ℕ) (n m : ℕ) 
  (hlen : l.length = n) 
  (hbound : ∀ x ∈ l, x ≤ m) :
  l.foldl (· + ·) 0 ≤ n * m := by
  subst hlen
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl]
    have hh : h ≤ m := hbound h (List.mem_cons_self h t)
    have ih' : t.foldl (· + ·) 0 ≤ t.length * m := by
      apply ih
      intro x hx
      exact hbound x (List.mem_cons_of_mem h hx)
    omega

/-- Suma con negación -/
lemma foldl_sum_neg (l : List ℤ) :
  (l.map (· * (-1))).foldl (· + ·) 0 = -(l.foldl (· + ·) 0) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.map, List.foldl]
    rw [ih]
    ring

/-! ## Lemas sobre Finset.image con funciones involutivas -/

/-- Cardinalidad se preserva bajo imagen de función involutiva -/
lemma card_image_involutive {α : Type*} [DecidableEq α] 
  (s : Finset α) (f : α → α) (hf : ∀ x, f (f x) = x) :
  (s.image f).card = s.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  calc x = f (f x) := (hf x).symm
       _ = f (f y) := by rw [hxy]
       _ = y := hf y

/-- Doble aplicación de imagen de función involutiva da identidad -/
lemma image_image_involutive {α : Type*} [DecidableEq α] 
  (s : Finset α) (f : α → α) (hf : ∀ x, f (f x) = x) :
  (s.image f).image f = s := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · intro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    rw [← hy, hf]
    exact hz
  · intro hx
    use f x
    constructor
    · use x, hx
    · exact hf x

/-! ## EJEMPLO: Implementación de mirror -/

-- Esta es una implementación ESQUEMÁTICA de mirror
-- Requiere completar las pruebas sorry

example (OrderedPair K3Config : Type) 
  [DecidableEq OrderedPair]
  (reverse : OrderedPair → OrderedPair)
  (reverse_involutive : ∀ p : OrderedPair, reverse (reverse p) = p)
  (pairs : K3Config → Finset OrderedPair)
  (card_eq : ∀ K : K3Config, (pairs K).card = 3)
  (is_partition : ∀ K : K3Config, True)  -- Simplificado para el ejemplo
  : K3Config → K3Config := fun K =>
  let reversed_pairs := (pairs K).image reverse
  ⟨reversed_pairs, 
   -- Prueba: reversed_pairs.card = 3
   by
     rw [card_image_involutive (pairs K) reverse reverse_involutive]
     exact card_eq K,
   -- Prueba: is_partition se preserva
   sorry  -- Esta es la parte no trivial
  ⟩

/-! ## Estrategia para probar partition_reverse -/

/-
Para probar que la partición se preserva bajo inversión de pares,
necesitamos mostrar:

Si K particiona Z/6Z con pares (eᵢ, sᵢ), entonces los pares invertidos 
(sᵢ, eᵢ) también particionan Z/6Z.

Demostración:
1. Todo elemento i ∈ Z/6Z aparece en exactamente un par (eⱼ, sⱼ) de K
2. O bien i = eⱼ, o bien i = sⱼ (pero no ambos por distinct)
3. En los pares invertidos:
   - Si i = eⱼ, entonces i aparece como segundo componente de (sⱼ, eⱼ)
   - Si i = sⱼ, entonces i aparece como primer componente de (sⱼ, eⱼ)
4. Por tanto, i aparece exactamente una vez en los pares invertidos

La unicidad se preserva porque reverse es inyectiva.
-/

-- Este lema requiere trabajar con la propiedad is_partition de K3Config
lemma partition_reverse_sketch 
  (K : K3Config) :
  ∀ i : ZMod 6, ∃! p ∈ (K.pairs.image OrderedPair.reverse), i = p.fst ∨ i = p.snd := by
  intro i
  -- Obtener el único par que contiene i en K
  obtain ⟨p, ⟨hp_mem, hp_has⟩, hp_unique⟩ := K.is_partition i
  -- Considerar p.reverse
  use p.reverse
  constructor
  · constructor
    · -- Mostrar que p.reverse ∈ K.pairs.image reverse
      simp only [Finset.mem_image]
      use p, hp_mem
    · -- Mostrar que i aparece en p.reverse
      rcases hp_has with hi_fst | hi_snd
      · -- i = p.fst, entonces i = p.reverse.snd
        right
        simp [OrderedPair.reverse, hi_fst]
      · -- i = p.snd, entonces i = p.reverse.fst
        left
        simp [OrderedPair.reverse, hi_snd]
  · -- Unicidad: cualquier otro par que contenga i debe ser p.reverse
    intro q ⟨hq_mem, hq_has⟩
    -- q ∈ image reverse, así que q = r.reverse para algún r ∈ K.pairs
    simp only [Finset.mem_image] at hq_mem
    obtain ⟨r, hr_mem, rfl⟩ := hq_mem
    -- Ahora mostramos r = p
    have : r = p := by
      apply hp_unique r
      constructor
      · exact hr_mem
      · -- i aparece en r, necesitamos mostrar i = r.fst ∨ i = r.snd
        -- Sabemos que i aparece en r.reverse
        rcases hq_has with hi_rfst | hi_rsnd
        · -- i = r.reverse.fst = r.snd
          right
          simp [OrderedPair.reverse] at hi_rfst
          exact hi_rfst
        · -- i = r.reverse.snd = r.fst
          left
          simp [OrderedPair.reverse] at hi_rsnd
          exact hi_rsnd
    rw [this]

/-! ## Template para TCN_01_Fundamentos.lean -/

/-
-- Agregar esto a TCN_01_Fundamentos.lean después de OrderedPair.reverse:

/-- Implementación correcta de mirror -/
def mirror (K : K3Config) : K3Config :=
  let reversed_pairs := K.pairs.image OrderedPair.reverse
  ⟨reversed_pairs,
   -- Prueba de card_eq
   by rw [card_image_involutive K.pairs OrderedPair.reverse OrderedPair.reverse_involutive]
      exact K.card_eq,
   -- Prueba de is_partition  
   partition_reverse K⟩

-- Luego todos los teoremas sobre mirror se pueden probar:

theorem dme_mirror (K : K3Config) :
  K.mirror.dme = K.dme.map (· * (-1)) := by
  unfold dme mirror pairsList
  -- K.mirror.pairs = K.pairs.image reverse
  simp [Finset.toList]
  sorry -- Requiere lemas sobre List y Finset.toList

theorem ime_mirror (K : K3Config) :
  K.mirror.ime = K.ime := by
  unfold ime
  rw [dme_mirror]
  simp [List.map]
  ext i
  simp [List.getElem?]
  sorry -- Requiere composición de maps y natAbs_neg

-- etc...
-/

end KnotTheory
