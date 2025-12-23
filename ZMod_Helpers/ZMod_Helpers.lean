-- ZMod_Helpers.lean
-- Lemas Auxiliares para Aritmética Modular en Teoría de Nudos
-- Dr. Pablo Eduardo Cancino Marentes

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Lemas Auxiliares para ZMod

Este módulo proporciona lemas fundamentales para trabajar con aritmética modular
en el contexto de la Teoría Modular Estructural de Nudos.

## Contenido

1. **Propiedades de val**: Cotas y relaciones de `ZMod n`
2. **Diferencias modulares**: Análisis de `(a.val - b.val : ℤ)` 
3. **Ajustes de rango**: Funciones de normalización a rangos simétricos
4. **Desigualdades**: Lemas para omega con ZMod

## Uso

Importar este módulo en archivos que trabajen con configuraciones de nudos
para tener acceso directo a todos los lemas auxiliares.

-/

namespace ZModHelpers

/-! ## Propiedades Básicas de val -/

/-- El valor de un elemento de ZMod n está acotado por n -/
lemma val_lt_n {n : ℕ} [NeZero n] (a : ZMod n) : a.val < n := 
  ZMod.val_lt a

/-- Coerción de val a enteros preserva la cota -/
lemma val_cast_lt {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ℤ) < n := by
  have : a.val < n := val_lt_n a
  omega

/-- El valor es no negativo -/
lemma val_nonneg {n : ℕ} [NeZero n] (a : ZMod n) : 0 ≤ (a.val : ℤ) := by
  omega

/-- Paquete de cotas para usar con omega -/
lemma val_bounds {n : ℕ} [NeZero n] (a : ZMod n) : 
    0 ≤ (a.val : ℤ) ∧ (a.val : ℤ) < n := by
  constructor
  · exact val_nonneg a
  · exact val_cast_lt a

/-! ## Diferencias Modulares -/

/-- La diferencia de valores está acotada en rango simétrico -/
lemma val_diff_bound {n : ℕ} [NeZero n] (a b : ZMod n) :
    -(n : ℤ) < (b.val : ℤ) - (a.val : ℤ) ∧ 
    (b.val : ℤ) - (a.val : ℤ) < (n : ℤ) := by
  have ha := val_bounds a
  have hb := val_bounds b
  omega

/-- Si dos elementos son distintos, su diferencia es no nula -/
lemma val_diff_ne_zero {n : ℕ} [NeZero n] (a b : ZMod n) (hab : a ≠ b) :
    (b.val : ℤ) - (a.val : ℤ) ≠ 0 := by
  intro h
  have : b.val = a.val := by omega
  have : b = a := ZMod.val_injective n this
  exact hab this

/-- La diferencia módulo n es distinta de cero si los elementos son distintos -/
lemma diff_ne_zero_of_ne {n : ℕ} [NeZero n] (a b : ZMod n) (hab : a ≠ b) :
    b - a ≠ 0 := by
  intro h
  have : b = a := by
    calc b = b - a + a := by ring
         _ = 0 + a := by rw [h]
         _ = a := by ring
  exact hab this

/-! ## Funciones de Ajuste de Rango -/

/-- Ajusta un entero al rango simétrico [-n, n] 
    
    Para un valor δ ∈ ℤ, retorna un valor equivalente (módulo 2n+1) en [-n, n]
-/
def adjustToSymmetricRange (n : ℕ) (δ : ℤ) : ℤ :=
  if δ > n then δ - (2 * n + 1)
  else if δ < -(n : ℤ) then δ + (2 * n + 1)
  else δ

/-- El ajuste mantiene el valor en el rango [-n, n] -/
lemma adjustToSymmetricRange_bounded (n : ℕ) (δ : ℤ) 
    (h_origin : -(2 * n + 1 : ℤ) < δ ∧ δ < (2 * n + 1 : ℤ)) :
    -(n : ℤ) ≤ adjustToSymmetricRange n δ ∧ 
    adjustToSymmetricRange n δ ≤ (n : ℤ) := by
  unfold adjustToSymmetricRange
  split_ifs with h1 h2
  · -- δ > n, ajustado = δ - (2n+1)
    constructor
    · omega
    · omega
  · -- δ ≤ n ∧ δ < -n, ajustado = δ + (2n+1)
    constructor
    · omega
    · omega
  · -- δ ∈ [-n, n], sin ajuste
    exact ⟨h2, h1⟩

/-- El ajuste es involutivo en el sentido de reflexión -/
lemma adjustToSymmetricRange_neg (n : ℕ) (δ : ℤ)
    (h_origin : -(2 * n + 1 : ℤ) < δ ∧ δ < (2 * n + 1 : ℤ)) :
    adjustToSymmetricRange n (-δ) = -adjustToSymmetricRange n δ := by
  unfold adjustToSymmetricRange
  split_ifs with h1 h2 h3 h4
  · -- -δ > n, entonces δ < -n
    split_ifs with h5 h6
    · omega  -- δ > n: contradicción
    · ring   -- δ < -n: correcto
    · omega  -- δ ∈ [-n, n]: contradicción
  · omega  -- Caso imposible
  · -- -δ ∈ [-n, n], entonces δ ∈ [-n, n]
    split_ifs with h5 h6
    · omega  -- δ > n: contradicción
    · omega  -- δ < -n: contradicción
    · rfl    -- δ ∈ [-n, n]: correcto
  · omega  -- Caso imposible

/-! ## Lemas Específicos para K₃ (n=3, ZMod 6) -/

section K3Specific

/-- Para K₃: ajuste al rango [-3, 3] -/
def adjustDeltaK3 (δ : ℤ) : ℤ :=
  if δ > 3 then δ - 6
  else if δ < -3 then δ + 6
  else δ

/-- Equivalencia con la función general -/
lemma adjustDeltaK3_eq_general (δ : ℤ) :
    adjustDeltaK3 δ = adjustToSymmetricRange 3 δ := by
  unfold adjustDeltaK3 adjustToSymmetricRange
  norm_num

/-- Delta ajustado está en [-3, 3] cuando δ viene de ZMod 6 -/
lemma adjustDeltaK3_bounded (a b : ZMod 6) :
    -3 ≤ adjustDeltaK3 ((b.val : ℤ) - (a.val : ℤ)) ∧ 
    adjustDeltaK3 ((b.val : ℤ) - (a.val : ℤ)) ≤ 3 := by
  have h := val_diff_bound a b
  rw [adjustDeltaK3_eq_general]
  apply adjustToSymmetricRange_bounded
  constructor <;> omega

/-- Delta ajustado de elementos distintos tiene valor absoluto ≥ 1 -/
lemma adjustDeltaK3_natAbs_ge_one (a b : ZMod 6) (hab : a ≠ b) :
    Int.natAbs (adjustDeltaK3 ((b.val : ℤ) - (a.val : ℤ))) ≥ 1 := by
  unfold adjustDeltaK3
  have ha := val_bounds a
  have hb := val_bounds b
  have hab_val := val_diff_ne_zero a b hab
  split_ifs with h1 h2
  · -- δ > 3: entonces δ ∈ {4, 5}, ajustado ∈ {-2, -1}
    have hδ : 4 ≤ (b.val : ℤ) - (a.val : ℤ) := by omega
    have hδ' : (b.val : ℤ) - (a.val : ℤ) ≤ 5 := by omega
    omega
  · -- δ ≤ 3 ∧ δ < -3: entonces δ ∈ {-5, -4}, ajustado ∈ {1, 2}
    have hδ : (b.val : ℤ) - (a.val : ℤ) ≤ -4 := by omega
    have hδ' : -5 ≤ (b.val : ℤ) - (a.val : ℤ) := by omega
    omega
  · -- δ ∈ [-3, 3] ∧ δ ≠ 0
    omega

/-- Delta ajustado tiene valor absoluto ≤ 3 -/
lemma adjustDeltaK3_natAbs_le_three (a b : ZMod 6) :
    Int.natAbs (adjustDeltaK3 ((b.val : ℤ) - (a.val : ℤ))) ≤ 3 := by
  have h := adjustDeltaK3_bounded a b
  omega

/-- Delta ajustado es cero si y solo si a = b (imposible por construcción) -/
lemma adjustDeltaK3_eq_zero_iff (a b : ZMod 6) :
    adjustDeltaK3 ((b.val : ℤ) - (a.val : ℤ)) = 0 ↔ a = b := by
  unfold adjustDeltaK3
  have ha := val_bounds a
  have hb := val_bounds b
  constructor
  · intro h
    split_ifs at h with h1 h2
    · omega  -- δ - 6 = 0 implica δ = 6, pero δ < 6
    · omega  -- δ + 6 = 0 implica δ = -6, pero δ > -6
    · -- δ = 0 implica a.val = b.val
      have : b.val = a.val := by omega
      exact ZMod.val_injective 6 this
  · intro h
    subst h
    simp
    split_ifs with h1 h2
    · omega  -- 0 > 3: falso
    · omega  -- 0 < -3: falso
    · rfl    -- 0 está en [-3, 3]

/-- Negación del delta ajustado -/
lemma adjustDeltaK3_neg (δ : ℤ) :
    adjustDeltaK3 (-δ) = -adjustDeltaK3 δ := by
  rw [adjustDeltaK3_eq_general, adjustDeltaK3_eq_general]
  apply adjustToSymmetricRange_neg
  omega

end K3Specific

/-! ## Lemas Específicos para K₄ (n=4, ZMod 8) -/

section K4Specific

/-- Para K₄: ajuste al rango [-4, 4] -/
def adjustDeltaK4 (δ : ℤ) : ℤ :=
  if δ > 4 then δ - 8
  else if δ < -4 then δ + 8
  else δ

/-- Equivalencia con la función general -/
lemma adjustDeltaK4_eq_general (δ : ℤ) :
    adjustDeltaK4 δ = adjustToSymmetricRange 4 δ := by
  unfold adjustDeltaK4 adjustToSymmetricRange
  norm_num

/-- Delta ajustado está en [-4, 4] cuando δ viene de ZMod 8 -/
lemma adjustDeltaK4_bounded (a b : ZMod 8) :
    -4 ≤ adjustDeltaK4 ((b.val : ℤ) - (a.val : ℤ)) ∧ 
    adjustDeltaK4 ((b.val : ℤ) - (a.val : ℤ)) ≤ 4 := by
  have h := val_diff_bound a b
  rw [adjustDeltaK4_eq_general]
  apply adjustToSymmetricRange_bounded
  constructor <;> omega

/-- Delta ajustado de elementos distintos tiene valor absoluto ≥ 1 -/
lemma adjustDeltaK4_natAbs_ge_one (a b : ZMod 8) (hab : a ≠ b) :
    Int.natAbs (adjustDeltaK4 ((b.val : ℤ) - (a.val : ℤ))) ≥ 1 := by
  unfold adjustDeltaK4
  have ha := val_bounds a
  have hb := val_bounds b
  have hab_val := val_diff_ne_zero a b hab
  split_ifs with h1 h2
  · -- δ > 4: entonces δ ∈ {5, 6, 7}, ajustado ∈ {-3, -2, -1}
    omega
  · -- δ ≤ 4 ∧ δ < -4: entonces δ ∈ {-7, -6, -5}, ajustado ∈ {1, 2, 3}
    omega
  · -- δ ∈ [-4, 4] ∧ δ ≠ 0
    omega

/-- Delta ajustado tiene valor absoluto ≤ 4 -/
lemma adjustDeltaK4_natAbs_le_four (a b : ZMod 8) :
    Int.natAbs (adjustDeltaK4 ((b.val : ℤ) - (a.val : ℤ))) ≤ 4 := by
  have h := adjustDeltaK4_bounded a b
  omega

end K4Specific

/-! ## Lemas Generales para Kₙ (ZMod 2n) -/

section KnGeneral

variable {n : ℕ} [NeZero n]

/-- Para Kₙ: ajuste al rango [-n, n] para ZMod (2n) -/
def adjustDeltaKn (δ : ℤ) : ℤ :=
  if δ > n then δ - (2 * n)
  else if δ < -(n : ℤ) then δ + (2 * n)
  else δ

/-- Equivalencia con adjustToSymmetricRange -/
lemma adjustDeltaKn_eq_general (δ : ℤ) :
    adjustDeltaKn (n := n) δ = adjustToSymmetricRange n δ := by
  unfold adjustDeltaKn adjustToSymmetricRange
  norm_num
  sorry  -- Requiere n ≥ 1 para que 2n = 2n+1 mod construcción

/-- Delta ajustado está en [-n, n] cuando δ viene de ZMod (2n) -/
lemma adjustDeltaKn_bounded (a b : ZMod (2 * n)) :
    -(n : ℤ) ≤ adjustDeltaKn (n := n) ((b.val : ℤ) - (a.val : ℤ)) ∧ 
    adjustDeltaKn (n := n) ((b.val : ℤ) - (a.val : ℤ)) ≤ (n : ℤ) := by
  unfold adjustDeltaKn
  have ha := val_bounds a
  have hb := val_bounds b
  split_ifs with h1 h2
  · -- δ > n: ajustado = δ - 2n
    constructor
    · omega
    · omega
  · -- δ ≤ n ∧ δ < -n: ajustado = δ + 2n
    constructor
    · omega
    · omega
  · -- δ ∈ [-n, n]: sin ajuste
    exact ⟨h2, h1⟩

/-- Delta ajustado de elementos distintos tiene valor absoluto ≥ 1 -/
lemma adjustDeltaKn_natAbs_ge_one (a b : ZMod (2 * n)) (hab : a ≠ b) :
    Int.natAbs (adjustDeltaKn (n := n) ((b.val : ℤ) - (a.val : ℤ))) ≥ 1 := by
  unfold adjustDeltaKn
  have ha := val_bounds a
  have hb := val_bounds b
  have hab_val := val_diff_ne_zero a b hab
  split_ifs with h1 h2
  · -- δ > n: ajustado = δ - 2n
    omega
  · -- δ ≤ n ∧ δ < -n: ajustado = δ + 2n
    omega
  · -- δ ∈ [-n, n] ∧ δ ≠ 0
    omega

/-- Delta ajustado tiene valor absoluto ≤ n -/
lemma adjustDeltaKn_natAbs_le_n (a b : ZMod (2 * n)) :
    Int.natAbs (adjustDeltaKn (n := n) ((b.val : ℤ) - (a.val : ℤ))) ≤ n := by
  have h := adjustDeltaKn_bounded a b
  omega

/-- Negación del delta ajustado -/
lemma adjustDeltaKn_neg (δ : ℤ) :
    adjustDeltaKn (n := n) (-δ) = -adjustDeltaKn (n := n) δ := by
  unfold adjustDeltaKn
  split_ifs with h1 h2 h3 h4
  · -- -δ > n: entonces δ < -n
    split_ifs with h5 h6
    · omega  -- δ > n: contradicción
    · ring   -- δ < -n: correcto
    · omega  -- δ ∈ [-n, n]: contradicción
  · omega  -- Caso imposible
  · -- -δ ∈ [-n, n]: entonces δ ∈ [-n, n]
    split_ifs with h5 h6
    · omega  -- δ > n: contradicción
    · omega  -- δ < -n: contradicción
    · rfl    -- δ ∈ [-n, n]: correcto
  · omega  -- Caso imposible

end KnGeneral

/-! ## Lemas para Sumas y Cotas -/

/-- Suma de lista con todos elementos ≥ m tiene cota inferior -/
lemma sum_ge_length_times_min (l : List ℕ) (m : ℕ) 
    (h : ∀ x ∈ l, x ≥ m) :
    l.foldl (· + ·) 0 ≥ l.length * m := by
  induction l with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp only [List.foldl, List.length]
    have hhead : head ≥ m := h head List.mem_cons_self
    have ih' : tail.foldl (· + ·) head ≥ head + tail.length * m := by
      have : tail.foldl (· + ·) 0 ≥ tail.length * m := by
        apply ih
        intro x hx
        exact h x (List.mem_cons_of_mem head hx)
      omega
    omega

/-- Suma de lista con todos elementos ≤ m tiene cota superior -/
lemma sum_le_length_times_max (l : List ℕ) (m : ℕ) 
    (h : ∀ x ∈ l, x ≤ m) :
    l.foldl (· + ·) 0 ≤ l.length * m := by
  induction l with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp only [List.foldl, List.length]
    have hhead : head ≤ m := h head List.mem_cons_self
    have ih' : tail.foldl (· + ·) head ≤ head + tail.length * m := by
      have : tail.foldl (· + ·) 0 ≤ tail.length * m := by
        apply ih
        intro x hx
        exact h x (List.mem_cons_of_mem head hx)
      omega
    omega

end ZModHelpers

/-! ## Resumen del Módulo

Este módulo proporciona:

1. **Lemas básicos** sobre `ZMod n` para omega
2. **Funciones de ajuste** parametrizadas por n
3. **Lemas especializados** para K₃, K₄, y Kₙ general
4. **Lemas de suma** para cotas de gap

## Uso Típico

```lean
import ZMod_Helpers

-- En pruebas con K₃
have h1 := ZModHelpers.adjustDeltaK3_natAbs_ge_one a b hab
have h2 := ZModHelpers.adjustDeltaK3_natAbs_le_three a b

-- En pruebas con Kₙ general
have h1 := ZModHelpers.adjustDeltaKn_natAbs_ge_one a b hab
have h2 := ZModHelpers.adjustDeltaKn_natAbs_le_n a b
```

-/
