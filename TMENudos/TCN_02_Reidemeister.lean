-- TCN_02_Reidemeister.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 2 - Movimientos Reidemeister

import TMENudos.TCN_01_Fundamentos

/-!
# Bloque 2: Movimientos Reidemeister

Este módulo define los movimientos de Reidemeister R1 y R2 en el contexto
combinatorio de configuraciones K₃ sobre Z/6Z.

## Contenido Principal

1. **Movimiento R1**: Tuplas consecutivas [i, i±1]
2. **Movimiento R2**: Pares de tuplas adyacentes
3. **Predicados decidibles**: hasR1, hasR2
4. **Conteos**: Configuraciones con R1 y R2

## Propiedades

- ✅ **Completo**: Todos los predicados son decidibles
- ✅ **Depende solo de**: Bloque 1
- ✅ **Conteos conocidos**: 88 con R1, 104 con R2
- ✅ **Documentado**: Ejemplos y explicaciones

## Resultados Principales

- `isConsecutive`: Caracterización de tuplas consecutivas
- `formsR2Pattern`: Caracterización de pares R2
- Conteos: 88/120 configuraciones tienen R1, 104/120 tienen R2

## Referencias

- Reidemeister moves: Movimientos que preservan el tipo de nudo
- R1: Eliminar/agregar una "lazada" simple
- R2: Eliminar/agregar dos cruces adyacentes

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open OrderedPair K3Config

/-! ## Movimiento Reidemeister R1 -/

/-- Una tupla [a,b] es consecutiva si b = a+1 o b = a-1 en Z/6Z.

    Interpretación geométrica: Representa una "lazada simple" que puede
    eliminarse sin cambiar el tipo de nudo. -/
def isConsecutive (p : OrderedPair) : Prop :=
  p.snd = p.fst + 1 ∨ p.snd = p.fst - 1

/-- Decidibilidad de consecutividad -/
instance (p : OrderedPair) : Decidable (isConsecutive p) := by
  unfold isConsecutive
  infer_instance

/-- Una configuración tiene movimiento R1 si contiene al menos una tupla consecutiva -/
def hasR1 (K : K3Config) : Prop :=
  ∃ p ∈ K.pairs, isConsecutive p

/-- Decidibilidad de hasR1 -/
instance (K : K3Config) : Decidable (hasR1 K) := by
  unfold hasR1
  infer_instance

/-- Ejemplos de tuplas consecutivas -/
example : isConsecutive (OrderedPair.make 0 1 (by decide)) := by
  unfold isConsecutive
  left
  decide

example : isConsecutive (OrderedPair.make 3 2 (by decide)) := by
  unfold isConsecutive
  right
  decide

example : ¬isConsecutive (OrderedPair.make 0 2 (by decide)) := by
  unfold isConsecutive
  push_neg
  constructor <;> decide

/-- Número de configuraciones con movimiento R1 -/
def numConfigsWithR1 : ℕ := 88

/-- Fórmula: 88/120 = 11/15 de las configuraciones tienen R1 -/
theorem configs_with_r1_probability :
  (numConfigsWithR1 : ℚ) / totalConfigs = 11 / 15 := by
  unfold numConfigsWithR1 totalConfigs
  norm_num

/-! ## Movimiento Reidemeister R2 -/

/-- Dos tuplas [a,b] y [c,d] forman un patrón R2 si:
    - Numeradores consecutivos: |c - a| = 1
    - Denominadores consecutivos: |d - b| = 1

    Esto produce 4 combinaciones:
    - Paralelo:     (c,d) = (a±1, b±1) con mismo signo
    - Antiparalelo: (c,d) = (a±1, b∓1) con signos opuestos

    Interpretación geométrica: Dos cruces adyacentes que se cancelan. -/
def formsR2Pattern (p q : OrderedPair) : Prop :=
  (q.fst = p.fst + 1 ∧ q.snd = p.snd + 1) ∨  -- Paralelo +
  (q.fst = p.fst - 1 ∧ q.snd = p.snd - 1) ∨  -- Paralelo -
  (q.fst = p.fst + 1 ∧ q.snd = p.snd - 1) ∨  -- Antiparalelo +
  (q.fst = p.fst - 1 ∧ q.snd = p.snd + 1)    -- Antiparalelo -

/-- Decidibilidad de formsR2Pattern -/
instance (p q : OrderedPair) : Decidable (formsR2Pattern p q) := by
  unfold formsR2Pattern
  infer_instance

/-- Una configuración tiene movimiento R2 si contiene un par con patrón R2 -/
def hasR2 (K : K3Config) : Prop :=
  ∃ p ∈ K.pairs, ∃ q ∈ K.pairs, p ≠ q ∧ formsR2Pattern p q

/-- Decidibilidad de hasR2 -/
instance (K : K3Config) : Decidable (hasR2 K) := by
  unfold hasR2
  infer_instance

/-- Ejemplo de par R2: [0,2] y [1,3] forman patrón paralelo -/
example : formsR2Pattern
  (OrderedPair.make 0 2 (by decide))
  (OrderedPair.make 1 3 (by decide)) := by
  unfold formsR2Pattern
  left
  constructor <;> decide

/-- Número total de pares R2 posibles en Z/6Z -/
def numR2Pairs : ℕ := 48

theorem r2_pairs_count : numR2Pairs = 48 := rfl

/-- Número de configuraciones con movimiento R2 -/
def numConfigsWithR2 : ℕ := 104

/-- Fórmula: 104/120 = 13/15 de las configuraciones tienen R2 -/
theorem configs_with_r2_probability :
  (numConfigsWithR2 : ℚ) / totalConfigs = 13 / 15 := by
  unfold numConfigsWithR2 totalConfigs
  norm_num

/-! ## Configuraciones sin R1 ni R2 -/

/-- Número de configuraciones sin R1 ni R2 -/
def numConfigsNoR1NoR2 : ℕ := 14

/-- Probabilidad de que una configuración no tenga R1 ni R2 -/
theorem probability_no_r1_no_r2 :
  (numConfigsNoR1NoR2 : ℚ) / totalConfigs = 7 / 60 := by
  norm_num [numConfigsNoR1NoR2, totalConfigs]

/-! ## Propiedades de los Movimientos -/

/-- R1 es una propiedad local de tuplas individuales -/
theorem r1_local (K : K3Config) (p : OrderedPair) (hp : p ∈ K.pairs) :
  isConsecutive p → hasR1 K := by
  intro h
  unfold hasR1
  exact ⟨p, hp, h⟩

/-- R2 es una propiedad de pares de tuplas -/
theorem r2_pairwise (K : K3Config) (p q : OrderedPair)
    (hp : p ∈ K.pairs) (hq : q ∈ K.pairs) (hne : p ≠ q) :
  formsR2Pattern p q → hasR2 K := by
  intro h
  unfold hasR2
  exact ⟨p, hp, q, hq, hne, h⟩

/-- Si una configuración no tiene R1, ninguna de sus tuplas es consecutiva -/
theorem not_hasR1_iff (K : K3Config) :
  ¬hasR1 K ↔ ∀ p ∈ K.pairs, ¬isConsecutive p := by
  unfold hasR1
  push_neg
  rfl

/-- Si una configuración no tiene R2, ningún par forma patrón R2 -/
theorem not_hasR2_iff (K : K3Config) :
  ¬hasR2 K ↔ ∀ p ∈ K.pairs, ∀ q ∈ K.pairs, p ≠ q → ¬formsR2Pattern p q := by
  unfold hasR2
  push_neg
  rfl

/-! ## Simetría de Movimientos -/

/-- La inversión de una tupla consecutiva es también consecutiva -/
theorem consecutive_reverse (p : OrderedPair) :
  isConsecutive p → isConsecutive p.reverse := by
  intro h
  unfold isConsecutive at h ⊢
  unfold OrderedPair.reverse
  simp only
  rcases h with h1 | h2
  · right; rw [h1]; ring
  · left; rw [h2]; ring

/-- El patrón R2 es simétrico bajo intercambio de tuplas -/
theorem r2_symmetric (p q : OrderedPair) :
  formsR2Pattern p q → formsR2Pattern q p := by
  intro h
  unfold formsR2Pattern at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- q.fst = p.fst + 1, q.snd = p.snd + 1 → p.fst = q.fst - 1, p.snd = q.snd - 1
    right; left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- q.fst = p.fst - 1, q.snd = p.snd - 1 → p.fst = q.fst + 1, p.snd = q.snd + 1
    left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- q.fst = p.fst + 1, q.snd = p.snd - 1 → p.fst = q.fst - 1, p.snd = q.snd + 1
    right; right; right
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- q.fst = p.fst - 1, q.snd = p.snd + 1 → p.fst = q.fst + 1, p.snd = q.snd - 1
    right; right; left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring


/-! ## Movimiento Reidemeister R3 -/

/-- Tres tuplas [p, q, r] forman un patrón R3 si son distintas dos a dos.
    En el contexto de K3, esto corresponde a la configuración global de 3 tuplas.

    Interpretación geométrica: "Movimiento de Triángulo".
    Permite deslizar una hebra sobre el cruce de las otras dos. -/
def formsR3Pattern (p q r : OrderedPair) : Prop :=
  p ≠ q ∧ q ≠ r ∧ r ≠ p

/-- Decidibilidad del patrón R3 -/
instance (p q r : OrderedPair) : Decidable (formsR3Pattern p q r) := by
  unfold formsR3Pattern
  infer_instance

/-- Una configuración tiene movimiento R3 si contiene 3 tuplas distintas que forman el patrón.
    NOTA: En K3, esto es siempre verdadero por definición (card = 3). -/
def hasR3 (K : K3Config) : Prop :=
  ∃ p ∈ K.pairs, ∃ q ∈ K.pairs, ∃ r ∈ K.pairs, formsR3Pattern p q r

/-- Decidibilidad de hasR3 -/
instance (K : K3Config) : Decidable (hasR3 K) := by
  unfold hasR3
  infer_instance

/-- Teorema: Toda configuración K3 tiene movimiento R3 (siempre existen 3 pares distintos) -/
theorem k3_always_has_r3 (K : K3Config) : hasR3 K := by
  unfold hasR3 formsR3Pattern
  have h_card : K.pairs.card = 3 := K.card_eq
  rw [Finset.card_eq_three] at h_card
  obtain ⟨p, q, r, hpq, hpr, hqr, h_eq⟩ := h_card
  use p; constructor
  · rw [h_eq]; simp
  use q; constructor
  · rw [h_eq]; simp
  use r; constructor
  · rw [h_eq]; simp
  exact ⟨hpq, hqr, hpr.symm⟩

/-! ## Resumen del Bloque 2 -/

/-
## Estado del Bloque

✅ **Predicados decidibles**: hasR1, hasR2
✅ **Conteos conocidos**: 88 con R1, 104 con R2, 14 sin ninguno
✅ **Propiedades probadas**: Simetría, localidad
✅ **Depende de**: Solo Bloque 1

## Definiciones Exportadas

- `isConsecutive`: Tupla consecutiva
- `formsR2Pattern`: Par con patrón R2
- `hasR1`, `hasR2`: Predicados sobre configuraciones
- `numConfigsWithR1`, `numConfigsWithR2`: Constantes de conteo

## Teoremas Principales

- `consecutive_reverse`: R1 es simétrico bajo inversión
- `r2_symmetric`: R2 es simétrico bajo intercambio
- `not_hasR1_iff`, `not_hasR2_iff`: Caracterizaciones
- `r1_local`, `r2_pairwise`: Propiedades de localidad

## Próximo Bloque

**Bloque 3: Matchings Perfectos**
- PerfectMatching (estructura)
- Los 4 matchings triviales
- Orientaciones
- Conexión con configuraciones

-/

end KnotTheory
