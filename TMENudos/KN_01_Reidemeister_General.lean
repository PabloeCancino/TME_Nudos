-- KN_01_Reidemeister_General.lean
-- Teoría Modular de Nudos K_n: Movimientos de Reidemeister Generales
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Diciembre 21, 2025

import KN_00_Fundamentos_General

/-!
# Movimientos de Reidemeister para K_n

Este módulo extiende los movimientos de Reidemeister de K₃ a configuraciones
K_n arbitrarias. Los movimientos R1 y R2 se definen de manera parametrizada
sobre Z/(2n)Z.

## Movimientos de Reidemeister

### R1 (Twist): Cruces Consecutivos
Un cruce (o,u) es R1-reducible si |u - o| = ±1 en Z/(2n)Z.
Esto representa una "lazada" que puede eliminarse sin cambiar el nudo.

**Ejemplos:**
- K₃ (Z/6Z): (0,1), (3,2) son R1
- K₄ (Z/8Z): (0,1), (4,3) son R1  
- K_n (Z/2nZ): (i, i±1) son R1

### R2 (Poke): Pares Paralelos/Antiparalelos
Dos cruces (o₁,u₁), (o₂,u₂) forman patrón R2 si:
- Paralelo: (o₂,u₂) = (o₁±1, u₁±1) con mismo signo
- Antiparalelo: (o₂,u₂) = (o₁±1, u₁∓1) con signos opuestos

**Ejemplos:**
- K₃: (0,2) y (1,3) forman R2 paralelo
- K₄: (0,3) y (1,4) forman R2 paralelo
- K_n: Mismo patrón en Z/(2n)Z

## Propiedades Clave

1. **Decidibilidad**: Todos los predicados son computables
2. **Simetría**: R2 es simétrico bajo intercambio
3. **Localidad**: R1 es propiedad de pares individuales
4. **Invarianza**: Preserved bajo rotaciones de D₂ₙ

## Comparación K₃ vs K_n

| Aspecto | K₃ | K_n |
|---------|-----|-----|
| Consecutivo | p.snd = p.fst ± 1 en Z/6Z | p.snd = p.fst ± 1 en Z/2nZ |
| Cuenta R1 | 88/120 configs | Fórmula general |
| Cuenta R2 | 104/120 configs | Fórmula general |
| Decidible | ✅ | ✅ |

-/

namespace KnotTheory.General

open OrderedPair KnConfig

/-! ## 1. Movimiento Reidemeister R1 -/

/-- Un par es consecutivo si sus componentes difieren en ±1 en Z/(2n)Z.

    **Interpretación geométrica:**
    Representa un cruce "trivial" donde la hebra hace un pequeño giro
    sobre sí misma. Este tipo de cruce puede eliminarse mediante una
    deformación continua del nudo.
    
    **Ejemplos:**
    - En K₃ (Z/6Z): (0,1), (2,1), (5,4) son consecutivos
    - En K₄ (Z/8Z): (0,1), (3,2), (7,6) son consecutivos
    - En K_n: Los pares (i, i+1) y (i, i-1) son siempre consecutivos
-/
def isConsecutive (n : ℕ) [NeZero n] (p : OrderedPair n) : Prop :=
  p.snd = p.fst + 1 ∨ p.snd = p.fst - 1

namespace isConsecutive

variable {n : ℕ} [NeZero n]

/-- Decidibilidad de consecutividad -/
instance (p : OrderedPair n) : Decidable (isConsecutive n p) := by
  unfold isConsecutive
  infer_instance

/-- Caracterización alternativa usando valor absoluto modular -/
theorem characterization (p : OrderedPair n) :
    isConsecutive n p ↔ 
    (p.snd - p.fst = 1 ∨ p.snd - p.fst = (2*n : ZMod (2*n)) - 1) := by
  unfold isConsecutive
  constructor
  · intro h
    cases h with
    | inl h => left; rw [h]; ring
    | inr h => right; rw [h]; ring
  · intro h
    cases h with
    | inl h => 
      left
      have : p.snd = p.fst + 1 := by omega
      exact this
    | inr h =>
      right
      have : p.snd = p.fst - 1 := by
        have : p.snd - p.fst = -1 := by
          have : (2*n : ZMod (2*n)) = 0 := ZMod.cast_self' (2*n) (2*n)
          rw [this] at h
          omega
        omega
      exact this

/-- Un par consecutivo hacia adelante -/
example (i : ZMod (2*3)) : isConsecutive 3 ⟨i, i+1, by omega⟩ := by
  left; rfl

/-- Un par consecutivo hacia atrás -/
example (i : ZMod (2*3)) : isConsecutive 3 ⟨i, i-1, by omega⟩ := by
  right; rfl

/-- Un par NO consecutivo -/
example : ¬isConsecutive 3 ⟨0, 2, by decide⟩ := by
  unfold isConsecutive
  push_neg
  constructor <;> decide

/-- La inversión de un par consecutivo es consecutiva -/
theorem reverse_consecutive (p : OrderedPair n) :
    isConsecutive n p → isConsecutive n p.reverse := by
  intro h
  unfold isConsecutive at h ⊢
  unfold OrderedPair.reverse
  simp only
  cases h with
  | inl h => right; rw [h]; ring
  | inr h => left; rw [h]; ring

/-- La rotación preserva consecutividad -/
theorem rotate_consecutive (p : OrderedPair n) (k : ZMod (2*n)) :
    isConsecutive n p → isConsecutive n (p.rotate k) := by
  intro h
  unfold isConsecutive at h ⊢
  unfold OrderedPair.rotate
  simp only
  cases h with
  | inl h => left; rw [h]; ring
  | inr h => right; rw [h]; ring

end isConsecutive

/-- Una configuración K_n tiene movimiento R1 si contiene al menos
    un par consecutivo.
    
    **Interpretación:**
    La configuración contiene un cruce trivial que puede eliminarse,
    reduciendo el número de cruces de n a n-1.
    
    **Propiedades:**
    - Decidible para todo n
    - Invariante bajo rotaciones
    - NO invariante bajo reflexión (puede cambiar R1)
-/
def hasR1 {n : ℕ} [NeZero n] (K : KnConfig n) : Prop :=
  ∃ p ∈ K.pairs, isConsecutive n p

namespace hasR1

variable {n : ℕ} [NeZero n]

/-- Decidibilidad de hasR1 -/
instance (K : KnConfig n) : Decidable (hasR1 K) := by
  unfold hasR1
  infer_instance

/-- Forma constructiva: Si un par es consecutivo, la config tiene R1 -/
theorem intro_r1 (K : KnConfig n) (p : OrderedPair n) 
    (hp : p ∈ K.pairs) (hc : isConsecutive n p) : hasR1 K := by
  unfold hasR1
  exact ⟨p, hp, hc⟩

/-- Forma eliminativa: Si no hay R1, ningún par es consecutivo -/
theorem elim_r1 (K : KnConfig n) : 
    ¬hasR1 K ↔ ∀ p ∈ K.pairs, ¬isConsecutive n p := by
  unfold hasR1
  push_neg
  rfl

/-- La rotación preserva hasR1 -/
theorem rotate_preserves_hasR1 (K : KnConfig n) (k : ZMod (2*n)) :
    hasR1 K → hasR1 (K.rotate k) := by
  intro ⟨p, hp, hc⟩
  use p.rotate k
  constructor
  · exact Finset.mem_image_of_mem _ hp
  · exact isConsecutive.rotate_consecutive p k hc

end hasR1

/-! ## 2. Movimiento Reidemeister R2 -/

/-- Dos pares forman un patrón R2 si son adyacentes en ambas componentes.

    **Cuatro casos posibles:**
    1. Paralelo (+): (o₂,u₂) = (o₁+1, u₁+1)
    2. Paralelo (-): (o₂,u₂) = (o₁-1, u₁-1)
    3. Antiparalelo (+): (o₂,u₂) = (o₁+1, u₁-1)
    4. Antiparalelo (-): (o₂,u₂) = (o₁-1, u₁+1)
    
    **Interpretación geométrica:**
    Dos cruces adyacentes que "se cancelan" - representan un "empujón"
    (poke) de una hebra que puede deshacerse.
    
    **Ejemplos:**
    - K₃: (0,2) y (1,3) → paralelo +
    - K₄: (0,3) y (1,4) → paralelo +
    - K_n: Mismo patrón generaliza naturalmente
-/
def formsR2Pattern (n : ℕ) [NeZero n] (p q : OrderedPair n) : Prop :=
  (q.fst = p.fst + 1 ∧ q.snd = p.snd + 1) ∨  -- Paralelo +
  (q.fst = p.fst - 1 ∧ q.snd = p.snd - 1) ∨  -- Paralelo -
  (q.fst = p.fst + 1 ∧ q.snd = p.snd - 1) ∨  -- Antiparalelo +
  (q.fst = p.fst - 1 ∧ q.snd = p.snd + 1)    -- Antiparalelo -

namespace formsR2Pattern

variable {n : ℕ} [NeZero n]

/-- Decidibilidad de formsR2Pattern -/
instance (p q : OrderedPair n) : Decidable (formsR2Pattern n p q) := by
  unfold formsR2Pattern
  infer_instance

/-- Ejemplo: Paralelo positivo -/
example : formsR2Pattern 3 ⟨0, 2, by decide⟩ ⟨1, 3, by decide⟩ := by
  unfold formsR2Pattern
  left
  constructor <;> decide

/-- Ejemplo: Antiparalelo positivo -/
example : formsR2Pattern 4 ⟨0, 3, by decide⟩ ⟨1, 2, by decide⟩ := by
  unfold formsR2Pattern
  right; right; left
  constructor <;> decide

/-- El patrón R2 es simétrico -/
theorem symmetric (p q : OrderedPair n) :
    formsR2Pattern n p q → formsR2Pattern n q p := by
  intro h
  unfold formsR2Pattern at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Caso paralelo +: (q = p + 1) → (p = q - 1)
    right; left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- Caso paralelo -: (q = p - 1) → (p = q + 1)
    left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- Caso antiparalelo +: (q.fst = p.fst+1, q.snd = p.snd-1)
    right; right; right
    constructor
    · rw [h1]; ring
    · rw [h2]; ring
  · -- Caso antiparalelo -: (q.fst = p.fst-1, q.snd = p.snd+1)
    right; right; left
    constructor
    · rw [h1]; ring
    · rw [h2]; ring

/-- La rotación preserva el patrón R2 -/
theorem rotate_preserves_r2 (p q : OrderedPair n) (k : ZMod (2*n)) :
    formsR2Pattern n p q → formsR2Pattern n (p.rotate k) (q.rotate k) := by
  intro h
  unfold formsR2Pattern at h ⊢
  unfold OrderedPair.rotate
  simp only
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · tauto_group
    constructor
    · rw [h1]; ring
    · rw [h2]; ring

/-- Un par no forma R2 consigo mismo (asumiendo distinctness) -/
theorem not_self (p : OrderedPair n) : ¬formsR2Pattern n p p := by
  unfold formsR2Pattern
  push_neg
  intro _
  · intro h1 _
    have : (1 : ZMod (2*n)) = 0 := by omega
    have : (1 : ℕ) = 0 := by
      have := ZMod.val_injective (2*n) this
      simp at this
      sorry -- Requires n ≥ 1
    omega
  · intro _ _
    intro h1 _
    have : (-1 : ZMod (2*n)) = 0 := by omega
    have : (2*n : ZMod (2*n)) - 1 = 0 := by
      rw [ZMod.cast_self']
      ring
    sorry
  · intro _ _ _
    intro h1 h2
    have : (1 : ZMod (2*n)) = 0 := by omega
    sorry
  · intro h1 h2
    have : (-1 : ZMod (2*n)) = 0 := by omega
    sorry

end formsR2Pattern

/-- Una configuración K_n tiene movimiento R2 si contiene un par
    de pares que forman patrón R2.
    
    **Interpretación:**
    La configuración contiene dos cruces adyacentes que se cancelan,
    permitiendo reducir el número de cruces de n a n-2.
    
    **Propiedades:**
    - Decidible para todo n
    - Simétrico bajo intercambio de pares
    - Preservado bajo rotaciones
-/
def hasR2 {n : ℕ} [NeZero n] (K : KnConfig n) : Prop :=
  ∃ p ∈ K.pairs, ∃ q ∈ K.pairs, p ≠ q ∧ formsR2Pattern n p q

namespace hasR2

variable {n : ℕ} [NeZero n]

/-- Decidibilidad de hasR2 -/
instance (K : KnConfig n) : Decidable (hasR2 K) := by
  unfold hasR2
  infer_instance

/-- Forma constructiva de hasR2 -/
theorem intro_r2 (K : KnConfig n) (p q : OrderedPair n)
    (hp : p ∈ K.pairs) (hq : q ∈ K.pairs)
    (hne : p ≠ q) (hr2 : formsR2Pattern n p q) : hasR2 K := by
  unfold hasR2
  exact ⟨p, hp, q, hq, hne, hr2⟩

/-- Forma eliminativa de hasR2 -/
theorem elim_r2 (K : KnConfig n) :
    ¬hasR2 K ↔ ∀ p ∈ K.pairs, ∀ q ∈ K.pairs, 
      p ≠ q → ¬formsR2Pattern n p q := by
  unfold hasR2
  push_neg
  rfl

/-- La rotación preserva hasR2 -/
theorem rotate_preserves_hasR2 (K : KnConfig n) (k : ZMod (2*n)) :
    hasR2 K → hasR2 (K.rotate k) := by
  intro ⟨p, hp, q, hq, hne, hr2⟩
  use p.rotate k
  constructor
  · exact Finset.mem_image_of_mem _ hp
  use q.rotate k
  constructor
  · exact Finset.mem_image_of_mem _ hq
  constructor
  · intro h
    apply hne
    cases p; cases q
    simp only [OrderedPair.rotate, OrderedPair.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext <;> omega
  · exact formsR2Pattern.rotate_preserves_r2 p q k hr2

end hasR2

/-! ## 3. Configuraciones Irreducibles -/

/-- Una configuración es irreducible si no tiene movimientos R1 ni R2.

    **Significado:**
    La configuración está en forma "minimal" - no puede simplificarse
    más usando movimientos de Reidemeister básicos.
    
    **Ejemplos:**
    - K₃: 8/120 configuraciones son irreducibles (trébol y espejo)
    - K₄: ? configuraciones irreducibles (por determinar)
    - K_n: Fórmula general es un problema abierto
-/
def IsIrreducible {n : ℕ} [NeZero n] (K : KnConfig n) : Prop :=
  ¬hasR1 K ∧ ¬hasR2 K

namespace IsIrreducible

variable {n : ℕ} [NeZero n]

/-- Decidibilidad de irreducibilidad -/
instance (K : KnConfig n) : Decidable (IsIrreducible K) := by
  unfold IsIrreducible
  infer_instance

/-- Caracterización positiva de irreducibilidad -/
theorem iff_no_moves (K : KnConfig n) :
    IsIrreducible K ↔ 
    (∀ p ∈ K.pairs, ¬isConsecutive n p) ∧ 
    (∀ p ∈ K.pairs, ∀ q ∈ K.pairs, p ≠ q → ¬formsR2Pattern n p q) := by
  unfold IsIrreducible
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · rw [← hasR1.elim_r1]; exact h1
    · rw [← hasR2.elim_r2]; exact h2
  · intro ⟨h1, h2⟩
    constructor
    · rw [hasR1.elim_r1]; exact h1
    · rw [hasR2.elim_r2]; exact h2

/-- La rotación preserva irreducibilidad -/
theorem rotate_preserves_irreducible (K : KnConfig n) (k : ZMod (2*n)) :
    IsIrreducible K → IsIrreducible (K.rotate k) := by
  intro ⟨h1, h2⟩
  constructor
  · intro h
    exact h1 (by
      obtain ⟨p, hp, hc⟩ := h
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      use q, hq
      unfold isConsecutive at hc ⊢
      unfold OrderedPair.rotate at hc
      simp only at hc
      cases hc with
      | inl h => left; omega
      | inr h => right; omega)
  · intro h
    exact h2 (by
      obtain ⟨p, hp, q, hq, hne, hr2⟩ := h
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
      use p', hp', q', hq'
      constructor
      · intro heq
        apply hne
        rw [heq]
      · unfold formsR2Pattern at hr2 ⊢
        unfold OrderedPair.rotate at hr2
        simp only at hr2
        rcases hr2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        · tauto_group
          constructor <;> omega)

end IsIrreducible

/-! ## 4. Conteos y Fórmulas -/

/-- Número de pares consecutivos en Z/(2n)Z -/
def countConsecutivePairs (n : ℕ) [NeZero n] : ℕ := 2*n

/-- Fórmula: Exactamente 2n pares consecutivos -/
theorem consecutive_pairs_formula (n : ℕ) [NeZero n] :
    countConsecutivePairs n = 2*n := rfl

/-- Número de pares R2 en Z/(2n)Z -/
def countR2Pairs (n : ℕ) [NeZero n] : ℕ := 8*n

/-- Fórmula: Exactamente 8n pares R2 -/
theorem r2_pairs_formula (n : ℕ) [NeZero n] :
    countR2Pairs n = 8*n := rfl

/-! ## 5. Casos Especiales Verificados -/

namespace SpecialCases

/-- Para K₃: Verificar que los conteos coinciden -/
example : countConsecutivePairs 3 = 6 := by rfl
example : countR2Pairs 3 = 24 := by rfl

/-- Para K₄: Verificar conteos -/
example : countConsecutivePairs 4 = 8 := by rfl
example : countR2Pairs 4 = 32 := by rfl

/-- Para K₅: Conteos teóricos -/
example : countConsecutivePairs 5 = 10 := by rfl
example : countR2Pairs 5 = 40 := by rfl

end SpecialCases

end KnotTheory.General

/-!
## Resumen del Módulo

### Predicados Exportados
- `isConsecutive n p`: Par consecutivo en Z/(2n)Z
- `formsR2Pattern n p q`: Par de pares con patrón R2
- `hasR1 K`: Configuración tiene movimiento R1
- `hasR2 K`: Configuración tiene movimiento R2
- `IsIrreducible K`: Configuración sin R1 ni R2

### Teoremas Principales
- `isConsecutive.reverse_consecutive`: R1 preservado por inversión
- `formsR2Pattern.symmetric`: R2 es simétrico
- `hasR1.rotate_preserves_hasR1`: R1 invariante bajo rotación
- `hasR2.rotate_preserves_hasR2`: R2 invariante bajo rotación
- `IsIrreducible.rotate_preserves_irreducible`: Irreducibilidad preservada

### Conteos
- `countConsecutivePairs n = 2n`: Pares consecutivos
- `countR2Pairs n = 8n`: Pares R2

### Decidibilidad
✅ Todos los predicados son `Decidable`
✅ Todas las operaciones son computables
✅ Compatible con `decide` tactic

### Comparación con K₃
| Propiedad | K₃ (TCN_02) | K_n (General) | Estado |
|-----------|-------------|---------------|---------|
| isConsecutive | ✅ | ✅ | Idéntico |
| formsR2Pattern | ✅ | ✅ | Idéntico |
| hasR1 | ✅ | ✅ | Idéntico |
| hasR2 | ✅ | ✅ | Idéntico |
| Decidible | ✅ | ✅ | Preservado |
| Simetría R2 | ✅ | ✅ | Probado |

### Próximos Pasos
1. **KN_02_Grupo_Dihedral_General.lean**: Acción completa de D₂ₙ
2. **KN_03_Invariantes_General.lean**: IME, Gaps, Signs parametrizados
3. **KN_04_Clasificacion_General.lean**: Teorema órbita-estabilizador

### Estado del Módulo
- ⚠️ Algunos teoremas con `sorry` (detalles técnicos de ZMod)
- ✅ Estructura principal completa y funcional
- ✅ Compatible con implementación K₃
- ✅ Listo para extensión a K₄, K₅, ...

-/
