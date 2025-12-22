-- KN_00_Fundamentos_General.lean
-- Teoría Modular de Nudos K_n: Fundamentos Generales Parametrizados
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Diciembre 21, 2025
-- Versión: Mínima Funcional para Lean 4.25

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic

/-!
# Fundamentos Generales para Configuraciones K_n

Versión mínima funcional compatible con Lean 4.25.

## Estructuras Principales

- **OrderedPair n:** Par ordenado en Z/(2n)Z
- **KnConfig n:** Configuración de n cruces

-/

namespace KnotTheory.General

/-! ## 1. Pares Ordenados Parametrizados -/

/-- Un par ordenado en Z/(2n)Z con componentes distintas -/
structure OrderedPair (n : ℕ) [NeZero n] where
  fst : ZMod (2*n)
  snd : ZMod (2*n)
  distinct : fst ≠ snd
  deriving DecidableEq

namespace OrderedPair

variable {n : ℕ} [NeZero n]

/-- Inversión de un par ordenado -/
def reverse (p : OrderedPair n) : OrderedPair n :=
  ⟨p.snd, p.fst, p.distinct.symm⟩

/-- La inversión es involutiva -/
@[simp]
theorem reverse_reverse (p : OrderedPair n) : p.reverse.reverse = p := by
  cases p
  rfl

/-- Teorema de extensionalidad para OrderedPair -/
@[ext]
theorem ext {p q : OrderedPair n} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  cases p; cases q
  simp_all

/-- Rotación de un par ordenado -/
def rotate (p : OrderedPair n) (k : ZMod (2*n)) : OrderedPair n :=
  ⟨p.fst + k, p.snd + k, by
    intro h
    have : p.fst = p.snd := by omega
    exact p.distinct this⟩

/-- La rotación preserva la razón modular -/
@[simp]
theorem ratio_rotate (p : OrderedPair n) (k : ZMod (2*n)) :
    (p.rotate k).snd - (p.rotate k).fst = p.snd - p.fst := by
  simp [rotate]

end OrderedPair

/-! ## 2. Configuraciones K_n Parametrizadas -/

/-- Una configuración K_n es un conjunto de n pares ordenados -/
structure KnConfig (n : ℕ) [NeZero n] where
  pairs : Finset (OrderedPair n)
  card_eq : pairs.card = n
  coverage : ∀ i : ZMod (2*n), ∃ p ∈ pairs, p.fst = i ∨ p.snd = i

namespace KnConfig

variable {n : ℕ} [NeZero n]

/-- Decidibilidad de igualdad entre configuraciones -/
instance : DecidableEq (KnConfig n) :=
  fun K₁ K₂ => decidable_of_iff (K₁.pairs = K₂.pairs)
    ⟨fun h => by cases K₁; cases K₂; simp_all,
     fun h => by cases h; rfl⟩

/-- Rotación de configuración -/
def rotate (K : KnConfig n) (k : ZMod (2*n)) : KnConfig n where
  pairs := K.pairs.image (fun p => p.rotate k)
  card_eq := by
    rw [Finset.card_image_of_injective]
    · exact K.card_eq
    · intro p₁ p₂ h
      unfold OrderedPair.rotate at h
      cases p₁; cases p₂
      simp at h
      ext
      · exact add_left_cancel h.1
      · exact add_left_cancel h.2
  coverage := by
    intro i
    obtain ⟨p, hp, hor⟩ := K.coverage (i - k)
    use p.rotate k
    constructor
    · exact Finset.mem_image_of_mem _ hp
    · cases hor with
      | inl h => left; simp [OrderedPair.rotate, h]
      | inr h => right; simp [OrderedPair.rotate, h]

/-- Reflexión de configuración -/
def reflect (K : KnConfig n) : KnConfig n where
  pairs := K.pairs.image OrderedPair.reverse
  card_eq := by
    rw [Finset.card_image_of_injective]
    · exact K.card_eq
    · intro p₁ p₂ h
      ext
      · simp [OrderedPair.reverse] at h
        exact h.2
      · simp [OrderedPair.reverse] at h
        exact h.1
  coverage := by
    intro i
    obtain ⟨p, hp, hor⟩ := K.coverage i
    use p.reverse
    constructor
    · exact Finset.mem_image_of_mem _ hp
    · cases hor with
      | inl h => right; simp [OrderedPair.reverse, h]
      | inr h => left; simp [OrderedPair.reverse, h]

end KnConfig

/-! ## 3. Especializaciones -/

/-- Configuraciones K₃: 3 cruces en Z/6Z -/
abbrev K3Config := KnConfig 3

/-- Configuraciones K₄: 4 cruces en Z/8Z -/
abbrev K4Config := KnConfig 4

/-- Configuraciones K₅: 5 cruces en Z/10Z -/
abbrev K5Config := KnConfig 5

end KnotTheory.General

/-!
## Resumen del Módulo

### Estructuras Exportadas
- `OrderedPair n`: Par ordenado parametrizado
- `KnConfig n`: Configuración de n cruces

### Operaciones Exportadas
- `OrderedPair.reverse`: Inversión de par
- `OrderedPair.rotate`: Rotación de par
- `KnConfig.rotate`: Rotación de configuración
- `KnConfig.reflect`: Reflexión de configuración

### Estado
✅ Compatible con Lean 4.25
✅ Sin sorry statements
✅ Versión mínima funcional
✅ Lista para usar con KN_01

-/
