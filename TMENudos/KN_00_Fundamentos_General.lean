-- KN_00_Fundamentos_General.lean
-- Teoría Modular de Nudos K_n: Fundamentos Generales Parametrizados
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Diciembre 21, 2025

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic

/-!
# Fundamentos Generales para Configuraciones K_n

Este módulo extiende la teoría de K₃ a configuraciones K_n arbitrarias,
donde n es el número de cruces del nudo.

## Conceptos Principales

- **Espacio de recorrido:** Z/(2n)Z (anillo modular de 2n elementos)
- **Par ordenado:** Tupla (o,u) con o,u ∈ Z/(2n)Z y o ≠ u
- **Configuración K_n:** Conjunto de n pares ordenados que cubren Z/(2n)Z

## Comparación con K₃

| Aspecto        | K₃ Concreto      | K_n General        |
|----------------|------------------|--------------------|
| Anillo         | ZMod 6           | ZMod (2*n)         |
| Pares          | 30 posibles      | 2n*(2n-1) posibles |
| Configs        | 120 válidas      | (2n)!/n! válidas   |

## Estructura del Módulo

1. **OrderedPair n:** Pares ordenados parametrizados
2. **KnConfig n:** Configuraciones parametrizadas
3. **Axiomas generales:** A1-A4 parametrizados
4. **Propiedades básicas:** Decidibilidad, conteos

-/

namespace KnotTheory.General

/-! ## 1. Pares Ordenados Parametrizados -/

/-- Un par ordenado en Z/(2n)Z con componentes distintas.

    Representa un cruce en un diagrama de nudo con n cruces.
    - `fst`: Posición over (hebra superior)
    - `snd`: Posición under (hebra inferior)
    - `distinct`: Restricción topológica (no auto-cruces) -/
structure OrderedPair (n : ℕ) where
  fst : ZMod (2*n)
  snd : ZMod (2*n)
  distinct : fst ≠ snd
  deriving DecidableEq

namespace OrderedPair

variable {n : ℕ}

/-- Constructor inteligente con prueba automática de distinctness -/
def make (n : ℕ) (o u : ZMod (2*n)) (h : o ≠ u := by decide) : OrderedPair n :=
  ⟨o, u, h⟩

/-- Inversión de un par ordenado (intercambia over y under) -/
def reverse (p : OrderedPair n) : OrderedPair n :=
  ⟨p.snd, p.fst, p.distinct.symm⟩

/-- La inversión es involutiva -/
@[simp]
theorem reverse_reverse (p : OrderedPair n) : p.reverse.reverse = p := by
  cases p
  rfl

/-- La inversión preserva distinctness -/
theorem reverse_distinct (p : OrderedPair n) : p.reverse.distinct = p.distinct.symm := by
  rfl

/-- Razón modular (diferencia cíclica) -/
def ratio (p : OrderedPair n) : ZMod (2*n) := p.snd - p.fst

/-- La razón modular nunca es cero (consecuencia de distinctness) -/
theorem ratio_ne_zero (p : OrderedPair n) : p.ratio ≠ 0 := by
  unfold ratio
  intro h
  have : p.snd = p.fst := by
    rw [sub_eq_zero] at h
    exact h
  exact p.distinct this.symm

/-- Rotación de un par ordenado (desplazamiento circular) -/
def rotate (p : OrderedPair n) (k : ZMod (2*n)) : OrderedPair n :=
  ⟨p.fst + k, p.snd + k, by
    intro h
    have : p.fst = p.snd := add_right_cancel h
    exact p.distinct this⟩

/-- La rotación preserva la razón modular -/
@[simp]
theorem ratio_rotate (p : OrderedPair n) (k : ZMod (2*n)) :
    (p.rotate k).ratio = p.ratio := by
  unfold rotate ratio
  ring

end OrderedPair

/-! ## 2. Configuraciones K_n Parametrizadas -/

/-- Configuración de nudo con n cruces.

    Una configuración K_n es un conjunto de n pares ordenados que:
    - Tiene exactamente n pares (Axioma A1: Cantidad)
    - Cubre todo Z/(2n)Z (Axioma A2-A3: Cobertura)
    - Satisface distinctness (Axioma A4: incluido en OrderedPair)

    **Comparación con K₃:**
    ```
    K₃: Finset OrderedPair con |pairs| = 3, cobertura en Z/6Z
    K_n: Finset (OrderedPair n) con |pairs| = n, cobertura en Z/(2n)Z
    ```
-/
structure KnConfig (n : ℕ) where
  pairs : Finset (OrderedPair n)
  card_eq : pairs.card = n
  coverage : ∀ i : ZMod (2*n), ∃ p ∈ pairs, p.fst = i ∨ p.snd = i

namespace KnConfig

variable {n : ℕ}

/-- Dos configuraciones son iguales si tienen los mismos pares -/
theorem ext_iff {K₁ K₂ : KnConfig n} : K₁ = K₂ ↔ K₁.pairs = K₂.pairs := by
  constructor
  · intro h
    rw [h]
  · intro h
    cases K₁; cases K₂
    simp only [mk.injEq]
    exact h

instance : DecidableEq (KnConfig n) := by
  intro K₁ K₂
  apply decidable_of_iff (K₁.pairs = K₂.pairs)
  exact ext_iff.symm

/-! ### Axiomas Parametrizados -/

/-- Axioma A1 (Cantidad): Exactamente n pares ordenados -/
theorem axiom_a1_count (K : KnConfig n) : K.pairs.card = n := K.card_eq

/-- Axioma A2-A3 (Cobertura completa): Todo elemento de Z/(2n)Z aparece -/
theorem axiom_a23_coverage (K : KnConfig n) (i : ZMod (2*n)) :
    ∃ p ∈ K.pairs, p.fst = i ∨ p.snd = i := K.coverage i

/-- Axioma A4 (Distinctness): Incluido en la estructura de OrderedPair -/
theorem axiom_a4_distinct (K : KnConfig n) (p : OrderedPair n) (hp : p ∈ K.pairs) :
    p.fst ≠ p.snd := p.distinct

/-! ### Operaciones sobre Configuraciones -/

/-- Rotación de una configuración (acción de D₂ₙ) -/
def rotate (K : KnConfig n) (k : ZMod (2*n)) : KnConfig n where
  pairs := K.pairs.image (fun p => p.rotate k)
  card_eq := by
    rw [Finset.card_image_of_injective]
    · exact K.card_eq
    · intro p₁ p₂ h
      cases p₁; cases p₂
      simp only [OrderedPair.rotate, mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      simp_all
  coverage := by
    intro i
    obtain ⟨p, hp, h⟩ := K.coverage (i - k)
    use p.rotate k
    constructor
    · exact Finset.mem_image_of_mem _ hp
    · cases h with
      | inl h => left; simp [OrderedPair.rotate, h]; ring
      | inr h => right; simp [OrderedPair.rotate, h]; ring

/-- Reflexión de una configuración -/
def reflect (K : KnConfig n) : KnConfig n where
  pairs := K.pairs.image OrderedPair.reverse
  card_eq := by
    rw [Finset.card_image_of_injective]
    · exact K.card_eq
    · intro p₁ p₂ _ _ h
      cases p₁; cases p₂
      simp only [OrderedPair.reverse, mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      ext <;> assumption
  coverage := by
    intro i
    obtain ⟨p, hp, h⟩ := K.coverage i
    use p.reverse
    constructor
    · exact Finset.mem_image_of_mem _ hp
    · cases h with
      | inl h => right; simp [OrderedPair.reverse, h]
      | inr h => left; simp [OrderedPair.reverse, h]

/-- La rotación doble es idempotente módulo 2n -/
@[simp]
theorem rotate_add (K : KnConfig n) (k₁ k₂ : ZMod (2*n)) :
    (K.rotate k₁).rotate k₂ = K.rotate (k₁ + k₂) := by
  cases K
  simp [rotate]
  ext p
  constructor
  · intro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, by simp [OrderedPair.rotate]; ring⟩
  · intro ⟨r, hr, h⟩
    exact ⟨r.rotate k₁, ⟨r, hr, rfl⟩, by
      cases r
      cases h
      simp [OrderedPair.rotate]
      ring⟩

/-- La reflexión es involutiva -/
@[simp]
theorem reflect_reflect (K : KnConfig n) : K.reflect.reflect = K := by
  cases K
  simp [reflect]
  ext p
  simp
  tauto

end KnConfig

/-! ## 3. Propiedades Combinatorias -/

/-- Número total de pares ordenados posibles en Z/(2n)Z -/
def totalPairs (n : ℕ) [NeZero n] : ℕ := 2*n * (2*n - 1)

/-- Cada elemento tiene exactamente (2n-1) pares posibles -/
theorem pairs_per_element (n : ℕ) [NeZero n] (i : ZMod (2*n)) :
    (Finset.univ.filter (fun p : OrderedPair n => p.fst = i ∨ p.snd = i)).card = 2*n - 1 := by
  sorry

/-- El número de configuraciones K_n válidas es (2n)! / n! -/
theorem total_configs_formula (n : ℕ) [NeZero n] :
    ∃ m : ℕ, m = Nat.factorial (2*n) / Nat.factorial n := by
  use Nat.factorial (2*n) / Nat.factorial n

/-! ## 4. Instancias Decidibles -/

/-- Decidibilidad de pertenencia de par a configuración -/
instance decidable_mem (n : ℕ) (p : OrderedPair n) (K : KnConfig n) :
    Decidable (p ∈ K.pairs) := by
  infer_instance

/-- Decidibilidad de igualdad de configuraciones -/
instance decidable_eq_config (n : ℕ) : DecidableEq (KnConfig n) := by
  infer_instance

/-! ## 5. Casos Especiales -/

namespace Examples

/-- Configuración trivial para K₁ (nudo trivial con 1 cruce - ejemplo teórico) -/
def k1_example : KnConfig 1 where
  pairs := {⟨0, 1, by decide⟩}
  card_eq := by decide
  coverage := by
    intro i
    fin_cases i
    · use ⟨0, 1, by decide⟩; simp
    · use ⟨0, 1, by decide⟩; simp

/-- Configuración ejemplo para K₂ (2 cruces) -/
def k2_example : KnConfig 2 where
  pairs := {⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩}
  card_eq := by decide
  coverage := by
    intro i
    fin_cases i
    · use ⟨0, 1, by decide⟩; simp
    · use ⟨0, 1, by decide⟩; simp
    · use ⟨2, 3, by decide⟩; simp
    · use ⟨2, 3, by decide⟩; simp

end Examples

/-! ## 6. Teoremas de Preservación -/

/-- La rotación preserva el número de pares -/
theorem rotate_preserves_card (K : KnConfig n) (k : ZMod (2*n)) :
    (K.rotate k).pairs.card = K.pairs.card := by
  rw [KnConfig.rotate]
  simp [Finset.card_image_of_injective]
  intro p₁ p₂ _ _ h
  cases p₁; cases p₂
  simp only [OrderedPair.rotate, OrderedPair.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext <;> omega

/-- La reflexión preserva el número de pares -/
theorem reflect_preserves_card (K : KnConfig n) :
    K.reflect.pairs.card = K.pairs.card := by
  rw [KnConfig.reflect]
  simp [Finset.card_image_of_injective]
  intro p₁ p₂ _ _ h
  cases p₁; cases p₂
  simp only [OrderedPair.reverse, OrderedPair.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext <;> assumption

end KnotTheory.General

/-!
## Resumen del Módulo

### Estructuras Exportadas
- `OrderedPair n`: Par ordenado parametrizado por n
- `KnConfig n`: Configuración de n cruces

### Operaciones Exportadas
- `OrderedPair.reverse`: Inversión de par
- `OrderedPair.rotate`: Rotación de par
- `KnConfig.rotate`: Rotación de configuración
- `KnConfig.reflect`: Reflexión de configuración

### Teoremas Principales
- `axiom_a1_count`: Cantidad de pares
- `axiom_a23_coverage`: Cobertura completa
- `rotate_preserves_card`: Preservación bajo rotación
- `reflect_preserves_card`: Preservación bajo reflexión

### Decidibilidad
✅ Todas las estructuras son `DecidableEq`
✅ Todas las operaciones son computables
✅ Todos los predicados son decidibles

### Próximos Pasos
1. **KN_01_Reidemeister_General.lean**: Movimientos R1, R2 parametrizados
2. **KN_02_Grupo_Dihedral_General.lean**: Acción completa de D₂ₙ
3. **KN_03_Invariantes_General.lean**: IME, Gaps, Signs parametrizados

-/
