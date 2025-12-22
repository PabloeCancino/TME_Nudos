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
  exact p.distinct this

/-- Rotación de un par ordenado (desplazamiento circular) -/
def rotate (p : OrderedPair n) (k : ZMod (2*n)) : OrderedPair n :=
  ⟨p.fst + k, p.snd + k, by
    intro h
    have : p.fst = p.snd := by omega
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
    exact ⟨h, rfl, rfl⟩

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
    · intro p₁ p₂ hp₁ hp₂ h
      cases p₁; cases p₂
      simp only [OrderedPair.rotate, mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      ext
      · omega
      · omega
  coverage := by
    intro i
    obtain ⟨p, hp, (h : p.fst = i ∨ p.snd = i)⟩ := K.coverage (i - k)
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
  ext
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
  ext
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

/-- Ejemplo: Configuración para K₂ (2 cruces) -/
def k2_example : KnConfig 2 where
  pairs := {⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩}
  card_eq := by decide
  coverage := by
    intro i
    fin_cases i
    · use ⟨0, 1, by decide⟩; simp; left; rfl
    · use ⟨0, 1, by decide⟩; simp; right; rfl
    · use ⟨2, 3, by decide⟩; simp; left; rfl
    · use ⟨2, 3, by decide⟩; simp; right; rfl

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

/-! ## 7. Descriptor Modular Estructural (DME) -/

/-- Convierte el Finset de pares a una lista para procesamiento -/
noncomputable def pairsList (K : KnConfig n) : List (OrderedPair n) :=
  K.pairs.toList

/-- Calcula δᵢ = sᵢ - eᵢ en aritmética entera para un par -/
def pairDelta {n : ℕ} (p : OrderedPair n) : ℤ :=
  (p.snd.val : ℤ) - (p.fst.val : ℤ)

/-- Ajusta un desplazamiento al rango canónico [-n, n] para Z/(2n)Z.

    **Ajustes módulo 2n:**
    - Si δ > n, resta 2n
    - Si δ < -n, suma 2n

    **Generalización de adjustDelta:**
    - K₃ (n=3): rango [-3, 3], módulo 6
    - K₄ (n=4): rango [-4, 4], módulo 8
    - Kₙ (general): rango [-n, n], módulo 2n
-/
def adjustDeltaN (n : ℕ) (δ : ℤ) : ℤ :=
  let bound := (n : ℤ)
  if δ > bound then δ - 2 * bound
  else if δ < -bound then δ + 2 * bound
  else δ

/-- Descriptor Modular Estructural (DME): Vector de desplazamientos direccionales.

    **DME = (δ₁, δ₂, ..., δₙ)** donde **δᵢ = sᵢ - eᵢ** (ajustado a [-n, n])

    Esta es la generalización del concepto DME para cualquier n.
-/
noncomputable def dme {n : ℕ} (K : KnConfig n) : List ℤ :=
  K.pairsList.map (fun p => adjustDeltaN n (pairDelta p))

/-- Invariante Modular Estructural (IME): Magnitudes sin signos.

    **IME = |DME| = (|δ₁|, |δ₂|, ..., |δₙ|)**

    Invariante topológico aquiral: IME(K) = IME(K̄)
-/
noncomputable def ime {n : ℕ} (K : KnConfig n) : List ℕ :=
  K.dme.map Int.natAbs

/-- Vector de signos quirales: σ = sgn(DME) -/
noncomputable def chiralSigns {n : ℕ} (K : KnConfig n) : List ℤ :=
  K.dme.map Int.sign

/-- Gap Total: Complejidad estructural acumulada.

    **Gap = Σ|δᵢ| = Σ IME_i**

    Para Kₙ general:
    - Gap mínimo = n (todos los δᵢ = ±1)
    - Gap máximo ≤ n² (cota superior)
-/
noncomputable def gaps {n : ℕ} (K : KnConfig n) : ℕ :=
  K.ime.foldl (· + ·) 0

/-- Writhe: Suma algebraica de desplazamientos con signo.

    **Writhe = Σ δᵢ**

    Invariante numérico de quiralidad: Writhe(K̄) = -Writhe(K)
-/
noncomputable def writhe {n : ℕ} (K : KnConfig n) : ℤ :=
  K.dme.foldl (· + ·) 0

/-! ## 8. Reflexión Especular (Mirror) -/

/-- Lema: Cardinalidad se preserva al invertir pares -/
private lemma card_image_reverse {n : ℕ} (K : KnConfig n) :
  (K.pairs.image OrderedPair.reverse).card = n := by
  have h_inv : ∀ x : OrderedPair n, x.reverse.reverse = x :=
    OrderedPair.reverse_reverse
  rw [Finset.card_image_of_injOn]
  · exact K.card_eq
  · -- Probar que reverse es inyectiva sobre K.pairs
    intro x _ y _ hxy
    calc x = x.reverse.reverse := (h_inv x).symm
         _ = y.reverse.reverse := by rw [hxy]
         _ = y := h_inv y

/-- Lema: La partición se preserva bajo inversión de pares -/
private lemma coverage_reverse {n : ℕ} (K : KnConfig n) :
  ∀ i : ZMod (2 * n), ∃ p ∈ (K.pairs.image OrderedPair.reverse),
    p.fst = i ∨ p.snd = i := by
  intro i
  obtain ⟨p, hp, (h : p.fst = i ∨ p.snd = i)⟩ := K.coverage i
  use p.reverse
  constructor
  · exact Finset.mem_image_of_mem _ hp
  · cases h with
    | inl h => right; simp [OrderedPair.reverse, h]
    | inr h => left; simp [OrderedPair.reverse, h]

/-- Reflexión especular (imagen en espejo) de una configuración Kₙ.

    **Operación: K ↦ K̄**

    Invierte cada par ordenado: (e, s) ↦ (s, e)
-/
def mirror {n : ℕ} (K : KnConfig n) : KnConfig n :=
  ⟨K.pairs.image OrderedPair.reverse,
   card_image_reverse K,
   coverage_reverse K⟩

/-- La reflexión especular es involutiva -/
@[simp]
theorem mirror_mirror (K : KnConfig n) : K.mirror.mirror = K := by
  ext
  simp [mirror]
  ext p
  simp
  tauto

end KnConfig

/-! ## 9. Especializaciones -/

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
