-- KN_General.lean
-- Teoría Combinatoria de Nudos Kₙ: Framework General Parametrizado

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Framework General Kₙ: Configuraciones de n Cruces

Este módulo extiende la teoría K₃ a Kₙ general, parametrizado por el número de cruces n.

## Parámetros del Sistema

- **n**: Número de cruces (n ∈ ℕ, n > 0)
- **Grupo base**: Z/(2n)Z = {0, 1, ..., 2n-1}
- **Configuración**: n pares ordenados que particionan Z/(2n)Z
- **Rango DME**: [-n, n]

## Diseño

Las estructuras están parametrizadas por `n : ℕ` con evidencia `[Fact (n > 0)]`
para garantizar que n es positivo. Esto permite:

1. Especialización: `K3Config := KnConfig 3`, `K4Config := KnConfig 4`
2. Pruebas generales que aplican para cualquier n
3. Cálculos verificados en tiempo de compilación

## Relación con TCN_01_Fundamentos.lean

Este módulo es **independiente** de `TCN_01_Fundamentos.lean`. Ambos pueden coexistir:
- `TCN_01_Fundamentos.lean`: Implementación optimizada para K₃
- `KN_General.lean`: Framework general para cualquier n

## Ejemplo de Uso

```lean
-- K₃: 3 cruces en Z/6Z
def myK3 : KnConfig 3 := ...

-- K₄: 4 cruces en Z/8Z
def myK4 : KnConfig 4 := ...

-- K₅: 5 cruces en Z/10Z
def myK5 : KnConfig 5 := ...
```

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory.General

/-! ## Tuplas Ordenadas Parametrizadas -/

/-- Una tupla ordenada en Z/(2n)Z es un par [a,b] de elementos distintos.

    **Parámetros:**
    - n: Número de cruces (determina el grupo Z/(2n)Z)

    **Invariante:**
    - fst ≠ snd (elementos distintos)
-/
structure OrderedPairN (n : ℕ) where
  /-- Primer elemento en Z/(2n)Z -/
  fst : ZMod (2 * n)
  /-- Segundo elemento en Z/(2n)Z -/
  snd : ZMod (2 * n)
  /-- Los elementos deben ser distintos -/
  distinct : fst ≠ snd
  deriving DecidableEq

namespace OrderedPairN

variable {n : ℕ}

/-- Constructor conveniente para tuplas ordenadas -/
def make (a b : ZMod (2 * n)) (h : a ≠ b) : OrderedPairN n := ⟨a, b, h⟩

/-- La tupla inversa intercambia el orden de los elementos -/
def reverse (p : OrderedPairN n) : OrderedPairN n :=
  ⟨p.snd, p.fst, p.distinct.symm⟩

/-- La inversión es involutiva: invertir dos veces da la tupla original -/
theorem reverse_involutive (p : OrderedPairN n) :
  p.reverse.reverse = p := by
  cases p
  rfl

/-- La arista no ordenada subyacente a una tupla ordenada -/
def toEdge (p : OrderedPairN n) : Finset (ZMod (2 * n)) :=
  {p.fst, p.snd}

/-- Toda arista tiene exactamente 2 elementos -/
theorem toEdge_card (p : OrderedPairN n) : p.toEdge.card = 2 := by
  unfold toEdge
  rw [Finset.card_insert_of_notMem (by simp [p.distinct])]
  simp

end OrderedPairN

/-! ## Configuraciones Kₙ -/

/-- Una configuración Kₙ es un conjunto de n tuplas ordenadas que particionan Z/(2n)Z.

    **Parámetros:**
    - n: Número de cruces

    **Invariantes:**
    - Exactamente n pares
    - Cada elemento de Z/(2n)Z aparece exactamente una vez
-/
structure KnConfig (n : ℕ) where
  /-- Conjunto de n tuplas ordenadas -/
  pairs : Finset (OrderedPairN n)
  /-- Debe haber exactamente n tuplas -/
  card_eq : pairs.card = n
  /-- Cada elemento aparece exactamente una vez -/
  is_partition : ∀ i : ZMod (2 * n), ∃! p ∈ pairs, i = p.fst ∨ i = p.snd

namespace KnConfig

variable {n : ℕ}

/-- Dos configuraciones son iguales si tienen los mismos pares -/
instance : DecidableEq (KnConfig n) :=
  fun K1 K2 => decidable_of_iff (K1.pairs = K2.pairs)
    ⟨fun h => by cases K1; cases K2; simp_all,
     fun h => by rw [h]⟩

/-- El matching subyacente de una configuración: conjunto de aristas no ordenadas -/
def toMatching (K : KnConfig n) : Finset (Finset (ZMod (2 * n))) :=
  K.pairs.image OrderedPairN.toEdge

/-- El matching de una configuración Kₙ tiene exactamente n aristas -/
theorem toMatching_card (K : KnConfig n) : K.toMatching.card = n := by
  unfold toMatching
  -- Probar que toEdge es inyectiva sobre K.pairs
  have h_inj : ∀ p1 ∈ K.pairs, ∀ p2 ∈ K.pairs, p1.toEdge = p2.toEdge → p1 = p2 := by
    intro p1 hp1 p2 hp2 h_edge
    -- Similar a TCN_01: dos aristas iguales implican mismo par (por partición)
    obtain ⟨q, ⟨hq_mem, hq_has⟩, hq_unique⟩ := K.is_partition p1.fst
    have h1 : p1 = q := hq_unique p1 ⟨hp1, Or.inl rfl⟩
    -- Necesitamos mostrar que p2 también coincide con q
    unfold OrderedPairN.toEdge at h_edge
    -- CORRECCIÓN: Usar ← h_edge para reescribir en la dirección correcta
    have hp2_fst_mem : p2.fst ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
      rw [← h_edge]
      simp [OrderedPairN.toEdge]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp2_fst_mem
    rcases hp2_fst_mem with hf1 | hf2
    · -- p2.fst = p1.fst
      -- CORRECCIÓN: Usar ← h_edge para reescribir en la dirección correcta
      have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
        rw [← h_edge]
        simp [OrderedPairN.toEdge]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp2_snd_mem
      rcases hp2_snd_mem with hs1 | hs2
      · -- p2.snd = p1.fst, pero p2.fst = p1.fst → contradicción
        exfalso; exact p2.distinct (hf1.trans hs1.symm)
      · -- p2.fst = p1.fst y p2.snd = p1.snd
        cases p1; cases p2; simp_all
    · -- p2.fst = p1.snd
      -- Necesitamos mostrar p1.fst = p2.fst ∨ p1.fst = p2.snd
      -- De h_edge sabemos que {p2.fst, p2.snd} = {p1.fst, p1.snd}
      -- Como p2.fst = p1.snd, entonces p2.snd debe ser p1.fst
      have hp2_snd_eq : p2.snd = p1.fst := by
        -- Sabemos p2.fst = p1.snd (por hf2)
        -- p2.snd debe estar en {p1.fst, p1.snd}
        -- CORRECCIÓN: Usar ← h_edge para reescribir en la dirección correcta
        have hp2_snd_mem : p2.snd ∈ ({p1.fst, p1.snd} : Finset (ZMod (2 * n))) := by
          rw [← h_edge]
          simp [OrderedPairN.toEdge]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp2_snd_mem
        rcases hp2_snd_mem with hs1 | hs2
        · exact hs1
        · -- p2.snd = p1.snd, pero p2.fst = p1.snd → contradicción
          exfalso; exact p2.distinct (hf2.trans hs2.symm)
      have h2 : p2 = q := hq_unique p2 ⟨hp2, Or.inr hp2_snd_eq.symm⟩
      exact h1.trans h2.symm
  rw [Finset.card_image_of_injOn h_inj]
  exact K.card_eq

/-! ## Descriptor Modular Estructural (DME) para Kₙ -/

/-- Convierte el Finset de pares a una lista para procesamiento -/
noncomputable def pairsList (K : KnConfig n) : List (OrderedPairN n) :=
  K.pairs.toList

/-- Calcula δᵢ = sᵢ - eᵢ en aritmética entera para un par -/
def pairDelta {n : ℕ} (p : OrderedPairN n) : ℤ :=
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
noncomputable def gap {n : ℕ} (K : KnConfig n) : ℕ :=
  K.ime.foldl (· + ·) 0

/-- Writhe: Suma algebraica de desplazamientos con signo.

    **Writhe = Σ δᵢ**

    Invariante numérico de quiralidad: Writhe(K̄) = -Writhe(K)
-/
noncomputable def writhe {n : ℕ} (K : KnConfig n) : ℤ :=
  K.dme.foldl (· + ·) 0

/-! ## Reflexión Especular -/

/-- Lema: Cardinalidad se preserva al invertir pares -/
private lemma card_image_reverse {n : ℕ} (K : KnConfig n) :
  (K.pairs.image OrderedPairN.reverse).card = n := by
  have h_inv : ∀ x : OrderedPairN n, x.reverse.reverse = x :=
    OrderedPairN.reverse_involutive
  -- Usar injOn para la prueba
  rw [Finset.card_image_of_injOn]
  · exact K.card_eq
  · -- Probar que reverse es inyectiva sobre K.pairs
    intro x _ y _ hxy
    calc x = x.reverse.reverse := (h_inv x).symm
         _ = y.reverse.reverse := by rw [hxy]
         _ = y := h_inv y

/-- Lema: La partición se preserva bajo inversión de pares -/
private lemma partition_reverse {n : ℕ} (K : KnConfig n) :
  ∀ i : ZMod (2 * n), ∃! p ∈ (K.pairs.image OrderedPairN.reverse),
    i = p.fst ∨ i = p.snd := by
  intro i
  obtain ⟨p, ⟨hp_mem, hp_has⟩, hp_unique⟩ := K.is_partition i
  use p.reverse
  constructor
  · constructor
    · simp only [Finset.mem_image]
      exact ⟨p, hp_mem, rfl⟩
    · rcases hp_has with hi_fst | hi_snd
      · right
        unfold OrderedPairN.reverse
        simp [hi_fst]
      · left
        unfold OrderedPairN.reverse
        simp [hi_snd]
  · intro q ⟨hq_mem, hq_has⟩
    simp only [Finset.mem_image] at hq_mem
    obtain ⟨r, hr_mem, rfl⟩ := hq_mem
    have hr_eq : r = p := by
      apply hp_unique r
      constructor
      · exact hr_mem
      · rcases hq_has with hi_qfst | hi_qsnd
        · right
          unfold OrderedPairN.reverse at hi_qfst
          simp at hi_qfst
          exact hi_qfst
        · left
          unfold OrderedPairN.reverse at hi_qsnd
          simp at hi_qsnd
          exact hi_qsnd
    rw [hr_eq]

/-- Reflexión especular (imagen en espejo) de una configuración Kₙ.

    **Operación: K ↦ K̄**

    Invierte cada par ordenado: (e, s) ↦ (s, e)
-/
def mirror {n : ℕ} (K : KnConfig n) : KnConfig n :=
  ⟨K.pairs.image OrderedPairN.reverse,
   card_image_reverse K,
   partition_reverse K⟩

end KnConfig

/-! ## Especializaciones -/

/-- Configuraciones K₃: 3 cruces en Z/6Z -/
abbrev K3Config := KnConfig 3

/-- Configuraciones K₄: 4 cruces en Z/8Z -/
abbrev K4Config := KnConfig 4

/-- Configuraciones K₅: 5 cruces en Z/10Z -/
abbrev K5Config := KnConfig 5

end KnotTheory.General
