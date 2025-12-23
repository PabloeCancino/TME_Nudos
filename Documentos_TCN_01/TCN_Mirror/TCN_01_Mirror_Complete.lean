-- TCN_01_Mirror_Complete.lean
-- Pruebas Completas de Teoremas de Reflexión
-- Dr. Pablo Eduardo Cancino Marentes
-- Compatible con Lean 4.25.0 - Versión Standalone

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-!
# Teoremas de Reflexión - Versión Completa para Lean 4.25.0

Este archivo proporciona las pruebas completas de los teoremas de reflexión
para el sistema K₃ de Teoría Modular Estructural de Nudos.

## Versión Standalone

Esta versión incluye las definiciones mínimas necesarias para ser completamente
independiente y compilable sin TCN_01_Fundamentos.lean.

## Contenido

1. **Definiciones básicas**: OrderedPair, K3Config, DME, invariantes
2. **gap_mirror**: Gap es invariante bajo reflexión
3. **writhe_mirror**: Writhe cambia de signo bajo reflexión
4. **mirror_involutive**: La reflexión es involutiva
5. **nonzero_writhe_implies_chiral**: Writhe ≠ 0 implica quiralidad

## Uso

Este archivo puede compilarse directamente:
```bash
lean TCN_01_Mirror_Complete.lean
```

-/

namespace KnotTheory

/-! ## Definiciones Básicas (Mínimas para Teoremas de Reflexión) -/

/-- Una tupla ordenada es un par [a,b] de elementos distintos de Z/6Z
 -/
structure OrderedPair where
  fst : ZMod 6
  snd : ZMod 6
  distinct : fst ≠ snd
  deriving DecidableEq

namespace OrderedPair

/-- La tupla inversa intercambia el orden de los elementos
 -/
def reverse (p : OrderedPair) : OrderedPair :=
  ⟨p.snd, p.fst, p.distinct.symm⟩

/-- La inversión es involutiva
 -/
theorem reverse_involutive (p : OrderedPair) :
  p.reverse.reverse = p := by
  cases p
  rfl

end OrderedPair

/-- Una configuración K₃: 3 tuplas que particionan Z/6Z
 -/
structure K3Config where
  pairs : Finset OrderedPair
  card_eq : pairs.card = 3
  is_partition : ∀ i : ZMod 6, ∃! p ∈ pairs, i = p.fst ∨ i = p.snd

namespace K3Config

/-! ## Representación y DME -/

noncomputable def pairsList (K : K3Config) : List OrderedPair :=
  K.pairs.toList

def pairDelta (p : OrderedPair) : ℤ :=
  (p.snd.val : ℤ) - (p.fst.val : ℤ)

def adjustDelta (δ : ℤ) : ℤ :=
  if δ > 3 then δ - 6
  else if δ < -3 then δ + 6
  else δ

noncomputable def dme (K : K3Config) : List ℤ :=
  K.pairsList.map (fun p => adjustDelta (pairDelta p))

noncomputable def ime (K : K3Config) : List ℕ :=
  K.dme.map Int.natAbs

noncomputable def gap (K : K3Config) : ℕ :=
  K.ime.foldl (· + ·) 0

noncomputable def writhe (K : K3Config) : ℤ :=
  K.dme.foldl (· + ·) 0

/-! ## Reflexión Especular -/

private lemma card_image_reverse (K : K3Config) :
    (K.pairs.image OrderedPair.reverse).card = 3 := by
  apply Finset.card_image_of_injective
  intro x y hxy
  calc x = x.reverse.reverse := (OrderedPair.reverse_involutive x).symm
       _ = y.reverse.reverse := by rw [hxy]
       _ = y := OrderedPair.reverse_involutive y

private lemma partition_reverse (K : K3Config) :
    ∀ i : ZMod 6, ∃! p ∈ (K.pairs.image OrderedPair.reverse),
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
        unfold OrderedPair.reverse
        simp [hi_fst]
      · left
        unfold OrderedPair.reverse
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
          unfold OrderedPair.reverse at hi_qfst
          simp at hi_qfst
          exact hi_qfst
        · left
          unfold OrderedPair.reverse at hi_qsnd
          simp at hi_qsnd
          exact hi_qsnd
    rw [hr_eq]

/-- Reflexión especular completa
 -/
def mirror (K : K3Config) : K3Config :=
  ⟨K.pairs.image OrderedPair.reverse,
   card_image_reverse K,
   partition_reverse K⟩

/-! ## Lemas Auxiliares -/

/-- Lema auxiliar generalizado: foldl con acumulador negado
 -/
lemma foldl_add_neg_aux (l : List ℤ) (acc : ℤ) :
    (l.map (· * (-1))).foldl (· + ·) (-acc) = -(l.foldl (· + ·) acc) := by
  induction l generalizing acc with
  | nil =>
    simp [List.foldl]
  | cons h t ih =>
    simp only [List.map, List.foldl]
    rw [ih]
    ring

/-- Lema: Suma con negación - Σ(-xᵢ) = -Σxᵢ
 -/
lemma foldl_sum_neg (l : List ℤ) :
    (l.map (· * (-1))).foldl (· + ·) 0 = -(l.foldl (· + ·) 0) := by
  have h := foldl_add_neg_aux l 0
  simp only [neg_zero] at h
  exact h

/-- Lema: mapear natAbs después de negar da el mismo resultado
 -/
lemma natAbs_map_neg_eq (l : List ℤ) :
    (l.map (· * (-1))).map Int.natAbs = l.map Int.natAbs := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map]
    congr 1
    · ring_nf
      exact Int.natAbs_neg h
    · exact ih

/-- Lema: aplicar reverse dos veces a un Finset da la identidad
 -/
private lemma image_reverse_twice (s : Finset OrderedPair) :
    (s.image OrderedPair.reverse).image OrderedPair.reverse = s := by
  ext p
  simp only [Finset.mem_image]
  constructor
  · intro ⟨q, ⟨r, hr, hrq⟩, hqp⟩
    rw [← hqp, ← hrq]
    have : r.reverse.reverse = r := OrderedPair.reverse_involutive r
    rw [this]
    exact hr
  · intro hp
    use p.reverse
    constructor
    · use p, hp, rfl
    · exact OrderedPair.reverse_involutive p

/-! ## Teorema Clave: DME cambia de signo bajo reflexión -/

/-- **LEMA FUNDAMENTAL**: DME cambia de signo bajo reflexión
 -/
theorem dme_mirror (K : K3Config) :
    K.mirror.dme = K.dme.map (· * (-1)) := by
  unfold mirror dme pairsList
  ext i
  simp only [List.get?_map]
  cases hi : ((K.pairs.image OrderedPair.reverse).toList)[i]? with
  | none =>
    simp [hi]
    have hlen : ((K.pairs.image OrderedPair.reverse).toList).length = 
                K.pairs.toList.length := by
      rw [Finset.length_toList, Finset.length_toList]
      rw [card_image_reverse]
      exact K.card_eq
    cases hj : (K.pairs.toList)[i]? with
    | none => rfl
    | some p =>
      have hip : i < K.pairs.toList.length := by
        rw [← List.get?_isSome_iff_lt_length]
        simp [hj]
      have hii : i < ((K.pairs.image OrderedPair.reverse).toList).length := by
        rw [hlen]; exact hip
      rw [← List.get?_isSome_iff_lt_length] at hii
      simp [hi] at hii
  | some p_rev =>
    simp [hi]
    have hex : ∃ p, p ∈ K.pairs ∧ p.reverse = p_rev := by
      have hmem : p_rev ∈ (K.pairs.image OrderedPair.reverse).toList := by
        apply List.get?_mem
        exact hi
      rw [Finset.mem_toList] at hmem
      simp only [Finset.mem_image] at hmem
      obtain ⟨p, hp, heq⟩ := hmem
      exact ⟨p, hp, heq⟩
    obtain ⟨p, hp_mem, hp_eq⟩ := hex
    rw [← hp_eq]
    unfold pairDelta OrderedPair.reverse
    simp only
    have : (p.fst.val : ℤ) - (p.snd.val : ℤ) = 
           -((p.snd.val : ℤ) - (p.fst.val : ℤ)) := by ring
    rw [this]
    -- Mostrar que adjustDelta (-δ) = -adjustDelta δ
    have adjust_neg : ∀ (δ : ℤ), adjustDelta (-δ) = -adjustDelta δ := by
      intro δ
      unfold adjustDelta
      split_ifs with h1 h2 h3 h4
      · omega
      · omega
      · split_ifs with h5 h6
        · omega
        · omega
        · rfl
      · omega
    exact adjust_neg ((p.snd.val : ℤ) - (p.fst.val : ℤ))

/-! ## Teoremas Principales de Reflexión -/

/-- **TEOREMA 1**: Gap es invariante bajo reflexión.
    
    Gap(K̄) = Gap(K)
 -/
theorem gap_mirror (K : K3Config) :
    K.mirror.gap = K.gap := by
  unfold gap ime
  have h_dme : K.mirror.dme = K.dme.map (· * (-1)) := dme_mirror K
  rw [h_dme, List.map_map]
  have : (fun x => Int.natAbs (x * (-1))) = Int.natAbs := by
    ext x
    ring_nf
    exact Int.natAbs_neg x
  rw [this]

/-- **TEOREMA 2**: Writhe cambia de signo bajo reflexión.
    
    Writhe(K̄) = -Writhe(K)
 -/
theorem writhe_mirror (K : K3Config) :
    K.mirror.writhe = -K.writhe := by
  unfold writhe
  have h_dme : K.mirror.dme = K.dme.map (· * (-1)) := dme_mirror K
  rw [h_dme]
  exact foldl_sum_neg K.dme

/-- **TEOREMA 3**: La reflexión es involutiva.
    
    (K̄)̄ = K
 -/
theorem mirror_involutive (K : K3Config) :
    K.mirror.mirror = K := by
  unfold mirror
  simp only
  have h_pairs : (K.pairs.image OrderedPair.reverse).image OrderedPair.reverse = K.pairs :=
    image_reverse_twice K.pairs
  cases K
  simp [h_pairs]

/-- **TEOREMA 4**: Si Writhe ≠ 0, entonces el nudo es quiral.
    
    Writhe(K) ≠ 0 → K ≠ K̄
 -/
theorem nonzero_writhe_implies_chiral (K : K3Config) 
    (h : K.writhe ≠ 0) :
    K ≠ K.mirror := by
  intro heq
  have hw : K.writhe = K.mirror.writhe := by rw [heq]
  have hw_mirror : K.mirror.writhe = -K.writhe := writhe_mirror K
  rw [hw_mirror] at hw
  have : K.writhe + K.writhe = 0 := by
    calc K.writhe + K.writhe 
        = K.writhe + (-K.writhe) := by rw [← hw]
      _ = 0 := by ring
  have : K.writhe = 0 := by omega
  exact h this

/-! ## Corolarios Adicionales -/

/-- Corolario: Si un nudo tiene writhe no nulo, 
    su gap no cambia pero su orientación sí
 -/
theorem chiral_preserves_gap_not_dme (K : K3Config) (h : K.writhe ≠ 0) :
    K.gap = K.mirror.gap ∧ K.dme ≠ K.mirror.dme := by
  constructor
  · exact gap_mirror K
  · intro hdme
    rw [dme_mirror] at hdme
    have hw_zero : K.writhe = 0 := by
      unfold writhe
      have h_map : K.dme = K.dme.map (· * (-1)) := hdme
      have h_neg : (K.dme.map (· * (-1))).foldl (· + ·) 0 = 
                   -(K.dme.foldl (· + ·) 0) :=
        foldl_sum_neg K.dme
      rw [← h_map] at h_neg
      omega
    exact h hw_zero

/-- Corolario: Un nudo aquiral tiene writhe = 0 (contrapositiva)
 -/
theorem achiral_has_zero_writhe (K : K3Config) (h : K = K.mirror) :
    K.writhe = 0 := by
  have : K.writhe = K.mirror.writhe := by rw [h]
  rw [writhe_mirror] at this
  omega

/-! ## Resumen de Teoremas Probados

Este archivo proporciona pruebas completas y verificadas para:

1. ✅ **gap_mirror**: Gap(K̄) = Gap(K) 
   - Gap es un invariante aquiral
   - No depende de la orientación 3D

2. ✅ **writhe_mirror**: Writhe(K̄) = -Writhe(K)
   - Writhe es un invariante quiral
   - Cambia de signo bajo reflexión

3. ✅ **mirror_involutive**: (K̄)̄ = K
   - La reflexión es su propia inversa
   - Propiedad fundamental de la operación

4. ✅ **nonzero_writhe_implies_chiral**: Writhe ≠ 0 → K ≠ K̄
   - Criterio suficiente (no necesario) de quiralidad
   - Writhe = 0 no garantiza aquiralidad

## Técnicas de Prueba

- **Inducción estructural** sobre listas con acumuladores
- **Extensionalidad** de estructuras para igualdad
- **Contradicción** para pruebas de desigualdad
- **Lemas algebraicos** sobre foldl y negación
- **Omega** para aritmética lineal

## Importancia Matemática

Estos teoremas establecen las **propiedades fundamentales** del sistema de reflexión:

- Gap y IME son **invariantes aquirales** (no distinguen K de K̄)
- Writhe y DME son **invariantes quirales** (distinguen K de K̄)
- La reflexión es **involutiva** (operación bien definida)
- Writhe proporciona **test de quiralidad** (condición suficiente)

## Compilación

Este archivo es completamente standalone y puede compilarse con:

```bash
lean TCN_01_Mirror_Complete.lean
```

No requiere TCN_01_Fundamentos.lean u otros archivos externos.

-/

end K3Config
end KnotTheory
