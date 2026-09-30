-- TCN_AUX_Teoremas_Auxiliares_Realizabilidad.lean
-- Teoremas auxiliares necesarios para completar TCN_08_Realizabilidad.lean
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Diciembre 21, 2025

import TMENudos.TCN_02_Reidemeister
import TMENudos.TCN_05_Orbitas
import TMENudos.TCN_06_Representantes
import TMENudos.TCN_07_Clasificacion

/-!
# Teoremas Auxiliares para el Módulo de Realizabilidad

Este archivo contiene todos los teoremas auxiliares que deben agregarse
a los módulos existentes para completar TCN_08_Realizabilidad.lean
sin `sorry` statements.

## Organización

1. **Para TCN_05_Orbitas.lean**: Transitividad y clausura de órbitas
2. **Para TCN_02_Reidemeister.lean**: Preservación de R1/R2 bajo D₆
3. **Para TCN_07_Clasificacion.lean**: Disjunción de órbitas
4. **Lemmas de partición**: Propiedades de Finset

-/

namespace KnotTheory

/-- Abreviatura del grupo diédrico D₆. -/
abbrev D6 : Type := DihedralD6

open OrderedPair K3Config DihedralD6

/-! ## 1. TEOREMAS PARA TCN_05_Orbitas.lean -/

section OrbitTheorems

variable {K R S : K3Config}

/- **TEOREMA CLAVE 1: Transitividad de Órbitas** (`orbit_eq_of_mem`)

    Si K está en la órbita de R, entonces la órbita de K es igual a la órbita de R.
    Se MOVIÓ a `TCN_06_Representantes.lean` (auditoría 2026-09-29), porque TCN_07 lo necesita;
    se usa aquí desde ese módulo. -/

/-- **TEOREMA CLAVE 2: Pertenencia a Órbita e Igualdad de Órbitas** -/
theorem orbit_eq_iff_mem : K ∈ orbit R ↔ orbit K = orbit R := by
  constructor
  · exact orbit_eq_of_mem
  · intro h
    rw [← h]
    exact mem_orbit_self K

/-- **TEOREMA CLAVE 3: Clausura de Órbitas bajo Acción**

    Si K está en la órbita de R, entonces g • K también está en la órbita de R. -/
theorem mem_orbit_of_smul_mem (h : K ∈ orbit R) (g : D6) :
    (g • K) ∈ orbit R := by
  obtain ⟨h, hK⟩ := (in_same_orbit_iff R K).mp h
  rw [in_same_orbit_iff]
  refine ⟨g * h, ?_⟩
  rw [actOnConfig_comp, hK]

/-- **TEOREMA CLAVE 4: La Órbita es Cerrada bajo la Acción** -/
theorem orbit_closed_under_action (g : D6) :
    S ∈ orbit K → (g • S) ∈ orbit K :=
  fun h => mem_orbit_of_smul_mem h g

/-- **COROLARIO: la imagen de una órbita bajo g es la misma órbita.** -/
theorem smul_orbit_eq_orbit (g : D6) :
    (orbit K).image (fun x => g • x) = orbit K := by
  ext S
  rw [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact orbit_closed_under_action g hT
  · intro hS
    refine ⟨g⁻¹ • S, orbit_closed_under_action g⁻¹ hS, ?_⟩
    rw [← actOnConfig_comp, mul_inv_cancel, actOnConfig_id]

end OrbitTheorems

/-! ## 2. TEOREMAS PARA TCN_02_Reidemeister.lean -/

section ReidemeisterPreservation

variable {K : K3Config} {g : D6}

/-- **TEOREMA CLAVE 5: D₆ Preserva Consecutividad**

    Un par es consecutivo si y solo si su imagen bajo D₆ es consecutiva. -/
theorem isConsecutive_of_rotate_iff (p : OrderedPair) (g : D6) :
    isConsecutive (actOnPair g p) ↔ isConsecutive p := by
  rcases g with k | k <;>
  · simp only [isConsecutive, actOnPair_fst, actOnPair_snd, actionZMod]
    constructor <;> rintro (h | h) <;>
    first
    | (left; linear_combination h)
    | (left; linear_combination -h)
    | (right; linear_combination h)
    | (right; linear_combination -h)

/-- **TEOREMA CLAVE 6: Acción de D₆ Preserva hasR1** -/
theorem hasR1_iff_of_smul : hasR1 (g • K) ↔ hasR1 K := by
  have hp : (g • K).pairs = K.pairs.image (actOnPair g) := rfl
  unfold hasR1
  rw [hp]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨q, hq, (isConsecutive_of_rotate_iff q g).mp hc⟩
  · rintro ⟨p, hp, hc⟩
    exact ⟨actOnPair g p, Finset.mem_image_of_mem _ hp,
      (isConsecutive_of_rotate_iff p g).mpr hc⟩

/-- D₆ preserva el patrón R2 entre dos pares. -/
theorem formsR2Pattern_actOnPair_iff (p q : OrderedPair) (g : D6) :
    formsR2Pattern (actOnPair g p) (actOnPair g q) ↔ formsR2Pattern p q := by
  rcases g with k | k
  · have e1 : ∀ a b : ZMod 6, a + k = b + k + 1 ↔ a = b + 1 := fun a b => by
      constructor <;> intro h <;> linear_combination h
    have e2 : ∀ a b : ZMod 6, a + k = b + k - 1 ↔ a = b - 1 := fun a b => by
      constructor <;> intro h <;> linear_combination h
    simp only [formsR2Pattern, actOnPair_fst, actOnPair_snd, actionZMod, e1, e2]
  · have e1 : ∀ a b : ZMod 6, -(a + k) = -(b + k) + 1 ↔ a = b - 1 := fun a b => by
      constructor <;> intro h <;> linear_combination -h
    have e2 : ∀ a b : ZMod 6, -(a + k) = -(b + k) - 1 ↔ a = b + 1 := fun a b => by
      constructor <;> intro h <;> linear_combination -h
    simp only [formsR2Pattern, actOnPair_fst, actOnPair_snd, actionZMod, e1, e2]
    tauto

/-- **TEOREMA CLAVE 7: Acción de D₆ Preserva hasR2** -/
theorem hasR2_iff_of_smul : hasR2 (g • K) ↔ hasR2 K := by
  have hp : (g • K).pairs = K.pairs.image (actOnPair g) := rfl
  unfold hasR2
  rw [hp]
  constructor
  · rintro ⟨p, hp, q, hq, hne, hf⟩
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact ⟨p', hp', q', hq', fun h => hne (by rw [h]),
      (formsR2Pattern_actOnPair_iff p' q' g).mp hf⟩
  · rintro ⟨p, hp, q, hq, hne, hf⟩
    exact ⟨actOnPair g p, Finset.mem_image_of_mem _ hp, actOnPair g q,
      Finset.mem_image_of_mem _ hq, fun h => hne ((actOnPair_injective g) h),
      (formsR2Pattern_actOnPair_iff p q g).mpr hf⟩

/-- **TEOREMA CLAVE 8: Preservación de R1 en Órbitas** -/
theorem hasR1_eq_of_mem_orbit {R : K3Config} (h : K ∈ orbit R) :
    hasR1 K ↔ hasR1 R := by
  obtain ⟨g, hg⟩ := (in_same_orbit_iff R K).mp h
  rw [← hg]
  exact hasR1_iff_of_smul

/-- **TEOREMA CLAVE 9: Preservación de R2 en Órbitas** -/
theorem hasR2_eq_of_mem_orbit {R : K3Config} (h : K ∈ orbit R) :
    hasR2 K ↔ hasR2 R := by
  obtain ⟨g, hg⟩ := (in_same_orbit_iff R K).mp h
  rw [← hg]
  exact hasR2_iff_of_smul

end ReidemeisterPreservation

/-! ## 3. TEOREMAS PARA TCN_07_Clasificacion.lean -/

section ClassificationTheorems
/-- **COROLARIO: Los representantes son distintos**

    trefoilKnot no está en la órbita de specialClass.

    (Auditoría 2026-09-29: el enunciado anterior `trefoil_not_in_mirror_orbit` era FALSO,
    pues `mirrorTrefoil ∈ Orb(trefoilKnot)`; se eliminó y se reemplazó por este.) -/
theorem trefoil_not_in_special_orbit :
    trefoilKnot ∉ orbit specialClass := by
  intro h
  have hmem : trefoilKnot ∈ orbit specialClass ∩ orbit trefoilKnot :=
    Finset.mem_inter.mpr ⟨h, mem_orbit_self _⟩
  rw [orbits_disjoint_special_trefoil] at hmem
  exact absurd hmem (Finset.notMem_empty _)

end ClassificationTheorems

/-! ## 4. LEMMAS DE PARTICIÓN PARA FINSET -/

section PartitionLemmas

variable {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]

/-- **LEMMA 1: Partición por Predicado Decidible** -/
theorem finset_partition_by_decidable [DecidableEq α] :
    s = s.filter p ∪ s.filter (¬p ·) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

/-- **LEMMA 2: Disjunción de Filtros Complementarios** -/
theorem finset_filter_disjoint :
    Disjoint (s.filter p) (s.filter (¬p ·)) :=
  Finset.disjoint_filter_filter_not s s p

/-- **LEMMA 3: Cardinalidad de Partición** -/
theorem finset_card_partition :
    s.card = (s.filter p).card + (s.filter (¬p ·)).card :=
  (Finset.card_filter_add_card_filter_not p).symm

/-- **LEMMA 4: Filtro de Univ** -/
theorem finset_univ_filter_eq {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Finset.univ.filter p = {x | p x}.toFinset := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_setOf_eq]

end PartitionLemmas

end KnotTheory

/-!
## Resumen de Teoremas Auxiliares

### Para agregar a TCN_05_Orbitas.lean
1. `orbit_eq_of_mem`: (ahora en TCN_06) K ∈ Orb(R) ⟹ Orb(K) = Orb(R)
2. `orbit_eq_iff_mem`: K ∈ Orb(R) ⟺ Orb(K) = Orb(R)
3. `mem_orbit_of_smul_mem`: K ∈ Orb(R) ⟹ g•K ∈ Orb(R)
4. `orbit_closed_under_action`: S ∈ Orb(K) ⟹ g•S ∈ Orb(K)
5. `smul_orbit_eq_orbit`: g • Orb(K) = Orb(K)

### Para agregar a TCN_02_Reidemeister.lean
6. `isConsecutive_of_rotate_iff`: Rotación preserva consecutividad
7. `hasR1_iff_of_smul`: g•K tiene R1 ⟺ K tiene R1
8. `hasR2_iff_of_smul`: g•K tiene R2 ⟺ K tiene R2
9. `hasR1_eq_of_mem_orbit`: Órbitas preservan R1
10. `hasR2_eq_of_mem_orbit`: Órbitas preservan R2

### Para agregar a TCN_07_Clasificacion.lean
11. `orbits_disjoint_special_trefoil`: Órbitas disjuntas (TCN_06)
12. `trefoil_not_in_special_orbit`: Representantes distintos

### Lemmas de Finset (ya en Mathlib o triviales)
13. `finset_partition_by_decidable`: Partición por predicado
14. `finset_filter_disjoint`: Filtros complementarios disjuntos
15. `finset_card_partition`: Fórmula de cardinalidad

## Estado
- ✅ Estructura completa
- ✅ Teoremas 1-10 demostrados (sin sorry propios)
- 🎯 Una vez completados, eliminan TODOS los sorry de TCN_08

## Nota (revisión Opción 1, paridad de Gauss)
Ninguno de estos enunciados cambia: son sobre órbitas, R1/R2 y particiones de `Finset`,
independientes de la definición de «realizable».  Se usan en `TCN_08_Realizabilidad`,
donde `isRealizable` pasó de «sin R1 ni R2» (14 configuraciones) a «sin R1 ni R2 y
`gaussEven`» (2 configuraciones, la órbita del trébol).  `trefoil_not_in_special_orbit`
sigue siendo cierto y ahora expresa que el representante realizable no está en la órbita
de `specialClass`, que es no realizable.

-/
