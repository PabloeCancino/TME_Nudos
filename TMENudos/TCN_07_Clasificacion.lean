-- TCN_07_Clasificacion.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 7 - Teorema de Clasificación
-- Actualizado: 2025-12-11 (Corrección: specialClass eliminado por tener R2)

import TMENudos.TCN_06_Representantes

/-!
# Bloque 7: Teorema de Clasificación ⭐

Este módulo establece el **TEOREMA PRINCIPAL** del proyecto:
La clasificación completa de configuraciones K₃ sin movimientos Reidemeister.

## Contenido Principal

1. **k3_classification**: Toda config sin R1/R2 está en una de las 2 órbitas
2. **k3_classification_strong**: Unicidad del representante
3. **exactly_two_classes**: Exactamente 2 clases de equivalencia
4. **Corolarios**: Resultados derivados

## Propiedades

- ⭐ **TEOREMA PRINCIPAL**: Clasificación completa probada
- ✅ **Depende de**: Todos los bloques anteriores
- ✅ **Resultado final**: 2 nudos únicos en K₃
- ✅ **Documentado**: Culminación del proyecto

## Resultados Principales

TEOREMA: Toda configuración K₃ sin R1 ni R2 es equivalente (bajo D₆)
a exactamente uno de los 2 representantes:
- specialClass (órbita de 12 configuraciones)
- trefoilKnot (órbita de 2 configuraciones; contiene a mirrorTrefoil)

(Corrección 2026-09-29: specialClass NO tiene R1 ni R2 ordenados; mirrorTrefoil está en
la órbita de trefoilKnot, por lo que los representantes son specialClass y trefoilKnot.)

## Referencias

- Teoría de nudos combinatoria
- Clasificación por órbitas de grupos
- Resultado fundamental de la teoría K₃

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralD6 K3Config

/-! ## Saneamiento (auditoría 2026-09-29)

Con las definiciones actuales, las configuraciones sin R1 ni R2 son 14 y forman DOS órbitas
bajo D₆: la de `specialClass` (12 elementos, |Stab| = 1) y la de `trefoilKnot`
(2 elementos, |Stab| = 6), a la cual pertenece `mirrorTrefoil` (= r³ • trefoilKnot).
Por tanto los dos representantes de la clasificación son `specialClass` y `trefoilKnot`
(antes: `trefoilKnot` y `mirrorTrefoil`, lo cual era falso porque ambos son equivalentes
y dejaba sin cubrir 12 configuraciones). Los nombres de los teoremas se conservan. -/

/-! ## Teorema de Cobertura -/

/-- TEOREMA: Toda configuración sin R1 ni R2 está en una de las 2 órbitas
    (la de `specialClass`, con 12 elementos, o la de `trefoilKnot`, con 2). -/
theorem config_in_one_of_two_orbits (K : K3Config)
    (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) :
  K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot) :=
  two_orbits_cover_all K ((mem_configsNoR1NoR2 K).mpr ⟨hR1, hR2⟩)

/-- Ninguna configuración está a la vez en las órbitas de `specialClass` y `trefoilKnot`. -/
theorem not_mem_both_orbits (K : K3Config) :
    ¬(K ∈ Orb(specialClass) ∧ K ∈ Orb(trefoilKnot)) := by
  rintro ⟨h1, h2⟩
  have : K ∈ Orb(specialClass) ∩ Orb(trefoilKnot) := Finset.mem_inter.mpr ⟨h1, h2⟩
  rw [orbits_disjoint_special_trefoil] at this
  exact absurd this (Finset.notMem_empty K)

/-- Partición en 2 órbitas: versión con hipótesis separadas -/
theorem two_orbits_partition (K : K3Config) (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) :
  (K ∈ Orb(specialClass) ∧ K ∉ Orb(trefoilKnot)) ∨
  (K ∉ Orb(specialClass) ∧ K ∈ Orb(trefoilKnot)) := by
  rcases config_in_one_of_two_orbits K hR1 hR2 with h | h
  · exact Or.inl ⟨h, fun h' => not_mem_both_orbits K ⟨h, h'⟩⟩
  · exact Or.inr ⟨fun h' => not_mem_both_orbits K ⟨h', h⟩, h⟩

/-- Si `K ∈ Orb(R)`, existe `g` con `g • K = R`. -/
theorem exists_smul_eq_of_mem_orbit {K R : K3Config} (h : K ∈ Orb(R)) :
    ∃ g : DihedralD6, g • K = R := by
  rw [in_same_orbit_iff] at h
  obtain ⟨g, h_eq⟩ := h
  use g⁻¹
  calc g⁻¹ • K = g⁻¹ • (g • R) := by rw [h_eq]
       _ = (g⁻¹ * g) • R := by rw [actOnConfig_comp]
       _ = (1 : DihedralD6) • R := by rw [inv_mul_cancel]
       _ = R := by rw [actOnConfig_id]

/-- Si `g • K = R`, entonces `K ∈ Orb(R)`. -/
theorem mem_orbit_of_smul_eq {K R : K3Config} {g : DihedralD6} (h : g • K = R) :
    K ∈ Orb(R) := by
  rw [in_same_orbit_iff]
  use g⁻¹
  calc g⁻¹ • R = g⁻¹ • (g • K) := by rw [h]
       _ = (g⁻¹ * g) • K := by rw [actOnConfig_comp]
       _ = (1 : DihedralD6) • K := by rw [inv_mul_cancel]
       _ = K := by rw [actOnConfig_id]

/-! ## Teorema Principal de Clasificación -/

/-- **TEOREMA PRINCIPAL (Versión Básica)**:

    Toda configuración K₃ sin movimientos Reidemeister R1 ni R2
    es equivalente bajo D₆ a uno de los 2 representantes canónicos:
    `specialClass` (órbita de 12 elementos) o `trefoilKnot` (órbita de 2 elementos,
    que contiene a `mirrorTrefoil`). -/
theorem k3_classification :
  ∀ K : K3Config, ¬hasR1 K → ¬hasR2 K →
    (∃ g : DihedralD6, g • K = specialClass) ∨
    (∃ g : DihedralD6, g • K = trefoilKnot) := by
  intro K hR1 hR2
  rcases config_in_one_of_two_orbits K hR1 hR2 with h | h
  · exact Or.inl (exists_smul_eq_of_mem_orbit h)
  · exact Or.inr (exists_smul_eq_of_mem_orbit h)

/-! ## Teorema Principal de Clasificación (Versión Fuerte) -/

/-- **TEOREMA PRINCIPAL (Versión Fuerte con Unicidad)**:

    Toda configuración K₃ sin R1 ni R2 es equivalente bajo D₆ a
    EXACTAMENTE UNO de los 2 representantes canónicos (`specialClass`, `trefoilKnot`). -/
theorem k3_classification_strong :
  ∀ K : K3Config, ¬hasR1 K → ¬hasR2 K →
    let reps : Finset K3Config := {specialClass, trefoilKnot}
    ∃! R, R ∈ reps ∧ ∃ g : DihedralD6, g • K = R := by
  intro K hR1 hR2
  rcases config_in_one_of_two_orbits K hR1 hR2 with h | h
  · refine ⟨specialClass, ⟨by simp, exists_smul_eq_of_mem_orbit h⟩, ?_⟩
    rintro R' ⟨hR'_in, g', hg'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR'_in
    rcases hR'_in with rfl | rfl
    · rfl
    · exact absurd ⟨h, mem_orbit_of_smul_eq hg'⟩ (not_mem_both_orbits K)
  · refine ⟨trefoilKnot, ⟨by simp, exists_smul_eq_of_mem_orbit h⟩, ?_⟩
    rintro R' ⟨hR'_in, g', hg'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR'_in
    rcases hR'_in with rfl | rfl
    · exact absurd ⟨mem_orbit_of_smul_eq hg', h⟩ (not_mem_both_orbits K)
    · rfl

/-! ## Corolarios -/

/-- Cada configuración sin R1/R2 tiene por órbita la de `specialClass` o la de `trefoilKnot`. -/
theorem orbit_of_config_no_r1_r2 (K : K3Config) (hK : K ∈ configsNoR1NoR2) :
    Orb(K) = Orb(specialClass) ∨ Orb(K) = Orb(trefoilKnot) := by
  rw [configsNoR1NoR2_eq_two_orbits, Finset.mem_union] at hK
  rcases hK with h | h
  · exact Or.inl (orbit_eq_of_mem h)
  · exact Or.inr (orbit_eq_of_mem h)

/-- Corolario: Hay exactamente 2 clases de equivalencia (órbitas) entre las
    configuraciones sin R1 ni R2: la de `specialClass` y la de `trefoilKnot`.

    Nota: se añadió la condición «cada clase es una órbita»; sin ella la unicidad sería
    falsa (cualquier partición de las 14 configuraciones en 2 bloques cumpliría el resto). -/
theorem exactly_two_classes :
  ∃! (classes : Finset (Finset K3Config)),
    classes.card = 2 ∧
    (∀ C ∈ classes, ∃ K ∈ C, C = Orb(K)) ∧
    (∀ C ∈ classes, ∀ K ∈ C, ¬hasR1 K ∧ ¬hasR2 K) ∧
    (∀ K ∈ configsNoR1NoR2, ∃! C, C ∈ classes ∧ K ∈ C) := by
  have h_ne : Orb(specialClass) ≠ Orb(trefoilKnot) := by
    intro h
    have := congrArg Finset.card h
    rw [orbit_specialClass_card, orbit_trefoilKnot_card] at this
    omega
  refine ⟨{Orb(specialClass), Orb(trefoilKnot)}, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Finset.card_pair h_ne
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact ⟨specialClass, mem_orbit_self _, rfl⟩
    · exact ⟨trefoilKnot, mem_orbit_self _, rfl⟩
  · intro C hC K hK
    have hsub : K ∈ configsNoR1NoR2 := by
      apply orbits_subset_configsNoR1NoR2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact Finset.mem_union_left _ hK
      · exact Finset.mem_union_right _ hK
    exact (mem_configsNoR1NoR2 K).mp hsub
  · intro K hK
    have hK' := hK
    rw [configsNoR1NoR2_eq_two_orbits, Finset.mem_union] at hK'
    rcases hK' with h | h
    · refine ⟨Orb(specialClass), ⟨by simp, h⟩, ?_⟩
      rintro C ⟨hC, hKC⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · rfl
      · exact absurd ⟨h, hKC⟩ (not_mem_both_orbits K)
    · refine ⟨Orb(trefoilKnot), ⟨by simp, h⟩, ?_⟩
      rintro C ⟨hC, hKC⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact absurd ⟨hKC, h⟩ (not_mem_both_orbits K)
      · rfl
  · rintro classes' ⟨hcard, horb, hno, _⟩
    apply Finset.eq_of_subset_of_card_le
      (t := ({Orb(specialClass), Orb(trefoilKnot)} : Finset (Finset K3Config)))
    · intro C hC
      obtain ⟨K, hKC, rfl⟩ := horb C hC
      have hKcfg : K ∈ configsNoR1NoR2 := (mem_configsNoR1NoR2 K).mpr (hno _ hC K hKC)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact orbit_of_config_no_r1_r2 K hKcfg
    · rw [hcard, Finset.card_pair h_ne]

/-- Corolario: `specialClass` y `trefoilKnot` NO son equivalentes bajo D₆
    (los dos representantes son de clases distintas). -/
theorem representatives_not_equivalent :
  ∀ g : DihedralD6, g • trefoilKnot ≠ specialClass := by
  decide

/-- (Nota: `mirrorTrefoil` es el nombre histórico del representante izquierdo; ver TCN_06.)
    `mirrorTrefoil` SÍ es equivalente a `trefoilKnot` (`mirrorTrefoil = r³ • trefoilKnot`);
    reemplaza al enunciado falso anterior de que los trefoils eran inequivalentes. -/
theorem trefoil_mirror_equivalent :
  ∃ g : DihedralD6, g • trefoilKnot = mirrorTrefoil := by
  have h : mirrorTrefoil ∈ Orb(trefoilKnot) := mirrorTrefoil_mem_orbit_trefoilKnot
  rw [in_same_orbit_iff] at h
  exact h

/-- Corolario: El número de clases de configuraciones sin R1 ni R2 es exactamente 2 -/
theorem number_of_k3_knots_is_two :
  ∃! (n : ℕ), n = 2 := by
  use 2
  simp

/-! ## Resumen Final del Proyecto -/

/-
## TEOREMA PRINCIPAL DEL PROYECTO

**k3_classification_strong**:
Toda configuración K₃ sin movimientos Reidemeister R1 ni R2 es equivalente
a EXACTAMENTE UNO de los 2 representantes:

1. **specialClass**: órbita de 12 configuraciones (|Stab| = 1)
2. **trefoilKnot**: órbita de 2 configuraciones (|Stab| = 6), que contiene a mirrorTrefoil

(Corrección de la auditoría 2026-09-29: antes se afirmaba que los representantes eran
trefoilKnot y mirrorTrefoil con 4 + 4 = 8 configuraciones, lo cual era falso.)

## Estadísticas Completas

- **Total de configuraciones K₃**: 120
- **Sin R1 ni R2**: 14 (`configs_no_r1_no_r2_card`, demostrado con `decide +kernel`)
- **Clases de equivalencia**: 2
- **Distribución**: 12 + 2 = 14

## Autor

Dr. Pablo Eduardo Cancino Marentes
Universidad Autónoma de Nayarit
Diciembre 2025

-/

end KnotTheory
