-- TCN_07_Clasificacion.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 7 - Teorema de Clasificación (FIRMADO)
-- Etapa 3 de la migración al signo como dato (2026-09-30)

import TMENudos.TCN_06_Representantes

/-!
# Bloque 7: Teorema de Clasificación firmado ⭐

## MIGRACIÓN (Etapa 3, signo como dato): antes → después

**Antes** (sin signo): las 14 configuraciones sin R1 ni R2 formaban DOS órbitas (12 + 2) y el
teorema decía «exactamente dos clases: `specialClass` y `trefoilKnot`».

**Después** (signo dato): hay 172 irreducibles firmadas en 18 órbitas de D₆ (recuento de
`irreducible_stabilizer_sum` en TCN_06: 216 = 12 · 18), y el enunciado «las irreducibles forman
exactamente dos clases» es **FALSO**; se reformula honestamente (regla 8 del plan):

> Entre las configuraciones firmadas **irreducibles con índice cero** hay exactamente dos
> clases de D₆: el trébol derecho (`trefoilKnot`, signos +) y el trébol izquierdo
> (`mirrorTrefoil`, signos −, = su imagen especular `swap`).

No se afirma ninguna clasificación de las 172 irreducibles sin la condición de índice.
Que el índice cero caracterice la planaridad en general es una CONJETURA no demostrada; para K₃
solo se ha comprobado que, junto con la irreducibilidad, da exactamente los dos tréboles.

## Contenido Principal

1. **k3_classification**: toda irreducible de índice cero está en la órbita de uno de los
   2 tréboles.
2. **k3_classification_strong**: unicidad del representante.
3. **exactly_two_classes**: exactamente 2 clases (órbitas) entre las irreducibles de índice cero.
4. **Reformulados**: `representatives_not_equivalent`, `trefoil_mirror_not_equivalent`
   (antes `trefoil_mirror_equivalent`, que con el signo dato es falso).

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralD6 K3Config

/-! ## Teorema de Cobertura (irreducibles con índice cero) -/

/-- **TEOREMA (cobertura firmada)**: toda configuración firmada sin R1 ni R2 y de índice cero está
    en la órbita de `trefoilKnot` (derecho) o en la de `mirrorTrefoil` (izquierdo).
    (Antes: toda irreducible estaba en `Orb(specialClass)` o `Orb(trefoilKnot)`.) -/
theorem config_in_one_of_two_orbits (K : K3Config)
    (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) (hI : indexZero K) :
  K ∈ Orb(trefoilKnot) ∨ K ∈ Orb(mirrorTrefoil) :=
  (irreducible_indexZero_iff K).mp ⟨hR1, hR2, hI⟩

/-- Ninguna configuración está a la vez en las órbitas de `trefoilKnot` y `mirrorTrefoil`. -/
theorem not_mem_both_orbits (K : K3Config) :
    ¬(K ∈ Orb(trefoilKnot) ∧ K ∈ Orb(mirrorTrefoil)) := by
  rintro ⟨h1, h2⟩
  have : K ∈ Orb(trefoilKnot) ∩ Orb(mirrorTrefoil) := Finset.mem_inter.mpr ⟨h1, h2⟩
  rw [orbits_disjoint_trefoil_mirror] at this
  exact absurd this (Finset.notMem_empty K)

/-- Partición en 2 órbitas: versión con hipótesis separadas -/
theorem two_orbits_partition (K : K3Config) (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K)
    (hI : indexZero K) :
  (K ∈ Orb(trefoilKnot) ∧ K ∉ Orb(mirrorTrefoil)) ∨
  (K ∉ Orb(trefoilKnot) ∧ K ∈ Orb(mirrorTrefoil)) := by
  rcases config_in_one_of_two_orbits K hR1 hR2 hI with h | h
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

/-- **TEOREMA PRINCIPAL (Versión Básica, firmada)**:

    Toda configuración K₃ firmada sin movimientos Reidemeister R1 ni R2 y de índice cero es
    equivalente bajo D₆ a uno de los 2 tréboles: `trefoilKnot` (derecho, signos +) o
    `mirrorTrefoil` (izquierdo, signos −).

    **Antes:** sin la hipótesis de índice y con representantes `specialClass`/`trefoilKnot`.
    **Después:** se añade `indexZero K` y los representantes son los dos tréboles. -/
theorem k3_classification :
  ∀ K : K3Config, ¬hasR1 K → ¬hasR2 K → indexZero K →
    (∃ g : DihedralD6, g • K = trefoilKnot) ∨
    (∃ g : DihedralD6, g • K = mirrorTrefoil) := by
  intro K hR1 hR2 hI
  rcases config_in_one_of_two_orbits K hR1 hR2 hI with h | h
  · exact Or.inl (exists_smul_eq_of_mem_orbit h)
  · exact Or.inr (exists_smul_eq_of_mem_orbit h)

/-! ## Teorema Principal de Clasificación (Versión Fuerte) -/

/-- **TEOREMA PRINCIPAL (Versión Fuerte con Unicidad, firmada)**:

    Toda configuración firmada sin R1 ni R2 y de índice cero es equivalente bajo D₆ a
    EXACTAMENTE UNO de los 2 tréboles (`trefoilKnot`, `mirrorTrefoil`). -/
theorem k3_classification_strong :
  ∀ K : K3Config, ¬hasR1 K → ¬hasR2 K → indexZero K →
    let reps : Finset K3Config := {trefoilKnot, mirrorTrefoil}
    ∃! R, R ∈ reps ∧ ∃ g : DihedralD6, g • K = R := by
  intro K hR1 hR2 hI
  rcases config_in_one_of_two_orbits K hR1 hR2 hI with h | h
  · refine ⟨trefoilKnot, ⟨by simp, exists_smul_eq_of_mem_orbit h⟩, ?_⟩
    rintro R' ⟨hR'_in, g', hg'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR'_in
    rcases hR'_in with rfl | rfl
    · rfl
    · exact absurd ⟨h, mem_orbit_of_smul_eq hg'⟩ (not_mem_both_orbits K)
  · refine ⟨mirrorTrefoil, ⟨by simp, exists_smul_eq_of_mem_orbit h⟩, ?_⟩
    rintro R' ⟨hR'_in, g', hg'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR'_in
    rcases hR'_in with rfl | rfl
    · exact absurd ⟨mem_orbit_of_smul_eq hg', h⟩ (not_mem_both_orbits K)
    · rfl

/-! ## Corolarios -/

/-- Cada irreducible de índice cero tiene por órbita la del trébol derecho o la del izquierdo. -/
theorem orbit_of_config_no_r1_r2 (K : K3Config) (hK : K ∈ configsNoR1NoR2) (hI : indexZero K) :
    Orb(K) = Orb(trefoilKnot) ∨ Orb(K) = Orb(mirrorTrefoil) := by
  rw [mem_configsNoR1NoR2] at hK
  rcases config_in_one_of_two_orbits K hK.1 hK.2 hI with h | h
  · exact Or.inl (orbit_eq_of_mem h)
  · exact Or.inr (orbit_eq_of_mem h)

/-- Corolario: entre las irreducibles de índice cero hay exactamente 2 clases de equivalencia
    (órbitas): la del trébol derecho y la del trébol izquierdo.

    **REFORMULADO** (antes: «exactamente 2 clases entre las configuraciones sin R1 ni R2»,
    `specialClass` y `trefoilKnot`; con el signo dato las irreducibles son 172 en 18 órbitas, así
    que ese enunciado es falso).  Ahora la hipótesis «sin R1 ni R2» se acompaña de `indexZero`.

    Nota: se conserva la condición “cada clase es una órbita”; sin ella la unicidad sería falsa. -/
theorem exactly_two_classes :
  ∃! (classes : Finset (Finset K3Config)),
    classes.card = 2 ∧
    (∀ C ∈ classes, ∃ K ∈ C, C = Orb(K)) ∧
    (∀ C ∈ classes, ∀ K ∈ C, ¬hasR1 K ∧ ¬hasR2 K ∧ indexZero K) ∧
    (∀ K : K3Config, ¬hasR1 K → ¬hasR2 K → indexZero K → ∃! C, C ∈ classes ∧ K ∈ C) := by
  have h_ne : Orb(trefoilKnot) ≠ Orb(mirrorTrefoil) := fun h =>
    orbit_mirrorTrefoil_ne_orbit_trefoilKnot h.symm
  have hmem : ∀ K ∈ Orb(trefoilKnot) ∪ Orb(mirrorTrefoil),
      ¬hasR1 K ∧ ¬hasR2 K ∧ indexZero K := fun K hK =>
    (irreducible_indexZero_iff K).mpr (Finset.mem_union.mp hK)
  refine ⟨{Orb(trefoilKnot), Orb(mirrorTrefoil)}, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Finset.card_pair h_ne
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact ⟨trefoilKnot, mem_orbit_self _, rfl⟩
    · exact ⟨mirrorTrefoil, mem_orbit_self _, rfl⟩
  · intro C hC K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact hmem K (Finset.mem_union_left _ hK)
    · exact hmem K (Finset.mem_union_right _ hK)
  · intro K hR1 hR2 hI
    rcases config_in_one_of_two_orbits K hR1 hR2 hI with h | h
    · refine ⟨Orb(trefoilKnot), ⟨by simp, h⟩, ?_⟩
      rintro C ⟨hC, hKC⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · rfl
      · exact absurd ⟨h, hKC⟩ (not_mem_both_orbits K)
    · refine ⟨Orb(mirrorTrefoil), ⟨by simp, h⟩, ?_⟩
      rintro C ⟨hC, hKC⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact absurd ⟨hKC, h⟩ (not_mem_both_orbits K)
      · rfl
  · rintro classes' ⟨hcard, horb, hno, _⟩
    apply Finset.eq_of_subset_of_card_le
      (t := ({Orb(trefoilKnot), Orb(mirrorTrefoil)} : Finset (Finset K3Config)))
    · intro C hC
      obtain ⟨K, hKC, rfl⟩ := horb C hC
      have h3 := hno _ hC K hKC
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (irreducible_indexZero_iff K).mp h3 with h | h
      · exact Or.inl (orbit_eq_of_mem h)
      · exact Or.inr (orbit_eq_of_mem h)
    · rw [hcard, Finset.card_pair h_ne]

/-- Corolario: `specialClass` y `trefoilKnot` NO son equivalentes bajo D₆. -/
theorem representatives_not_equivalent :
  ∀ g : DihedralD6, g • trefoilKnot ≠ specialClass := by
  decide

/-- **REFORMULADO** (antes `trefoil_mirror_equivalent : ∃ g, g • trefoilKnot = mirrorTrefoil`,
    que con el signo dato es FALSO: los dos tréboles son quirales distintos y D₆ conserva el
    signo).  Ahora: el trébol derecho y el izquierdo NO son equivalentes bajo D₆. -/
theorem trefoil_mirror_not_equivalent :
  ∀ g : DihedralD6, g • trefoilKnot ≠ mirrorTrefoil := by
  intro g h
  exact mirrorTrefoil_not_mem_orbit_trefoilKnot
    ((in_same_orbit_iff trefoilKnot mirrorTrefoil).mpr ⟨g, h⟩)

/-- Corolario (tautológico, conservado por compatibilidad): existe un único `n` igual a 2.
    El contenido matemático está en `exactly_two_classes`. -/
theorem number_of_k3_knots_is_two :
  ∃! (n : ℕ), n = 2 := by
  use 2
  simp

/-! ## Resumen Final -/

/-
## TEOREMA PRINCIPAL (firmado)

**k3_classification_strong**:
Toda configuración K₃ firmada sin movimientos Reidemeister R1 ni R2 y de índice cero es
equivalente a EXACTAMENTE UNO de los 2 tréboles:

1. **trefoilKnot**: órbita de 2 configuraciones (|Stab| = 6), signos +
2. **mirrorTrefoil**: órbita de 2 configuraciones (|Stab| = 6), signos −, imagen especular

## Estadísticas completas (antes → después)

- Total de configuraciones K₃: 120 → 960
- Sin R1 ni R2: 14 → 172 (en 18 órbitas; NO se clasifican)
- Sin R1 ni R2 y con índice cero: — → 4 (en 2 órbitas)
- Clases de equivalencia (irreducibles con índice cero): 2 → 2 (pero ahora son los dos tréboles
  y no `specialClass`/`trefoilKnot`)

La órbita de `specialClass` (12 configuraciones) sigue siendo irreducible pero ya no entra en
ningún enunciado de clasificación: no cumple la paridad de Gauss ni el índice cero.

## Autor

Dr. Pablo Eduardo Cancino Marentes
-/

end KnotTheory
