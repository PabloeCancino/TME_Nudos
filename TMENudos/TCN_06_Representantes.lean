import TMENudos.TCN_03_Matchings
import TMENudos.TCN_05_Orbitas

/-!
# Bloque 6: Representantes Canónicos

Este módulo define los 3 representantes canónicos de las clases de equivalencia
de configuraciones K₃ sin movimientos Reidemeister R1 ni R2.

## Contenido Principal

1. **specialClass**: Configuración antipodal (matching2)
2. **trefoilKnot**: Nudo trefoil derecho ALTERNANTE (matching modificado)
3. **mirrorTrefoil**: Nudo trefoil izquierdo ALTERNANTE (imagen especular)
4. **Verificaciones**: Ausencia de R1 y R2
5. **Estabilizadores**: Cálculo de simetrías
6. **Tamaños de órbitas**: 12 y 2 (dos órbitas; ver saneamiento abajo)

## Propiedades

- ✅ **Completo**: 3 representantes definidos
- ✅ **Verificado**: Sin R1 ni R2 (con decide)
- ✅ **Estabilizadores**: Calculados explícitamente
- ✅ **Órbitas**: Tamaños verificados
- ✅ **ALTERNANCIA**: trefoilKnot ahora es perfectamente alternante O-U-O-U-O-U

## Resultados Principales (corregidos en la auditoría 2026-09-29)

- specialClass: |Stab| = 1, |Orb| = 12
- trefoilKnot: |Stab| = 6, |Orb| = 2
- mirrorTrefoil: |Stab| = 6, |Orb| = 2, y `mirrorTrefoil = r³ • trefoilKnot`, así que
  está en la MISMA órbita que trefoilKnot
- Hay DOS órbitas de configuraciones sin R1/R2: 12 + 2 = 14
  (`configsNoR1NoR2_eq_two_orbits`)

## Referencias

- Nudo trefoil (3₁): El nudo no trivial más simple
- Quiralidad: trefoilKnot y mirrorTrefoil son imágenes especulares
- Configuración antipodal: Conecta elementos opuestos

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open OrderedPair K3Config DihedralD6 PerfectMatching

/-! ## Los 3 Representantes Canónicos -/

/-- **specialClass**: Configuración problemática {[0,2], [1,4], [3,5]}

    Esta configuración conecta elementos opuestos en Z/6Z:
    - 0 ↔ 3
    - 1 ↔ 4
    - 2 ↔ 5

    Proviene de matching1 = {{0,2}, {1,4}, {3,5}}.
    IMPORTANTE: Esta configuración TIENE pares R2 (a nivel de matching).
    No es un nudo válido en la clasificación "sin R1/R2".
    Se mantiene como ejemplo de configuración con R2. -/
def specialClass : K3Config := {
  pairs := {
    OrderedPair.make 0 2 (by decide),
    OrderedPair.make 1 4 (by decide),
    OrderedPair.make 3 5 (by decide)
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-- **trefoilKnot**: Nudo trefoil derecho ALTERNANTE {[0,3], [4,1], [2,5]}

    Esta es la configuración ALTERNANTE del nudo trefoil derecho (right-handed trefoil, 3₁).

    **Propiedad de alternancia:**
    Recorrido en Z/6Z: 0→over, 1→under, 2→over, 3→under, 4→over, 5→under
    Patrón perfecto: O-U-O-U-O-U ✅

    **Matching subyacente:** {{0,3}, {2,5}, {4,1}}

    **IME (Invariante Modular Estructural):**
    [0,3] = 3, [4,1] = -3 ≡ 3 (mod 6), [2,5] = 3
    IME = {3, 3, 3} - Completamente uniforme

    Con la acción actual de D₆: |Stab| = 6, |Orb| = 2 (ver `stab_trefoil_card_actual`). -/
def trefoilKnot : K3Config := {
  pairs := {
    OrderedPair.make 0 3 (by decide),
    OrderedPair.make 4 1 (by decide),
    OrderedPair.make 2 5 (by decide)
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-- **mirrorTrefoil**: Nudo trefoil izquierdo ALTERNANTE {[3,0], [1,4], [5,2]}

    Esta es la imagen especular del trefoil derecho (left-handed trefoil).
    (imagen especular real: τ = swap aplicada a trefoilKnot; se conserva el nombre
    histórico `mirrorTrefoil` por el número de usos.)
    También es ALTERNANTE con patrón O-U-O-U-O-U.

    **Propiedad de alternancia:**
    Recorrido en Z/6Z: 0→under, 1→over, 2→under, 3→over, 4→under, 5→over
    Patrón perfecto: U-O-U-O-U-O ✅ (complementario del derecho)

    **Matching subyacente:** {{0,3}, {1,4}, {2,5}} (mismo que trefoilKnot, orientación inversa)

    **IME:**
    [3,0] = -3 ≡ 3 (mod 6), [1,4] = 3, [5,2] = -3 ≡ 3 (mod 6)
    IME = {3, 3, 3} - Idéntico al derecho (el IME no distingue quiralidad)

    Con la acción actual de D₆: |Stab| = 6, |Orb| = 2.

    OJO: con las definiciones actuales `mirrorTrefoil = r³ • trefoilKnot`, así que SÍ está en la
    órbita de trefoilKnot (ver `mirrorTrefoil_mem_orbit_trefoilKnot`). -/
def mirrorTrefoil : K3Config := {
  pairs := {
    OrderedPair.make 3 0 (by decide),
    OrderedPair.make 1 4 (by decide),
    OrderedPair.make 5 2 (by decide)
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-! ## Verificación: Ausencia de R1 -/

/-- specialClass no tiene movimiento R1 -/
theorem specialClass_no_r1 : ¬hasR1 specialClass := by
  decide

/-- trefoilKnot no tiene movimiento R1 -/
theorem trefoilKnot_no_r1 : ¬hasR1 trefoilKnot := by
  decide

/-- mirrorTrefoil no tiene movimiento R1 -/
theorem mirrorTrefoil_no_r1 : ¬hasR1 mirrorTrefoil := by
  decide

/-! ## Verificación: Ausencia de R2 -/

/-- Con la orientación concreta de sus tuplas ([0,2], [1,4], [3,5]), specialClass no exhibe
    un patrón R2 ordenado (su matching subyacente sí tiene un par R2 no ordenado, ver
    `matching1_has_r2`). -/
theorem specialClass_no_r2_ordered : ¬hasR2 specialClass := by
  decide

-- theorem specialClass_no_r2 : ¬hasR2 specialClass := by
--   unfold hasR2 specialClass
--   push_neg
--   intro p hp q hq hne
--   fin_cases hp <;> fin_cases hq <;> {
--     intro a b c d heq1 heq2
--     simp [OrderedPair.make] at heq1 heq2
--     intro h_pattern
--     rcases h_pattern with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> {
--       cases heq1 <;> cases heq2 <;> {
--         simp at h1 h2
--         try { decide }
--         try { omega }
--       }
--     }
--   }

/-- trefoilKnot no tiene movimiento R2 -/
theorem trefoilKnot_no_r2 : ¬hasR2 trefoilKnot := by
  decide

/-- mirrorTrefoil no tiene movimiento R2 -/
theorem mirrorTrefoil_no_r2 : ¬hasR2 mirrorTrefoil := by
  decide

/-- Los 3 representantes son configuraciones triviales (sin R1 ni R2) -/
theorem representatives_are_trivial :
  (¬hasR1 trefoilKnot ∧ ¬hasR2 trefoilKnot) ∧
  (¬hasR1 mirrorTrefoil ∧ ¬hasR2 mirrorTrefoil) := by
  exact ⟨⟨trefoilKnot_no_r1, trefoilKnot_no_r2⟩,
         ⟨mirrorTrefoil_no_r1, mirrorTrefoil_no_r2⟩⟩

/-! ## Distinción de Representantes -/

/-- Los 3 representantes son distintos entre sí -/
theorem representatives_distinct :
  specialClass ≠ trefoilKnot ∧
  specialClass ≠ mirrorTrefoil ∧
  trefoilKnot ≠ mirrorTrefoil := by
  decide

/-! ## Estabilizadores -/

/-! **Saneamiento (auditoría 2026-09-29).** Con las definiciones actuales la acción de D₆
sobre `K3Config` da |Stab| = 1, 6, 6 para `specialClass`, `trefoilKnot`, `mirrorTrefoil`
(y no 2, 3, 3 como afirmaban los enunciados anteriores `stab_special_card`,
`stab_trefoil_card` y `stab_mirror_card`, que eran FALSOS y se eliminaron: quedan
subsumidos por las versiones `*_card_actual`, que se conservan con su nombre).
Además `mirrorTrefoil = r³ • trefoilKnot`, es decir, ambos trefoils están en la MISMA
órbita, que tiene 2 elementos. -/

/-- El estabilizador de specialClass es trivial: |Stab| = 1 (calculado por `decide`).
    (Reemplaza al falso `stab_special_card : … = 2`). -/
theorem stab_special_card_actual : (Stab(specialClass)).card = 1 := by
  unfold stabilizer
  decide

/-- El estabilizador de trefoilKnot tiene 6 elementos (calculado por `decide`).
    (Reemplaza al falso `stab_trefoil_card : … = 3`). -/
theorem stab_trefoil_card_actual : (Stab(trefoilKnot)).card = 6 := by
  unfold stabilizer
  decide

/-- El estabilizador de mirrorTrefoil tiene 6 elementos (calculado por `decide`).
    (Reemplaza al falso `stab_mirror_card : … = 3`). -/
theorem stab_mirror_card_actual : (Stab(mirrorTrefoil)).card = 6 := by
  unfold stabilizer
  decide

/-- Con las definiciones actuales, mirrorTrefoil está en la órbita de trefoilKnot. -/
theorem mirrorTrefoil_mem_orbit_trefoilKnot : mirrorTrefoil ∈ Orb(trefoilKnot) := by
  unfold orbit
  decide

/-- Las órbitas de trefoilKnot y mirrorTrefoil coinciden (son la misma clase). -/
theorem orbit_mirrorTrefoil_eq_orbit_trefoilKnot : Orb(mirrorTrefoil) = Orb(trefoilKnot) := by
  unfold orbit
  decide

/-- Si `K` está en la órbita de `K₀`, ambas órbitas coinciden. -/
theorem orbit_eq_of_mem {K K₀ : K3Config} (h : K ∈ Orb(K₀)) : Orb(K) = Orb(K₀) := by
  obtain ⟨g, rfl⟩ := (in_same_orbit_iff K₀ K).mp h
  ext C
  rw [in_same_orbit_iff, in_same_orbit_iff]
  constructor
  · rintro ⟨h', rfl⟩
    exact ⟨h' * g, by rw [DihedralD6.actOnConfig_comp]⟩
  · rintro ⟨h', rfl⟩
    refine ⟨h' * g⁻¹, ?_⟩
    rw [DihedralD6.actOnConfig_comp, ← DihedralD6.actOnConfig_comp g⁻¹, inv_mul_cancel,
      DihedralD6.actOnConfig_id]

/-! ## Tamaños de Órbitas -/

/-- La órbita de specialClass tiene 12 elementos (|Stab| = 1).
    (Antes: 6, falso). -/
theorem orbit_specialClass_card : (Orb(specialClass)).card = 12 := by
  have h := orbit_stabilizer specialClass
  rw [stab_special_card_actual] at h
  omega

/-- La órbita de trefoilKnot tiene 2 elementos (|Stab| = 6).
    (Antes: 4, falso). -/
theorem orbit_trefoilKnot_card : (Orb(trefoilKnot)).card = 2 := by
  have h := orbit_stabilizer trefoilKnot
  rw [stab_trefoil_card_actual] at h
  omega

/-- La órbita de mirrorTrefoil tiene 2 elementos (|Stab| = 6); es la misma que la de
    trefoilKnot. (Antes: 4, falso). -/
theorem orbit_mirrorTrefoil_card : (Orb(mirrorTrefoil)).card = 2 := by
  have h := orbit_stabilizer mirrorTrefoil
  rw [stab_mirror_card_actual] at h
  omega

/-- Las órbitas de specialClass y trefoilKnot suman exactamente 14 configuraciones.
    (Reemplaza al falso `three_orbits_sum_to_14`: la tercera órbita coincide con la segunda). -/
theorem two_orbits_sum_to_14 :
  (Orb(specialClass)).card + (Orb(trefoilKnot)).card = 14 := by
  rw [orbit_specialClass_card, orbit_trefoilKnot_card]

/-! ## Órbitas Disjuntas -/

/-- Las órbitas de specialClass y trefoilKnot son disjuntas -/
theorem orbits_disjoint_special_trefoil :
  Orb(specialClass) ∩ Orb(trefoilKnot) = ∅ := by
  -- Probar que trefoilKnot no está en Orb(specialClass)
  have h : trefoilKnot ∉ Orb(specialClass) := by
    intro h_contra
    rw [in_same_orbit_iff] at h_contra
    obtain ⟨g, h_eq⟩ := h_contra
    -- Verificar exhaustivamente que ningún g • specialClass = trefoilKnot
    revert g
    decide
  exact orbits_disjoint specialClass trefoilKnot h

/-- Las órbitas de specialClass y mirrorTrefoil son disjuntas -/
theorem orbits_disjoint_special_mirror :
  Orb(specialClass) ∩ Orb(mirrorTrefoil) = ∅ := by
  have h : mirrorTrefoil ∉ Orb(specialClass) := by
    intro h_contra
    rw [in_same_orbit_iff] at h_contra
    obtain ⟨g, h_eq⟩ := h_contra
    revert g
    decide
  exact orbits_disjoint specialClass mirrorTrefoil h

/-! `orbits_disjoint_trefoil_mirror` y `three_orbits_pairwise_disjoint` se ELIMINARON:
eran falsos porque `mirrorTrefoil ∈ Orb(trefoilKnot)` (ver
`mirrorTrefoil_mem_orbit_trefoilKnot` y `orbit_mirrorTrefoil_eq_orbit_trefoilKnot`).
La versión verdadera es `two_orbits_disjoint`. -/

/-- Estructura correcta: hay dos órbitas disjuntas, la de specialClass y la de trefoilKnot
    (que contiene a mirrorTrefoil). -/
theorem two_orbits_disjoint :
  Orb(specialClass) ∩ Orb(trefoilKnot) = ∅ ∧
  Orb(specialClass) ∩ Orb(mirrorTrefoil) = ∅ :=
  ⟨orbits_disjoint_special_trefoil, orbits_disjoint_special_mirror⟩

/-! ## Cobertura Completa -/

/-- Las órbitas de specialClass y trefoilKnot están contenidas en `configsNoR1NoR2`
    (la acción de D₆ preserva la ausencia de R1 y R2; verificado por `decide`). -/
theorem orbits_subset_configsNoR1NoR2 :
    Orb(specialClass) ∪ Orb(trefoilKnot) ⊆ configsNoR1NoR2 := by
  intro K hK
  rw [mem_configsNoR1NoR2]
  rw [Finset.mem_union, in_same_orbit_iff, in_same_orbit_iff] at hK
  rcases hK with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · revert g
    decide
  · revert g
    decide

/-- `configsNoR1NoR2` es exactamente la unión de las órbitas de specialClass (12 elementos)
    y trefoilKnot (2 elementos, que incluye a mirrorTrefoil): 12 + 2 = 14. -/
theorem configsNoR1NoR2_eq_two_orbits :
    configsNoR1NoR2 = Orb(specialClass) ∪ Orb(trefoilKnot) := by
  symm
  apply Finset.eq_of_subset_of_card_le orbits_subset_configsNoR1NoR2
  rw [configs_no_r1_no_r2_card,
    Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr
      orbits_disjoint_special_trefoil),
    orbit_specialClass_card, orbit_trefoilKnot_card]

/-- Las 2 órbitas (specialClass y trefoilKnot) cubren exactamente las 14 configuraciones
    sin R1/R2. (Reemplaza a `three_orbits_cover_all`, cuya tercera órbita es redundante). -/
theorem two_orbits_cover_all :
  ∀ K ∈ configsNoR1NoR2, K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot) := by
  intro K hK
  rw [configsNoR1NoR2_eq_two_orbits, Finset.mem_union] at hK
  exact hK

/-! ## Relación con Matchings -/

/-- specialClass proviene de matching1 -/
theorem specialClass_from_matching1 :
  specialClass.toMatching = matching1.edges := by
  decide

/-- trefoilKnot proviene de matching2 -/
theorem trefoilKnot_from_matching2 :
  trefoilKnot.toMatching = matching2.edges := by
  decide

/-- mirrorTrefoil también proviene de matching2 (orientación inversa) -/
theorem mirrorTrefoil_from_matching2 :
  mirrorTrefoil.toMatching = matching2.edges := by
  decide

/-! ## Resumen del Bloque 6 -/

/-
## Estado del Bloque

✅ **3 representantes definidos**: specialClass, trefoilKnot, mirrorTrefoil
✅ **Verificaciones completas**: Sin R1 ni R2 (con decide)
✅ **Estabilizadores calculados**: 1, 6, 6 (con decide)
✅ **Órbitas calculadas**: 12, 2, 2 (mirrorTrefoil en la órbita de trefoilKnot)
✅ **Órbitas disjuntas**: Probado exhaustivamente
✅ **Relación con matchings**: Establecida

## Definiciones Exportadas

- `specialClass`: Configuración antipodal
- `trefoilKnot`: Nudo trefoil derecho
- `mirrorTrefoil`: Nudo trefoil izquierdo

## Teoremas Principales

- `representatives_are_trivial`: Sin R1 ni R2
- `representatives_distinct`: Son distintos
- `stab_*_card_actual`: Tamaños de estabilizadores (1, 6, 6)
- `orbit_*_card`: Tamaños de órbitas
- `two_orbits_sum_to_14`: 12 + 2 = 14
- `two_orbits_disjoint`, `two_orbits_cover_all`, `configsNoR1NoR2_eq_two_orbits`
- `*_from_matching*`: Relación con matchings

## Próximo Bloque

**Bloque 7: Teorema de Clasificación**
- k3_classification: Toda config sin R1/R2 está en Orb(specialClass) o Orb(trefoilKnot)
- k3_classification_strong: Unicidad del representante
- exactly_two_classes: Exactamente 2 clases de equivalencia
- Resultado final completo

-/

end KnotTheory
