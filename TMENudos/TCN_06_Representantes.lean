import TMENudos.TCN_03_Matchings
import TMENudos.TCN_05_Orbitas

/-!
# Bloque 6: Representantes Canónicos (firmados)

Representantes canónicos de las configuraciones K₃ FIRMADAS sin R1 ni R2 y su estructura de
órbitas bajo D₆ (que CONSERVA el signo).

## MIGRACIÓN (Etapa 3, signo como dato): antes → después

| Cifra | antes (sin signo) | después (signo dato) |
|---|---|---|
| configuraciones sin R1 ni R2 | 14 | 172 |
| órbitas de D₆ entre ellas | 2 (12 + 2) | 18 (doce de tamaño 12, cuatro de 6, dos de 2) |
| \|Stab(specialClass)\|, órbita | 1, 12 | 1, 12 (con signos +) |
| \|Stab(trefoilKnot)\|, órbita | 6, 2 | 6, 2 (signos +) |
| \|Stab(mirrorTrefoil)\|, órbita | 6, 2 | 6, 2 (signos −) |
| `mirrorTrefoil` en la órbita de `trefoilKnot` | SÍ (`r³ • trefoilKnot`) | **NO** (dos órbitas) |
| irreducibles con índice cero | — | 4 = 2 + 2 (las dos órbitas de tréboles) |
| configuraciones con índice cero (de 960) | — | 336 |

## Contenido Principal

1. **specialClass**: {[0,2]+, [1,4]+, [3,5]+} (irreducible, NO realizable: viola la paridad de
   Gauss y el índice cero).
2. **trefoilKnot**: trébol derecho ALTERNANTE {[0,3]+, [4,1]+, [2,5]+}.
3. **mirrorTrefoil**: trébol izquierdo = imagen especular τ (`swap`) del derecho, con signos −.
4. **Clasificación firmada**: entre las irreducibles con **índice cero** hay exactamente las
   órbitas de `trefoilKnot` y `mirrorTrefoil` (`irreducible_indexZero_iff`). Las 172 irreducibles
   sin condición de índice NO se clasifican aquí (solo se cuenta: 18 órbitas).

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open OrderedPair K3Config DihedralD6 PerfectMatching

/-! ## Los 3 Representantes Canónicos -/

/-- **specialClass**: {[0,2]+, [1,4]+, [3,5]+} (todos los signos positivos).

    Su matching subyacente es `matching1 = {{0,2}, {1,4}, {3,5}}`.  Es IRREDUCIBLE (sin R1 ni R2:
    con todos los signos iguales ningún par forma R2), pero NO es realizable: viola la paridad de
    Gauss y tiene índice ≠ 0.  Se mantiene como ejemplo de irreducible no plana.
    Con la acción de D₆ (que conserva el signo): |Stab| = 1, |Orb| = 12. -/
def specialClass : K3Config := {
  pairs := {
    OrderedPair.make 0 2 (by decide) true,
    OrderedPair.make 1 4 (by decide) true,
    OrderedPair.make 3 5 (by decide) true
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-- **trefoilKnot**: trébol derecho ALTERNANTE {[0,3]+, [4,1]+, [2,5]+}, todos los signos
    positivos (la quiralidad la da ahora el DATO `pos`).

    Recorrido en Z/6Z: 0→over, 1→under, 2→over, 3→under, 4→over, 5→under (O-U-O-U-O-U).
    Matching subyacente: {{0,3}, {2,5}, {4,1}}.  IME = {3, 3, 3}.
    |Stab| = 6, |Orb| = 2 (ver `stab_trefoil_card_actual`). -/
def trefoilKnot : K3Config := {
  pairs := {
    OrderedPair.make 0 3 (by decide) true,
    OrderedPair.make 4 1 (by decide) true,
    OrderedPair.make 2 5 (by decide) true
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-- **mirrorTrefoil**: trébol izquierdo {[3,0]−, [1,4]−, [5,2]−}.

    Es la imagen especular τ (`swap`) de `trefoilKnot` (intercambia over/under y NIEGA los
    signos): `mirrorTrefoil_eq_swap`.  MIGRACIÓN: antes (sin signo)
    `mirrorTrefoil = r³ • trefoilKnot`
    estaba en la MISMA órbita que el derecho; con el signo como dato son DOS órbitas distintas
    (`mirrorTrefoil_not_mem_orbit_trefoilKnot`).  |Stab| = 6, |Orb| = 2. -/
def mirrorTrefoil : K3Config := {
  pairs := {
    OrderedPair.make 3 0 (by decide) false,
    OrderedPair.make 1 4 (by decide) false,
    OrderedPair.make 5 2 (by decide) false
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-- `mirrorTrefoil` es la imagen especular (τ = `swap`) de `trefoilKnot`. -/
theorem mirrorTrefoil_eq_swap : mirrorTrefoil = trefoilKnot.swap := by
  decide

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

/-- specialClass no tiene R2 (con todos los signos iguales, ningún par puede formar R2). -/
theorem specialClass_no_r2_ordered : ¬hasR2 specialClass := by
  decide

/-- trefoilKnot no tiene movimiento R2 -/
theorem trefoilKnot_no_r2 : ¬hasR2 trefoilKnot := by
  decide

/-- mirrorTrefoil no tiene movimiento R2 -/
theorem mirrorTrefoil_no_r2 : ¬hasR2 mirrorTrefoil := by
  decide

/-- Los dos tréboles son configuraciones irreducibles (sin R1 ni R2) -/
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

/-! Con el signo como dato (la acción de D₆ lo conserva) los estabilizadores se RECALCULAN:
|Stab| = 1, 6, 6 para `specialClass`, `trefoilKnot`, `mirrorTrefoil`
(antes → después: 1, 6, 6 → 1, 6, 6; no cambian, porque cada representante tiene los tres signos
iguales y D₆ no los mueve). Los nombres `*_card_actual` se conservan. -/

/-- El estabilizador de specialClass es trivial: |Stab| = 1 (calculado por `decide`). -/
theorem stab_special_card_actual : (Stab(specialClass)).card = 1 := by
  unfold stabilizer
  decide

/-- El estabilizador de trefoilKnot tiene 6 elementos (calculado por `decide`). -/
theorem stab_trefoil_card_actual : (Stab(trefoilKnot)).card = 6 := by
  unfold stabilizer
  decide

/-- El estabilizador de mirrorTrefoil tiene 6 elementos (calculado por `decide`). -/
theorem stab_mirror_card_actual : (Stab(mirrorTrefoil)).card = 6 := by
  unfold stabilizer
  decide

/-- **REFORMULADO** (antes: `mirrorTrefoil_mem_orbit_trefoilKnot`,
    que con el signo dato es FALSO): el trébol izquierdo NO está en la órbita del derecho. -/
theorem mirrorTrefoil_not_mem_orbit_trefoilKnot : mirrorTrefoil ∉ Orb(trefoilKnot) := by
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

/-- **REFORMULADO** (antes: `Orb(mirrorTrefoil) = Orb(trefoilKnot)`): las órbitas de los dos
    tréboles son DISTINTAS. -/
theorem orbit_mirrorTrefoil_ne_orbit_trefoilKnot : Orb(mirrorTrefoil) ≠ Orb(trefoilKnot) := by
  intro h
  exact mirrorTrefoil_not_mem_orbit_trefoilKnot (h ▸ mem_orbit_self mirrorTrefoil)

/-! ## Tamaños de Órbitas -/

/-- La órbita de specialClass tiene 12 elementos (|Stab| = 1). (Sin cambio: 12 → 12.) -/
theorem orbit_specialClass_card : (Orb(specialClass)).card = 12 := by
  have h := orbit_stabilizer specialClass
  rw [stab_special_card_actual] at h
  omega

/-- La órbita de trefoilKnot tiene 2 elementos (|Stab| = 6). (Sin cambio: 2 → 2.) -/
theorem orbit_trefoilKnot_card : (Orb(trefoilKnot)).card = 2 := by
  have h := orbit_stabilizer trefoilKnot
  rw [stab_trefoil_card_actual] at h
  omega

/-- La órbita de mirrorTrefoil tiene 2 elementos (|Stab| = 6); es DISTINTA de la de trefoilKnot.
    (Sin cambio de cifra: 2 → 2, pero antes era la misma órbita.) -/
theorem orbit_mirrorTrefoil_card : (Orb(mirrorTrefoil)).card = 2 := by
  have h := orbit_stabilizer mirrorTrefoil
  rw [stab_mirror_card_actual] at h
  omega

/-- **REFORMULADO** (antes `two_orbits_sum_to_14 : … = 14`): las órbitas de los dos tréboles
    suman 2 + 2 = 4 configuraciones (las realizables). -/
theorem trefoil_orbits_sum_to_4 :
  (Orb(trefoilKnot)).card + (Orb(mirrorTrefoil)).card = 4 := by
  rw [orbit_trefoilKnot_card, orbit_mirrorTrefoil_card]

/-! ## Órbitas Disjuntas -/

/-- Las órbitas de specialClass y trefoilKnot son disjuntas -/
theorem orbits_disjoint_special_trefoil :
  Orb(specialClass) ∩ Orb(trefoilKnot) = ∅ := by
  have h : trefoilKnot ∉ Orb(specialClass) := by
    intro h_contra
    rw [in_same_orbit_iff] at h_contra
    obtain ⟨g, h_eq⟩ := h_contra
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

/-- **NUEVO** (con el signo dato): las órbitas de los dos tréboles son disjuntas. -/
theorem orbits_disjoint_trefoil_mirror :
  Orb(trefoilKnot) ∩ Orb(mirrorTrefoil) = ∅ :=
  orbits_disjoint trefoilKnot mirrorTrefoil
    (fun h => mirrorTrefoil_not_mem_orbit_trefoilKnot h)

/-- Las tres órbitas (specialClass, trefoilKnot, mirrorTrefoil) son disjuntas dos a dos. -/
theorem three_orbits_pairwise_disjoint :
  Orb(specialClass) ∩ Orb(trefoilKnot) = ∅ ∧
  Orb(specialClass) ∩ Orb(mirrorTrefoil) = ∅ ∧
  Orb(trefoilKnot) ∩ Orb(mirrorTrefoil) = ∅ :=
  ⟨orbits_disjoint_special_trefoil, orbits_disjoint_special_mirror,
    orbits_disjoint_trefoil_mirror⟩

/-! ## Cobertura y clasificación firmada -/

/-- Las órbitas de los tres representantes están contenidas en `configsNoR1NoR2`
    (la acción de D₆ preserva la ausencia de R1 y R2; verificado por `decide`). -/
theorem orbits_subset_configsNoR1NoR2 :
    Orb(specialClass) ∪ Orb(trefoilKnot) ∪ Orb(mirrorTrefoil) ⊆ configsNoR1NoR2 := by
  intro K hK
  rw [mem_configsNoR1NoR2]
  rw [Finset.mem_union, Finset.mem_union, in_same_orbit_iff, in_same_orbit_iff,
    in_same_orbit_iff] at hK
  rcases hK with (⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨g, rfl⟩
  · revert g
    decide
  · revert g
    decide
  · revert g
    decide

/-- **CLASIFICACIÓN FIRMADA (clave, `decide +kernel` sobre las 960 configuraciones).**

    Una configuración firmada es irreducible (sin R1 ni R2) y de índice cero SI Y SOLO SI está
    en la órbita de `trefoilKnot` (trébol derecho, signos +) o en la de `mirrorTrefoil`
    (trébol izquierdo, signos −).

    Se demuestra enumerando `Fintype K3Config` (960 configuraciones; la equivalencia con los
    subconjuntos de pares es la de `equivFinset`, ya demostrada), sin enumeraciones auxiliares.

    **Es un resultado sobre las irreducibles con índice cero, NO una clasificación de las 172
    irreducibles firmadas.** Que el índice cero caracterice la planaridad en general es una
    CONJETURA no demostrada. -/
theorem irreducible_indexZero_iff (K : K3Config) :
    (¬hasR1 K ∧ ¬hasR2 K ∧ indexZero K) ↔ (K ∈ Orb(trefoilKnot) ∨ K ∈ Orb(mirrorTrefoil)) := by
  revert K
  decide +kernel

/-- Las irreducibles de índice cero son exactamente las 2 + 2 configuraciones de las órbitas de
    los dos tréboles. -/
theorem configsNoR1NoR2_indexZero_eq :
    configsNoR1NoR2.filter (fun K => indexZero K) = Orb(trefoilKnot) ∪ Orb(mirrorTrefoil) := by
  ext K
  simp only [Finset.mem_filter, mem_configsNoR1NoR2, Finset.mem_union]
  rw [← irreducible_indexZero_iff, and_assoc]

/-- **Conteo**: hay exactamente 4 irreducibles firmadas con índice cero (antes, sin signo,
    «realizables» = 2). -/
theorem configsNoR1NoR2_indexZero_card :
    (configsNoR1NoR2.filter (fun K => indexZero K)).card = 4 := by
  rw [configsNoR1NoR2_indexZero_eq,
    Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr
      orbits_disjoint_trefoil_mirror),
    orbit_trefoilKnot_card, orbit_mirrorTrefoil_card]

/-- **Conteo de la sonda 14**: 336 de las 960 configuraciones tienen índice cero en todas las
    cuerdas (`decide +kernel`). -/
theorem indexZero_card : (Finset.univ.filter (fun K : K3Config => indexZero K)).card = 336 := by
  decide +kernel

/-- **Suma de estabilizadores sobre las 172 irreducibles firmadas: 216 = 12 · 18.**

    Por órbita-estabilizador (`orbit_stabilizer`) cada órbita `O` aporta `Σ_{K∈O} |Stab K| = 12`,
    así que esta suma es `12 ×` (número de órbitas): hay 18 órbitas de D₆ entre las 172
    irreducibles firmadas (antes, sin signo: 14 configuraciones en 2 órbitas).  Solo es un RECUENTO
    (coincide con la sonda 14: dos órbitas de tamaño 2, cuatro de 6 y doce de 12); no es una
    clasificación.  (Cálculo directo por `decide +kernel`; el conteo de órbitas como `Finset` de
    `Finset`s es mucho más caro, ver la bitácora.) -/
theorem irreducible_stabilizer_sum :
    ∑ K ∈ configsNoR1NoR2, (Stab(K)).card = 216 := by
  decide +kernel

/-! ## Relación con Matchings -/

/-- specialClass proviene de matching1 -/
theorem specialClass_from_matching1 :
  specialClass.toMatching = matching1.edges := by
  decide

/-- trefoilKnot proviene de matching2 -/
theorem trefoilKnot_from_matching2 :
  trefoilKnot.toMatching = matching2.edges := by
  decide

/-- mirrorTrefoil también proviene de matching2 (orientación y signo inversos) -/
theorem mirrorTrefoil_from_matching2 :
  mirrorTrefoil.toMatching = matching2.edges := by
  decide

/-! ## Resumen del Bloque 6 -/

/-
## Estado del Bloque (firmado)

✅ 3 representantes: specialClass (+++), trefoilKnot (+++), mirrorTrefoil (−−−, = swap)
✅ Estabilizadores: 1, 6, 6; órbitas 12, 2, 2 (las de los tréboles son DISTINTAS)
✅ Irreducibles firmadas: 172 en 18 órbitas (recuento)
✅ Irreducibles con índice cero: exactamente las 2 + 2 configuraciones de los tréboles
   (`irreducible_indexZero_iff`)

## Teoremas Principales

- `representatives_are_trivial`, `representatives_distinct`, `mirrorTrefoil_eq_swap`
- `stab_*_card_actual`, `orbit_*_card`, `trefoil_orbits_sum_to_4`
- `three_orbits_pairwise_disjoint`, `orbits_subset_configsNoR1NoR2`
- `irreducible_indexZero_iff`, `configsNoR1NoR2_indexZero_eq`, `configsNoR1NoR2_indexZero_card`
- `indexZero_card`, `irreducible_stabilizer_sum` (216 = 12 · 18 órbitas)

## Eliminados (falsos con el signo dato)

`mirrorTrefoil_mem_orbit_trefoilKnot`, `orbit_mirrorTrefoil_eq_orbit_trefoilKnot`,
`two_orbits_sum_to_14`, `two_orbits_disjoint`, `configsNoR1NoR2_eq_two_orbits`,
`two_orbits_cover_all` (las 172 irreducibles firmadas NO son dos órbitas).
-/

end KnotTheory
