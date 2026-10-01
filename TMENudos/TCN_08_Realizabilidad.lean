-- TCN_08_Realizabilidad.lean
-- Teoría Combinatoria de Nudos K₃: Teorema de Realizabilidad (FIRMADO)
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Diciembre 21, 2025
-- Revisión (Opción 1, paridad de Gauss): "realizable" excluye la órbita de `specialClass`.
-- Revisión Etapa 3 (2026-09-30, signo como dato): "realizable" = irreducible ∧ gaussEven ∧ indexZero.

import TMENudos.TCN_05_Orbitas
import TMENudos.TCN_06_Representantes
import TMENudos.TCN_07_Clasificacion
import TMENudos.TCN_AUX_Teoremas_Auxiliares_Realizabilidad
import Mathlib.Data.Finset.Card

/-!
# Teorema de Realizabilidad para Configuraciones K₃ firmadas

Este módulo formaliza el **criterio de órbitas de grupo** para el problema
de realizabilidad de códigos de Gauss, ahora con el signo del cruce como DATO.

## DECISIÓN DE DISEÑO (Etapa 3, regla 8): el tipo es libre, la clasicidad es un PREDICADO

El tipo firmado `K3Config` tiene 960 configuraciones, sin restringir.  Una configuración es
**realizable** (candidata a diagrama de nudo clásico) cuando cumple tres condiciones:

1. **irreducible**: sin R1 y sin R2 (R2 exige signos opuestos);
2. **`gaussEven`**: paridad de Gauss (no mira el signo);
3. **`indexZero`**: el índice de toda cuerda es 0 (SÍ mira el signo).

Ambas condiciones (2) y (3) son NECESARIAS de planaridad.  **Conjetura NO demostrada**: que el
índice cero (junto con la paridad de Gauss) caracterice la planaridad en general; para K₃ se ha
comprobado por cálculo que el conjunto resultante es exactamente el de los dos tréboles.

**Resultado:** `realizable_iff_trefoil_orbits`: realizable ⟺ `K ∈ Orb(trefoilKnot) ∪
Orb(mirrorTrefoil)`, 4 configuraciones en 2 órbitas de tamaño 2.

## Cambios de enunciado (antes → después)

Cifras:

| Cifra | antes | después |
|---|---|---|
| configuraciones K₃ | 120 | 960 |
| irreducibles (sin R1 ni R2) | 14 (12 + 2) | 172 (18 órbitas) |
| realizables | 2 (órbita de `trefoilKnot`) | 4 (2 + 2: órbitas de ambos tréboles) |
| fracción de realizables | 1/60 (= 2/120) | 1/240 (= 4/960) |
| no realizables | 118 | 956 |
| irreducibles no realizables | 12 | 168 (= 172 − 4; incluye la órbita de 12 de `specialClass`) |

Enunciados:

- `card_k3_config`: `Fintype.card K3Config = 120` → `= 960` (ahora se reduce a
  `K3Config.card_eq_960`; ya no hace falta la enumeración por `allOrderedPairs`).
- `isRealizable`: `(¬hasR1 ∧ ¬hasR2) ∧ gaussEven` → `(¬hasR1 ∧ ¬hasR2) ∧ gaussEven ∧ indexZero`.
- `realizable_iff_trefoil_orbit : isRealizable K ↔ K ∈ orbit trefoilKnot` → **FALSO** con el signo
  dato (el trébol izquierdo está en otra órbita); se reformula como
  `realizable_iff_trefoil_orbits : … ↔ K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil`.
- `realizableConfigs`: `Orb(trefoilKnot)` → `Orb(trefoilKnot) ∪ Orb(mirrorTrefoil)`.
- `total_realizable_configs`: `= 2` → `= 4`;  `realizable_fraction`: `1/60` → `1/240`;
  `non_realizable_count`: `118` → `956`;  `irreducible_not_realizable_count`: `12` → `168`.
- `configsNoR1NoR2_eq_realizable_union_special` (falso: las irreducibles son 172, no 4 + 12) →
  ELIMINADO; sustituido por `realizableConfigs_subset_configsNoR1NoR2` y
  `realizable_eq_irreducible_indexZero`.
- `realizable_orbit_card_eq_two`, `realizable_orbit_card_cases`: se conservan (la órbita sigue
  teniendo 2 elementos).
- `irreducible_realizable_iff`: `… ↔ K ∈ orbit trefoilKnot` → `… ↔ K ∈ orbit trefoilKnot ∨
  K ∈ orbit mirrorTrefoil` (y nuevo `irreducible_realizable_iff_indexZero`:
  para irreducibles, realizable ⟺ índice cero).
- `k3_realizability_characterization`, `realizable_iff_representative`,
  `realizable_by_transformation`, `only_trefoil_orbit_realizable`
  (→ `only_trefoil_orbits_realizable`):
  se amplían a los dos tréboles.
- `not_realizable_criterion`: `hasR1 ∨ hasR2 ∨ ¬gaussEven` → `… ∨ ¬indexZero`.
- `irreducible_dichotomy` (`realizable ∨ K ∈ Orb(specialClass)`, FALSO ahora: hay 156 irreducibles
  no realizables fuera de esa órbita) → ELIMINADO; sustituido por
  `irreducible_dichotomy_indexZero` y `irreducible_realizable_iff_indexZero`.
- `irreducible_realizable_iff_not_special` (FALSO ahora) → ELIMINADO.
- `realizable_preserved_by_D6`: mismo enunciado, nueva demostración (vía las órbitas).

## Contexto Histórico

El **problema de realizabilidad** (Gauss, siglo XIX): no toda configuración combinatoria que
satisface A1-A4 es realizable.  Condiciones conocidas (paridad de Gauss, Dehn, Whitney) son
necesarias pero NO suficientes en general.

## Referencias

- TCN_05_Orbitas.lean: teorema órbita-estabilizador y predicados `gaussEven`, `indexZero`
- TCN_07_Clasificacion.lean: clasificación firmada
- `Procesos/Tests/auditoria_20260929/14_conteos_k3_firmados.py`: sonda de conteos

-/

namespace KnotTheory

open OrderedPair K3Config DihedralD6

/-! ## 0. Instancias de finitud para K₃Config -/

/-- Hay exactamente 960 configuraciones K₃ firmadas (5!! · 2³ · 2³ = 15 · 8 · 8).

    MIGRACIÓN (cifra): antes → después: 120 → 960.  Ya NO se cuenta aquí por
    `allOrderedPairs.powersetCard 3`: el conteo es `K3Config.card_eq_960` (TCN_01). -/
theorem card_k3_config : Fintype.card K3Config = 960 :=
  K3Config.card_eq_960

/-! ## 0.5. Paridad de Gauss e índice cero

Las definiciones de `strictlyBetween`, `chordsInterlace`, `gaussEven`, `inArc`, `chordIndex`,
`indexZero` están en `TCN_05_Orbitas` (TCN_07 ya necesita `indexZero`).  Aquí quedan sus
propiedades de invariancia. -/

/-- El entrelazamiento de dos parejas es invariante bajo D₆ (rotaciones y reflexiones
    de `actionZMod`).  Se decide sobre todos los valores de `ZMod 6` (12 acciones).
    No depende del signo. -/
theorem chordsInterlace_actOnPair (g : D6) (p q : OrderedPair) :
    chordsInterlace (actOnPair g p) (actOnPair g q) ↔ chordsInterlace p q := by
  have key1 : ∀ i a b c d : ZMod 6,
      (((a + i ≠ c + i ∧ a + i ≠ d + i ∧ b + i ≠ c + i ∧ b + i ≠ d + i) ∧
        (strictlyBetween (a + i) (b + i) (c + i) ↔ ¬ strictlyBetween (a + i) (b + i) (d + i))) ↔
      ((a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) ∧
        (strictlyBetween a b c ↔ ¬ strictlyBetween a b d))) := by decide +kernel
  have key2 : ∀ i a b c d : ZMod 6,
      (((-(a + i) ≠ -(c + i) ∧ -(a + i) ≠ -(d + i) ∧ -(b + i) ≠ -(c + i) ∧
          -(b + i) ≠ -(d + i)) ∧
        (strictlyBetween (-(a + i)) (-(b + i)) (-(c + i)) ↔
          ¬ strictlyBetween (-(a + i)) (-(b + i)) (-(d + i)))) ↔
      ((a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) ∧
        (strictlyBetween a b c ↔ ¬ strictlyBetween a b d))) := by decide +kernel
  rcases g with i | i
  · exact key1 i p.fst p.snd q.fst q.snd
  · exact key2 i p.fst p.snd q.fst q.snd

/-- **Invariancia de la paridad de Gauss bajo D₆**: `g • K` cumple `gaussEven` sii `K` lo cumple. -/
theorem gaussEven_iff_of_smul (g : D6) (K : K3Config) : gaussEven (g • K) ↔ gaussEven K := by
  have hp : (g • K).pairs = K.pairs.image (actOnPair g) := rfl
  have hcard : ∀ p ∈ K.pairs,
      (((g • K).pairs).filter (chordsInterlace (actOnPair g p))).card =
        (K.pairs.filter (chordsInterlace p)).card := by
    intro p _
    rw [hp, Finset.filter_image]
    rw [Finset.card_image_of_injective _ (actOnPair_injective g)]
    congr 1
    apply Finset.filter_congr
    intro q _
    exact chordsInterlace_actOnPair g p q
  unfold gaussEven
  constructor
  · intro h p hpK
    rw [← hcard p hpK]
    apply h
    rw [hp]; exact Finset.mem_image_of_mem _ hpK
  · intro h p' hp'
    rw [hp] at hp'
    obtain ⟨p, hpK, rfl⟩ := Finset.mem_image.mp hp'
    rw [hcard p hpK]
    exact h p hpK

/-- `gaussEven` es propiedad de la órbita. -/
theorem gaussEven_iff_of_mem_orbit {K R : K3Config} (h : K ∈ orbit R) :
    gaussEven K ↔ gaussEven R := by
  obtain ⟨g, hg⟩ := (in_same_orbit_iff R K).mp h
  rw [← hg]
  exact gaussEven_iff_of_smul g R

/-- El trébol derecho cumple la paridad de Gauss. -/
theorem gaussEven_trefoilKnot : gaussEven trefoilKnot := by decide +kernel

/-- El trébol izquierdo cumple la paridad de Gauss. -/
theorem gaussEven_mirrorTrefoil : gaussEven mirrorTrefoil := by decide +kernel

/-- `specialClass` NO cumple la paridad de Gauss. -/
theorem not_gaussEven_specialClass : ¬gaussEven specialClass := by decide +kernel

/-- El trébol derecho tiene índice cero. -/
theorem indexZero_trefoilKnot : indexZero trefoilKnot := by decide +kernel

/-- El trébol izquierdo tiene índice cero. -/
theorem indexZero_mirrorTrefoil : indexZero mirrorTrefoil := by decide +kernel

/-- `specialClass` NO tiene índice cero (con todos los signos +). -/
theorem not_indexZero_specialClass : ¬indexZero specialClass := by decide +kernel

/-- Ninguna configuración de `Orb(specialClass)` cumple la paridad de Gauss
    (no son diagramas de nudos clásicos). -/
theorem not_gaussEven_of_mem_orbit_special {K : K3Config} (h : K ∈ orbit specialClass) :
    ¬gaussEven K := by
  rw [gaussEven_iff_of_mem_orbit h]
  exact not_gaussEven_specialClass

/-- Un trébol de signos mixtos `{[0,3]+, [4,1]+, [2,5]−}` pasa la paridad de Gauss pero NO el
    índice cero: es el ejemplo que justifica la condición de índice (regla 8). -/
def mixedTrefoil : K3Config := {
  pairs := {
    OrderedPair.make 0 3 (by decide) true,
    OrderedPair.make 4 1 (by decide) true,
    OrderedPair.make 2 5 (by decide) false
  }
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card _ _ (by revert i; decide)
}

/-- El trébol mixto es irreducible y cumple la paridad de Gauss, pero no tiene índice cero. -/
theorem mixedTrefoil_irreducible_gauss_not_indexZero :
    (¬hasR1 mixedTrefoil ∧ ¬hasR2 mixedTrefoil) ∧ gaussEven mixedTrefoil ∧
      ¬indexZero mixedTrefoil := by
  decide +kernel

/-! ## 1. Definiciones Básicas -/

/-- Una configuración K₃ firmada es **realizable** (como diagrama de nudo clásico) si es
    irreducible (sin R1 ni R2, con R2 de signos opuestos), cumple la paridad de Gauss y tiene
    índice cero.

    **Elección de forma (documentada):** conjunción de PREDICADOS sobre el tipo libre `K3Config`
    (regla 8); la equivalencia con las órbitas de los dos tréboles es un teorema
    (`realizable_iff_trefoil_orbits`), que se apoya en `irreducible_indexZero_iff` (TCN_06).

    **Antes:** `(¬hasR1 ∧ ¬hasR2) ∧ gaussEven` (2 configuraciones).
    **Después:** `… ∧ gaussEven ∧ indexZero` (4 configuraciones).

    **Advertencia:** `gaussEven` e `indexZero` son sólo NECESARIAS de planaridad; que el índice
    cero (con paridad de Gauss) caracterice la planaridad en general es una CONJETURA no
    demostrada.  Para K₃ la lista resultante es exactamente la de los dos tréboles. -/
def isRealizable (K : K3Config) : Prop :=
  (¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K ∧ indexZero K

/-- Conjunto de todas las configuraciones K₃ realizables: las órbitas del trébol derecho y del
    izquierdo, 2 + 2 = 4 elementos.  (Antes: sólo `Orb(trefoilKnot)`, 2 elementos.) -/
def realizableConfigs : Finset K3Config :=
  orbit trefoilKnot ∪ orbit mirrorTrefoil

/-! ### Decidibilidad -/

/-- La realizabilidad es decidible para cualquier configuración K₃. -/
instance (K : K3Config) : Decidable (isRealizable K) :=
  inferInstanceAs (Decidable ((¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K ∧ indexZero K))

/-- La pertenencia a `realizableConfigs` es decidible -/
instance (K : K3Config) : Decidable (K ∈ realizableConfigs) :=
  inferInstanceAs (Decidable (K ∈ orbit trefoilKnot ∪ orbit mirrorTrefoil))

/-! ### Realizable ⟺ órbitas de los tréboles -/

/-- En una irreducible de índice cero la paridad de Gauss es automática: pertenece a una de las
    órbitas de los tréboles, que la cumplen. -/
theorem gaussEven_of_irreducible_indexZero {K : K3Config}
    (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) (hI : indexZero K) : gaussEven K := by
  rcases config_in_one_of_two_orbits K hR1 hR2 hI with h | h
  · rw [gaussEven_iff_of_mem_orbit h]; exact gaussEven_trefoilKnot
  · rw [gaussEven_iff_of_mem_orbit h]; exact gaussEven_mirrorTrefoil

/-- **TEOREMA PRINCIPAL (firmado):** una configuración K₃ firmada es realizable si y sólo si está
    en la órbita del trébol derecho (`trefoilKnot`, signos +) o del izquierdo
    (`mirrorTrefoil`, signos −).

    **REFORMULADO** (antes `realizable_iff_trefoil_orbit : isRealizable K ↔ K ∈ orbit trefoilKnot`,
    que con el signo dato deja fuera al trébol izquierdo). -/
theorem realizable_iff_trefoil_orbits (K : K3Config) :
    isRealizable K ↔ K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil := by
  constructor
  · rintro ⟨⟨hR1, hR2⟩, _, hI⟩
    exact (irreducible_indexZero_iff K).mp ⟨hR1, hR2, hI⟩
  · intro h
    obtain ⟨hR1, hR2, hI⟩ := (irreducible_indexZero_iff K).mpr h
    exact ⟨⟨hR1, hR2⟩, gaussEven_of_irreducible_indexZero hR1 hR2 hI, hI⟩

/-- Realizable ⟺ irreducible con índice cero (la paridad de Gauss es consecuencia). -/
theorem realizable_eq_irreducible_indexZero (K : K3Config) :
    isRealizable K ↔ (¬hasR1 K ∧ ¬hasR2 K ∧ indexZero K) :=
  (realizable_iff_trefoil_orbits K).trans (irreducible_indexZero_iff K).symm

/-- El trébol derecho es realizable (no vacuidad). -/
theorem isRealizable_trefoilKnot : isRealizable trefoilKnot :=
  (realizable_iff_trefoil_orbits _).mpr (Or.inl (mem_orbit_self _))

/-- El trébol izquierdo es realizable. -/
theorem isRealizable_mirrorTrefoil : isRealizable mirrorTrefoil :=
  (realizable_iff_trefoil_orbits _).mpr (Or.inr (mem_orbit_self _))

/-- `specialClass` NO es realizable. -/
theorem specialClass_not_realizable : ¬isRealizable specialClass := fun h =>
  not_gaussEven_specialClass h.2.1

/-- Ninguna configuración de `Orb(specialClass)` es realizable (las 12). -/
theorem orbit_specialClass_not_realizable {K : K3Config} (h : K ∈ orbit specialClass) :
    ¬isRealizable K := fun hr =>
  not_gaussEven_of_mem_orbit_special h hr.2.1

/-- El trébol de signos mixtos NO es realizable (pasa Gauss pero no el índice cero). -/
theorem mixedTrefoil_not_realizable : ¬isRealizable mixedTrefoil := fun h =>
  mixedTrefoil_irreducible_gauss_not_indexZero.2.2 h.2.2

/-! ## 2. Equivalencias Básicas -/

/-- Realizabilidad es equivalente a pertenencia al conjunto realizable -/
theorem isRealizable_iff_mem_set (K : K3Config) :
    isRealizable K ↔ K ∈ realizableConfigs := by
  unfold realizableConfigs
  rw [Finset.mem_union]
  exact realizable_iff_trefoil_orbits K

/-- Las órbitas de los dos tréboles son disjuntas -/
theorem realizable_orbits_disjoint :
    Disjoint (orbit trefoilKnot) (orbit mirrorTrefoil) := by
  exact Finset.disjoint_iff_inter_eq_empty.mpr orbits_disjoint_trefoil_mirror

/-- Los realizables son un subconjunto de las configuraciones sin R1 ni R2: son exactamente las
    que además tienen índice cero.

    **Antes:** `configsNoR1NoR2 = realizableConfigs ∪ Orb(specialClass)` (falso ahora: las
    irreducibles son 172). -/
theorem realizableConfigs_eq_filter_indexZero :
    realizableConfigs = configsNoR1NoR2.filter (fun K => indexZero K) :=
  configsNoR1NoR2_indexZero_eq.symm

/-- Los realizables están contenidos en las configuraciones sin R1 ni R2. -/
theorem realizableConfigs_subset_configsNoR1NoR2 :
    realizableConfigs ⊆ configsNoR1NoR2 := by
  rw [realizableConfigs_eq_filter_indexZero]
  exact Finset.filter_subset _ _

/-! ## 3. Teoremas de Caracterización -/

/-- **TEOREMA 1a: Cota de órbita (refinada)**

    Toda configuración realizable tiene órbita de cardinalidad exactamente 2. -/
theorem realizable_orbit_card_eq_two (K : K3Config) :
    isRealizable K → (orbit K).card = 2 := by
  intro h
  rcases (realizable_iff_trefoil_orbits K).mp h with h' | h'
  · rw [orbit_eq_of_mem h']
    exact orbit_trefoilKnot_card
  · rw [orbit_eq_of_mem h']
    exact orbit_mirrorTrefoil_card

/-- **TEOREMA 1: Condición Necesaria (Cota de Órbita)** (enunciado conservado)

    Si una configuración K₃ es realizable, entonces su órbita tiene cardinalidad 12 o 2
    (de hecho 2: ver `realizable_orbit_card_eq_two`; la cota 12 es vacua). -/
theorem realizable_orbit_card_cases (K : K3Config) :
    isRealizable K → (orbit K).card = 12 ∨ (orbit K).card = 2 :=
  fun h => Or.inr (realizable_orbit_card_eq_two K h)

/-- **TEOREMA 2: Criterio para Configuraciones Irreducibles**

    Para configuraciones sin R1 ni R2, la realizabilidad es exactamente la pertenencia a la
    órbita de uno de los dos tréboles.

    **Antes:** `isRealizable K ↔ K ∈ orbit trefoilKnot`.
    **Después:** `isRealizable K ↔ K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil`. -/
theorem irreducible_realizable_iff (K : K3Config)
    (_hR1 : ¬hasR1 K) (_hR2 : ¬hasR2 K) :
    isRealizable K ↔ K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil :=
  realizable_iff_trefoil_orbits K

/-- **NUEVO: para irreducibles, realizable ⟺ índice cero.** -/
theorem irreducible_realizable_iff_indexZero (K : K3Config)
    (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) :
    isRealizable K ↔ indexZero K := by
  rw [realizable_eq_irreducible_indexZero]
  simp [hR1, hR2]

/-- **TEOREMA 3: Caracterización Completa**

    Una configuración K₃ es realizable si y solo si:
    1. No tiene movimientos R1 ni R2 (es irreducible), Y
    2. Pertenece a la órbita del trébol derecho o del izquierdo.

    **Antes:** `... ∧ K ∈ Orb(trefoilKnot)`.
    **Después:** `... ∧ (K ∈ Orb(trefoilKnot) ∨ K ∈ Orb(mirrorTrefoil))`. -/
theorem k3_realizability_characterization (K : K3Config) :
    isRealizable K ↔
      (¬hasR1 K ∧ ¬hasR2 K) ∧ (K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil) := by
  constructor
  · intro h
    exact ⟨h.1, (realizable_iff_trefoil_orbits K).mp h⟩
  · intro ⟨_, h_orbit⟩
    exact (realizable_iff_trefoil_orbits K).mpr h_orbit

/-- **TEOREMA 4: Realizable ⟺ Representante Conocido**

    K es realizable si y sólo si existe un representante R ∈ {trefoilKnot, mirrorTrefoil}
    tal que K ∈ Orb(R) y R es realizable.

    **Antes:** `R ∈ {specialClass, trefoilKnot}`.
    **Después:** `R ∈ {trefoilKnot, mirrorTrefoil}`. -/
theorem realizable_iff_representative (K : K3Config) :
    isRealizable K ↔
    ∃ R ∈ ({trefoilKnot, mirrorTrefoil} : Finset K3Config),
      K ∈ orbit R ∧ isRealizable R := by
  constructor
  · intro h
    rcases (realizable_iff_trefoil_orbits K).mp h with h' | h'
    · exact ⟨trefoilKnot, by simp, h', isRealizable_trefoilKnot⟩
    · exact ⟨mirrorTrefoil, by simp, h', isRealizable_mirrorTrefoil⟩
  · rintro ⟨R, hR_mem, hK_orbit, _⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR_mem
    rcases hR_mem with rfl | rfl
    · exact (realizable_iff_trefoil_orbits K).mpr (Or.inl hK_orbit)
    · exact (realizable_iff_trefoil_orbits K).mpr (Or.inr hK_orbit)

/-- Realizable implica irreducible (sin R1 ni R2). -/
theorem irreducible_of_realizable {K : K3Config} (h : isRealizable K) :
    ¬hasR1 K ∧ ¬hasR2 K := h.1

/-- Sólo las órbitas de los dos tréboles son realizables; la de `specialClass` no. -/
theorem only_trefoil_orbits_realizable :
    (∀ K ∈ orbit trefoilKnot, isRealizable K) ∧
    (∀ K ∈ orbit mirrorTrefoil, isRealizable K) ∧
    (∀ K ∈ orbit specialClass, ¬isRealizable K) :=
  ⟨fun _ h => (realizable_iff_trefoil_orbits _).mpr (Or.inl h),
    fun _ h => (realizable_iff_trefoil_orbits _).mpr (Or.inr h),
    fun _ h => orbit_specialClass_not_realizable h⟩

/-! ## 4. Teoremas de Conteo -/

/-- **TEOREMA 5: Cardinalidad de Configuraciones Realizables**

    El número total de configuraciones K₃ realizables es exactamente 4 (2 + 2).
    (Antes: 2; antes aún: 14, y 8 falso.) -/
theorem total_realizable_configs :
    realizableConfigs.card = 4 := by
  unfold realizableConfigs
  rw [Finset.card_union_of_disjoint realizable_orbits_disjoint, orbit_trefoilKnot_card,
    orbit_mirrorTrefoil_card]

/-- **TEOREMA 6: Fracción de Configuraciones Realizables**

    La probabilidad de que una configuración K₃ firmada aleatoria sea realizable
    es exactamente 4/960 = 1/240.  (Antes: 2/120 = 1/60; antes aún 14/120 = 7/60.) -/
theorem realizable_fraction :
    (realizableConfigs.card : ℚ) / totalConfigs = 1 / 240 := by
  rw [total_realizable_configs]
  unfold totalConfigs
  norm_num

/-- **TEOREMA 7: Conteo de Configuraciones No Realizables**

    Exactamente 956 de las 960 configuraciones K₃ firmadas NO son realizables.
    (Antes: 118 de 120.)

    **Descomposición:** 960 − 172 = 788 reducibles (R1 o R2), 168 irreducibles no realizables
    (entre ellas la órbita de 12 de `specialClass`), 4 realizables: 788 + 168 + 4 = 960. -/
theorem non_realizable_count :
    (Finset.univ.filter (fun K : K3Config => ¬isRealizable K)).card = 956 := by
  have h_total : (Finset.univ : Finset K3Config).card = (960 : ℕ) := by
    rw [Finset.card_univ]
    exact card_k3_config
  have h_real : ((Finset.univ : Finset K3Config).filter isRealizable).card = 4 := by
    have : (Finset.univ : Finset K3Config).filter isRealizable = realizableConfigs := by
      ext K
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, isRealizable_iff_mem_set]
    rw [this]
    exact total_realizable_configs
  have h_card := finset_card_partition (Finset.univ : Finset K3Config) isRealizable
  omega

/-- Las irreducibles pero no realizables son exactamente 168 = 172 − 4.
    (Antes: 12, la órbita de `specialClass`; ahora esa órbita es sólo una de las 16 órbitas
    irreducibles no realizables.) -/
theorem irreducible_not_realizable_count :
    (configsNoR1NoR2.filter (fun K => ¬isRealizable K)).card = 168 := by
  have h1 : configsNoR1NoR2.filter isRealizable = realizableConfigs := by
    ext K
    simp only [Finset.mem_filter, isRealizable_iff_mem_set, and_iff_right_iff_imp]
    intro hK
    exact realizableConfigs_subset_configsNoR1NoR2 hK
  have h2 := finset_card_partition configsNoR1NoR2 isRealizable
  rw [h1, total_realizable_configs, configs_no_r1_no_r2_card] at h2
  omega

/-! ## 5. Criterios Constructivos -/

/-- **CRITERIO 1: No-Realizabilidad Constructiva**

    Una configuración NO es realizable si y solo si tiene R1, o tiene R2, o viola la
    paridad de Gauss, o viola el índice cero.

    **Antes:** `hasR1 ∨ hasR2 ∨ ¬gaussEven`.  **Después:** `… ∨ ¬indexZero`. -/
theorem not_realizable_criterion (K : K3Config) :
    ¬isRealizable K ↔ hasR1 K ∨ hasR2 K ∨ ¬gaussEven K ∨ ¬indexZero K := by
  unfold isRealizable
  by_cases h1 : hasR1 K <;> by_cases h2 : hasR2 K <;> by_cases h3 : gaussEven K <;>
    by_cases h4 : indexZero K <;> simp [h1, h2, h3, h4]

/-- **CRITERIO 2: Certificado de Pertenencia a Órbita**

    Para verificar si K ∈ Orb(R), basta verificar que existe g ∈ D₆ tal que g • R = K. -/
theorem orbit_membership_certificate (K R : K3Config) :
    K ∈ orbit R ↔ ∃ g : D6, g • R = K := by
  unfold orbit
  simp [Finset.mem_image]

/-- **CRITERIO 3: Realizabilidad por Comparación Directa**

    K es realizable si y sólo si existe g ∈ D₆ con g • trefoilKnot = K o g • mirrorTrefoil = K.

    **Antes:** `∃ g, g • trefoilKnot = K`. -/
theorem realizable_by_transformation (K : K3Config) :
    isRealizable K ↔ (∃ g : D6, g • trefoilKnot = K) ∨ (∃ g : D6, g • mirrorTrefoil = K) := by
  rw [realizable_iff_trefoil_orbits, orbit_membership_certificate K trefoilKnot,
    orbit_membership_certificate K mirrorTrefoil]

/-! ## 6. Corolarios y Propiedades -/

/-- **COROLARIO 1: Preservación bajo D₆**

    La realizabilidad se preserva bajo la acción del grupo diédrico D₆
    (enunciado conservado; ahora se apoya en la clausura de las órbitas de los tréboles). -/
theorem realizable_preserved_by_D6 (K : K3Config) (g : D6) :
    isRealizable K ↔ isRealizable (g • K) := by
  rw [realizable_iff_trefoil_orbits, realizable_iff_trefoil_orbits]
  constructor
  · rintro (h | h)
    · exact Or.inl (mem_orbit_of_smul_mem h g)
    · exact Or.inr (mem_orbit_of_smul_mem h g)
  · intro h
    have h' : g⁻¹ • (g • K) = K := by
      rw [← actOnConfig_comp, inv_mul_cancel, actOnConfig_id]
    rcases h with h | h
    · exact Or.inl (h' ▸ mem_orbit_of_smul_mem h g⁻¹)
    · exact Or.inr (h' ▸ mem_orbit_of_smul_mem h g⁻¹)

/-- **COROLARIO 2: Dicotomía de las Irreducibles con índice cero**

    Toda configuración irreducible es realizable o tiene índice ≠ 0.  (Reemplaza a
    `irreducible_dichotomy : realizable ∨ K ∈ Orb(specialClass)`, FALSO con el signo dato.) -/
theorem irreducible_dichotomy_indexZero (K : K3Config) (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) :
    isRealizable K ∨ ¬indexZero K := by
  by_cases hI : indexZero K
  · exact Or.inl ((irreducible_realizable_iff_indexZero K hR1 hR2).mpr hI)
  · exact Or.inr hI

/-- **COROLARIO 3: Algoritmo de Verificación**

    Existe un algoritmo decidible que verifica realizabilidad en tiempo O(1) para K₃.

    **Procedimiento:** enumerar las dos órbitas de los tréboles (4 elementos) y verificar
    pertenencia. -/
def realizabilityAlgorithm (K : K3Config) : Bool :=
  K ∈ realizableConfigs

/-- El algoritmo es correcto -/
theorem realizability_algorithm_correct (K : K3Config) :
    realizabilityAlgorithm K = true ↔ isRealizable K := by
  unfold realizabilityAlgorithm
  exact decide_eq_true_iff.trans (isRealizable_iff_mem_set K).symm

/-! ## 7. Ejemplos y Verificaciones -/

section Examples

/-- El trébol derecho es realizable -/
example : isRealizable trefoilKnot := isRealizable_trefoilKnot

/-- El trébol izquierdo (espejo) es realizable: está en su propia órbita, distinta de la del
    derecho -/
example : isRealizable mirrorTrefoil := isRealizable_mirrorTrefoil

/-- `specialClass` no es realizable (viola la paridad de Gauss y el índice cero). -/
example : ¬isRealizable specialClass := specialClass_not_realizable

/-- Verificación computacional: total de configuraciones realizables -/
example : realizableConfigs.card = 4 := total_realizable_configs

/-- Verificación computacional: fracción de realizables -/
example : (realizableConfigs.card : ℚ) / totalConfigs = 1 / 240 :=
  realizable_fraction

/-- El trébol derecho no tiene R1 -/
example : ¬hasR1 trefoilKnot := trefoilKnot_no_r1

/-- El trébol derecho no tiene R2 -/
example : ¬hasR2 trefoilKnot := trefoilKnot_no_r2

end Examples

/-! ## 8. Contribución al Problema Abierto 1.3.3 -/

/-!
### Resolución para K₃ (firmado)

**TEOREMA (Caracterización de Realizabilidad K₃ firmada):**
```
(¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K ∧ indexZero K
   ⟺ K ∈ Orb(trefoilKnot) ∨ K ∈ Orb(mirrorTrefoil)
```

**Consecuencias:**
1. Criterio algebraico decidible en O(1)
2. 4/960 = 1/240 configuraciones realizables; de las 172 irreducibles firmadas sólo las 4 de
   los tréboles tienen índice cero
3. Verificación formal en Lean 4 (sin `sorry` propios ni axiomas)

**Limitaciones:**
- Específico para n = 3
- La paridad de Gauss y el índice cero son sólo condiciones NECESARIAS de planaridad; que el
  índice cero caracterice la planaridad en general es una CONJETURA no demostrada.  Para K₃
  coincide con lo realizable porque las irreducibles que lo cumplen son los tréboles.
- La órbita de `specialClass` (12 configuraciones) es irreducible pero no realizable; las otras
  156 irreducibles no realizables tienen índice ≠ 0 (o violan Gauss).

### Referencias Cruzadas

- **Código Lean:**
  * TCN_05_Orbitas.lean: órbita-estabilizador, `gaussEven`, `indexZero`
  * TCN_06_Representantes.lean: representantes, `irreducible_indexZero_iff`
  * TCN_07_Clasificacion.lean: clasificación firmada (irreducibles con índice cero)
- **Literatura:** Reidemeister (1927); Rosenstiehl & Tarjan (1984); Kauffman (1999)
-/

end KnotTheory

/-!
## Resumen del Módulo

### Definiciones Exportadas
- `isRealizable`: irreducible ∧ paridad de Gauss ∧ índice cero
- `realizableConfigs`: `Orb(trefoilKnot) ∪ Orb(mirrorTrefoil)` (4 elementos)
- `mixedTrefoil`: contraejemplo (Gauss sí, índice no)
- `realizabilityAlgorithm`: Algoritmo decidible

### Teoremas Principales
- `realizable_iff_trefoil_orbits`, `realizable_eq_irreducible_indexZero`
- `k3_realizability_characterization`, `realizable_iff_representative`
- `specialClass_not_realizable`, `only_trefoil_orbits_realizable`
- `total_realizable_configs` (4), `realizable_fraction` (1/240), `non_realizable_count` (956),
  `irreducible_not_realizable_count` (168)
- `not_realizable_criterion`, `realizable_by_transformation`
- `gaussEven_iff_of_smul`, `realizable_preserved_by_D6`, `realizability_algorithm_correct`

### Estado del Módulo
- Sin `sorry` ni axiomas propios
-/
