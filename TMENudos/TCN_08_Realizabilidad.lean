-- TCN_08_Realizabilidad.lean
-- Teoría Combinatoria de Nudos K₃: Teorema de Realizabilidad
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Diciembre 21, 2025
-- Revisión (Opción 1, paridad de Gauss): "realizable" excluye la órbita de `specialClass`.

import TMENudos.TCN_05_Orbitas
import TMENudos.TCN_06_Representantes
import TMENudos.TCN_07_Clasificacion
import TMENudos.TCN_AUX_Teoremas_Auxiliares_Realizabilidad
import Mathlib.Data.Finset.Card

/-!
# Teorema de Realizabilidad para Configuraciones K₃

Este módulo formaliza el **criterio de órbitas de grupo** para el problema
de realizabilidad de códigos de Gauss, proporcionando una caracterización
completa de qué configuraciones K₃ son realizables como nudos clásicos en ℝ³.

## DECISIÓN DE DISEÑO (revisión Opción 1): paridad de Gauss

**Antes:** `isRealizable K := K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot)`
(= "sin R1 ni R2"), con 14 configuraciones realizables (12 + 2).

**Después:** `isRealizable K := (¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K`, donde
`gaussEven K` es la **condición de paridad de Gauss**: cada cuerda (pareja) del
diagrama se entrelaza con un número PAR de las otras cuerdas. Se demuestra
`realizable_iff_trefoil_orbit : isRealizable K ↔ K ∈ Orb(trefoilKnot)`, es decir,
sólo quedan **2** configuraciones realizables (el trébol derecho e izquierdo).

**Razón (planaridad).** La paridad de Gauss es condición NECESARIA de planaridad
(todo código de Gauss de un diagrama clásico la cumple: una curva cerrada en el
plano corta a cada cuerda-lazo un número par de veces). Se comprueba
(`gaussEven_trefoilKnot`, `not_gaussEven_specialClass`, y `TMENudos/Etapa1_Modular.lean`
de la rama de trabajo paralela) que NINGUNA de las 12 configuraciones de
`Orb(specialClass)` la cumple; por tanto no son diagramas de nudos clásicos (sólo
serían nudos virtuales), y la definición anterior de "realizable" era demasiado
generosa. Las 2 configuraciones de `Orb(trefoilKnot)` sí la cumplen.
`gaussEven` es invariante bajo D₆ (`gaussEven_iff_of_smul`), por lo que "realizable"
sigue siendo propiedad de la órbita.

**Cambios de enunciado en este módulo (antes → después):**
- `isRealizable`: `K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot)` →
  `(¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K` (equivalente a `K ∈ Orb(trefoilKnot)`).
- `realizableConfigs`: `Orb(specialClass) ∪ Orb(trefoilKnot)` (14) → `Orb(trefoilKnot)` (2).
- `total_realizable_configs`: `= 14` → `= 2`.
- `realizable_fraction`: `= 7/60` → `= 1/60`.
- `non_realizable_count`: `= 106` → `= 118` (106 reducibles + 12 de `Orb(specialClass)`).
- `realizableConfigs_eq_configsNoR1NoR2`: `realizableConfigs = configsNoR1NoR2` (falso ahora) →
  `configsNoR1NoR2 = realizableConfigs ∪ Orb(specialClass)`.
- `irreducible_realizable_iff`: `isRealizable K ↔ K ∈ Orb(special) ∨ K ∈ Orb(trefoil)` →
  `isRealizable K ↔ K ∈ Orb(trefoilKnot)` (para irreducibles).
- `k3_realizability_characterization`: `... ∧ (K ∈ Orb(special) ∨ K ∈ Orb(trefoil))` →
  `... ∧ K ∈ Orb(trefoilKnot)`.
- `realizable_iff_representative`: `∃ R ∈ {special, trefoil}, K ∈ Orb(R)` →
  `∃ R ∈ {special, trefoil}, K ∈ Orb(R) ∧ isRealizable R`.
- `realizable_by_transformation`: `(∃ g, g•special = K) ∨ (∃ g, g•trefoil = K)` →
  `∃ g, g • trefoilKnot = K`.
- `not_realizable_criterion`: `hasR1 ∨ hasR2 ∨ (K ∉ Orb(special) ∧ K ∉ Orb(trefoil))` →
  `hasR1 K ∨ hasR2 K ∨ ¬gaussEven K`.
- `realizable_orbit_card_cases`: se conserva (`12 ∨ 2`), y se añade el refinamiento
  `realizable_orbit_card_eq_two` (`= 2`).
- `irreducible_dichotomy`: (tautología `realizable ∨ ¬realizable`) → dicotomía real
  `realizable ∨ K ∈ Orb(specialClass)`.
- `irreducible_is_realizable` («toda irreducible es realizable», FALSO ahora) → ELIMINADO;
  sustituido por `irreducible_of_realizable` (realizable ⇒ irreducible),
  `specialClass_not_realizable`, `orbit_specialClass_not_realizable` e
  `irreducible_realizable_iff_not_special`.
- `realizable_preserved_by_D6`: mismo enunciado, nueva demostración.
- Se conserva la clasificación de TCN_07 (14 irreducibles = 2 órbitas, 12 + 2) y se añade
  `only_trefoil_orbit_realizable`: SÓLO la órbita del trébol es realizable.

## Contexto Histórico

El **problema de realizabilidad** (Gauss, siglo XIX):
- No toda configuración combinatoria que satisface A1-A4 es realizable
- Condiciones conocidas (paridad de Gauss, Dehn, Whitney) son necesarias pero NO
  suficientes en general
- Problema parcialmente abierto para n general

## Solución para K₃

Este módulo proporciona:
1. **Caracterización exacta**: Una configuración K₃ es realizable ⟺ pertenece a
   Orb(trefoilKnot) (2 configuraciones)
2. **Criterio decidible**: Verificación en tiempo O(12n) = O(1) para K₃
3. **Certificados constructivos**: Pruebas algebraicas de realizabilidad/no-realizabilidad

## Reducción Dramática

```
120 configuraciones K₃ válidas (A1-A4)
  ↓ Filtro R1, R2
  14 configuraciones irreducibles (sin R1 ni R2)
  ↓ Acción de D₆
  2 órbitas distintas (12 de specialClass + 2 del trébol)
  ↓ Paridad de Gauss (necesaria para planaridad)
   2 configuraciones realizables (trébol derecho e izquierdo)
```

## Estructura del Módulo

1. **Paridad de Gauss**: `gaussEven` y su invariancia bajo D₆
2. **Definiciones básicas**: `isRealizable`, `realizableConfigs`
3. **Teoremas de caracterización**: Condiciones necesarias y suficientes
4. **Teoremas de conteo**: 2/120 configuraciones realizables
5. **Criterios constructivos**: Certificados de realizabilidad
6. **Corolarios**: Preservación bajo D₆, algoritmo decidible

## Referencias

- Sección 1.3.3 (LaTeX): Realizabilidad y Nudos Virtuales
- Sección 1.3.3.1 (LaTeX): Criterio de Órbitas de Grupo
- TCN_05_Orbitas.lean: Teorema órbita-estabilizador
- TCN_07_Clasificacion.lean: Clasificación K₃
- TMENudos/Etapa1_Modular.lean (otra rama): paridad de Gauss de las 12 configuraciones

-/

namespace KnotTheory

open OrderedPair K3Config DihedralD6

/-! ## 0. Instancias de finitud para K₃Config -/

/-- Hay exactamente 120 configuraciones K₃ (5!! · 2³ = 15 · 8).

    ✅ Antes era `sorry`; ahora se demuestra contando (con `decide +kernel`) los
    subconjuntos de 3 tuplas ordenadas que particionan `Z/6Z`. -/
theorem card_k3_config : Fintype.card K3Config = 120 := by
  have h : (Finset.univ : Finset K3Config).map ⟨K3Config.pairs, fun K L h => by
        cases K; cases L; simp only at h; subst h; rfl⟩ =
      (allOrderedPairs.powersetCard 3).filter
        (fun S => ∀ i : ZMod 6, (S.filter (fun p => i = p.fst ∨ i = p.snd)).card = 1) := by
    ext S
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨K, rfl⟩
      refine ⟨⟨fun p _ => mem_allOrderedPairs p, K.card_eq⟩, fun i => ?_⟩
      obtain ⟨p, ⟨hp, hi⟩, huniq⟩ := K.is_partition i
      rw [Finset.card_eq_one]
      refine ⟨p, ?_⟩
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => huniq q h, fun h => h ▸ ⟨hp, hi⟩⟩
    · rintro ⟨⟨_, hcard⟩, hpart⟩
      refine ⟨⟨S, hcard, fun i => ?_⟩, rfl⟩
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (hpart i)
      have hp' : p ∈ S.filter (fun p => i = p.fst ∨ i = p.snd) := by
        rw [hp]; exact Finset.mem_singleton_self p
      rw [Finset.mem_filter] at hp'
      refine ⟨p, hp', fun q hq => ?_⟩
      have : q ∈ S.filter (fun p => i = p.fst ∨ i = p.snd) := Finset.mem_filter.mpr hq
      rw [hp] at this
      exact Finset.mem_singleton.mp this
  have h2 := congrArg Finset.card h
  rw [Finset.card_map, Finset.card_univ] at h2
  rw [h2]
  decide +kernel

/-! ## 0.5. Paridad de Gauss -/

/-- `x` está **estrictamente entre** `a` y `b` en el orden lineal `0 < 1 < ... < 5` de los
    representantes `.val` de `ZMod 6` (se compara con `.val`, NO con el orden cíclico). -/
def strictlyBetween (a b x : ZMod 6) : Prop :=
  min a.val b.val < x.val ∧ x.val < max a.val b.val

instance (a b x : ZMod 6) : Decidable (strictlyBetween a b x) :=
  inferInstanceAs (Decidable (min a.val b.val < x.val ∧ x.val < max a.val b.val))

/-- La pareja `q` **se entrelaza** con la pareja `p` si exactamente uno de los extremos
    de `q` está estrictamente entre los extremos de `p` (las cuerdas se cruzan en el
    círculo de 6 puntos).  Se exige además que los cuatro extremos sean distintos (en una
    configuración K₃ esto ocurre siempre entre parejas distintas, por la partición), lo que
    hace el predicado invariante bajo rotaciones; una pareja no se entrelaza consigo
    misma. -/
def chordsInterlace (p q : OrderedPair) : Prop :=
  (p.fst ≠ q.fst ∧ p.fst ≠ q.snd ∧ p.snd ≠ q.fst ∧ p.snd ≠ q.snd) ∧
  (strictlyBetween p.fst p.snd q.fst ↔ ¬ strictlyBetween p.fst p.snd q.snd)

instance (p q : OrderedPair) : Decidable (chordsInterlace p q) :=
  inferInstanceAs (Decidable ((p.fst ≠ q.fst ∧ p.fst ≠ q.snd ∧ p.snd ≠ q.fst ∧ p.snd ≠ q.snd) ∧
    (strictlyBetween p.fst p.snd q.fst ↔ ¬ strictlyBetween p.fst p.snd q.snd)))

/-- **Condición de paridad de Gauss** para K₃: cada pareja se entrelaza con un número PAR
    de las otras parejas de la configuración.  Es condición NECESARIA de planaridad
    (todo código de Gauss de un diagrama de nudo clásico la cumple). -/
def gaussEven (K : K3Config) : Prop :=
  ∀ p ∈ K.pairs, (K.pairs.filter (chordsInterlace p)).card % 2 = 0

instance (K : K3Config) : Decidable (gaussEven K) :=
  Finset.decidableDforallFinset

/-- El entrelazamiento de dos parejas es invariante bajo D₆ (rotaciones y reflexiones
    de `actionZMod`).  Se decide sobre todos los valores de `ZMod 6` (12 acciones). -/
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

/-- Ninguna configuración de `Orb(specialClass)` cumple la paridad de Gauss
    (no son diagramas de nudos clásicos). -/
theorem not_gaussEven_of_mem_orbit_special {K : K3Config} (h : K ∈ orbit specialClass) :
    ¬gaussEven K := by
  rw [gaussEven_iff_of_mem_orbit h]
  exact not_gaussEven_specialClass


/-! ## 1. Definiciones Básicas -/

/-- Una configuración K₃ es **realizable** (como diagrama de nudo clásico) si es
    irreducible (sin R1 ni R2) y cumple la paridad de Gauss.

    **Elección de forma (documentada):** se toma la conjunción `(¬hasR1 ∧ ¬hasR2) ∧ gaussEven`
    (y no directamente la pertenencia a `Orb(trefoilKnot)`) para que la definición exprese
    la ESTRUCTURA de la condición (irreducible + necesaria de planaridad) y la
    equivalencia con la órbita del trébol sea un teorema (`realizable_iff_trefoil_orbit`),
    que se apoya en la clasificación de TCN_07.

    **Antes:** `K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot)` (14 configuraciones).
    **Después:** sólo `Orb(trefoilKnot)` (2 configuraciones), pues las 12 de
    `Orb(specialClass)` violan la paridad de Gauss (`not_gaussEven_specialClass`) y por
    tanto no son diagramas planos.

    **Advertencia:** la paridad de Gauss es sólo NECESARIA de planaridad; que las 2
    configuraciones del trébol sean realmente diagramas de nudos (lo son: el trébol) se
    verifica aparte, no lo garantiza esta definición por sí sola. -/
def isRealizable (K : K3Config) : Prop :=
  (¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K

/-- Conjunto de todas las configuraciones K₃ realizables: la órbita del trébol
    (`trefoilKnot` y `mirrorTrefoil`), 2 elementos.  (Antes: `Orb(specialClass) ∪
    Orb(trefoilKnot)`, 14 elementos.) -/
def realizableConfigs : Finset K3Config :=
  orbit trefoilKnot

/-! ### Decidibilidad -/

/-- La realizabilidad es decidible para cualquier configuración K₃. -/
instance (K : K3Config) : Decidable (isRealizable K) :=
  inferInstanceAs (Decidable ((¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K))

/-- La pertenencia a `realizableConfigs` es decidible -/
instance (K : K3Config) : Decidable (K ∈ realizableConfigs) :=
  inferInstanceAs (Decidable (K ∈ orbit trefoilKnot))

/-! ### Realizable ⟺ órbita del trébol -/

/-- **TEOREMA PRINCIPAL:** una configuración K₃ es realizable si y sólo si está en la
    órbita del trébol (`trefoilKnot` o `mirrorTrefoil`).

    (⇐) `trefoilKnot` no tiene R1/R2 y cumple la paridad; ambas propiedades son
    invariantes bajo D₆.  (⇒) Un realizable es irreducible, luego (TCN_07) está en
    `Orb(specialClass)` o en `Orb(trefoilKnot)`; en la primera no cumpliría la paridad. -/
theorem realizable_iff_trefoil_orbit (K : K3Config) :
    isRealizable K ↔ K ∈ orbit trefoilKnot := by
  constructor
  · rintro ⟨⟨hR1, hR2⟩, hG⟩
    rcases config_in_one_of_two_orbits K hR1 hR2 with h | h
    · exact absurd hG (not_gaussEven_of_mem_orbit_special h)
    · exact h
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hasR1_eq_of_mem_orbit h]; exact trefoilKnot_no_r1
    · rw [hasR2_eq_of_mem_orbit h]; exact trefoilKnot_no_r2
    · rw [gaussEven_iff_of_mem_orbit h]; exact gaussEven_trefoilKnot

/-- El trébol derecho es realizable (no vacuidad). -/
theorem isRealizable_trefoilKnot : isRealizable trefoilKnot := by decide +kernel

/-- El trébol izquierdo es realizable. -/
theorem isRealizable_mirrorTrefoil : isRealizable mirrorTrefoil := by decide +kernel

/-- `specialClass` NO es realizable. -/
theorem specialClass_not_realizable : ¬isRealizable specialClass := by decide +kernel

/-- Ninguna configuración de `Orb(specialClass)` es realizable (las 12). -/
theorem orbit_specialClass_not_realizable {K : K3Config} (h : K ∈ orbit specialClass) :
    ¬isRealizable K := fun hr =>
  not_gaussEven_of_mem_orbit_special h hr.2

/-! ## 2. Equivalencias Básicas -/

/-- Realizabilidad es equivalente a pertenencia al conjunto realizable -/
theorem isRealizable_iff_mem_set (K : K3Config) :
    isRealizable K ↔ K ∈ realizableConfigs :=
  realizable_iff_trefoil_orbit K

/-- Las dos órbitas de las configuraciones irreducibles son disjuntas -/
theorem realizable_orbits_disjoint :
    Disjoint (orbit specialClass) (orbit trefoilKnot) := by
  exact Finset.disjoint_iff_inter_eq_empty.mpr orbits_disjoint_special_trefoil

/-- Los realizables son un subconjunto propio de las configuraciones sin R1 ni R2:
    éstas son los realizables más la órbita de `specialClass` (12 no planas).

    **Antes:** `realizableConfigs = configsNoR1NoR2` (ya no es cierto).
    **Después:** `configsNoR1NoR2 = realizableConfigs ∪ Orb(specialClass)`. -/
theorem configsNoR1NoR2_eq_realizable_union_special :
    configsNoR1NoR2 = realizableConfigs ∪ orbit specialClass := by
  unfold realizableConfigs
  rw [configsNoR1NoR2_eq_two_orbits, Finset.union_comm]

/-- Los realizables están contenidos en las configuraciones sin R1 ni R2. -/
theorem realizableConfigs_subset_configsNoR1NoR2 :
    realizableConfigs ⊆ configsNoR1NoR2 := by
  rw [configsNoR1NoR2_eq_realizable_union_special]
  exact Finset.subset_union_left

/-! ## 3. Teoremas de Caracterización -/

/-- **TEOREMA 1a: Cota de órbita (refinada)**

    Toda configuración realizable tiene órbita de cardinalidad exactamente 2. -/
theorem realizable_orbit_card_eq_two (K : K3Config) :
    isRealizable K → (orbit K).card = 2 := by
  intro h
  rw [orbit_eq_of_mem ((realizable_iff_trefoil_orbit K).mp h)]
  exact orbit_trefoilKnot_card

/-- **TEOREMA 1: Condición Necesaria (Cota de Órbita)** (enunciado conservado)

    Si una configuración K₃ es realizable, entonces su órbita tiene cardinalidad 12 o 2
    (de hecho 2: ver `realizable_orbit_card_eq_two`; la cota 12 es ahora vacua). -/
theorem realizable_orbit_card_cases (K : K3Config) :
    isRealizable K → (orbit K).card = 12 ∨ (orbit K).card = 2 :=
  fun h => Or.inr (realizable_orbit_card_eq_two K h)

/-- **TEOREMA 2: Criterio para Configuraciones Irreducibles**

    Para configuraciones sin R1 ni R2, la realizabilidad es exactamente la pertenencia
    a la órbita del trébol.

    **Antes:** `isRealizable K ↔ K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot)`.
    **Después:** `isRealizable K ↔ K ∈ Orb(trefoilKnot)`. -/
theorem irreducible_realizable_iff (K : K3Config)
    (_hR1 : ¬hasR1 K) (_hR2 : ¬hasR2 K) :
    isRealizable K ↔ K ∈ orbit trefoilKnot :=
  realizable_iff_trefoil_orbit K

/-- **TEOREMA 3: Caracterización Completa**

    Una configuración K₃ es realizable si y solo si:
    1. No tiene movimientos R1 ni R2 (es irreducible), Y
    2. Pertenece a la órbita del trébol.

    **Antes:** `... ∧ (K ∈ Orb(specialClass) ∨ K ∈ Orb(trefoilKnot))`.
    **Después:** `... ∧ K ∈ Orb(trefoilKnot)`. -/
theorem k3_realizability_characterization (K : K3Config) :
    isRealizable K ↔
      (¬hasR1 K ∧ ¬hasR2 K) ∧ K ∈ orbit trefoilKnot := by
  constructor
  · intro h
    exact ⟨h.1, (realizable_iff_trefoil_orbit K).mp h⟩
  · intro ⟨_, h_orbit⟩
    exact (realizable_iff_trefoil_orbit K).mpr h_orbit

/-- **TEOREMA 4: Realizable ⟺ Representante Conocido**

    K es realizable si y sólo si existe un representante R ∈ {specialClass, trefoilKnot}
    tal que K ∈ Orb(R) y R es realizable (i.e. R = trefoilKnot).

    **Antes:** `∃ R ∈ {special, trefoil}, K ∈ Orb(R)` (la cláusula sobre `specialClass`
    ya no es cierta).  **Después:** se añade `isRealizable R`. -/
theorem realizable_iff_representative (K : K3Config) :
    isRealizable K ↔
    ∃ R ∈ ({specialClass, trefoilKnot} : Finset K3Config),
      K ∈ orbit R ∧ isRealizable R := by
  constructor
  · intro h
    exact ⟨trefoilKnot, by simp, (realizable_iff_trefoil_orbit K).mp h, isRealizable_trefoilKnot⟩
  · rintro ⟨R, hR_mem, hK_orbit, hR⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR_mem
    rcases hR_mem with rfl | rfl
    · exact absurd hR specialClass_not_realizable
    · exact (realizable_iff_trefoil_orbit K).mpr hK_orbit

/-- Realizable implica irreducible (sin R1 ni R2).

    Reemplaza (dirección verdadera) a `irreducible_is_realizable`. -/
theorem irreducible_of_realizable {K : K3Config} (h : isRealizable K) :
    ¬hasR1 K ∧ ¬hasR2 K := h.1

/-- Sólo UNA de las dos órbitas de irreducibles es realizable: la del trébol. -/
theorem only_trefoil_orbit_realizable :
    (∀ K ∈ orbit trefoilKnot, isRealizable K) ∧
    (∀ K ∈ orbit specialClass, ¬isRealizable K) :=
  ⟨fun _ h => (realizable_iff_trefoil_orbit _).mpr h,
    fun _ h => orbit_specialClass_not_realizable h⟩

/-! ## 4. Teoremas de Conteo -/

/-- **TEOREMA 5: Cardinalidad de Configuraciones Realizables**

    El número total de configuraciones K₃ realizables es exactamente 2.
    (Antes: 14; antes aún: 8, falso.) -/
theorem total_realizable_configs :
    realizableConfigs.card = 2 := by
  unfold realizableConfigs
  exact orbit_trefoilKnot_card

/-- **TEOREMA 6: Fracción de Configuraciones Realizables**

    La probabilidad de que una configuración K₃ aleatoria sea realizable
    es exactamente 2/120 = 1/60.  (Antes: 14/120 = 7/60.) -/
theorem realizable_fraction :
    (realizableConfigs.card : ℚ) / totalConfigs = 1 / 60 := by
  rw [total_realizable_configs]
  unfold totalConfigs
  norm_num

/-- **TEOREMA 7: Conteo de Configuraciones No Realizables**

    Exactamente 118 de las 120 configuraciones K₃ NO son realizables.
    (Antes: 106.)

    **Descomposición:**
    - 106 con movimientos R1 o R2 (reducibles)
    - 12 irreducibles pero no planas (`Orb(specialClass)`, violan la paridad de Gauss)
    - 2 realizables (`Orb(trefoilKnot)`)
    - Total: 106 + 12 + 2 = 120 ✓ -/
theorem non_realizable_count :
    (Finset.univ.filter (fun K : K3Config => ¬isRealizable K)).card = 118 := by
  have h_total : (Finset.univ : Finset K3Config).card = (120 : ℕ) := by
    rw [Finset.card_univ]
    exact card_k3_config
  have h_real : ((Finset.univ : Finset K3Config).filter isRealizable).card = 2 := by
    have : (Finset.univ : Finset K3Config).filter isRealizable = realizableConfigs := by
      ext K
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, isRealizable_iff_mem_set]
    rw [this]
    exact total_realizable_configs
  have h_card := finset_card_partition (Finset.univ : Finset K3Config) isRealizable
  omega

/-- Las irreducibles pero no realizables son exactamente las 12 de `Orb(specialClass)`. -/
theorem irreducible_not_realizable_count :
    (configsNoR1NoR2.filter (fun K => ¬isRealizable K)).card = 12 := by
  have : configsNoR1NoR2.filter (fun K => ¬isRealizable K) = orbit specialClass := by
    ext K
    simp only [Finset.mem_filter, mem_configsNoR1NoR2, realizable_iff_trefoil_orbit]
    constructor
    · rintro ⟨⟨hR1, hR2⟩, hn⟩
      rcases config_in_one_of_two_orbits K hR1 hR2 with h | h
      · exact h
      · exact absurd h hn
    · intro h
      refine ⟨⟨?_, ?_⟩, fun h' => not_mem_both_orbits K ⟨h, h'⟩⟩
      · rw [hasR1_eq_of_mem_orbit h]; exact specialClass_no_r1
      · rw [hasR2_eq_of_mem_orbit h]; exact specialClass_no_r2_ordered
  rw [this]
  exact orbit_specialClass_card

/-! ## 5. Criterios Constructivos -/

/-- **CRITERIO 1: No-Realizabilidad Constructiva**

    Una configuración NO es realizable si y solo si tiene R1, o tiene R2, o viola la
    paridad de Gauss.

    **Antes:** `hasR1 ∨ hasR2 ∨ (K ∉ Orb(special) ∧ K ∉ Orb(trefoil))`.
    **Después:** `hasR1 K ∨ hasR2 K ∨ ¬gaussEven K`. -/
theorem not_realizable_criterion (K : K3Config) :
    ¬isRealizable K ↔ hasR1 K ∨ hasR2 K ∨ ¬gaussEven K := by
  unfold isRealizable
  by_cases h1 : hasR1 K <;> by_cases h2 : hasR2 K <;> by_cases h3 : gaussEven K <;>
    simp [h1, h2, h3]

/-- **CRITERIO 2: Certificado de Pertenencia a Órbita**

    Para verificar si K ∈ Orb(R), basta verificar que existe g ∈ D₆ tal que g • R = K. -/
theorem orbit_membership_certificate (K R : K3Config) :
    K ∈ orbit R ↔ ∃ g : D6, g • R = K := by
  unfold orbit
  simp [Finset.mem_image]

/-- **CRITERIO 3: Realizabilidad por Comparación Directa**

    K es realizable si y sólo si existe g ∈ D₆ con g • trefoilKnot = K.

    **Antes:** `(∃ g, g • specialClass = K) ∨ (∃ g, g • trefoilKnot = K)`.
    **Después:** `∃ g, g • trefoilKnot = K`. -/
theorem realizable_by_transformation (K : K3Config) :
    isRealizable K ↔ ∃ g : D6, g • trefoilKnot = K :=
  (realizable_iff_trefoil_orbit K).trans (orbit_membership_certificate K trefoilKnot)

/-! ## 6. Corolarios y Propiedades -/

/-- **COROLARIO 1: Preservación bajo D₆**

    La realizabilidad se preserva bajo la acción del grupo diédrico D₆
    (enunciado conservado; ahora se apoya en la invariancia de R1, R2 y `gaussEven`). -/
theorem realizable_preserved_by_D6 (K : K3Config) (g : D6) :
    isRealizable K ↔ isRealizable (g • K) := by
  unfold isRealizable
  rw [hasR1_iff_of_smul, hasR2_iff_of_smul, gaussEven_iff_of_smul]

/-- **COROLARIO 2: Dicotomía de las Irreducibles**

    Toda configuración irreducible es, o bien realizable (`Orb(trefoilKnot)`), o bien
    está en `Orb(specialClass)` (no plana, sólo nudo virtual).

    **Antes:** `isRealizable K ∨ ¬isRealizable K` (tautología, con prueba «left»).
    **Después:** `isRealizable K ∨ K ∈ Orb(specialClass)`. -/
theorem irreducible_dichotomy (K : K3Config) (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) :
    isRealizable K ∨ K ∈ orbit specialClass := by
  rcases config_in_one_of_two_orbits K hR1 hR2 with h | h
  · exact Or.inr h
  · exact Or.inl ((realizable_iff_trefoil_orbit K).mpr h)

/-- **COROLARIO: una irreducible es realizable sii no está en `Orb(specialClass)`.**

    Reemplaza a `irreducible_is_realizable` («toda irreducible es realizable»), que ya
    no es cierto: hay 12 irreducibles no realizables (`specialClass_not_realizable`). -/
theorem irreducible_realizable_iff_not_special (K : K3Config)
    (hR1 : ¬hasR1 K) (hR2 : ¬hasR2 K) :
    isRealizable K ↔ K ∉ orbit specialClass := by
  constructor
  · intro h hs; exact orbit_specialClass_not_realizable hs h
  · intro h
    rcases irreducible_dichotomy K hR1 hR2 with h' | h'
    · exact h'
    · exact absurd h' h

/-- **COROLARIO 3: Algoritmo de Verificación**

    Existe un algoritmo decidible que verifica realizabilidad en tiempo O(1) para K₃.

    **Procedimiento:** enumerar `Orb(trefoilKnot)` (2 elementos) y verificar pertenencia. -/
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

/-- El trébol izquierdo (espejo) es realizable: está en la órbita de `trefoilKnot` -/
example : isRealizable mirrorTrefoil := isRealizable_mirrorTrefoil

/-- `specialClass` no es realizable (viola la paridad de Gauss). -/
example : ¬isRealizable specialClass := specialClass_not_realizable

/-- Verificación computacional: total de configuraciones realizables -/
example : realizableConfigs.card = 2 := total_realizable_configs

/-- Verificación computacional: fracción de realizables -/
example : (realizableConfigs.card : ℚ) / totalConfigs = 1 / 60 :=
  realizable_fraction

/-- El trébol derecho no tiene R1 -/
example : ¬hasR1 trefoilKnot := trefoilKnot_no_r1

/-- El trébol derecho no tiene R2 -/
example : ¬hasR2 trefoilKnot := trefoilKnot_no_r2

end Examples

/-! ## 8. Contribución al Problema Abierto 1.3.3 -/

/-!
### Resolución para K₃

Este módulo proporciona una solución al problema de realizabilidad
(Conjetura Abierta 1.3.3) para el caso n = 3:

**TEOREMA (Caracterización de Realizabilidad K₃):**
```
Una configuración K₃ es realizable como nudo clásico en ℝ³ ⟺
  (¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K ⟺ K ∈ Orb(trefoilKnot)
```

**Consecuencias:**
1. Criterio algebraico decidible en O(1)
2. Certificados constructivos de realizabilidad/no-realizabilidad
3. 2/120 configuraciones realizables; de las 14 irreducibles sólo la órbita del trébol
4. Verificación formal en Lean 4 (sin `sorry` propios ni axiomas)

**Limitaciones:**
- Específico para n = 3
- La paridad de Gauss es sólo condición necesaria; para K₃ coincide con lo realizable
  porque las configuraciones que la cumplen son los tréboles.
- Generalización a K_n requiere clasificación de órbitas bajo D₂ₙ y condiciones
  adicionales (Dehn, Whitney/Rosenstiehl).

### Referencias Cruzadas

- **Código Lean:**
  * TCN_05_Orbitas.lean: Teorema órbita-estabilizador
  * TCN_06_Representantes.lean: Representantes canónicos
  * TCN_07_Clasificacion.lean: Clasificación completa K₃ (14 irreducibles en 2 órbitas)
  * TMENudos/Etapa1_Modular.lean (otra rama): paridad de Gauss de las 12 configuraciones

- **Literatura:**
  * Reidemeister (1927): Movimientos de equivalencia
  * Rosenstiehl & Tarjan (1984): Algoritmos de planarización
  * Kauffman (1999): Teoría de nudos virtuales
-/

end KnotTheory

/-!
## Resumen del Módulo

### Definiciones Exportadas
- `gaussEven`, `chordsInterlace`, `strictlyBetween`: paridad de Gauss
- `isRealizable`: predicado de realizabilidad (irreducible + paridad de Gauss)
- `realizableConfigs`: conjunto de configs realizables (= `Orb(trefoilKnot)`)
- `realizabilityAlgorithm`: Algoritmo decidible

### Teoremas Principales

**Caracterización:**
- `realizable_iff_trefoil_orbit`: realizable ⟺ órbita del trébol
- `k3_realizability_characterization`: criterio completo
- `realizable_iff_representative`: caracterización por representantes
- `specialClass_not_realizable`, `only_trefoil_orbit_realizable`

**Conteos:**
- `total_realizable_configs`: 2 configuraciones
- `realizable_fraction`: 1/60 de probabilidad
- `non_realizable_count`: 118 no realizables
- `irreducible_not_realizable_count`: 12 irreducibles no realizables

**Criterios:**
- `not_realizable_criterion`: Certificado de no-realizabilidad
- `orbit_membership_certificate`: Verificación de pertenencia
- `realizable_by_transformation`: Realizabilidad por transformación

**Corolarios:**
- `gaussEven_iff_of_smul`, `realizable_preserved_by_D6`: preservación bajo simetrías
- `realizability_algorithm_correct`: Corrección del algoritmo

### Estado del Módulo
- Sin `sorry` ni axiomas propios
- Ejemplos y verificaciones funcionales

-/
