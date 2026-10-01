-- TCN_05_Orbitas.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 5 - Órbitas y Simetrías

import TMENudos.TCN_04_DihedralD6
import TMENudos.TCN_02_Reidemeister
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bloque 5: Órbitas y Simetrías

Definiciones de órbitas y estabilizadores usando acciones de D₆.

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralD6 K3Config
open BigOperators

instance : DecidableEq K3Config := inferInstance
instance : DecidableEq DihedralD6 := inferInstance

/-! ## Instancia MulAction -/

-- La instancia se hereda de TCN_04_DihedralD6

/-! ## Órbitas -/

/-- La órbita de una configuración K bajo D₆.

    ✅ RESUELTO: Implementación concreta -/
def orbit (K : K3Config) : Finset K3Config :=
  Finset.univ.image (fun g : DihedralD6 => DihedralD6.actOnConfig g K)

/-- Notación para órbita -/
notation "Orb(" K ")" => orbit K

/-! ## Estabilizadores -/

/-- El estabilizador de una configuración K.

    ✅ RESUELTO: Implementación concreta -/
def stabilizer (K : K3Config) : Finset DihedralD6 :=
  Finset.univ.filter (fun g => DihedralD6.actOnConfig g K = K)

/-- Notación para estabilizador -/
notation "Stab(" K ")" => stabilizer K

/-! ## Teoremas Básicos -/

/-- Toda configuración está en su propia órbita -/
theorem mem_orbit_self (K : K3Config) : K ∈ Orb(K) := by
  unfold orbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  use 1
  exact DihedralD6.actOnConfig_id K

/-- La identidad siempre está en el estabilizador -/
theorem one_mem_stabilizer (K : K3Config) : 1 ∈ Stab(K) := by
  unfold stabilizer
  simp [DihedralD6.actOnConfig_id]

/-! ## Propiedades de Órbitas -/

/-- Dos configuraciones están en la misma órbita ssi una es imagen de la otra -/
theorem in_same_orbit_iff (K₁ K₂ : K3Config) :
  K₂ ∈ Orb(K₁) ↔ ∃ g : DihedralD6, DihedralD6.actOnConfig g K₁ = K₂ := by
  unfold orbit
  simp [Finset.mem_image]

/-- Si K₂ no está en Orb(K₁), entonces las órbitas son disjuntas -/
theorem orbits_disjoint (K₁ K₂ : K3Config) :
  K₂ ∉ Orb(K₁) → Orb(K₁) ∩ Orb(K₂) = ∅ := by
  intro hK
  ext C
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  apply hK
  obtain ⟨g1, hg1⟩ := (in_same_orbit_iff K₁ C).mp h1
  obtain ⟨g2, hg2⟩ := (in_same_orbit_iff K₂ C).mp h2
  refine (in_same_orbit_iff K₁ K₂).mpr ⟨g2⁻¹ * g1, ?_⟩
  rw [DihedralD6.actOnConfig_comp, hg1, ← hg2, ← DihedralD6.actOnConfig_comp,
    inv_mul_cancel, DihedralD6.actOnConfig_id]

/-! ## Lemas auxiliares -/

/-- El grupo D₆ tiene cardinalidad 12 -/
lemma card_D6 : Finset.card (Finset.univ : Finset DihedralD6) = 12 := by
  exact calc
    Finset.card (Finset.univ : Finset DihedralD6) = 12 := by
      simp [DihedralD6.card_eq_12]
    _ = 12 := rfl

/-- El estabilizador es un subgrupo -/
theorem stabilizer_is_subgroup (K : K3Config) :
    (1 : DihedralD6) ∈ Stab(K) ∧
    (∀ g h, g ∈ Stab(K) → h ∈ Stab(K) → g * h ∈ Stab(K)) ∧
    (∀ g, g ∈ Stab(K) → g⁻¹ ∈ Stab(K)) := by
  constructor
  · exact one_mem_stabilizer K
  constructor
  · intro g h hg hh
    unfold stabilizer at *
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg hh ⊢
    rw [DihedralD6.actOnConfig_comp, hh, hg]
  · intro g hg
    unfold stabilizer at *
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [← hg, ← DihedralD6.actOnConfig_comp, inv_mul_cancel, DihedralD6.actOnConfig_id, hg]

/-! ## Teorema Órbita-Estabilizador -/

/-- Teorema órbita-estabilizador: |Orb(K)| * |Stab(K)| = |D₆| = 12 -/
theorem orbit_stabilizer (K : K3Config) :
    (Orb(K)).card * (Stab(K)).card = 12 := by
  let f : DihedralD6 → K3Config := fun g => DihedralD6.actOnConfig g K
  have h_fiber_bij (C : K3Config) (hC : C ∈ Orb(K)) :
      ∃ g, C = f g ∧ (Finset.filter (fun x => f x = C) Finset.univ).card = (Stab(K)).card := by
    rcases (in_same_orbit_iff K C).mp hC with ⟨g, hg⟩
    use g
    constructor
    · exact hg.symm
    · let map : DihedralD6 → DihedralD6 := fun s => g * s
      have h_im : (Stab(K)).image map = Finset.filter (fun x => f x = C) Finset.univ := by
        ext x
        simp only [map, stabilizer, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro h
          rcases h with ⟨s, hs, rfl⟩
          dsimp [f]
          rw [← hg, DihedralD6.actOnConfig_comp, hs]
        · intro hx
          refine ⟨g⁻¹ * x, ?_, ?_⟩
          · dsimp [f] at hx ⊢
            rw [DihedralD6.actOnConfig_comp, hx, ← hg, ← DihedralD6.actOnConfig_comp,
              inv_mul_cancel, DihedralD6.actOnConfig_id]
          · simp
      rw [← h_im, Finset.card_image_of_injective]
      intro a b h
      exact mul_left_cancel h
  calc
    (Orb(K)).card * (Stab(K)).card
        = Finset.sum (Orb(K) : Finset K3Config) (fun C => (Stab(K)).card) := by
      rw [Finset.sum_const, smul_eq_mul]
    _ = Finset.sum (Orb(K) : Finset K3Config)
          (fun C => (Finset.filter (fun g => f g = C)
            (Finset.univ : Finset DihedralD6)).card) := by
      refine Finset.sum_congr rfl fun C hC => ?_
      rcases h_fiber_bij C hC with ⟨_, _, h_card⟩
      rw [h_card]
    _ = (Finset.univ : Finset DihedralD6).card := by
      -- Orb(K) == univ.image f
      symm
      exact Finset.card_eq_sum_card_fiberwise (f := f) (t := Orb(K))
        (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
    _ = 12 := card_D6

/-! ## Cálculo de tamaño de órbita -/

/-- Cálculo de tamaño de órbita a partir del tamaño del estabilizador -/
theorem orbit_card_from_stabilizer (K : K3Config) (n : ℕ) (hn : 0 < n) (_ : n ∣ 12) :
    (Stab(K)).card = n → (Orb(K)).card = 12 / n := by
  intro h_stab
  have h_total := orbit_stabilizer K
  rw [h_stab, mul_comm] at h_total
  exact Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt hn) h_total

/-! ## Corolarios útiles -/

/-- Versión alternativa del teorema órbita-estabilizador -/
theorem orbit_stabilizer' (K : K3Config) :
    (Orb(K)).card = 12 / (Stab(K)).card ∧ (Stab(K)).card ∣ 12 := by
  have h_card := orbit_stabilizer K
  have h_pos : 0 < (Stab(K)).card := by
    have : 1 ∈ Stab(K) := one_mem_stabilizer K
    exact Finset.card_pos.mpr ⟨1, this⟩
  constructor
  · rw [mul_comm] at h_card
    exact Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt h_pos) h_card
  · exact Dvd.intro_left _ h_card

/-- El tamaño de la órbita divide al tamaño del grupo -/
theorem orbit_card_dvd (K : K3Config) : (Orb(K)).card ∣ 12 := by
  have h := orbit_stabilizer' K
  rcases h with ⟨h_eq, h_div⟩
  rw [h_eq]
  exact Nat.div_dvd_of_dvd h_div

/-- El tamaño del estabilizador divide al tamaño del grupo -/
theorem stabilizer_card_dvd (K : K3Config) : (Stab(K)).card ∣ 12 :=
  (orbit_stabilizer' K).2

/-- Órbita de tamaño 6 -/
theorem orbit_card_6_of_stab_2 (K : K3Config) :
  (Stab(K)).card = 2 → (Orb(K)).card = 6 := by
  exact orbit_card_from_stabilizer K 2 (by norm_num) (by norm_num)

/-- Órbita de tamaño 4 -/
theorem orbit_card_4_of_stab_3 (K : K3Config) :
  (Stab(K)).card = 3 → (Orb(K)).card = 4 := by
  exact orbit_card_from_stabilizer K 3 (by norm_num) (by norm_num)

/-- Órbita de tamaño 3 -/
theorem orbit_card_3_of_stab_4 (K : K3Config) :
  (Stab(K)).card = 4 → (Orb(K)).card = 3 := by
  exact orbit_card_from_stabilizer K 4 (by norm_num) (by norm_num)


/-! ## Configuraciones sin R1 ni R2 -/

/-- Conjunto de todas las configuraciones K₃ FIRMADAS sin movimientos R1 ni R2
    (R2 exige signos opuestos).

    MIGRACIÓN (signo como dato): antes era `noncomputable` porque `Fintype K3Config` lo era;
    ahora `Fintype K3Config` es computable (TCN_01) y la definición es un `Finset.filter`
    ordinario sobre las 960 configuraciones. -/
def configsNoR1NoR2 : Finset K3Config :=
  Finset.univ.filter (fun K => ¬hasR1 K ∧ ¬hasR2 K)

/-- Membresía en `configsNoR1NoR2`. -/
theorem mem_configsNoR1NoR2 (K : K3Config) :
    K ∈ configsNoR1NoR2 ↔ ¬hasR1 K ∧ ¬hasR2 K := by
  simp [configsNoR1NoR2]

/-- **El número de configuraciones firmadas sin R1 ni R2 es 172.**

    MIGRACIÓN (cifra): antes → después: 14 (de 120) → 172 (de 960).
    Se obtiene directamente de `counts_signed` (TCN_02, `decide +kernel` sobre las 960
    configuraciones). Ya NO hace falta la enumeración auxiliar `allOrderedPairs`/`goodPairs`/
    `configsNoR1NoR2_map_pairs`/`good_pairs_card` (subconjuntos de 3 de los 30 pares sin signo,
    que con el signo serían 34 220 de 60): `K3Config` es `Fintype` computable, así que se cuenta
    el tipo mismo, y la equivalencia con los subconjuntos de pares es la de `equivFinset`
    (demostrada, `K3Config.card_eq_960`).

    ✅ Antes era un `axiom`; luego teorema con `decide +kernel`; ahora es un corolario de
    `counts_signed`. -/
theorem configs_no_r1_no_r2_card : configsNoR1NoR2.card = 172 :=
  counts_signed.2.2

/-! ## Predicados de clasicidad (regla 8 del plan de migración)

El TIPO firmado `K3Config` es libre (960 configuraciones). La clasicidad (que la configuración
sea un diagrama plano) se impone por PREDICADOS, no restringiendo el tipo:
`gaussEven` (paridad de Gauss, NO mira el signo) e `indexZero` (consistencia de signos: el
índice de cada cuerda es 0, condición NECESARIA de planaridad). Se definen aquí (y no en
TCN_08) porque la clasificación de TCN_07 ya necesita `indexZero`. -/

/-- `x` está **estrictamente entre** `a` y `b` en el orden lineal `0 < 1 < ... < 5` de los
    representantes `.val` de `ZMod 6` (se compara con `.val`, NO con el orden cíclico). -/
def strictlyBetween (a b x : ZMod 6) : Prop :=
  min a.val b.val < x.val ∧ x.val < max a.val b.val

instance (a b x : ZMod 6) : Decidable (strictlyBetween a b x) :=
  inferInstanceAs (Decidable (min a.val b.val < x.val ∧ x.val < max a.val b.val))

/-- La pareja `q` **se entrelaza** con la pareja `p` si exactamente uno de los extremos
    de `q` está estrictamente entre los extremos de `p` (las cuerdas se cruzan en el
    círculo de 6 puntos).  Se exige además que los cuatro extremos sean distintos, lo que
    hace el predicado invariante bajo rotaciones; una pareja no se entrelaza consigo
    misma.  NO depende del signo. -/
def chordsInterlace (p q : OrderedPair) : Prop :=
  (p.fst ≠ q.fst ∧ p.fst ≠ q.snd ∧ p.snd ≠ q.fst ∧ p.snd ≠ q.snd) ∧
  (strictlyBetween p.fst p.snd q.fst ↔ ¬ strictlyBetween p.fst p.snd q.snd)

instance (p q : OrderedPair) : Decidable (chordsInterlace p q) :=
  inferInstanceAs (Decidable ((p.fst ≠ q.fst ∧ p.fst ≠ q.snd ∧ p.snd ≠ q.fst ∧ p.snd ≠ q.snd) ∧
    (strictlyBetween p.fst p.snd q.fst ↔ ¬ strictlyBetween p.fst p.snd q.snd)))

/-- **Condición de paridad de Gauss** para K₃: cada pareja se entrelaza con un número PAR
    de las otras parejas de la configuración.  Es condición NECESARIA de planaridad
    (todo código de Gauss de un diagrama de nudo clásico la cumple) y no mira el signo. -/
def gaussEven (K : K3Config) : Prop :=
  ∀ p ∈ K.pairs, (K.pairs.filter (chordsInterlace p)).card % 2 = 0

instance (K : K3Config) : Decidable (gaussEven K) :=
  Finset.decidableDforallFinset

/-- `x` está en el **arco abierto** que va de `o` a `u` recorriendo `Z/6Z` en sentido creciente
    (las posiciones `o+1, o+2, …, u-1`).  Copia de `arc` de la sonda
    `Procesos/Tests/auditoria_20260929/14_conteos_k3_firmados.py`. -/
def inArc (o u x : ZMod 6) : Prop :=
  0 < (x - o).val ∧ (x - o).val < (u - o).val

instance (o u x : ZMod 6) : Decidable (inArc o u x) :=
  inferInstanceAs (Decidable (0 < (x - o).val ∧ (x - o).val < (u - o).val))

/-- **Índice de la cuerda `c = (o,u)`** en la configuración `K`: suma, sobre las cuerdas `d`
    entrelazadas con `c` (automáticamente `d ≠ c`), de `+sgn d` si el extremo SUPERIOR de `d`
    (`d.fst`, el primero de la pareja) cae en el arco de `o` a `u` (`inArc`), y `-sgn d` si cae
    el inferior (`d.snd`).  `sgn d = d.posSign` se lee del campo `pos`. -/
def chordIndex (K : K3Config) (c : OrderedPair) : ℤ :=
  ∑ d ∈ K.pairs.filter (chordsInterlace c),
    (if inArc c.fst c.snd d.fst then d.posSign else -d.posSign)

/-- **Condición de índice cero**: el índice de TODA cuerda de la configuración es 0.  Es una
    condición NECESARIA de planaridad que SÍ mira el signo (un trébol con signos mixtos pasa la
    paridad de Gauss pero no el índice cero).

    **CONJETURA NO DEMOSTRADA:** que el índice cero caracterice la planaridad en general.  Para
    K₃ solo se ha comprobado (por cálculo, en este proyecto) que, junto con irreducibilidad, da
    exactamente los dos tréboles. -/
def indexZero (K : K3Config) : Prop :=
  ∀ c ∈ K.pairs, chordIndex K c = 0

instance (K : K3Config) : Decidable (indexZero K) :=
  Finset.decidableDforallFinset


/-!
## Resumen

✅ **Definiciones resueltas** (sin sorry):
- `orbit`: Línea 36
- `stabilizer`: Línea 45
- `MulAction` instance

✅ **Teoremas básicos probados**:
- `mem_orbit_self`
- `one_mem_stabilizer`

✅ **Teoremas avanzados probados** (sin sorry): `orbit_stabilizer`, `orbit_card_from_stabilizer`,
`configsNoR1NoR2` (definición concreta) y `configs_no_r1_no_r2_card` (= 172 firmadas; antes 14).
✅ **Predicados de clasicidad**: `gaussEven`, `indexZero` (regla 8).

-/

end KnotTheory
