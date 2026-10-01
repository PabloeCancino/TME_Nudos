import TMENudos.Basic

/-!
# Teoria modular con signo del cruce como DATO explicito (capa residual, ETAPA 4)

HISTORIA. Esta capa nacio como prototipo ADITIVO (antes de migrar `Basic` y `TCN`): definia un
cruce firmado propio, configuraciones firmadas de K3 (`SignedK3`), su accion de D₆ y la prueba de
que `mirrorS` no esta en la orbita de `trefoilS`.

ESTADO TRAS LA MIGRACION. `Basic.RationalCrossing` y `TCN.OrderedPair` ya llevan el campo
`pos : Bool`, `K3Config` tiene 960 configuraciones y D₆ conserva el signo. Por eso la parte K3 de
esta capa SE RETIRO (era duplicado): sus resultados viven ahora en `TCN_05`/`TCN_06`/`TCN_07`:
`mirrorTrefoil_not_mem_orbit_trefoilKnot`, `orbit_mirrorTrefoil_ne_orbit_trefoilKnot`,
`trefoil_mirror_not_equivalent`, `irreducible_indexZero_iff`, `k3_classification`.

QUE QUEDA. Solo la seccion 1, que conserva el hecho del signo DERIVADO (`zmod_sign (u - o)`):
en parejas antipodales el intercambio no cambia el signo derivado
(`ofDerived_swap_ne_of_antipodal`),
y eso es lo que justifico pasar el signo a dato.

Sin `sorry`, sin axiomas nuevos, sin `native_decide`.
-/

namespace TMENudos.Signo

open TMENudos

/-! ## 1. Cruce con signo (n general) -/

/-- Cruce con signo explicito: `pos = true` significa positivo.
    -- ETAPA 4: redundante con `Basic.RationalCrossing` (que ya lleva el campo `pos`). Por ahora
    se conserva tal cual: aquí `cross.pos` y `pos` son dos signos independientes; los teoremas de
    esta capa solo usan el campo `SignedCrossing.pos`. -/
@[ext]
structure SignedCrossing (n : ℕ) where
  cross : RationalCrossing n
  pos : Bool
deriving DecidableEq

/-- Imagen especular: intercambia over/under y NIEGA el signo. -/
def swapS {n : ℕ} (c : SignedCrossing n) : SignedCrossing n :=
  ⟨swap_crossing c.cross, !c.pos⟩

/-- Rotacion por `k`; conserva el signo. -/
def rotateS {n : ℕ} (k : ℝ[n]) (c : SignedCrossing n) : SignedCrossing n :=
  ⟨rotate_crossing k c.cross, c.pos⟩

/-- Signo derivado de las POSICIONES como caso particular: `σ := (zmod_sign (u - o) = 1)`.
    MIGRACIÓN: antes → después: antes `decide (crossing_sign c = 1)` (con `crossing_sign` derivado);
    ahora `crossing_sign` lee el campo `pos`, así que se usa `zmod_sign` explícitamente. -/
def ofDerived {n : ℕ} (c : RationalCrossing n) : SignedCrossing n :=
  ⟨c, decide (zmod_sign (c.under_pos - c.over_pos) = 1)⟩

theorem swapS_involutive {n : ℕ} (c : SignedCrossing n) : swapS (swapS c) = c := by
  cases c with
  | mk c b => cases c; simp [swapS, swap_crossing]

theorem rotateS_swapS {n : ℕ} (k : ℝ[n]) (c : SignedCrossing n) :
    rotateS k (swapS c) = swapS (rotateS k c) := by
  cases c with
  | mk c b => cases c; simp [swapS, rotateS, swap_crossing, rotate_crossing]

/-- Para una razon `d ≠ 0`, `zmod_sign (-d) = - zmod_sign d` salvo cuando `d.val = n`. -/
private theorem sign_neg_ne {n : ℕ} [NeZero n] (d : ℝ[n]) (hd : d ≠ 0) :
    zmod_sign (-d) = - zmod_sign d ↔ d.val ≠ n := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  haveI : NeZero d := ⟨hd⟩
  have hv : (-d).val = 2 * n - d.val := ZMod.val_neg_of_ne_zero d
  have hpos : 0 < d.val := by
    rcases Nat.eq_zero_or_pos d.val with h | h
    · exact absurd ((ZMod.val_eq_zero d).mp h) hd
    · exact h
  have hlt : d.val < 2 * n := ZMod.val_lt d
  unfold zmod_sign
  rw [hv]
  split_ifs <;> simp <;> omega

private theorem sign_cases {n : ℕ} (x : ℝ[n]) : zmod_sign x = 1 ∨ zmod_sign x = -1 := by
  unfold zmod_sign; split_ifs <;> simp

/-- El signo derivado conmuta con el intercambio SI Y SOLO SI la razon no es antipodal. -/
theorem ofDerived_swap_iff {n : ℕ} [NeZero n] (c : RationalCrossing n) :
    ofDerived (swap_crossing c) = swapS (ofDerived c) ↔ (modular_ratio c).val ≠ n := by
  have hd : modular_ratio c ≠ 0 := ratio_nonzero c
  have e1 : c.over_pos - c.under_pos = -(modular_ratio c) := by simp [modular_ratio]
  have hc : c.under_pos - c.over_pos = modular_ratio c := rfl
  have key := sign_neg_ne (modular_ratio c) hd
  simp only [ofDerived, swapS, swap_crossing, SignedCrossing.mk.injEq, true_and,
    e1, hc]
  rw [← key]
  rcases sign_cases (modular_ratio c) with h | h <;>
    rcases sign_cases (-(modular_ratio c)) with h' | h' <;> simp [h, h']

/-- Pierde quiralidad: para una pareja antipodal, el signo derivado NO conmuta con el swap. -/
theorem ofDerived_swap_ne_of_antipodal {n : ℕ} [NeZero n] (c : RationalCrossing n)
    (h : (modular_ratio c).val = n) : ofDerived (swap_crossing c) ≠ swapS (ofDerived c) := by
  intro he
  exact ((ofDerived_swap_iff c).mp he) h

/-- Y si no es antipodal, conmuta. -/
theorem ofDerived_swap_of_not_antipodal {n : ℕ} [NeZero n] (c : RationalCrossing n)
    (h : (modular_ratio c).val ≠ n) : ofDerived (swap_crossing c) = swapS (ofDerived c) :=
  (ofDerived_swap_iff c).mpr h

/-- Ejemplo concreto en n = 3: la pareja (0,3) es antipodal y pierde la quiralidad. -/
example : ofDerived (swap_crossing (⟨(0 : ℝ[3]), 3, by decide, true⟩ : RationalCrossing 3)) ≠
    swapS (ofDerived (⟨(0 : ℝ[3]), 3, by decide, true⟩ : RationalCrossing 3)) := by decide +kernel

/-! ## Axiomas -/

#print axioms swapS_involutive
#print axioms rotateS_swapS
#print axioms ofDerived_swap_iff
#print axioms ofDerived_swap_ne_of_antipodal

end TMENudos.Signo
