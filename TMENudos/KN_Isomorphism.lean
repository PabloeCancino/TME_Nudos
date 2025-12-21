-- KN_Isomorphism.lean
-- Isomorfismo General: Topología ↔ Álgebra para Kₙ
-- Dr. Pablo Eduardo Cancino Marentes - UAN 2025

import TMENudos.Basic
import TMENudos.KN_General

/-!
# Isomorfismo General Kₙ: RationalCrossing n ≃ OrderedPairN n

Este módulo establece el isomorfismo fundamental entre las representaciones
topológica (Basic.lean) y algebraica (KN_General.lean) para nudos de n cruces.

## Componentes

**Topología (TMENudos.Basic):**
- `RationalCrossing n` - Cruces con over_pos/under_pos en Z/(2n)Z
- Namespace: `TMENudos`

**Álgebra (TMENudos.KN_General):**
- `OrderedPairN n` - Pares ordenados con fst/snd en Z/(2n)Z
- Namespace: `KnotTheory.General`

## Isomorfismo

```lean
RationalCrossing n ≃ OrderedPairN n
  over_pos ↔ fst
  under_pos ↔ snd
```

## Uso

```lean
open TMENudos KnotTheory.General

-- Topológico → Algebraico
def c : RationalCrossing 4 := ...
def p := toAlgebraic c  -- p : OrderedPairN 4

-- Algebraico → Topológico
def p : OrderedPairN 5 := ...
def c := toTopological p  -- c : RationalCrossing 5
```

-/

namespace TMENudos.KN_Iso

open TMENudos
open KnotTheory.General

/-! ## Isomorfismo Principal -/

/-- **Isomorfismo fundamental: RationalCrossing n ≃ OrderedPairN n**

    Conecta las representaciones topológica y algebraica de nudos de n cruces.

    **Dirección topológica → algebraica:**
    - Cruce topológico con (over_pos, under_pos)
    - Se convierte en par algebraico con (fst := over_pos, snd := under_pos)

    **Propiedades:**
    - Biyección verificable
    - Preserva distintitud
    - Preserva desplazamiento modular
-/
def crossingToPair {n : ℕ} : RationalCrossing n ≃ OrderedPairN n where
  toFun c := ⟨c.over_pos, c.under_pos, c.distinct⟩
  invFun p := ⟨p.fst, p.snd, p.distinct⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl

/-- Isomorfismo inverso -/
def pairToCrossing {n : ℕ} : OrderedPairN n ≃ RationalCrossing n :=
  crossingToPair.symm

/-! ## Funciones de Conversión -/

/-- Convierte un cruce topológico a par algebraico -/
def toAlgebraic {n : ℕ} (c : RationalCrossing n) : OrderedPairN n :=
  crossingToPair c

/-- Convierte un par algebraico a cruce topológico -/
def toTopological {n : ℕ} (p : OrderedPairN n) : RationalCrossing n :=
  pairToCrossing p

/-! ## Propiedades Básicas -/

/-- Conversión preserva el primer elemento -/
theorem toAlgebraic_fst {n : ℕ} (c : RationalCrossing n) :
  (toAlgebraic c).fst = c.over_pos := rfl

/-- Conversión preserva el segundo elemento -/
theorem toAlgebraic_snd {n : ℕ} (c : RationalCrossing n) :
  (toAlgebraic c).snd = c.under_pos := rfl

/-- Conversión inversa preserva over_pos -/
theorem toTopological_over {n : ℕ} (p : OrderedPairN n) :
  (toTopological p).over_pos = p.fst := rfl

/-- Conversión inversa preserva under_pos -/
theorem toTopological_under {n : ℕ} (p : OrderedPairN n) :
  (toTopological p).under_pos = p.snd := rfl

/-- La conversión es involutiva: ida y vuelta recupera el original -/
theorem roundtrip_crossing {n : ℕ} (c : RationalCrossing n) :
  toTopological (toAlgebraic c) = c := by
  simp [toTopological, toAlgebraic, pairToCrossing, crossingToPair]

/-- La conversión inversa es involutiva -/
theorem roundtrip_pair {n : ℕ} (p : OrderedPairN n) :
  toAlgebraic (toTopological p) = p := by
  simp [toTopological, toAlgebraic, pairToCrossing, crossingToPair]

/-! ## Transferencia de Propiedades -/

/-- **Transferencia: Algebraico → Topológico**

    Si una propiedad vale para todos los pares algebraicos,
    entonces vale para todos los cruces topológicos.
-/
theorem transferToCrossing {n : ℕ} {P : RationalCrossing n → Prop}
    (h : ∀ p : OrderedPairN n, P (toTopological p)) :
  ∀ c : RationalCrossing n, P c := by
  intro c
  have : P (toTopological (toAlgebraic c)) := h (toAlgebraic c)
  simpa [roundtrip_crossing] using this

/-- **Transferencia: Topológico → Algebraico**

    Si una propiedad vale para todos los cruces topológicos,
    entonces vale para todos los pares algebraicos.
-/
theorem transferToPair {n : ℕ} {P : OrderedPairN n → Prop}
    (h : ∀ c : RationalCrossing n, P (toAlgebraic c)) :
  ∀ p : OrderedPairN n, P p := by
  intro p
  have : P (toAlgebraic (toTopological p)) := h (toTopological p)
  simpa [roundtrip_pair] using this

/-! ## Igualdades -/

/-- Igualdad en cruces si y solo si igualdad en pares -/
theorem crossing_eq_iff_pair_eq {n : ℕ} (c₁ c₂ : RationalCrossing n) :
  c₁ = c₂ ↔ toAlgebraic c₁ = toAlgebraic c₂ := by
  constructor
  · intro h; rw [h]
  · intro h
    have h₁ := congr_arg toTopological h
    simp [roundtrip_crossing] at h₁
    exact h₁

/-- Igualdad en pares si y solo si igualdad en cruces -/
theorem pair_eq_iff_crossing_eq {n : ℕ} (p₁ p₂ : OrderedPairN n) :
  p₁ = p₂ ↔ toTopological p₁ = toTopological p₂ := by
  constructor
  · intro h; rw [h]
  · intro h
    have h₁ := congr_arg toAlgebraic h
    simp [roundtrip_pair] at h₁
    exact h₁

/-! ## Especialización para K₃ y K₄ -/

section Specializations

/-- Conversión para K₃ (3 cruces en Z/6Z) -/
abbrev k3ToPair : RationalCrossing 3 ≃ OrderedPairN 3 := crossingToPair

/-- Conversión para K₄ (4 cruces en Z/8Z) -/
abbrev k4ToPair : RationalCrossing 4 ≃ OrderedPairN 4 := crossingToPair

/-- Ejemplo: K₃ roundtrip -/
example (c : RationalCrossing 3) :
  toTopological (toAlgebraic c) = c := roundtrip_crossing c

/-- Ejemplo: K₄ roundtrip -/
example (c : RationalCrossing 4) :
  toTopological (toAlgebraic c) = c := roundtrip_crossing c

end Specializations

/-! ## Ejemplos de Uso -/

section Examples

/-- Ejemplo 1: Transferir distinción -/
example {n : ℕ} (h : ∀ p : OrderedPairN n, p.fst ≠ p.snd) :
  ∀ c : RationalCrossing n, c.over_pos ≠ c.under_pos := by
  intro c
  have := h (toAlgebraic c)
  exact this

/-- Ejemplo 2: Bidireccionalidad -/
example {n : ℕ} (c : RationalCrossing n) :
  let p := toAlgebraic c
  let c' := toTopological p
  c' = c := roundtrip_crossing c

/-- Ejemplo 3: Transferencia de igualdad -/
example {n : ℕ} (c₁ c₂ : RationalCrossing n)
    (h : toAlgebraic c₁ = toAlgebraic c₂) :
  c₁ = c₂ := by
  rw [← roundtrip_crossing c₁, ← roundtrip_crossing c₂]
  rw [h]

end Examples

end TMENudos.KN_Iso

/-!
## Resumen

Este módulo establece el isomorfismo fundamental entre:
- **RationalCrossing n** (TMENudos.Basic - topológico)
- **OrderedPairN n** (KnotTheory.General - algebraico)

Funciones principales:
- `toAlgebraic` : RationalCrossing n → OrderedPairN n
- `toTopological` : OrderedPairN n → RationalCrossing n

Propiedades:
- ✅ Biyección verificable
- ✅ Conversiones involutivas (roundtrip)
- ✅ Transferencia de teoremas entre contextos
- ✅ Especialización para K₃, K₄, K₅, ...

**Uso típico:**
```lean
open TMENudos KnotTheory.General TMENudos.KN_Iso

def c : RationalCrossing 4 := ...
def p := toAlgebraic c  -- Ahora en contexto algebraico
```
-/
