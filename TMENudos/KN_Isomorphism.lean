-- KN_Isomorphism.lean
-- Isomorfismo General: Topología ↔ Álgebra para Kₙ
-- Dr. Pablo Eduardo Cancino Marentes - UAN 2025

import TMENudos.Basic
import TMENudos.KN_General

/-!
# Isomorfismo General Kₙ: RationalCrossing n ≃ OrderedPairN n × Bool

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
RationalCrossing n ≃ OrderedPairN n × Bool
  over_pos ↔ fst
  under_pos ↔ snd
  pos ↔ factor Bool (el signo; `KN_General` no lo tiene)
```

## Uso

```lean
open TMENudos KnotTheory.General

-- Topológico → Algebraico
def c : RationalCrossing 4 := ...
def p := toAlgebraic c  -- p : OrderedPairN 4 (olvida el signo)

-- Algebraico → Topológico
def p : OrderedPairN 5 := ...
def c := toTopological p true  -- c : RationalCrossing 5 (signo positivo)
```

-/

namespace TMENudos.KN_Iso

open TMENudos
open KnotTheory.General

/-! ## Isomorfismo Principal

MIGRACIÓN (signo como dato, Etapa 1): antes → después
- antes: `crossingToPair : RationalCrossing n ≃ OrderedPairN n` (cruce sin signo, biyección).
- después: `RationalCrossing n` lleva el signo `pos : Bool`, pero `OrderedPairN` (de `KN_General`,
  que NO se migra) no. El isomorfismo pasa a ser POR UN FACTOR `Bool`:
  `crossingToPair : RationalCrossing n ≃ OrderedPairN n × Bool`
  (cruce firmado ≃ cruce sin signo × signo). `toAlgebraic` olvida el signo (ya no es biyección) y
  `toTopological p s` construye el cruce con signo `s`. -/

/-- **Isomorfismo fundamental por un factor `Bool`:
    `RationalCrossing n ≃ OrderedPairN n × Bool`** (cruce firmado ≃ cruce sin signo × signo).

    **Dirección topológica → algebraica:**
    - Cruce topológico con (over_pos, under_pos, pos)
    - Se convierte en (par algebraico con fst := over_pos, snd := under_pos) y el signo `pos`.

    **Propiedades:**
    - Biyección verificable
    - Preserva distintitud
    - Preserva desplazamiento modular
-/
def crossingToPair {n : ℕ} : RationalCrossing n ≃ OrderedPairN n × Bool where
  toFun c := (⟨c.over_pos, c.under_pos, c.distinct⟩, c.pos)
  invFun p := ⟨p.1.fst, p.1.snd, p.1.distinct, p.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨⟨_, _, _⟩, _⟩; rfl

/-- Isomorfismo inverso -/
def pairToCrossing {n : ℕ} : OrderedPairN n × Bool ≃ RationalCrossing n :=
  crossingToPair.symm

/-! ## Funciones de Conversión -/

/-- Convierte un cruce topológico a par algebraico, OLVIDANDO el signo
    (antes: biyección; ahora es la primera proyección del isomorfismo). -/
def toAlgebraic {n : ℕ} (c : RationalCrossing n) : OrderedPairN n :=
  (crossingToPair c).1

/-- El signo (factor `Bool`) de un cruce topológico. -/
def toSign {n : ℕ} (c : RationalCrossing n) : Bool :=
  (crossingToPair c).2

/-- Convierte un par algebraico y un signo a cruce topológico firmado
    (antes: `toTopological p`; ahora lleva además el signo `s`). -/
def toTopological {n : ℕ} (p : OrderedPairN n) (s : Bool) : RationalCrossing n :=
  pairToCrossing (p, s)

/-! ## Propiedades Básicas -/

/-- Conversión preserva el primer elemento -/
theorem toAlgebraic_fst {n : ℕ} (c : RationalCrossing n) :
  (toAlgebraic c).fst = c.over_pos := rfl

/-- Conversión preserva el segundo elemento -/
theorem toAlgebraic_snd {n : ℕ} (c : RationalCrossing n) :
  (toAlgebraic c).snd = c.under_pos := rfl

/-- La conversión preserva el signo (factor `Bool`). -/
theorem toSign_eq {n : ℕ} (c : RationalCrossing n) : toSign c = c.pos := rfl

/-- Conversión inversa preserva over_pos -/
theorem toTopological_over {n : ℕ} (p : OrderedPairN n) (s : Bool) :
  (toTopological p s).over_pos = p.fst := rfl

/-- Conversión inversa preserva under_pos -/
theorem toTopological_under {n : ℕ} (p : OrderedPairN n) (s : Bool) :
  (toTopological p s).under_pos = p.snd := rfl

/-- Conversión inversa preserva el signo -/
theorem toTopological_pos {n : ℕ} (p : OrderedPairN n) (s : Bool) :
  (toTopological p s).pos = s := rfl

/-- La conversión es involutiva: ida y vuelta (con el signo) recupera el original -/
theorem roundtrip_crossing {n : ℕ} (c : RationalCrossing n) :
  toTopological (toAlgebraic c) (toSign c) = c := by
  simp [toTopological, toAlgebraic, toSign, pairToCrossing, crossingToPair]

/-- La conversión inversa es involutiva -/
theorem roundtrip_pair {n : ℕ} (p : OrderedPairN n) (s : Bool) :
  (toAlgebraic (toTopological p s) = p) ∧ toSign (toTopological p s) = s := by
  simp [toTopological, toAlgebraic, toSign, pairToCrossing, crossingToPair]

/-! ## Transferencia de Propiedades -/

/-- **Transferencia: Algebraico → Topológico**

    Si una propiedad vale para todos los pares algebraicos con cualquier signo,
    entonces vale para todos los cruces topológicos.
-/
theorem transferToCrossing {n : ℕ} {P : RationalCrossing n → Prop}
    (h : ∀ (p : OrderedPairN n) (s : Bool), P (toTopological p s)) :
  ∀ c : RationalCrossing n, P c := by
  intro c
  have : P (toTopological (toAlgebraic c) (toSign c)) := h (toAlgebraic c) (toSign c)
  simpa [roundtrip_crossing] using this

/-- **Transferencia: Topológico → Algebraico**

    Si una propiedad vale para (la proyección de) todos los cruces topológicos firmados,
    entonces vale para todos los pares algebraicos.
-/
theorem transferToPair {n : ℕ} {P : OrderedPairN n → Prop}
    (h : ∀ c : RationalCrossing n, P (toAlgebraic c)) :
  ∀ p : OrderedPairN n, P p := by
  intro p
  have : P (toAlgebraic (toTopological p true)) := h (toTopological p true)
  simpa [(roundtrip_pair p true).1] using this

/-! ## Igualdades -/

/-- Igualdad en cruces si y solo si igualdad en (par, signo) -/
theorem crossing_eq_iff_pair_eq {n : ℕ} (c₁ c₂ : RationalCrossing n) :
  c₁ = c₂ ↔ toAlgebraic c₁ = toAlgebraic c₂ ∧ toSign c₁ = toSign c₂ := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    rw [← roundtrip_crossing c₁, ← roundtrip_crossing c₂, h₁, h₂]

/-- Igualdad en pares si y solo si igualdad en cruces (con el mismo signo) -/
theorem pair_eq_iff_crossing_eq {n : ℕ} (p₁ p₂ : OrderedPairN n) (s : Bool) :
  p₁ = p₂ ↔ toTopological p₁ s = toTopological p₂ s := by
  constructor
  · intro h; rw [h]
  · intro h
    have h₁ := congr_arg toAlgebraic h
    rwa [(roundtrip_pair p₁ s).1, (roundtrip_pair p₂ s).1] at h₁

/-! ## Especialización para K₃ y K₄ -/

section Specializations

/-- Conversión para K₃ (3 cruces en Z/6Z) -/
abbrev k3ToPair : RationalCrossing 3 ≃ OrderedPairN 3 × Bool := crossingToPair

/-- Conversión para K₄ (4 cruces en Z/8Z) -/
abbrev k4ToPair : RationalCrossing 4 ≃ OrderedPairN 4 × Bool := crossingToPair

/-- Ejemplo: K₃ roundtrip -/
example (c : RationalCrossing 3) :
  toTopological (toAlgebraic c) (toSign c) = c := roundtrip_crossing c

/-- Ejemplo: K₄ roundtrip -/
example (c : RationalCrossing 4) :
  toTopological (toAlgebraic c) (toSign c) = c := roundtrip_crossing c

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
  let c' := toTopological p (toSign c)
  c' = c := roundtrip_crossing c

/-- Ejemplo 3: Transferencia de igualdad -/
example {n : ℕ} (c₁ c₂ : RationalCrossing n)
    (h : toAlgebraic c₁ = toAlgebraic c₂) (hs : toSign c₁ = toSign c₂) :
  c₁ = c₂ := by
  rw [← roundtrip_crossing c₁, ← roundtrip_crossing c₂]
  rw [h, hs]

end Examples

end TMENudos.KN_Iso

/-!
## Resumen

Este módulo establece el isomorfismo fundamental entre:
- **RationalCrossing n** (TMENudos.Basic - topológico)
- **OrderedPairN n × Bool** (KnotTheory.General - algebraico, más el signo)

Funciones principales:
- `toAlgebraic` : RationalCrossing n → OrderedPairN n (olvida el signo)
- `toSign` : RationalCrossing n → Bool
- `toTopological` : OrderedPairN n → Bool → RationalCrossing n

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
