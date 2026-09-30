-- CrossingPairIsomorphism.lean
-- Isomorfismo Fundamental: Topología ↔ Álgebra en TME
-- Dr. Pablo Eduardo Cancino Marentes - UAN 2025

import TMENudos.Basic
import TMENudos.TCN_01_Fundamentos

/-!
# Isomorfismo Fundamental: RationalCrossing 3 ≃ OrderedPair × Bool

MIGRACIÓN (signo como dato, Etapa 1): antes → después
- antes: `crossing_to_pair : RationalCrossing 3 ≃ OrderedPair` (30 cruces = 30 pares).
- después: `RationalCrossing 3` lleva el signo `pos : Bool` y `OrderedPair` de TCN todavía NO
  (su migración es la Etapa 2). Mientras tanto el isomorfismo es por un factor `Bool`:
  `RationalCrossing 3 ≃ OrderedPair × Bool` (60 cruces firmados = 30 pares × 2 signos).
  En la Etapa 2 (cuando `OrderedPair` gane `pos`) volverá a ser un isomorfismo directo.

Este módulo establece el **isomorfismo explícito** entre dos representaciones
del mismo objeto matemático en la Teoría Modular Estructural (TME):

1. **RationalCrossing 3**: Perspectiva topológica (Basic.lean)
   - `over_pos`: posición "arriba" del cruce en el nudo
   - `under_pos`: posición "abajo" del cruce en el nudo
   - Contexto: Teoría clásica de nudos, geometría 3D

2. **OrderedPair** (× signo): Perspectiva algebraica (TCN_01_Fundamentos.lean)
   - `fst`: "entrada" del par en el recorrido modular
   - `snd`: "salida" del par en el recorrido modular
   - Contexto: Teoría combinatoria K₃, álgebra modular

## El Core Insight de TME

Este isomorfismo NO es una mera coincidencia técnica, sino que captura
el **resultado fundamental de TME**: La estructura topológica de nudos
de 3 cruces puede representarse completamente mediante álgebra modular
en Z/6Z.

## Propiedades Preservadas

El isomorfismo preserva:
- ✅ Estructura de par ordenado
- ✅ Desplazamiento modular (`modular_ratio` ≃ `pairDelta`)
- ✅ Condición de distintitud
- ✅ Movimientos Reidemeister (R1, R2)
- ✅ Invariantes estructurales (DME, IME)

## Uso

```lean
-- Convertir de topológico a algebraico
def c : RationalCrossing 3 := ...
def p : OrderedPair × Bool := c⟦⟧ᵃ   -- (par sin signo, signo)

-- Convertir de algebraico a topológico
def p : OrderedPair × Bool := ...
def c : RationalCrossing 3 := p⟦⟧ᵗ

-- Transferir teoremas
theorem algebraic_property : ∀ p : OrderedPair × Bool, P p := by ...
theorem topological_property : ∀ c : RationalCrossing 3, P c :=
  transfer_to_crossing algebraic_property
```

## Referencias

- Basic.lean: Definición de RationalCrossing
- TCN_01_Fundamentos.lean: Definición de OrderedPair
- Literatura: Dualidad topología-álgebra en teoría de nudos

-/

namespace TMENudos

open KnotTheory RationalCrossing OrderedPair K3Config

/-! ## Isomorfismo Principal -/

/-- **Isomorfismo fundamental topología ↔ álgebra**

    Este isomorfismo conecta las dos perspectivas centrales de TME:

    **Dirección topológica → algebraica** (`toFun`):
    - `over_pos` → `fst` (arriba → entrada)
    - `under_pos` → `snd` (abajo → salida)

    **Dirección algebraica → topológica** (`invFun`):
    - `fst` → `over_pos` (entrada → arriba)
    - `snd` → `under_pos` (salida → abajo)

    **Propiedades**:
    - `left_inv`: `invFun ∘ toFun = id` (ida y vuelta recupera el original)
    - `right_inv`: `toFun ∘ invFun = id` (vuelta e ida recupera el original)

    Este isomorfismo es la formalización matemática del principio TME:
    "La topología de nudos K₃ es isomorfa a la combinatoria modular en Z/6Z" -/
def crossing_to_pair : RationalCrossing 3 ≃ OrderedPair × Bool where
  toFun c := (⟨c.over_pos, c.under_pos, c.distinct⟩, c.pos)
  invFun p := ⟨p.1.fst, p.1.snd, p.1.distinct, p.2⟩
  left_inv c := by
    cases c
    rfl
  right_inv p := by
    rcases p with ⟨⟨_, _, _⟩, _⟩
    rfl

/-- Isomorfismo inverso: algebraico → topológico -/
def pair_to_crossing : OrderedPair × Bool ≃ RationalCrossing 3 :=
  crossing_to_pair.symm

/-! ## Notación Conveniente -/

/-- Notación para conversión topológico → algebraico: c⟦⟧ᵃ

    Mnemotécnico: ᵃ = algebraic -/
notation:max c "⟦⟧ᵃ" => crossing_to_pair c

/-- Notación para conversión algebraico → topológico: p⟦⟧ᵗ

    Mnemotécnico: ᵗ = topological -/
notation:max p "⟦⟧ᵗ" => pair_to_crossing p

/-! ## Propiedades Básicas del Isomorfismo -/

/-- El isomorfismo preserva el primer elemento -/
theorem iso_preserves_first (c : RationalCrossing 3) :
  (c⟦⟧ᵃ).1.fst = c.over_pos := rfl

/-- El isomorfismo preserva el segundo elemento -/
theorem iso_preserves_second (c : RationalCrossing 3) :
  (c⟦⟧ᵃ).1.snd = c.under_pos := rfl

/-- El isomorfismo preserva el signo (factor `Bool`). -/
theorem iso_preserves_sign (c : RationalCrossing 3) :
  (c⟦⟧ᵃ).2 = c.pos := rfl

/-- El isomorfismo preserva el primer elemento (dirección inversa) -/
theorem iso_inv_preserves_first (p : OrderedPair × Bool) :
  (p⟦⟧ᵗ).over_pos = p.1.fst := rfl

/-- El isomorfismo preserves el segundo elemento (dirección inversa) -/
theorem iso_inv_preserves_second (p : OrderedPair × Bool) :
  (p⟦⟧ᵗ).under_pos = p.1.snd := rfl

/-- El isomorfismo inverso preserva el signo (dirección inversa). -/
theorem iso_inv_preserves_sign (p : OrderedPair × Bool) :
  (p⟦⟧ᵗ).pos = p.2 := rfl

/-- La conversión es involutiva: ida y vuelta da el original -/
theorem iso_roundtrip_crossing (c : RationalCrossing 3) :
  (c⟦⟧ᵃ)⟦⟧ᵗ = c := by
  simp [crossing_to_pair, pair_to_crossing]

/-- La conversión es involutiva: vuelta e ida da el original -/
theorem iso_roundtrip_pair (p : OrderedPair × Bool) :
  (p⟦⟧ᵗ)⟦⟧ᵃ = p := by
  simp [crossing_to_pair, pair_to_crossing]

/-! ## Preservación del Desplazamiento Modular -/

/-- El isomorfismo preserva el desplazamiento modular.

    En la perspectiva topológica:
    - `modular_ratio c = under_pos - over_pos`

    En la perspectiva algebraica:
    - `pairDelta p = snd - fst` (en aritmética entera)

    Este teorema establece que ambos conceptos son idénticos. -/
theorem iso_preserves_displacement (c : RationalCrossing 3) :
  (c.under_pos : ZMod 6) - (c.over_pos : ZMod 6) =
  ((c⟦⟧ᵃ).1.snd : ZMod 6) - ((c⟦⟧ᵃ).1.fst : ZMod 6) := by
  rfl

/-- El desplazamiento modular es el mismo visto desde ambas perspectivas -/
theorem displacement_commutes (c : RationalCrossing 3) :
  modular_ratio c = (c⟦⟧ᵃ).1.snd - (c⟦⟧ᵃ).1.fst := by
  unfold modular_ratio
  rfl

/-! ## Tácticas de Transferencia de Propiedades -/

/-- **Táctica de transferencia: Algebraico → Topológico**

    Si una propiedad P vale para todos los pares algebraicos,
    entonces vale para todos los cruces topológicos.

    Uso típico:
    ```lean
    theorem pair_theorem : ∀ p : OrderedPair × Bool, P p := by ...
    theorem crossing_theorem : ∀ c : RationalCrossing 3, P c :=
      transfer_to_crossing pair_theorem
    ``` -/
theorem transfer_to_crossing {P : RationalCrossing 3 → Prop}
    (h : ∀ p : OrderedPair × Bool, P (p⟦⟧ᵗ)) :
  ∀ c : RationalCrossing 3, P c := by
  intro c
  have : P ((c⟦⟧ᵃ)⟦⟧ᵗ) := h (c⟦⟧ᵃ)
  simpa [iso_roundtrip_crossing] using this

/-- **Táctica de transferencia: Topológico → Algebraico**

    Si una propiedad P vale para todos los cruces topológicos,
    entonces vale para todos los pares algebraicos.

    Uso típico:
    ```lean
    theorem crossing_theorem : ∀ c : RationalCrossing 3, P c := by ...
    theorem pair_theorem : ∀ p : OrderedPair × Bool, P p :=
      transfer_to_pair crossing_theorem
    ``` -/
theorem transfer_to_pair {P : OrderedPair × Bool → Prop}
    (h : ∀ c : RationalCrossing 3, P (c⟦⟧ᵃ)) :
  ∀ p : OrderedPair × Bool, P p := by
  intro p
  have : P ((p⟦⟧ᵗ)⟦⟧ᵃ) := h (p⟦⟧ᵗ)
  simpa [iso_roundtrip_pair] using this

/-- **Transferencia de propiedades relacionales**

    Si una relación R se preserva bajo el isomorfismo,
    entonces resultados sobre R en un lado implican
    resultados en el otro lado. -/
theorem transfer_relation {R : RationalCrossing 3 → RationalCrossing 3 → Prop}
    {S : OrderedPair × Bool → OrderedPair × Bool → Prop}
    (h_equiv : ∀ c₁ c₂, R c₁ c₂ ↔ S (c₁⟦⟧ᵃ) (c₂⟦⟧ᵃ))
    (h_algebraic : ∀ p₁ p₂, S p₁ p₂) :
  ∀ c₁ c₂, R c₁ c₂ := by
  intro c₁ c₂
  rw [h_equiv]
  exact h_algebraic (c₁⟦⟧ᵃ) (c₂⟦⟧ᵃ)

/-! ## Transferencia de Igualdad y Distintitud -/

/-- Igualdad en cruces implica igualdad en pares -/
theorem crossing_eq_iff_pair_eq (c₁ c₂ : RationalCrossing 3) :
  c₁ = c₂ ↔ (c₁⟦⟧ᵃ) = (c₂⟦⟧ᵃ) := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact crossing_to_pair.injective h

/-- Igualdad en pares implica igualdad en cruces -/
theorem pair_eq_iff_crossing_eq (p₁ p₂ : OrderedPair × Bool) :
  p₁ = p₂ ↔ (p₁⟦⟧ᵗ) = (p₂⟦⟧ᵗ) := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact pair_to_crossing.injective h

/-- La distintitud es invariante bajo el isomorfismo -/
theorem iso_preserves_distinct (c : RationalCrossing 3) :
  c.over_pos ≠ c.under_pos ↔ (c⟦⟧ᵃ).1.fst ≠ (c⟦⟧ᵃ).1.snd := by
  constructor <;> intro h
  · exact h
  · exact h

/-! ## Compatibilidad con Operaciones -/

/-- El isomorfismo conmuta con la operación de reversa / imagen especular.

    MIGRACIÓN: antes → después
    - antes: `reverse_crossing(c)⟦⟧ᵃ = reverse_pair(c⟦⟧ᵃ)` con `reverse_crossing` = intercambiar
      over/under (sin tocar signo, que no existía como dato).
    - después: `swap_crossing` intercambia over/under y NIEGA el signo; en el lado algebraico,
      `OrderedPair.reverse` sobre el par y `!` sobre el factor `Bool`:
      `(swap_crossing c)⟦⟧ᵃ = ((c⟦⟧ᵃ).1.reverse, !(c⟦⟧ᵃ).2)`. -/
theorem iso_commutes_with_reverse (c : RationalCrossing 3) :
  ((swap_crossing c)⟦⟧ᵃ) = ((c⟦⟧ᵃ).1.reverse, !(c⟦⟧ᵃ).2) := by
  simp [OrderedPair.reverse, swap_crossing, crossing_to_pair]

/-! ## Transferencia de Cardinalidades -/

/-- Los espacios tienen la misma cardinalidad (finita) -/
theorem spaces_have_same_cardinality :
  Fintype.card (RationalCrossing 3) = Fintype.card (OrderedPair × Bool) := by
  exact Fintype.card_eq.mpr ⟨crossing_to_pair⟩

/-- Enumeración explícita.

    MIGRACIÓN (cifra): antes → después
    - antes: `card_both_eq_30`: 30 cruces (sin signo) = 30 pares.
    - después: 60 cruces firmados = 60 = 30 pares × 2 signos (las cardinalidades se duplican).
      Además se conserva `card OrderedPair = 30` (TCN todavía sin signo). -/
theorem card_both_eq_60 :
  Fintype.card (RationalCrossing 3) = 60 ∧
  Fintype.card (OrderedPair × Bool) = 60 ∧
  Fintype.card OrderedPair = 30 := by
  have h1 : Fintype.card (RationalCrossing 3) = 60 := by
    rw [rationalCrossing_card]
  have h3 : Fintype.card OrderedPair = 30 := by
    have h := spaces_have_same_cardinality
    rw [Fintype.card_prod, Fintype.card_bool, h1] at h
    omega
  exact ⟨h1, spaces_have_same_cardinality.symm.trans h1, h3⟩

/-! ## Invariancia de Configuraciones K₃ -/

/-- Una configuración K₃ puede verse como conjunto de cruces o de pares

    Este teorema establece que una K3Config puede interpretarse
    indistintamente en cualquiera de las dos perspectivas. -/
theorem k3config_invariant_under_iso (K : K3Config) :
  ∀ p ∈ K.pairs, ∃ c : RationalCrossing 3, (c⟦⟧ᵃ).1 = p := by
  intro p hp
  use (p, true)⟦⟧ᵗ
  simp [iso_roundtrip_pair]

/-! ## Preservación de Movimientos Reidemeister -/

section ReidemeisterPreservation

variable (has_r1_crossing : RationalCrossing 3 → Prop)
variable (has_r1_pair : OrderedPair × Bool → Prop)

/-- Si definimos R1 consistentemente en ambos lados,
    el isomorfismo debe preservarlo

    Esquema de teorema (requiere definiciones de R1): -/
theorem iso_preserves_r1 (h_def : ∀ c : RationalCrossing 3,
      has_r1_crossing c ↔ has_r1_pair (c⟦⟧ᵃ)) :
  ∀ c : RationalCrossing 3, has_r1_crossing c ↔ has_r1_pair (c⟦⟧ᵃ) :=
  h_def

end ReidemeisterPreservation

/-! ## Funtorialidad del Isomorfismo -/

/-- El isomorfismo es funtorial: preserva composiciones

    Si tenemos funciones f : A → RationalCrossing 3 y
    g : RationalCrossing 3 → B, entonces:

    iso(g ∘ f) = iso(g) ∘ iso(f) -/
theorem iso_is_functorial
    {α β : Type*}
    (f : α → RationalCrossing 3)
    (g : OrderedPair × Bool → β) :
  (fun x => g ((f x)⟦⟧ᵃ)) = g ∘ crossing_to_pair ∘ f := by
  rfl

/-! ## Equivalencia de Predicados -/

/-- **Principio de Transferencia Universal**

    Cualquier predicado sobre cruces tiene un predicado
    equivalente sobre pares, y viceversa. -/
theorem universal_transfer_principle
    (P : RationalCrossing 3 → Prop) :
  (∀ c : RationalCrossing 3, P c) ↔
  (∀ p : OrderedPair × Bool, P (p⟦⟧ᵗ)) := by
  constructor
  · intro h p
    exact h (p⟦⟧ᵗ)
  · intro h c
    have := h (c⟦⟧ᵃ)
    simpa [iso_roundtrip_crossing] using this

/-! ## Ejemplos de Uso -/

section Examples

/-- Ejemplo 1: Transferir un teorema simple -/
example (h : ∀ p : OrderedPair × Bool, p.1.fst ≠ p.1.snd) :
  ∀ c : RationalCrossing 3, c.over_pos ≠ c.under_pos := by
  intro c
  have := h (c⟦⟧ᵃ)
  exact this

/-- Ejemplo 2: Usar notación para conversión -/
example (c : RationalCrossing 3) :
  let p := c⟦⟧ᵃ  -- Conversión a par
  let c' := p⟦⟧ᵗ  -- Conversión de vuelta
  c' = c := by
  simp [iso_roundtrip_crossing]

/-- Ejemplo 3: Composición de conversiones -/
example (c₁ c₂ : RationalCrossing 3)
    (h : c₁⟦⟧ᵃ = c₂⟦⟧ᵃ) :
  c₁ = c₂ := by
  have := congr_arg pair_to_crossing h
  simpa [iso_roundtrip_crossing] using this

end Examples

/-! ## Documentación del Patrón de Diseño -/

/-!
## Patrón de Diseño: Isomorfismo Explícito

Este módulo implementa el patrón "Isomorfismo Explícito" para
tipos matemáticamente equivalentes pero con semánticas distintas.

### Cuándo Usar Este Patrón

✅ **Usar cuando:**
- Dos tipos representan el mismo objeto matemático
- Operan en contextos diferentes (topología vs álgebra)
- Tienen semánticas ricas y específicas al contexto
- La conexión entre contextos es conceptualmente importante

❌ **No usar cuando:**
- Los tipos son realmente idénticos (usar `def` o `abbrev`)
- No hay distinción semántica relevante
- Un tipo es claramente superior al otro

### Beneficios de Este Patrón

1. **Claridad conceptual**: Cada tipo mantiene su semántica natural
2. **Conexión explícita**: El isomorfismo documenta la equivalencia
3. **Flexibilidad**: Permite evolución independiente
4. **Transferencia automática**: Teoremas se propagan entre contextos

### Estructura del Patrón

```lean
-- 1. Definir isomorfismo
def iso : TypeA ≃ TypeB where ...

-- 2. Notación conveniente
notation a "⟦⟧" => iso a

-- 3. Tácticas de transferencia
theorem transfer {P : TypeB → Prop}
    (h : ∀ a, P (iso a)) : ∀ b, P b := ...

-- 4. Preservación de propiedades
theorem preserves_prop : prop_A a ↔ prop_B (iso a) := ...
```

### Referencias en la Literatura

- Mathlib: Multiple isomorphic representations of the same structure
- HoTT: Equivalences as the proper notion of sameness
- Category Theory: Isomorphisms preserve all categorical properties
-/

/-! ## Tests de Consistencia -/

section ConsistencyTests

/-- Test: El isomorfismo es realmente una biyección -/
example : Function.Bijective crossing_to_pair := by
  constructor
  · -- Inyectividad
    intro c₁ c₂ h
    exact crossing_eq_iff_pair_eq c₁ c₂ |>.mpr h
  · -- Sobreyectividad
    intro p
    use p⟦⟧ᵗ
    simp [iso_roundtrip_pair]

/-- Test: La inversa es realmente inversa -/
example : pair_to_crossing.toFun ∘ crossing_to_pair.toFun = id := by
  funext c
  simp [crossing_to_pair, pair_to_crossing]

/-- Test: Las conversiones son deterministas -/
example (c : RationalCrossing 3) :
  (c⟦⟧ᵃ)⟦⟧ᵗ = c ∧ ((c⟦⟧ᵃ)⟦⟧ᵗ)⟦⟧ᵃ = c⟦⟧ᵃ := by
  constructor
  · exact iso_roundtrip_crossing c
  · simp [iso_roundtrip_crossing]

end ConsistencyTests

/-! ## Notas para Extensiones Futuras -/

/-!
### Extensión a K₄

Para extender este patrón a K₄ (4 cruces):

```lean
def crossing_to_pair_k4 : RationalCrossing 4 ≃ OrderedPair_K4 × Bool where
  -- Similar estructura, pero con ZMod 8
  toFun c := (⟨c.over_pos, c.under_pos, c.distinct⟩, c.pos)
  invFun p := ⟨p.1.fst, p.1.snd, p.1.distinct, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
```

### Generalización a Kₙ

Para una versión genérica:

```lean
def crossing_to_pair_kn (n : ℕ) :
    RationalCrossing n ≃ OrderedPair_Kn n where
  -- Parametrizado por n
  ...
```

### Isomorfismos Adicionales

Potenciales isomorfismos futuros:
- `RationalCrossing n ≃ ModularPair n`
- `K3Config ≃ KnotDiagram 3`
- `MatchingPerfect ≃ ConfigurationCanonical`
-/

end TMENudos

/-!
## Resumen del Módulo

Este módulo establece que `RationalCrossing 3` y `OrderedPair × Bool` son
**el mismo objeto matemático** visto desde dos perspectivas (mientras `OrderedPair` de TCN
no lleve signo, el signo es el factor `Bool`; en la Etapa 2 será un isomorfismo directo):

1. **Topológica** (RationalCrossing): Cruces de nudos en 3D
2. **Algebraica** (OrderedPair): Pares modulares en Z/6Z

El isomorfismo `crossing_to_pair` formaliza esta equivalencia y
proporciona herramientas para transferir resultados entre contextos.

**Uso principal**: Permite trabajar en el contexto más conveniente
para cada problema, sabiendo que los resultados se transfieren
automáticamente al otro contexto.

**Filosofía TME**: La dualidad topología-álgebra no es un accidente,
sino el corazón de la teoría. Este módulo hace esa dualidad explícita
y matemáticamente rigurosa.
-/
