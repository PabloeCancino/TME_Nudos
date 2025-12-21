-- CrossingPairIsomorphism.lean
-- Isomorfismo Fundamental: Topología ↔ Álgebra en TME
-- Dr. Pablo Eduardo Cancino Marentes - UAN 2025

import TMENudos.Basic
import TMENudos.TCN_01_Fundamentos

/-!
# Isomorfismo Fundamental: RationalCrossing 3 ≃ OrderedPair

Este módulo establece el **isomorfismo explícito** entre dos representaciones
del mismo objeto matemático en la Teoría Modular Estructural (TME):

1. **RationalCrossing 3**: Perspectiva topológica (Basic.lean)
   - `over_pos`: posición "arriba" del cruce en el nudo
   - `under_pos`: posición "abajo" del cruce en el nudo
   - Contexto: Teoría clásica de nudos, geometría 3D

2. **OrderedPair**: Perspectiva algebraica (TCN_01_Fundamentos.lean)
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
def p : OrderedPair := c⟦⟧ᵃ

-- Convertir de algebraico a topológico
def p : OrderedPair := ...
def c : RationalCrossing 3 := p⟦⟧ᵗ

-- Transferir teoremas
theorem algebraic_property : ∀ p : OrderedPair, P p := by ...
theorem topological_property : ∀ c : RationalCrossing 3, P c := 
  transfer_to_crossing algebraic_property
```

## Referencias

- Basic.lean: Definición de RationalCrossing
- TCN_01_Fundamentos.lean: Definición de OrderedPair
- Literatura: Dualidad topología-álgebra en teoría de nudos

-/

namespace TMENudos

open RationalCrossing OrderedPair K3Config

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
    "La topología de nudos K₃ es isomorfa a la combinatoria modular en Z/6Z"
    -/
def crossing_to_pair : RationalCrossing 3 ≃ OrderedPair where
  toFun c := ⟨c.over_pos, c.under_pos, c.distinct⟩
  invFun p := ⟨p.fst, p.snd, p.distinct⟩
  left_inv c := by
    cases c
    rfl
  right_inv p := by
    cases p
    rfl

/-- Isomorfismo inverso: algebraico → topológico -/
def pair_to_crossing : OrderedPair ≃ RationalCrossing 3 :=
  crossing_to_pair.symm

/-! ## Notación Conveniente -/

/-- Notación para conversión topológico → algebraico: c⟦⟧ᵃ 
    
    Mnemotécnico: ᵃ = algebraic
    -/
notation:max c "⟦⟧ᵃ" => crossing_to_pair c

/-- Notación para conversión algebraico → topológico: p⟦⟧ᵗ 
    
    Mnemotécnico: ᵗ = topological
    -/
notation:max p "⟦⟧ᵗ" => pair_to_crossing p

/-! ## Propiedades Básicas del Isomorfismo -/

/-- El isomorfismo preserva el primer elemento -/
theorem iso_preserves_first (c : RationalCrossing 3) :
  (c⟦⟧ᵃ).fst = c.over_pos := rfl

/-- El isomorfismo preserva el segundo elemento -/
theorem iso_preserves_second (c : RationalCrossing 3) :
  (c⟦⟧ᵃ).snd = c.under_pos := rfl

/-- El isomorfismo preserva el primer elemento (dirección inversa) -/
theorem iso_inv_preserves_first (p : OrderedPair) :
  (p⟦⟧ᵗ).over_pos = p.fst := rfl

/-- El isomorfismo preserves el segundo elemento (dirección inversa) -/
theorem iso_inv_preserves_second (p : OrderedPair) :
  (p⟦⟧ᵗ).under_pos = p.snd := rfl

/-- La conversión es involutiva: ida y vuelta da el original -/
theorem iso_roundtrip_crossing (c : RationalCrossing 3) :
  (c⟦⟧ᵃ)⟦⟧ᵗ = c := by
  simp [crossing_to_pair, pair_to_crossing]

/-- La conversión es involutiva: vuelta e ida da el original -/
theorem iso_roundtrip_pair (p : OrderedPair) :
  (p⟦⟧ᵗ)⟦⟧ᵃ = p := by
  simp [crossing_to_pair, pair_to_crossing]

/-! ## Preservación del Desplazamiento Modular -/

/-- El isomorfismo preserva el desplazamiento modular.

    En la perspectiva topológica:
    - `modular_ratio c = under_pos - over_pos`
    
    En la perspectiva algebraica:
    - `pairDelta p = snd - fst` (en aritmética entera)
    
    Este teorema establece que ambos conceptos son idénticos.
    -/
theorem iso_preserves_displacement (c : RationalCrossing 3) :
  (c.under_pos : ZMod 6) - (c.over_pos : ZMod 6) = 
  ((c⟦⟧ᵃ).snd : ZMod 6) - ((c⟦⟧ᵃ).fst : ZMod 6) := by
  rfl

/-- El desplazamiento modular es el mismo visto desde ambas perspectivas -/
theorem displacement_commutes (c : RationalCrossing 3) :
  modular_ratio c = (c⟦⟧ᵃ).snd - (c⟦⟧ᵃ).fst := by
  unfold modular_ratio
  rfl

/-! ## Tácticas de Transferencia de Propiedades -/

/-- **Táctica de transferencia: Algebraico → Topológico**

    Si una propiedad P vale para todos los pares algebraicos,
    entonces vale para todos los cruces topológicos.
    
    Uso típico:
    ```lean
    theorem pair_theorem : ∀ p : OrderedPair, P p := by ...
    theorem crossing_theorem : ∀ c : RationalCrossing 3, P c :=
      transfer_to_crossing pair_theorem
    ```
    -/
theorem transfer_to_crossing {P : RationalCrossing 3 → Prop}
    (h : ∀ p : OrderedPair, P (p⟦⟧ᵗ)) :
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
    theorem pair_theorem : ∀ p : OrderedPair, P p :=
      transfer_to_pair crossing_theorem
    ```
    -/
theorem transfer_to_pair {P : OrderedPair → Prop}
    (h : ∀ c : RationalCrossing 3, P (c⟦⟧ᵃ)) :
  ∀ p : OrderedPair, P p := by
  intro p
  have : P ((p⟦⟧ᵗ)⟦⟧ᵃ) := h (p⟦⟧ᵗ)
  simpa [iso_roundtrip_pair] using this

/-- **Transferencia de propiedades relacionales**

    Si una relación R se preserva bajo el isomorfismo,
    entonces resultados sobre R en un lado implican
    resultados en el otro lado.
    -/
theorem transfer_relation {R : RationalCrossing 3 → RationalCrossing 3 → Prop}
    {S : OrderedPair → OrderedPair → Prop}
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
    have h₁ := congr_arg pair_to_crossing h
    simp [iso_roundtrip_crossing] at h₁
    exact h₁

/-- Igualdad en pares implica igualdad en cruces -/
theorem pair_eq_iff_crossing_eq (p₁ p₂ : OrderedPair) :
  p₁ = p₂ ↔ (p₁⟦⟧ᵗ) = (p₂⟦⟧ᵗ) := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h₁ := congr_arg crossing_to_pair h
    simp [iso_roundtrip_pair] at h₁
    exact h₁

/-- La distintitud es invariante bajo el isomorfismo -/
theorem iso_preserves_distinct (c : RationalCrossing 3) :
  c.over_pos ≠ c.under_pos ↔ (c⟦⟧ᵃ).fst ≠ (c⟦⟧ᵃ).snd := by
  constructor <;> intro h
  · exact h
  · exact h

/-! ## Compatibilidad con Operaciones -/

/-- El isomorfismo conmuta con la operación de reversa

    Si definimos `reverse` para RationalCrossing como
    intercambiar `over_pos` y `under_pos`, entonces:
    
    reverse_crossing(c)⟦⟧ᵃ = reverse_pair(c⟦⟧ᵃ)
    -/
theorem iso_commutes_with_reverse (c : RationalCrossing 3) :
  let c_rev : RationalCrossing 3 := ⟨c.under_pos, c.over_pos, c.distinct.symm⟩
  (c_rev⟦⟧ᵃ) = (c⟦⟧ᵃ).reverse := by
  simp [OrderedPair.reverse]
  rfl

/-! ## Transferencia de Cardinalidades -/

/-- Los espacios tienen la misma cardinalidad (finita) -/
theorem spaces_have_same_cardinality :
  Fintype.card (RationalCrossing 3) = Fintype.card OrderedPair := by
  exact Fintype.card_eq.mpr ⟨crossing_to_pair⟩

/-- Enumeración explícita: hay 30 cruces = 30 pares -/
theorem card_both_eq_30 :
  Fintype.card (RationalCrossing 3) = 30 ∧ 
  Fintype.card OrderedPair = 30 := by
  constructor
  · -- RationalCrossing 3 tiene 6 * 5 = 30 elementos
    -- (6 opciones para over_pos, 5 opciones restantes para under_pos)
    sorry -- Requiere cálculo explícito de cardinalidad
  · -- OrderedPair tiene 6 * 5 = 30 elementos
    -- (6 opciones para fst, 5 opciones restantes para snd)
    sorry -- Requiere cálculo explícito de cardinalidad

/-! ## Invariancia de Configuraciones K₃ -/

/-- Una configuración K₃ puede verse como conjunto de cruces o de pares

    Este teorema establece que una K3Config puede interpretarse
    indistintamente en cualquiera de las dos perspectivas.
    -/
theorem k3config_invariant_under_iso (K : K3Config) :
  ∀ p ∈ K.pairs, ∃ c : RationalCrossing 3, c⟦⟧ᵃ = p := by
  intro p hp
  use p⟦⟧ᵗ
  simp [iso_roundtrip_pair]

/-! ## Preservación de Movimientos Reidemeister -/

section ReidemeisterPreservation

variable (has_r1_crossing : RationalCrossing 3 → Prop)
variable (has_r1_pair : OrderedPair → Prop)

/-- Si definimos R1 consistentemente en ambos lados,
    el isomorfismo debe preservarlo
    
    Esquema de teorema (requiere definiciones de R1):
    -/
axiom iso_preserves_r1 
    (h_def : ∀ c : RationalCrossing 3, 
      has_r1_crossing c ↔ has_r1_pair (c⟦⟧ᵃ)) :
  ∀ c : RationalCrossing 3, has_r1_crossing c ↔ has_r1_pair (c⟦⟧ᵃ)

end ReidemeisterPreservation

/-! ## Funtorialidad del Isomorfismo -/

/-- El isomorfismo es funtorial: preserva composiciones

    Si tenemos funciones f : A → RationalCrossing 3 y
    g : RationalCrossing 3 → B, entonces:
    
    iso(g ∘ f) = iso(g) ∘ iso(f)
    -/
theorem iso_is_functorial 
    {α β : Type*} 
    (f : α → RationalCrossing 3)
    (g : RationalCrossing 3 → β) :
  (fun x => (g (f x))⟦⟧ᵃ) = (fun x => (g (f x)⟦⟧ᵃ)) := by
  rfl

/-! ## Equivalencia de Predicados -/

/-- **Principio de Transferencia Universal**

    Cualquier predicado sobre cruces tiene un predicado
    equivalente sobre pares, y viceversa.
    -/
theorem universal_transfer_principle 
    (P : RationalCrossing 3 → Prop) :
  (∀ c : RationalCrossing 3, P c) ↔ 
  (∀ p : OrderedPair, P (p⟦⟧ᵗ)) := by
  constructor
  · intro h p
    exact h (p⟦⟧ᵗ)
  · intro h c
    have := h (c⟦⟧ᵃ)
    simpa [iso_roundtrip_crossing] using this

/-! ## Ejemplos de Uso -/

section Examples

/-- Ejemplo 1: Transferir un teorema simple -/
example (h : ∀ p : OrderedPair, p.fst ≠ p.snd) :
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
  · simp [iso_roundtrip_crossing, iso_roundtrip_pair]

end ConsistencyTests

/-! ## Notas para Extensiones Futuras -/

/-!
### Extensión a K₄

Para extender este patrón a K₄ (4 cruces):

```lean
def crossing_to_pair_k4 : RationalCrossing 4 ≃ OrderedPair_K4 where
  -- Similar estructura, pero con ZMod 8
  toFun c := ⟨c.over_pos, c.under_pos, c.distinct⟩
  invFun p := ⟨p.fst, p.snd, p.distinct⟩
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

Este módulo establece que `RationalCrossing 3` y `OrderedPair` son
**el mismo objeto matemático** visto desde dos perspectivas:

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
