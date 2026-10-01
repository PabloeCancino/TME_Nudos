import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import TMENudos.TCN_08_UniformityCriterion

/-!
# ETAPA 2: Verificación de Movimientos de Reidemeister

Este archivo implementa la **segunda etapa** del pipeline de discriminación de configuraciones:
verificar si un nudo (1 componente) es **trivial** o **no trivial** mediante movimientos
de Reidemeister.

## Pipeline Completo

```
Configuración K
    |
    v
ETAPA 1: countComponents(K)  [TCN_09_ComponentAnalysis.lean]
    |
    +---> > 1 componentes → ENLACE
    |
    +---> 1 componente → Continuar a ETAPA 2
              |
              v
        ETAPA 2: hasReidemeisterReduction(K)  [ESTE ARCHIVO]
              |
              +---> Reducible → NUDO TRIVIAL
              |
              +---> No reducible → NUDO NO TRIVIAL
```

## Contenido

1. Detección de patrones R2
2. Verificación de K₃,special
3. Clasificación completa de configuraciones

-/

namespace TMENudos.ReidemeisterVerification

open TMENudos.UniformityCriterion

/-!
## 1. PATRÓN R2: DEFINICIÓN

Dos cruces forman un patrón R2 si:
- Son "paralelos desplazados": (a,b) y (a+1,b+1)
- O variantes: (a,b) y (a-1,b-1), etc.

En configuraciones racionales, buscamos cruces con esta relación modular.
-/

/-- Parte POSICIONAL del patrón R2: los dos cruces son "paralelos desplazados" en ambos extremos.
    No mira el signo. -/
def formR2Positions {n : ℕ} (c1 c2 : RationalCrossing n) : Bool :=
  let o1 := c1.over_pos
  let u1 := c1.under_pos
  let o2 := c2.over_pos
  let u2 := c2.under_pos
  -- Patrón 1: (a,b) y (a+1,b+1)
  (o2 = o1 + 1 && u2 = u1 + 1) ||
  -- Patrón 2: (a,b) y (a-1,b-1)
  (o2 = o1 - 1 && u2 = u1 - 1) ||
  -- Patrón 3: (a,b) y (a+1,b-1)
  (o2 = o1 + 1 && u2 = u1 - 1) ||
  -- Patrón 4: (a,b) y (a-1,b+1)
  (o2 = o1 - 1 && u2 = u1 + 1)

/-- Verifica si dos cruces forman un patrón R2: patrón posicional Y SIGNOS OPUESTOS.

    MIGRACIÓN (regla 4, signo como dato; tensión T1 resuelta): antes → después
    - antes: solo se miraban las posiciones (`formR2Positions`); el signo no intervenía.
    - después: además se exige `c1.pos != c2.pos`, igual que `Basic.is_R2_candidate` y que la
      regla R2 de `TCN` (dos cruces de signo opuesto).
    Consecuencia (honesta, NO es un debilitamiento): los tres cruces de `K3_special` son
    positivos, así que ningún par tiene signos opuestos y `K3_special` YA NO tiene patrón R2
    (ver `K3_special_no_R2`), como `specialClass` en `TCN` (irreducible). -/
def formR2Pair {n : ℕ} (c1 c2 : RationalCrossing n) : Bool :=
  formR2Positions c1 c2 && (c1.pos != c2.pos)

/-- Busca un par de cruces que forma patrón R2 en la configuración -/
def findR2Pair {n : ℕ} (K : RationalConfiguration n) : Option (Fin n × Fin n) :=
  -- Iterar sobre todos los pares de cruces distintos
  (List.range n).foldl (fun acc i =>
    match acc with
    | some pair => some pair  -- Ya encontramos uno
    | none =>
      (List.range n).foldl (fun acc' j =>
        match acc' with
        | some pair => some pair
        | none =>
          if hi : i < n then
            if hj : j < n then
              if i ≠ j then
                let c1 := K.crossings ⟨i, hi⟩
                let c2 := K.crossings ⟨j, hj⟩
                if formR2Pair c1 c2 then
                  some (⟨i, hi⟩, ⟨j, hj⟩)
                else
                  none
              else none
            else none
          else none
      ) acc
  ) none

/-!
## 2. VERIFICADOR DE PATRÓN R2

Determina si una configuración tiene al menos un patrón R2.
-/

/-- Verifica si una configuración tiene patrón R2 -/
def hasR2Pattern {n : ℕ} (K : RationalConfiguration n) : Bool :=
  match findR2Pair K with
  | some _ => true
  | none => false

/-!
## 3. VERIFICACIÓN ESPECÍFICA: K₃,special

K₃,special = {(0,3), (1,4), (2,5)}, con el signo de cada cruce DERIVADO de las posiciones
(`withDerivedSign`), es decir, los tres cruces POSITIVOS.

MIGRACIÓN (T1): antes → después
- antes: `K3_special_has_R2 : hasR2Pattern K3_special = true` (los cruces (0,3) y (1,4) cumplen el
  patrón posicional 1 = 0+1 y 4 = 3+1) y se concluía "K₃,special es trivial".
- después: el patrón posicional sigue cumpliéndose (`K3_special_positions_0_1`), pero R2 exige
  signos OPUESTOS y los tres cruces son positivos: `hasR2Pattern K3_special = false`
  (`K3_special_no_R2`). El significado cambia: con el signo como dato, K₃,special (todos +) NO es
  R2-reducible, igual que `specialClass` en `TCN` (irreducible, y no planar). La conclusión antigua
  "K₃,special es un nudo trivial" era un artefacto de ignorar el signo.
- Control positivo: la variante `K3_special_mixed` (mismas posiciones, un cruce negativo) SÍ
  tiene R2.
-/

/-- El patrón POSICIONAL de R2 se cumple entre los cruces 0 y 1 de K₃,special (sin mirar signos). -/
theorem K3_special_positions_0_1 :
    formR2Positions (K3_special.crossings 0) (K3_special.crossings 1) = true := by
  unfold K3_special formR2Positions
  decide

/-- K₃,special NO tiene patrón R2 (todos sus cruces son positivos, ningún par es de signos
    opuestos). Sustituye al antiguo `K3_special_has_R2`, que era falso con el signo como dato. -/
theorem K3_special_no_R2 : hasR2Pattern K3_special = false := by
  unfold hasR2Pattern findR2Pair
  unfold K3_special formR2Pair formR2Positions
  decide

/-- Variante con el mismo trazado pero el cruce 1 NEGATIVO: ahora (0,3,+) y (1,4,−) forman R2. -/
def K3_special_mixed : RationalConfiguration 3 := {
  crossings := fun i =>
    if h0 : i = 0 then .withDerivedSign 0 3 (by decide)
    else if h1 : i = 1 then ⟨1, 4, by decide, false⟩
    else .withDerivedSign 2 5 (by decide)
  coverage := by decide
}

/-- Control positivo: con un par de signos opuestos el detector SÍ encuentra R2. -/
theorem K3_special_mixed_has_R2 : hasR2Pattern K3_special_mixed = true := by
  unfold hasR2Pattern findR2Pair
  unfold K3_special_mixed formR2Pair formR2Positions RationalCrossing.withDerivedSign zmod_sign
  decide

/-!
## 4. CLASIFICACIÓN DE TRIVIALIDAD

Un nudo es trivial si:
- Tiene patrón R2 (puede reducirse), O
- Tiene patrón R1 (puede desenredarse), O
- Ya no tiene cruces

Por simplicidad, verificamos solo R2 por ahora.
-/

/-- Predicado: configuración es reducible a trivial -/
def isReducibleToTrivial {n : ℕ} (K : RationalConfiguration n) : Bool :=
  -- Caso base: sin cruces = trivial
  if n = 0 then true
  else
    -- Si tiene R2, es reducible
    hasR2Pattern K

/-!
## 5. TIPO DE CLASIFICACIÓN COMPLETA

Combinamos ambas etapas en una clasificación completa.
-/

/-- Tipo de nudo/enlace -/
inductive KnotType where
  | TrivialKnot      -- unknot (círculo simple)
  | NonTrivialKnot   -- nudo no trivial (trébol, etc.)
  | Link (k : ℕ)     -- enlace de k componentes
  | Invalid          -- configuración inválida
  deriving DecidableEq, Repr

/-!
## 6. EJEMPLOS Y VERIFICACIONES

Verificamos la clasificación en casos conocidos.
-/

section Examples

/-- K₃,special NO es R2-reducible a trivial (T1: antes era `= true`; ver sección 3). -/
example : isReducibleToTrivial K3_special = false := by
  unfold isReducibleToTrivial
  -- n = 3 ≠ 0
  simpa using K3_special_no_R2

/-- La variante con un cruce negativo SÍ es reducible por R2. -/
example : isReducibleToTrivial K3_special_mixed = true := by
  unfold isReducibleToTrivial
  simpa using K3_special_mixed_has_R2

/-- Los cruces 0 y 1 de K₃,special cumplen el patrón posicional pero NO forman R2 (mismo signo). -/
example : formR2Pair (K3_special.crossings 0) (K3_special.crossings 1) = false := by
  unfold K3_special formR2Pair formR2Positions
  decide

end Examples

/-!
## 7. ANÁLISIS DETALLADO DE K₃,special

Demostramos paso a paso por qué K₃,special es trivial.
-/

section K3SpecialAnalysis

/-- Los cruces de K₃,special -/
def K3_cruce0 : RationalCrossing 3 := K3_special.crossings 0
def K3_cruce1 : RationalCrossing 3 := K3_special.crossings 1
def K3_cruce2 : RationalCrossing 3 := K3_special.crossings 2

/-- Cruce 0 es (0,3) -/
example : K3_cruce0.over_pos = 0 ∧ K3_cruce0.under_pos = 3 := by
  unfold K3_cruce0 K3_special
  decide

/-- Cruce 1 es (1,4) -/
example : K3_cruce1.over_pos = 1 ∧ K3_cruce1.under_pos = 4 := by
  unfold K3_cruce1 K3_special
  decide

/-- Cruce 2 es (2,5) -/
example : K3_cruce2.over_pos = 2 ∧ K3_cruce2.under_pos = 5 := by
  unfold K3_cruce2 K3_special
  decide

/-- Verificación del patrón R2 entre cruces 0 y 1 -/
example :
  (K3_cruce1.over_pos : ZMod 6) = K3_cruce0.over_pos + 1 ∧
  (K3_cruce1.under_pos : ZMod 6) = K3_cruce0.under_pos + 1 := by
  unfold K3_cruce0 K3_cruce1 K3_special
  constructor <;> decide

/-- findR2Pair NO encuentra ningún par en K₃,special (T1: antes encontraba el (0,1)) -/
example : findR2Pair K3_special = none := by
  unfold findR2Pair K3_special formR2Pair formR2Positions
  decide

/-- En la variante con un cruce negativo encuentra el par (0,1). -/
example : findR2Pair K3_special_mixed = some (0, 1) := by
  unfold findR2Pair K3_special_mixed formR2Pair formR2Positions RationalCrossing.withDerivedSign
    zmod_sign
  decide

end K3SpecialAnalysis

/-!
## 8. TABLA DE CLASIFICACIÓN

Resumen de resultados para configuraciones conocidas.
-/

section ClassificationTable

/-!
### Tabla de Clasificación de K₂ y K₃

| Configuración | IME | Componentes | R2 | Clasificación |
|--------------|-----|-------------|----|--------------|
| K₂,₁         | [3,1] | 1 (nudo)  | ? | Nudo (¿trivial?) |
| K₂,₂         | [2,2] | 2 (enlace) | N/A | Enlace 2-comp |
| K₃,special   | [3,3,3] | 1 (nudo) | ✗ (signos iguales) | No R2-reducible (T1) |

-/

/-- K₂,₁: Verificar si tiene R2 -/
def K2_1_has_R2 : Bool := hasR2Pattern K2_1

-- K₂,₂: No aplica (es enlace, no nudo)
-- N/A para K₂,₂ porque tiene 2 componentes

/-- K₃,special: NO tiene R2 (T1) -/
example : hasR2Pattern K3_special = false := K3_special_no_R2

end ClassificationTable

/-!
## 9. RESUMEN Y CONCLUSIONES

### Implementación Completa de ETAPA 2

✅ **Detector de patrón R2** (posiciones Y signos opuestos): `hasR2Pattern`
✅ **Verificado en K₃,special**: NO tiene R2 (`K3_special_no_R2`)
✅ **Clasificación**: `isReducibleToTrivial`

### Resultado Principal (T1, signo como dato)

**K₃,special = {(0,3,+), (1,4,+), (2,5,+)}**:
- Etapa 1: 1 componente → Nudo
- Etapa 2: **sin R2** (los tres cruces son positivos) → este detector NO lo reduce.

Los cruces (0,3) y (1,4) cumplen el patrón posicional (1 = 0+1, 4 = 3+1), pero R2 exige signos
opuestos. Antes de la migración se concluía "nudo trivial"; esa conclusión era un artefacto de
ignorar el signo. Con un cruce negativo (`K3_special_mixed`) el par sí se reduce.

### Próximos Pasos

1. ✅ Implementar detector R2
2. ✅ Verificar K₃,special tiene R2
3. ⬜ Implementar detector R1
4. ⬜ Combinar con ETAPA 1 (countComponents) en pipeline completo
5. ⬜ Clasificar todos los representantes de K₃
6. ⬜ Extender a K₄ y más allá

### Integración con Pipeline

```lean
-- Pipeline completo (futuro)
def classifyConfiguration {n : ℕ} [NeZero n]
    (K : RationalConfiguration n) : KnotType :=
  match countComponents K with  -- ETAPA 1 (por implementar)
  | 0 => .Invalid
  | 1 =>
      if isReducibleToTrivial K then  -- ETAPA 2 (este archivo)
        .TrivialKnot
      else
        .NonTrivialKnot
  | k => .Link k
```

-/

end TMENudos.ReidemeisterVerification
