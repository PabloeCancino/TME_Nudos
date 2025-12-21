# Análisis Detallado de Errores en TCN_03_Matchings.lean

**Fecha**: 2025-12-07 09:18  
**Archivo afectado**: `TCN_03_Matchings.lean`  
**Causa raíz**: Agregar atributo `@[ext]` a las estructuras `OrderedPair` y `K3Config`

---

## 📊 Resumen de Errores

Al agregar `@[ext]` a las estructuras base en `TCN_01_Fundamentos.lean`:

```lean
@[ext]
structure OrderedPair where
  fst : ZMod 6
  snd : ZMod 6
  distinct : fst ≠ snd

@[ext]
structure K3Config where
  pairs : Finset OrderedPair
  card_eq : pairs.card = 3
  is_partition : ∀ i : ZMod 6, ∃! p ∈ pairs, i = p.fst ∨ i = p.snd
```

Se generaron **16 errores de compilación** en `TCN_03_Matchings.lean`:
- 2 errores "No goals to be solved" (líneas 647, 650)
- 16 errores "`simp` made no progress" (líneas 839, 842, 845, 848, 854, 857, 860, 863, 869, 872, 875, 878, 884, 887, 890, 893)

---

## 🔍 Análisis Detallado de los Errores

### Tipo 1: "No goals to be solved" (Líneas 647, 650)

**Ubicación**: Dentro del teorema `matching_r2_implies_config_r2`

**Código problemático**:
```lean
use p1
constructor
· use {a, b}, he1; dsimp [p1]  -- ❌ Línea 647: No goals to be solved
use p2
constructor
· use {c, d}, he2; dsimp [p2]  -- ❌ Línea 650: No goals to be solved
```

**¿Por qué falló?**

El código está construyendo una prueba existencial con `use`. La táctica `dsimp` se usa para simplificar la meta después de `use`. 

**Antes de `@[ext]`**: 
- Después de `use {a, b}, he1`, queda una meta que `dsimp [p1]` puede simplificar
- La meta probablemente era algo como: `p1 ∈ imagen de pares`

**Después de `@[ext]`**:
- El atributo `@[ext]` cambia cómo Lean maneja la igualdad estructural
- Esto alteró la forma de la meta después de `use`
- `dsimp [p1]` no encontró nada que simplificar porque la meta ya estaba completamente simplificada
- Como `dsimp` no hizo progreso pero aún había metas, Lean reporta "No goals to be solved" cuando el autor esperaba que `dsimp` terminara la prueba

**Solución**: Eliminar `dsimp [p1]` o reemplazar con `rfl` o simplemente omitir (la meta se resuelve automáticamente).

---

### Tipo 2: "`simp` made no progress" (16 ocurrencias)

**Ubicación**: Dentro del teorema `trivial_matching_implies_trivial_configs`

**Patrón recurrente** (líneas 839, 842, 845, 848, 854, 857, 860, 863, 869, 872, 875, 878, 884, 887, 890, 893):

```lean
· use edgeMin e1 he1_card, edgeMax e1 he1_card, edgeMin e2 he2_card, edgeMax e2 he2_card
  simp [edge_eq_minmax]; left; rw [← hp1_eq, ← hp2_eq] at hfst hsnd
  exact ⟨hfst, hsnd⟩
```

**Contexto**: El código está probando que si un matching tiene par R2, entonces existe una orientación dando config con R2. Divide en 4 casos según orientaciones (true/true, true/false, false/true, false/false), y cada caso tiene 4 subcasos del patrón R2.

**¿Por qué falló?**

**Antes de `@[ext]`**:
- `simp [edge_eq_minmax]` podía simplificar expresiones relacionadas con igualdad de aristas
- El lema `edge_eq_minmax` dice: `e = {edgeMin e h, edgeMax e h}`
- `simp` usaba esto para reescribir expresiones

**Después de `@[ext]`**:
- El atributo `@[ext]` para `OrderedPair` registra un nuevo teorema de extensionalidad
- Esto dice: "dos `OrderedPair` son iguales ssi sus `fst` y `snd` son iguales"
- Este nuevo teorema interactúa con el simplificador de maneras inesperadas
- `simp [edge_eq_minmax]` ahora intenta usar reglas de extensionalidad además de `edge_eq_minmax`
- Estas reglas pueden conflictuar o hacer que `simp` no sepa qué hacer
- Resultado: `simp` no hace ningún progreso y reporta error

**Ejemplo concreto**:

```lean
-- Meta antes de simp:
-- Probar que existe a,b,c,d tal que e1 = {a,b} ∧ e2 = {c,d} ∧ patrón R2

-- Antes de @[ext]: simp [edge_eq_minmax] reescribe:
e1 = {edgeMin e1 h, edgeMax e1 h}  -- Simplifica bien

-- Después de @[ext]: simp tiene reglas conflictivas:
-- 1. edge_eq_minmax: e1 = {min, max}
-- 2. ext para OrderedPair: igualdad definida por fst y snd
-- 3. ext para Finset: igualdad definida por membresía
-- Simp no sabe cuál aplicar primero → hace nada → error
```

---

## 🎯 Impacto Específico por Línea

### Líneas 839, 842, 845, 848 (Caso: ambas orientaciones true)
- Cada línea corresponde a uno de los 4 patrones R2
- Patrones: (c = a+1, d = b+1), (c = a-1, d = b-1), (c = a+1, d = b-1), (c = a-1, d = b+1)
- `simp [edge_eq_minmax]` necesario para igualar las aristas con sus elementos min/max

### Líneas 854, 857, 860, 863 (Caso: orient1=true, orient2=false)
- Similar al anterior pero con orientación mixta
- El código espera: p1 = [min,max], p2 = [max,min]

### Líneas 869, 872, 875, 878 (Caso: orient1=false, orient2=true)
- Opuesto: p1 = [max,min], p2 = [min,max]

### Líneas 884, 887, 890, 893 (Caso: ambas orientaciones false)
- Ambos pares invertidos: p1 = [max,min], p2 = [max,min]

---

## 💡 Por Qué `@[ext]` Causa Este Problema

### Funcionamiento de `@[ext]`

El atributo `@[ext]` le dice a Lean:
> "Para probar que dos valores de este tipo son iguales, basta probar que todos sus campos son iguales"

Para `OrderedPair`:
```lean
@[ext]
structure OrderedPair where
  fst : ZMod 6
  snd : ZMod 6
  distinct : fst ≠ snd
```

Lean genera automáticamente:
```lean
theorem OrderedPair.ext {p q : OrderedPair} (h_fst : p.fst = q.fst) (h_snd : p.snd = q.snd) : p = q
```

### Problema con el Simplificador

El simplificador (`simp`) tiene reglas para:
1. Igualdad de `OrderedPair` (vía `ext`)
2. Igualdad de `Finset` (vía `ext` si se agrega)
3. Relaciones entre `edgeMin`, `edgeMax` y la arista
4. Propiedades de `ZMod 6`

Cuando se agregan reglas de extensionalidad:
- `simp` tiene **múltiples caminos** para probar/simplificar igualdades
- Puede entrar en **loops** intentando aplicar reglas
- Puede **no saber** qué regla priorizar
- Resultado: "made no progress" porque no puede decidir

### Solución Teórica

Para que `@[ext]` funcione sin romper TCN_03, necesitarías:

1. **Marcar teoremas específicos con `@[simp]`** para guiar al simplificador
2. **Desactivar ciertas reglas** en contextos específicos: `simp only [...]`
3. **Reescribir pruebas** usando `ext; simp` en lugar de solo `simp`
4. **Usar tácticas más específicas**: `rw`, `exact` en lugar de `simp` genérico

**Ejemplo de corrección**:
```lean
-- Antes (con error):
simp [edge_eq_minmax]; left; rw [...]

-- Después (funcional):
rw [edge_eq_minmax e1, edge_eq_minmax e2]
left
exact ⟨hfst, hsnd⟩
```

---

## 📋 Lista Completa de Líneas Afectadas

| Línea | Tipo de Error         | Contexto                                 | Caso              |
| ----- | --------------------- | ---------------------------------------- | ----------------- |
| 647   | No goals to be solved | matching_r2_implies_config_r2            | Constructor de p1 |
| 650   | No goals to be solved | matching_r2_implies_config_r2            | Constructor de p2 |
| 839   | simp made no progress | trivial_matching_implies_trivial_configs | TT, patrón 1      |
| 842   | simp made no progress | trivial_matching_implies_trivial_configs | TT, patrón 2      |
| 845   | simp made no progress | trivial_matching_implies_trivial_configs | TT, patrón 3      |
| 848   | simp made no progress | trivial_matching_implies_trivial_configs | TT, patrón 4      |
| 854   | simp made no progress | trivial_matching_implies_trivial_configs | TF, patrón 1      |
| 857   | simp made no progress | trivial_matching_implies_trivial_configs | TF, patrón 2      |
| 860   | simp made no progress | trivial_matching_implies_trivial_configs | TF, patrón 3      |
| 863   | simp made no progress | trivial_matching_implies_trivial_configs | TF, patrón 4      |
| 869   | simp made no progress | trivial_matching_implies_trivial_configs | FT, patrón 1      |
| 872   | simp made no progress | trivial_matching_implies_trivial_configs | FT, patrón 2      |
| 875   | simp made no progress | trivial_matching_implies_trivial_configs | FT, patrón 3      |
| 878   | simp made no progress | trivial_matching_implies_trivial_configs | FT, patrón 4      |
| 884   | simp made no progress | trivial_matching_implies_trivial_configs | FF, patrón 1      |
| 887   | simp made no progress | trivial_matching_implies_trivial_configs | FF, patrón 2      |
| 890   | simp made no progress | trivial_matching_implies_trivial_configs | FF, patrón 3      |
| 893   | simp made no progress | trivial_matching_implies_trivial_configs | FF, patrón 4      |

**TT** = ambas orientaciones true, **TF** = true/false, **FT** = false/true, **FF** = ambas false

---

## 🔧 Estrategias de Corrección

### Opción 1: Corrección Mínima (Recomendada para TCN_03)

Reemplazar las tácticas problemáticas:

```lean
-- Líneas 647, 650:
· use {a, b}, he1  -- Eliminar dsimp [p1]

-- Líneas 839-893:
simp only [edge_eq_minmax]  -- En lugar de simp [edge_eq_minmax]
-- O mejor:
rw [edge_eq_minmax e1 he1_card, edge_eq_minmax e2 he2_card]
```

### Opción 2: Reescritura Estructural

Dividir las pruebas complejas en lemas auxiliares que no dependan de `simp`.

### Opción 3: Evitar `@[ext]` (Elegido en este proyecto)

No agregar `@[ext]` a las estructuras base para evitar romper TCN_03.

---

## 📊 Estimación de Esfuerzo de Corrección

Si se quisiera mantener `@[ext]` y arreglar TCN_03:

- **Líneas a modificar**: ~20 líneas
- **Complejidad**: Media (requiere entender el contexto de cada prueba)
- **Tiempo estimado**: 1-2 horas
- **Riesgo**: Medio (posibles efectos secundarios en otras partes)
- **Pruebas requeridas**: Compilación completa + verificar que sigue probando lo mismo

---

## 🎯 Conclusión

El atributo `@[ext]` es muy útil para simplificar pruebas de igualdad estructural, pero introduce **efectos secundarios no triviales** en código existente que depende del comportamiento del simplificador. 

En este proyecto, TCN_03 es un archivo grande (960 líneas) y completamente funcional. Los **beneficios de agregar `@[ext]`** (simplificar algunas pruebas en TCN_04-TCN_06) **no justifican el riesgo** de romper TCN_03 y posiblemente otros archivos.

**Decisión correcta**: No agregar `@[ext]` y buscar soluciones alternativas para las correcciones propuestas.
