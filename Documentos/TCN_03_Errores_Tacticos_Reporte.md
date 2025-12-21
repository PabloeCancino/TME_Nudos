# Reporte de Errores: TCN_03_Matchings.lean

**Fecha**: 2025-12-05  
**Estado**: ❌ BUILD FAILED  
**Impacto**: Bloquea compilación de TCN_06_Representantes.lean

---

## Entorno y Compatibilidad

### Versión de Lean

```
Lean (version 4.26.0-rc2, x86_64-w64-windows-gnu, commit 9d4ad1273f6cea397c3066c2c83062a4410d16bf, Release)
Toolchain: leanprover/lean4:v4.26.0-rc2
```

### Especificaciones de Compatibilidad

#### Comportamiento de Tácticas en Lean 4.26

**1. `simp` - Simplificación Automática**
- ❌ **No permite redundancia**: Si `simp` no puede simplificar nada, falla con "made no progress"
- ✅ **Requiere contexto**: Las variables deben ser simplificables en el contexto actual
- ⚠️ **Cambio vs Lean 3**: Más estricto que Lean 3, no es no-op silencioso

**2. `congr` - Congruencia**
- ❌ **Requiere metas activas**: Falla con "No goals to be solved" si se llama sin metas pendientes
- ✅ **Uso correcto**: Solo después de `constructor`, `split`, etc. que generan submetas
- ⚠️ **Cambio vs 4.25**: Más estricto en verificación de estado

**3. `decide` - Decisión Computacional**
- ❌ **No funciona con variables libres**: Requiere todos los valores sean conocidos
- ✅ **DecidableEq**: El tipo debe tener instancia `DecidableEq`
- ⚠️ **Límite de evaluación**: Fallos en computaciones grandes

#### Convenciones del Proyecto TME_Nudos

**Imports**:
```lean
-- ✅ Correcto
import TMENudos.TCN_XX_Nombre

-- ❌ Incorrecto
import TCN_XX_Nombre
```

**Nombres de Módulo**:
```lean
-- ✅ Correcto
TCN_05_Orbitas.lean  (sin puntos internos)

-- ❌ Incorrecto  
TCN_05.1_Orbitas.lean  (Lake no puede importar)
```

**Operadores Personalizados**:
```lean
-- ❌ • no disponible directamente
g • K

-- ✅ Usar función explícita
DihedralD6.actOnConfig g K
```

#### Restricciones de Pattern Matching

**Lean 4.26 con Mathlib**:
- ❌ **No permite pattern matching en tipos opacos**: `DihedralGroup` de Mathlib
- ✅ **Alternativa**: Usar funciones auxiliares y propiedades
- ⚠️ **Workaround**: Definir acciones via funciones, no por casos

#### Gestión de Sorry

**Aceptables**:
- ✅ Teoremas matemáticos avanzados (ej: orbit-stabilizer formal)
- ✅ Implementaciones que requieren API externa no disponible
- ✅ Temporales con comentario explicativo

**Inaceptables**:
- ❌ En definiciones básicas (tipos, funciones principales)
- ❌ Sin documentación de por qué
- ❌ En código "productivo"

### Dependencias Mathlib

**Versión**: Compatible con Lean 4.26.0-rc2

**Módulos Críticos Usados**:
- `Mathlib.GroupTheory.SpecificGroups.Dihedral`
- `Mathlib.Data.Finset.Card`
- `Mathlib.Data.ZMod.Basic`
- `Mathlib.Tactic`

---

## Resumen Ejecutivo


TCN_03_Matchings.lean contiene **18 errores tácticos** que impiden su compilación. Estos errores bloquean TCN_06 ya que este último importa TCN_03. Los errores son de dos tipos principales:

1. **"No goals to be solved"** (2 errores) - Líneas 647, 650
2. **"simp made no progress"** (16 errores) - Líneas 839-893

---

## Errores Detallados

### Tipo 1: "No goals to be solved"

#### Error en Línea 647
```lean
647:   · use {a, b}, he1; dsimp [p1]; congr
```
**Problema**: La táctica `congr` se ejecuta cuando ya no hay metas por resolver.

**Contexto**: Dentro de `matching_r2_implies_config_r2`, construyendo prueba de membresía de `p1`.

**Solución**: Remover `congr` de la línea.

#### Error en Línea 650
```lean
650:   · use {c, d}, he2; dsimp [p2]; congr
```
**Problema**: Idéntico al anterior, `congr` sin metas.

**Solución**: Remover `congr` de la línea.

---

### Tipo 2: "simp made no progress"

Estos 16 errores ocurren en el teorema `trivial_matching_implies_trivial_configs`, específicamente en la segunda parte de la prueba que demuestra ausencia de R2.

#### Patrón de Error

Todas las líneas problemáticas siguen este patrón:
```lean
simp [edge_eq_minmax]; <constructor>; simp at hp1_eq hp2_eq; rw [← hp1_eq, ← hp2_eq] at hfst hsnd
```

**Problema**: `simp at hp1_eq hp2_eq` no hace progreso en el contexto.

**Líneas afectadas**:
- **Caso 1** (orientaciones true/true): 839, 842, 845, 848
- **Caso 2** (orientación true/false): 854, 857, 860, 863
- **Caso 3** (orientación false/true): 869, 872, 875, 878
- **Caso 4** (orientaciones false/false): 884, 887, 890, 893

#### Ejemplo Detallado - Línea 839

**Contexto**:
```lean
-- Dentro de trivial_matching_implies_trivial_configs
-- Caso 1: ambas orientaciones true (p1 = [min1, max1], p2 = [min2, max2])
rcases hpat with (⟨hfst, hsnd⟩|⟨hfst, hsnd⟩|⟨hfst, hsnd⟩|⟨hfst, hsnd⟩)
· use edgeMin e1 he1_card, edgeMax e1 he1_card, edgeMin e2 he2_card, edgeMax e2 he2_card
  simp [edge_eq_minmax]; left; simp at hp1_eq hp2_eq; rw [← hp1_eq, ← hp2_eq] at hfst hsnd
  exact ⟨hfst, hsnd⟩
```

**Problema**: 
- `simp [edge_eq_minmax]` funciona correctamente
- `simp at hp1_eq hp2_eq` NO hace progreso (hp1_eq y hp2_eq ya están simplificados)

**Solución**:
```lean
simp [edge_eq_minmax]; left; rw [← hp1_eq, ← hp2_eq] at hfst hsnd
exact ⟨hfst, hsnd⟩
```

---

## Análisis por Casos

### Estructura del Teorema Problemático

El teorema `trivial_matching_implies_trivial_configs` tiene la siguiente estructura:

```lean
theorem trivial_matching_implies_trivial_configs (M : PerfectMatching) (orient : Orientation M) :
    M.isTrivial → ¬hasR1 (matchingToConfig M orient) ∧ ¬hasR2 (matchingToConfig M orient) := by
  intro ⟨hnoR1, hnoR2⟩
  constructor
  · -- Prueba de ¬hasR1: ✅ FUNCIONA
    ...
  · -- Prueba de ¬hasR2: ❌ ERRORES AQUÍ
    intro hR2
    ...
    -- División en 4 casos según orientaciones
    split_ifs at hp1_eq hp2_eq with ho1 ho2 ho2
    
    · -- Caso 1: ho1=true, ho2=true ❌ 4 errores (839,842,845,848)
      rcases hpat with ...
    
    · -- Caso 2: ho1=true, ho2=false ❌ 4 errores (854,857,860,863)
      rcases hpat with ...
    
    · -- Caso 3: ho1=false, ho2=true ❌ 4 errores (869,872,875,878)
      rcases hpat with ...
    
    · -- Caso 4: ho1=false, ho2=false ❌ 4 errores (884,887,890,893)
      rcases hpat with ...
```

Cada caso tiene 4 subcasos correspondientes a los 4 patrones R2 posibles, y **cada subcaso** tiene el mismo error táctico.

---

## Solución Propuesta

### Opción 1: Fix Quirúrgico (Recomendado)

Remover todas las ocurrencias de `simp at hp1_eq hp2_eq;` en las líneas problemáticas:

**Cambio a aplicar**:
```diff
- simp [edge_eq_minmax]; <constructor>; simp at hp1_eq hp2_eq; rw [← hp1_eq, ← hp2_eq] at hfst hsnd
+ simp [edge_eq_minmax]; <constructor>; rw [← hp1_eq, ← hp2_eq] at hfst hsnd
```

**Líneas a modificar**: 18 líneas totales
- Líneas 647, 650: Remover `congr`
- Líneas 839, 842, 845, 848, 854, 857, 860, 863, 869, 872, 875, 878, 884, 887, 890, 893: Remover `simp at hp1_eq hp2_eq;`

### Opción 2: Refactoring Completo

Extraer la lógica repetitiva en un lema auxiliar:

```lean
private lemma r2_pattern_from_edges (e1 e2 : Finset (ZMod 6)) 
    (he1 : e1.card = 2) (he2 : e2.card = 2)
    (hp1_eq : p1 = ...) (hp2_eq : p2 = ...)
    (hpat : formsR2Pattern p1 p2) :
    ∃ a b c d, ... := by
  rcases hpat with (⟨hfst, hsnd⟩|⟨hfst, hsnd⟩|⟨hfst, hsnd⟩|⟨hfst, hsnd⟩)
  <;> (use edgeMin/Max ...; simp [edge_eq_minmax]; ...)
```

### Opción 3: Simplificación Radical

Reemplazar las 4 divisiones de caso con una prueba más abstracta usando propiedades de `edgeToPair`.

---

## Impacto en TCN_06

### Bloqueo Directo

TCN_06_Representantes.lean declara:
```lean
import TMENudos.TCN_03_Matchings
import TMENudos.TCN_05_Orbitas
```

**Consecuencia**: TCN_06 no puede compilar mientras TCN_03 tenga errores.

### Funcionalidad Afectada en TCN_06

TCN_06 usa las siguientes definiciones de TCN_03:
- ✅ `matching1`, `matching2`: Definiciones básicas (funcionan)
- ✅ `PerfectMatching`: Tipo (funciona)
- ❌ No puede importar debido a errores de compilación

### Workaround Temporal

Mientras se corrige TCN_03, TCN_06 podría:
1. Comentar temporalmente el import de TCN_03
2. Redeclarar `matching1` y `matching2` localmente
3. O mover solo las definiciones necesarias a un módulo separado

---

## Estadísticas

| Métrica                    | Valor                                          |
| -------------------------- | ---------------------------------------------- |
| **Total de errores**       | 18                                             |
| **Líneas afectadas**       | 647, 650, 839-893                              |
| **Teoremas problemáticos** | 1 (`trivial_matching_implies_trivial_configs`) |
| **Tipo de errores**        | 2 (No goals, simp no progress)                 |
| **Archivos bloqueados**    | 1 (TCN_06)                                     |
| **Tamaño del archivo**     | 960 líneas                                     |
| **Complejidad de fix**     | Baja a Media                                   |

---

## Prioridad y Dificultad

**Prioridad**: 🔴 **ALTA**  
- Bloquea progreso en TCN_06
- Resto del proyecto funcional

**Dificultad**: 🟡 **MEDIA**  
- Fix es mecánico (buscar y reemplazar)
- Requiere cuidado para no romper pruebas
- 18 líneas a modificar

**Tiempo Estimado**: 15-30 minutos

---

## Pasos para Resolución

1. **Backup**: Copiar TCN_03_Matchings.lean
2. **Fix líneas 647, 650**:
   - Remover ` congr` al final de cada línea
3. **Fix líneas 839-893**:
   - Buscar: `simp at hp1_eq hp2_eq; `
   - Reemplazar: `(vacío)`
4. **Verificar**: `lake build TMENudos.TCN_03_Matchings`
5. **Probar TCN_06**: `lake build TMENudos.TCN_06_Representantes`

---

## Riesgos

- **Bajo riesgo**: Los cambios son mínimos y bien localizados
- **Riesgo de regresión**: Las pruebas podrían fallar si `simp at` era necesario en algún caso
- **Mitigación**: Verificar que todas las pruebas pasen después del cambio

---

## Conclusión

Los errores en TCN_03 son **superficiales y mecánicos**, resultado de tácticas redundantes que no hacen progreso. La solución es directa: remover las tácticas problemáticas. Una vez corregidos, TCN_06 podrá compilar sin problemas.

**Recomendación**: Aplicar Opción 1 (Fix Quirúrgico) de inmediato.

---

**Generado**: 2025-12-05  
**Autor**: Análisis automático  
**Versión**: 1.0
