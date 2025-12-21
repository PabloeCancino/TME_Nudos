# Normas de Desarrollo - Proyecto TME_Nudos

**Versión**: 2.0  
**Fecha**: 2025-12-11  
**Autor**: Dr. Pablo Eduardo Cancino Marentes  
**Estado**: Documento Normativo Oficial al Proyecto TME_Nudos
**Version de LEAN**: Lean 4.26+ (más estricto que versiones anteriores)

---

## 📜 Propósito del Documento

Este documento establece las **normas técnicas obligatorias** para modificaciones al proyecto TME_Nudos. Su objetivo es prevenir errores recurrentes y mantener la estabilidad del código existente.

**Todos los cambios al proyecto deben cumplir con estas normas.**

---

## 🎯 Principios Rectores

### Principio 1: Estabilidad Primero

> **Un archivo que compila sin errores es un activo valioso que debe protegerse.**

- NUNCA modificar archivos base funcionales sin verificación exhaustiva
- Preferir adaptación de código nuevo sobre refactorización de código viejo
- Mantener retrocompatibilidad siempre que sea posible

### Principio 2: Cambios Incrementales

> **Cada modificación debe ser compilable y verificable independientemente.**

- Hacer un cambio a la vez
- Compilar después de cada modificación
- Revertir inmediatamente si algo falla
- No acumular cambios no verificados

### Principio 3: Documentación de Decisiones

> **Cada decisión técnica debe estar documentada con su justificación.**

- Explicar POR QUÉ se tomó una decisión, no solo QUÉ se hizo
- Documentar alternativas consideradas y por qué se descartaron
- Mantener registro de errores pasados y sus soluciones

---

## ⚠️ NORMAS PROHIBITIVAS

### ❌ NORMA 1: Prohibición de `@[ext]` en Estructuras Base

**PROHIBIDO**: Agregar el atributo `@[ext]` a las siguientes estructuras:

```lean
-- ❌ NUNCA HACER ESTO:
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

**Razón**: 
- Causa 16+ errores de compilación en TCN_03_Matchings.lean (960 líneas de código funcional)
- Modifica el comportamiento del simplificador de forma impredecible
- Genera conflictos con código existente que depende de `simp`

**Excepción**: Solo permitido si:
1. Se ha creado un branch de prueba
2. TODOS los archivos dependientes (TCN_03, TCN_06, TCN_07) han sido adaptados
3. El proyecto completo compila con `lake build`
4. Los cambios han sido revisados y aprobados

**Documentos de referencia**: 
- `20251207_091808_Analisis_Errores_TCN03.md`
- `20251207_090440_Evaluacion_Correcciones_Propuestas.md`

---

### ❌ NORMA 2: Prohibición de Refactorización Masiva

**PROHIBIDO**: Refactorizar múltiples archivos simultáneamente sin plan documentado.

**En su lugar**:
- Crear documento de diseño previo
- Identificar todos los archivos afectados
- Establecer orden de modificaciones
- Definir criterios de éxito
- Crear branch específico para refactorización

---

### ❌ NORMA 3: Prohibición de Cambios en Archivos Base sin Impacto Assessment

**Archivos "base" del proyecto** (requieren análisis de impacto antes de modificar):
- `TCN_01_Fundamentos.lean` (250 líneas)
- `TCN_02_Reidemeister.lean` (220 líneas)
- `TCN_03_Matchings.lean` (960 líneas) ⚠️ ESPECIALMENTE CRÍTICO

**Antes de modificar cualquier archivo base**:
1. ✅ Identificar todos los archivos que lo importan
2. ✅ Buscar todos los usos de sus definiciones
3. ✅ Crear branch de prueba
4. ✅ Verificar compilación de archivos dependientes
5. ✅ Documentar cambios y justificación

---

## ✅ NORMAS PRESCRIPTIVAS

### ✅ NORMA 4: Proceso de Modificación Estándar

**Para cualquier modificación al proyecto, seguir este protocolo**:

#### Fase 1: Planificación (OBLIGATORIA)

1. **Definir el objetivo**
   - ¿Qué problema se está resolviendo?
   - ¿Qué funcionalidad se está agregando?

2. **Análisis de impacto**
   - ¿Qué archivos se modificarán?
   - ¿Qué archivos dependen de ellos?
   - ¿Hay riesgo de romper código existente?

3. **Diseño de solución**
   - ¿Cuál es el cambio mínimo necesario?
   - ¿Existen alternativas menos invasivas?
   - ¿Se necesita crear nuevos archivos auxiliares?

4. **Documentación previa**
   - Crear documento de diseño (puede ser breve)
   - Listar archivos afectados
   - Definir criterios de éxito

#### Fase 2: Implementación (INCREMENTAL)

1. **Crear branch de trabajo** (si el cambio es significativo)
   ```bash
   git checkout -b fix/nombre-descriptivo
   ```

2. **Modificar UN archivo a la vez**

3. **Compilar después de cada cambio**
   ```bash
   lake build
   ```

4. **Si falla**:
   - Revertir cambio inmediatamente
   - Analizar causa
   - Ajustar enfoque
   - Intentar de nuevo

5. **Si compila**:
   - Commit con mensaje descriptivo
   - Continuar con siguiente cambio

#### Fase 3: Verificación (OBLIGATORIA)

1. **Compilación completa**
   ```bash
   lake build --verbose
   ```

2. **Verificar archivos dependientes**
   - TCN_06_Representantes.lean
   - TCN_07_Clasificacion.lean
   - Cualquier otro archivo que importe los modificados

3. **Pruebas funcionales**
   - Verificar que ejemplos concretos funcionen
   - Probar casos límite si aplica

4. **Documentación post-implementación**
   - Actualizar comentarios en el código
   - Documentar decisiones no obvias
   - Agregar ejemplos de uso si aplica

---

### ✅ NORMA 5: Uso de Tácticas y Atributos

#### Tácticas Permitidas Libremente

✅ **Seguras de usar en cualquier contexto**:
- `rfl` - Reflexividad
- `exact` - Prueba directa con término
- `intro` / `intros` - Introducción de variables
- `cases` / `rcases` - Análisis de casos
- `split` - División de metas
- `left` / `right` - Elección en disyunciones
- `constructor` - Construcción de estructuras
- `apply` - Aplicación de lemas
- `have` - Lemas intermedios
- `rw` / `rewrite` - Reescritura
- `calc` - Cadenas de igualdades
- `unfold` - Desplegar definiciones
- `omega` - Decisión aritmética
- `decide` - Decisión decidible
- `norm_num` - Normalización numérica
- `ring` - Álgebra de anillos
- `field_simp` - Simplificación de campos

#### Tácticas que Requieren Precaución

⚠️ **Usar con cuidado** (pueden tener efectos secundarios):
- `simp` - Simplificación automática
  - **Advertencia**: Comportamiento depende de atributos `@[simp]` en contexto
  - **Alternativa segura**: `simp only [lista_explícita_de_lemas]`
  - **Cuándo usar**: Solo si entiendes qué lemas aplicará
  
- `ext` - Prueba por extensionalidad
  - **Advertencia**: Requiere atributo `@[ext]` en estructuras
  - **Alternativa segura**: `cases` + análisis manual
  - **Cuándo usar**: Solo en código nuevo, NO en modificaciones a archivos base

- `dsimp` - Simplificación definitoria
  - **Advertencia**: Puede no hacer progreso si metas ya simplificadas
  - **Alternativa segura**: `unfold` + `simp only`
  - **Cuándo usar**: Cuando sabes que hay definiciones por desplegar

#### Atributos Prohibidos/Restringidos

❌ **Prohibido en archivos base**:
- `@[ext]` - Extensionalidad automática
  - Ver NORMA 1

⚠️ **Usar con extremo cuidado**:
- `@[simp]` - Agregar lema al simplificador
  - Solo en lemas nuevos, NUNCA en archivos base
  - Documentar razón para agregarlo
  - Verificar que no causa loops infinitos

✅ **Seguro de usar**:
- `@[reducible]` - Transparencia definitoria
- `@[inline]` - Inlining de funciones
- Otros atributos de optimización

---

### ✅ NORMA 6: Resolución de Proof Obligations

**Cuando encuentres `sorry` en el código**:

#### Paso 1: Clasificar la Obligación

- **Tipo A**: Prueba matemática no trivial (requiere teorema)
- **Tipo B**: Prueba técnica de Lean (manipulación sintáctica)
- **Tipo C**: Proof obligation estructural (preservación de propiedades)

#### Paso 2: Estrategia por Tipo

**Tipo A - Pruebas Matemáticas**:
1. Buscar teorema correspondiente en literatura matemática
2. Consultar `Teoría_Combinatoria_de_Nudos_de_Tres_Cruces_en_Z_6Z.md`
3. Implementar prueba siguiendo estructura matemática
4. Usar lemas auxiliares si es necesario

**Ejemplo**:
```lean
-- Tipo A: Requiere teorema matemático
theorem orbit_stabilizer (K : K3Config) :
  (Orb(K)).card * (Stab(K)).card = 12 := by
  -- Ver TNC_05_1_Teorema_Orbitas_y_estabilizadores.lean
  -- para la prueba completa
  sorry
```

**Tipo B - Pruebas Técnicas**:
1. Usar análisis de casos exhaustivo
2. Aplicar `omega` para aritmética
3. Usar `decide` para propiedades decidibles
4. Simplificar con `simp only` si es seguro

**Ejemplo**:
```lean
-- Tipo B: Técnica de Lean
theorem actionZMod_preserves_ne (g : DihedralD6) (a b : ZMod 6) (h : a ≠ b) :
    actionZMod g a ≠ actionZMod g b := by
  unfold actionZMod
  cases g <;> omega  -- ✅ Directo y seguro
```

**Tipo C - Proof Obligations Estructurales**:
1. Identificar qué propiedad debe preservarse
2. Usar el teorema que garantiza preservación
3. Aplicar directamente con `exact`
4. Si no existe, crear lema auxiliar primero

**Ejemplo**:
```lean
-- Tipo C: Preservación estructural
def actOnPair (g : DihedralD6) (p : OrderedPair) : OrderedPair :=
  OrderedPair.make
    (actionZMod g p.fst)
    (actionZMod g p.snd)
    (actionZMod_preserves_ne g p.fst p.snd p.distinct)
    --                       ↑ Proof obligation resuelta con teorema previo
```

---

### ✅ NORMA 7: Importaciones y Dependencias

#### Estructura de Importaciones

**Orden estándar** (aplicar consistentemente):

```lean
-- 1. Archivos del proyecto (en orden de dependencia)
import TMENudos.TCN_01_Fundamentos
import TMENudos.TCN_02_Reidemeister
import TMENudos.TCN_03_Matchings

-- 2. Mathlib (agrupados por tema)
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

-- 3. Tácticas y utilidades
import Mathlib.Tactic
```

#### Reglas de Importación

✅ **Permitido**:
- Importar archivo previo en la secuencia (TCN_04 puede importar TCN_03)
- Importar Mathlib según necesidad
- Agregar imports si se necesita acceder a definiciones

❌ **Prohibido**:
- Importaciones circulares
- Importar archivo posterior (TCN_03 NO puede importar TCN_04)
- Importar todo Mathlib (`import Mathlib`) sin necesidad

⚠️ **Requiere justificación**:
- Importar archivo "saltándose" uno intermedio
- Ejemplo: TCN_05 importando directamente TCN_01 (debe explicar por qué)

---

### ✅ NORMA 8: Documentación de Código

#### Docstrings Obligatorios

**Toda definición pública debe tener docstring**:

```lean
/-- Una tupla ordenada es un par [a,b] de elementos distintos de Z/6Z
    donde el orden importa: [a,b] ≠ [b,a] 
    
    Esta estructura es fundamental para representar cruces en nudos K₃. -/
structure OrderedPair where
  fst : ZMod 6
  snd : ZMod 6
  distinct : fst ≠ snd
```

#### Comentarios de Decisiones Técnicas

**Documentar decisiones no obvias**:

```lean
-- DECISIÓN: Usar pattern matching en lugar de if-then-else
-- RAZÓN: Pattern matching es más eficiente y permite a Lean
--        verificar exhaustividad de casos
def actionZMod (g : DihedralD6) (i : ZMod 6) : ZMod 6 :=
  match g with
  | DihedralGroup.r k => i + k
  | DihedralGroup.sr k => k - i
```

#### Secciones de Estado

**Al inicio de cada archivo**:

```lean
/-!
# Bloque X: Nombre Descriptivo

## Estado del Archivo

✅ Completamente funcional - 0 sorry
⚠️ En desarrollo - 3 sorry restantes
❌ Bloqueado - depende de TCN_04

## Dependencias

- TCN_01_Fundamentos (estructuras base)
- TCN_02_Reidemeister (movimientos)

## Exporta

- `definición_importante`: Descripción breve
- `teorema_clave`: Descripción breve

## Próximos Pasos

- [ ] Completar prueba de teorema_X
- [ ] Eliminar sorry en línea 245

-/
```

---

## 🔍 Checklist de Verificación Pre-Commit

**Antes de hacer commit, verificar**:

### Checklist Básico

- [ ] `lake build` ejecuta sin errores
- [ ] No hay nuevos warnings introducidos
- [ ] Todos los archivos modificados están documentados
- [ ] Se agregaron comentarios explicando decisiones no obvias
- [ ] Mensaje de commit es descriptivo

### Checklist para Modificaciones Significativas

- [ ] Se creó documento de diseño
- [ ] Se analizó impacto en archivos dependientes
- [ ] Se verificó compilación de TCN_03, TCN_06, TCN_07
- [ ] Se actualizó documentación del proyecto
- [ ] Se agregó entrada a CHANGELOG (si existe)

### Checklist para Cambios a Archivos Base

- [ ] Se creó branch de prueba
- [ ] Se documentó análisis de impacto
- [ ] Se probaron todos los archivos dependientes
- [ ] Se obtuvo revisión/aprobación
- [ ] Se actualizó este documento de normas si es necesario

---

## 🔧 NORMA 9: Manejo de Errores Tácticos en Pruebas Existentes

### Situación Común
Cuando encuentres errores como `"simp made no progress"` o `"No goals to be solved"` en pruebas existentes:

### Diagnóstico Rápido
1. **`simp made no progress`**: Usualmente significa que:
   - La táctica `simp` no encuentra lemas aplicables
   - Faltan argumentos implícitos en los lemas
   - La meta requiere construcción explícita, no simplificación

2. **`No goals to be solved`**: Significa que:
   - La meta ya se resolvió (por `use`, `exact`, etc.)
   - Hay tácticas redundantes después de resolver la meta

### Protocolo de Corrección

#### Paso 1: Análisis del Error
```lean
-- ERROR ORIGINAL (línea 839)
simp [edge_eq_minmax]; left; rw [← hp1_eq, ← hp2_eq] at hfst hsnd

-- DIAGNÓSTICO
-- 1. `edge_eq_minmax` tiene tipo: ∀ e h, e = {edgeMin e h, edgeMax e h}
-- 2. `simp` no puede inferir el argumento `h : e.card = 2`
-- 3. Necesita construcción explícita con `refine`
```

#### Paso 2: Refactorización Segura
```lean
-- SOLUCIÓN CORRECTA (según NORMA 5)
refine ⟨edgeMin e1 he1_card, edgeMax e1 he1_card, 
        edgeMin e2 he2_card, edgeMax e2 he2_card, ?_, ?_, ?_⟩
· exact edge_eq_minmax e1 he1_card  -- Proporciona argumento explícito
· exact edge_eq_minmax e2 he2_card  -- Proporciona argumento explícito
· left; rw [← hp1_eq, ← hp2_eq] at hfst hsnd; exact ⟨hfst, hsnd⟩
```

#### Paso 3: Patrones Comunes de Refactorización

**Patrón A**: `use ...; simp [...]` → `refine ⟨..., ?_⟩`
```lean
-- ANTES (problemático)
use a, b, c, d
simp [lema_con_argumento_implícito]

-- DESPUÉS (seguro)
refine ⟨a, b, c, d, ?_⟩
· exact lema_con_argumento_implícito arg_necesario
```

**Patrón B**: Tácticas redundantes después de `use`
```lean
-- ANTES (problemático)
use x, hx; dsimp [definición]

-- DESPUÉS (seguro)
use x, hx  -- `dsimp` era redundante
```

### Reglas Específicas

✅ **SIEMPRE para `edge_eq_minmax` y similares**:
- Usar `exact edge_eq_minmax e h` en lugar de `simp [edge_eq_minmax]`
- Proporcionar explícitamente el argumento `h : e.card = 2`

✅ **SIEMPRE verificar si `use` ya resuelve la meta**:
- Después de `use`, no agregar `dsimp`, `simp` u otras tácticas a menos que sea necesario
- Si la meta persiste, usar `refine` en lugar de `use`

❌ **NUNCA asumir que `simp` inferirá argumentos implícitos**:
- Lean 4.26+ es más estricto que versiones anteriores
- Documentar dependencias de versión cuando sea relevante

---

## 📊 NORMA 10: Documentación de Cambios en Archivos Críticos

### Para TCN_03_Matchings.lean y archivos similares (960+ líneas)

#### Sección Obligatoria al Inicio del Archivo
```lean
/-!
# HISTORIAL DE CORRECCIONES TÉCNICAS

## Corrección 2025-12-07: Errores en trivial_matching_implies_trivial_configs

### Problemas Identificados:
1. Líneas 647, 650: `dsimp` redundante después de `use`
2. Líneas 839-893: `simp [edge_eq_minmax]` falla (16 errores)

### Cambios Aplicados:
- Removido `; dsimp [p1]` y `; dsimp [p2]` (líneas 647, 650)
- Reemplazado 16 bloques `use ...; simp [edge_eq_minmax]` por `refine` explícito
- Agregado lema `edge_eq_maxmin` para casos de orientación invertida

### Justificación Técnica:
`edge_eq_minmax` requiere argumento `h : e.card = 2` que `simp` no puede inferir.
La solución con `refine` proporciona testigos explícitos.

### Verificación:
✅ `lake build TMENudos.TCN_03_Matchings` compila sin errores
✅ TCN_06_Representantes.lean se desbloquea
✅ 0 `sorry` introducidos
-/
```

#### Template para Futuras Correcciones
```markdown
### Corrección [FECHA]: [BREVE DESCRIPCIÓN]

**Problemas**:
- [ ] Línea X: [Descripción del error]
- [ ] Línea Y: [Descripción del error]

**Cambios**:
- [ ] Cambio 1
- [ ] Cambio 2

**Justificación**:
[Explicación técnica]

**Verificación**:
- [ ] `lake build` exitoso
- [ ] Archivos dependientes verificados
- [ ] Sin `sorry` introducidos
```

---

## 🎯 NORMA 11: Priorización de Errores de Compilación

### Orden de Prioridad para Resolución de Errores

#### Nivel 1: Errores que Bloquean Múltiples Archivos (URGENTE)
```markdown
**Ejemplo**: TCN_03 bloquea TCN_06, TCN_07
**Acción**: Corrección inmediata según NORMA 9
**Tiempo máximo**: 24 horas
```

#### Nivel 2: Errores en Archivos Individuales (ALTA)
```markdown
**Ejemplo**: TCN_04 tiene errores pero no bloquea otros
**Acción**: Planificación en sprint actual
**Tiempo máximo**: 72 horas
```

#### Nivel 3: Warnings y Mejoras (MEDIA)
```markdown
**Ejemplo**: Linter warnings, optimizaciones
**Acción**: Programar para próximo sprint
**Tiempo máximo**: 2 semanas
```

#### Nivel 4: Refactorización Estética (BAJA)
```markdown
**Ejemplo**: Reorganización de imports, renombre
**Acción**: Cuando haya disponibilidad
**Sin plazo estricto**
```

---

## 🔍 NORMA 12: Verificación de Dependencias Post-Corrección

### Checklist Obligatorio Después de Modificar Archivo Base

```markdown
## Verificación Post-Corrección: [ARCHIVO_MODIFICADO]

### Compilación Directa
- [ ] `lake build TMENudos.[ARCHIVO_MODIFICADO]`

### Dependencias Directas
- [ ] TCN_06_Representantes.lean (si aplica)
- [ ] TCN_07_Clasificacion.lean (si aplica)
- [ ] [OTRO_ARCHIVO] (verificar con `grep -r "import TMENudos.[ARCHIVO]"`)

### Compilación Completa
- [ ] `lake build` (todo el proyecto)

### Pruebas de Humo (Smoke Tests)
- [ ] Ejecutar ejemplos clave si existen
- [ ] Verificar teoremas críticos mencionados en documentación

### Documentación
- [ ] Actualizado historial de correcciones
- [ ] Commit con mensaje descriptivo
- [ ] Comentarios en código para cambios no obvios
```

---

## 📚 Casos de Estudio

### Caso de Estudio 1: Error con `@[ext]` (Diciembre 2025)

**Situación**: Se propuso agregar `@[ext]` a `OrderedPair` y `K3Config` para simplificar pruebas.

**Resultado**: 16 errores de compilación en TCN_03_Matchings.lean

**Lección aprendida**: Atributos en estructuras base tienen efectos secundarios en cascada.

**Norma creada**: NORMA 1 - Prohibición de `@[ext]` en estructuras base

**Documentos**: 
- `20251207_091808_Analisis_Errores_TCN03.md`
- `20251207_090440_Evaluacion_Correcciones_Propuestas.md`

**Solución aplicada**: Revertir cambios, usar `cases` en lugar de `ext`

---

### Caso de Estudio 2: Implementación de `actionZMod` (Diciembre 2025)

**Situación**: TCN_04 tenía `sorry` en definición de `actionZMod`

**Solución correcta**: Implementar con pattern matching directo

```lean
def actionZMod (g : DihedralD6) (i : ZMod 6) : ZMod 6 :=
  match g with
  | DihedralGroup.r k => i + k
  | DihedralGroup.sr k => k - i
```

**Lección aprendida**: Preferir pattern matching sobre construcciones complejas

**Buenas prácticas demostradas**:
- Implementación clara y directa
- No requiere atributos especiales
- Compatible con todo el código existente
- Fácil de probar y verificar

---

## 📚 Caso de Estudio 3: Corrección de TCN_03_Matchings.lean (Diciembre 2025)

**Situación**: 
- 18 errores de compilación en TCN_03
- Bloqueaba TCN_06 completamente
- Errores en pruebas complejas (960 líneas)

**Diagnóstico**:
1. **Tipo de error**: Táctico (`simp made no progress`, `No goals to be solved`)
2. **Causa raíz**: `edge_eq_minmax` necesita argumento `h` que `simp` no infiere
3. **Contexto**: Código original asumía comportamiento más permisivo de Lean

**Solución Aplicada**:
1. **Análisis sistemático**: Identificar patrón repetitivo (16 ocurrencias)
2. **Refactorización incremental**: Un caso a la vez, compilando después de cada uno
3. **Uso de `refine`**: En lugar de `use; simp`, construcción explícita
4. **Lema auxiliar**: `edge_eq_maxmin` para casos de orden invertido

**Lecciones aprendidas**:
1. ✅ `refine` es más robusto que `use; simp` para construcciones complejas
2. ✅ Proporcionar argumentos explícitos a lemas con hipótesis
3. ✅ Compilar después de cada cambio en código crítico
4. ✅ Documentar patrones de error recurrentes

**Normas creadas/modificadas**:
- NORMA 9: Manejo de errores tácticos
- NORMA 10: Documentación en archivos críticos
- NORMA 11: Priorización de errores
- NORMA 12: Verificación post-corrección

**Tiempo invertido**: 3 horas (vs. 5 minutos propuestos para solución con `sorry`)
**Resultado**: Código matemáticamente correcto, 0 `sorry`, desbloqueo completo

---

### Caso de Estudio 4: Error de Definición Topológica en TCN_06 (Diciembre 2025)

**Situación**: 
- `trefoilKnot` definido incorrectamente como configuración con IME {2,3,2}.
- `specialClass` definido incorrectamente como Trefoil real.
- Error descubierto por análisis matemático externo (`ANALISIS_ERROR_IME_TREFOIL.md`).

**Impacto**:
- Invalidez de teoremas geométricos en TCN_06.
- Clasificación incorrecta en TCN_07.
- Bloqueo de verificación por contradicciones lógicas.

**Solución Aplicada**:
1. **Auditoría Matemática**: Comparar definiciones de código con fuentes matemáticas primarias.
2. **Intercambio Controlado**: Swap de definiciones `trefoilKnot` ↔ `specialClass`.
3. **Aislamiento**: Marcar configuración problemática (`specialClass` / Matching 1) como "Status Unknown/R2-prone".
4. **Verificación Estructural**: Asegurar simetría rotacional en las nuevas definiciones.

**Lecciones aprendidas**:
1. 🛑 **Código ≠ Verdad**: Que compile no significa que sea matemáticamente correcto.
2. ⚠️ **Verificación Externa**: Las definiciones topológicas base deben validarse contra papel/literatura antes de codificar.
3. 🔄 **Simetría como prueba**: Si un objeto simétrico (Trefoil) no muestra simetría en código, la definición está mal.

**Normas reforzadas**:
- PRINCIPIO 1: Estabilidad (Corrección de fundamentos antes de teoremas complejos).
- NORMA 8: Documentación explícita del origen matemático (Matching 2 vs Matching 1).

---

## 🛠️ Checklist de Tácticas Seguras vs. Problemáticas (ACTUALIZADO)

### Tácticas Seguras en Cualquier Contexto (✅ AMPLIADO)
```lean
-- CONSTRUCCIÓN EXPLÍCITA (nuevo énfasis)
refine ⟨testigo1, testigo2, ?_, ?_⟩  -- Para metas con existenciales
exact lema_con_argumentos_explícitos  -- Para aplicaciones de lemas

-- CONSTRUCCIÓN DE CASOS
cases h with
| caso1 h1 => ...
| caso2 h2 => ...

-- Las ya existentes...
```

### Tácticas que Requieren Análisis (⚠️ ACTUALIZADO)
```lean
-- ⚠️ `use` seguido de otras tácticas
use x, hx  -- ✅ Bueno
use x, hx; dsimp [def]  -- ❌ Posiblemente redundante

-- ⚠️ `simp` con lemas que tienen argumentos implícitos
simp [edge_eq_minmax]  -- ❌ Falla si falta argumento `h`
simp only [edge_eq_minmax e h]  -- ✅ Mejor (pero aún problemático)
exact edge_eq_minmax e h  -- ✅ Óptimo (proporciona argumentos)
```

### Patrones Prohibidos (❌ NUEVOS)
```lean
-- ❌ NUNCA: `simp` con lemas que necesitan hipótesis explícitas
simp [teorema_con_hipótesis_implícita]

-- ❌ NUNCA: Tácticas después de `use` sin verificar si la meta persiste
use x; try { otras_tácticas }  -- Mejor: verificar primero

-- ❌ NUNCA: Asumir que Lean inferirá argumentos en pruebas críticas
-- En su lugar: ser explícito siempre
```

---

## 🧠 NORMA 13: Pruebas sobre `foldl` con Omega (Diciembre 2025)

### Problema Común: Omega y Acumuladores en Inducción

**Situación**: Al probar propiedades sobre `List.foldl`, la inducción estándar causa fallos de `omega`.

**Síntoma típico**:
```lean
lemma sum_list_ge (l : List ℕ) (n m : ℕ)
  (hlen : l.length = n)
  (hbound : ∀ x ∈ l, x ≥ m) :
  l.foldl (· + ·) 0 ≥ n * m := by
  induction l with
  | nil => simp
  | cons h t ih =>
    -- Hipótesis inductiva: t.foldl (· + ·) 0 ≥ t.length * m
    -- Pero necesito: t.foldl (· + ·) h ≥ ...
    --                                  ^^^ acumulador diferente!
    omega  -- ❌ ERROR: omega no puede conectar acc=0 con acc=h
```

**Error de omega**:
```
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  f ≥ 0, e ≥ 0, e - f ≥ 1, ...
where
  e := ↑(t.length + 1) * ↑m
  f := ↑(List.foldl (· + ·) h t)
```

### Causa Raíz

**Problema**: La hipótesis inductiva usa `foldl` con acumulador `0`, pero el caso recursivo usa acumulador `h`.

**Por qué falla omega**: 
- Omega solo conoce propiedades aritméticas lineales
- NO conoce propiedades estructurales de `foldl`
- No puede relacionar `foldl (· + ·) 0 t` con `foldl (· + ·) h t`

### ✅ SOLUCIÓN: Patrón `generalizing acc`

**Lema auxiliar con acumulador generalizado**:
```lean
/-- Lema auxiliar: foldl con cota inferior y acumulador ARBITRARIO -/
lemma foldl_add_ge_aux (l : List ℕ) (m acc : ℕ)
  (hbound : ∀ x ∈ l, x ≥ m) :
  l.foldl (· + ·) acc ≥ acc + l.length * m := by
  induction l generalizing acc with  -- ✅ CLAVE: generalizing acc
  | nil => 
    simp [List.foldl]
  | cons h t ih =>
    simp only [List.foldl, List.length]
    have hh : h ≥ m := hbound h (List.mem_cons_self h t)
    have ih' : t.foldl (· + ·) (acc + h) ≥ acc + h + t.length * m := by
      apply ih  -- ✅ Hipótesis se adapta a acumulador (acc + h)
      intro x hx
      exact hbound x (List.mem_cons_of_mem h hx)
    calc t.foldl (· + ·) (acc + h)
        ≥ acc + h + t.length * m := ih'
      _ = acc + (h + t.length * m) := by ring
      _ ≥ acc + (m + t.length * m) := by omega  -- ✅ Ahora omega funciona
      _ = acc + (t.length + 1) * m := by ring
```

**Lema principal como caso especial**:
```lean
/-- Lema principal: caso especial con acc = 0 -/
lemma sum_list_ge (l : List ℕ) (n m : ℕ)
  (hlen : l.length = n)
  (hbound : ∀ x ∈ l, x ≥ m) :
  l.foldl (· + ·) 0 ≥ n * m := by
  have h := foldl_add_ge_aux l m 0 hbound
  simp at h
  rw [hlen]
  exact h
```

### Por qué Funciona

1. **`generalizing acc`**: Permite que la hipótesis inductiva use **cualquier** acumulador
2. **Invariante correcto**: `result ≥ acc + n*m` (relativo al acumulador)
3. **Omega puede probar**: Con invariante expresado como `acc + ...`, omega maneja la aritmética

### Reglas de Aplicación

✅ **SIEMPRE para lemas sobre `foldl`**:
1. Crear lema auxiliar con `generalizing acc`
2. Formular invariante como `resultado REL acc + ...`
3. Usar `ring` para reorganizar expresiones algebraicas
4. Aplicar `omega` solo después de tener forma `acc + ...`
5. Lema principal es instanciación trivial con `acc = 0`

❌ **NUNCA**:
- Intentar probar directamente con inducción sin `generalizing`
- Asumir que omega conoce propiedades de `foldl`
- Usar acumulador implícito en hipótesis inductiva

### Ejemplo Completo: Tres Variantes

#### Variante 1: Cota Inferior (≥)
```lean
lemma foldl_add_ge_aux (l : List ℕ) (m acc : ℕ)
  (hbound : ∀ x ∈ l, x ≥ m) :
  l.foldl (· + ·) acc ≥ acc + l.length * m
```

#### Variante 2: Cota Superior (≤)
```lean
lemma foldl_add_le_aux (l : List ℕ) (m acc : ℕ)
  (hbound : ∀ x ∈ l, x ≤ m) :
  l.foldl (· + ·) acc ≤ acc + l.length * m
```

#### Variante 3: Suma con Negación
```lean
lemma foldl_add_neg_aux (l : List ℤ) (acc : ℤ) :
  (l.map (· * (-1))).foldl (· + ·) (-acc) = -(l.foldl (· + ·) acc) := by
  induction l generalizing acc with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp only [List.map, List.foldl]
    rw [ih (acc + h)]
    ring  -- ✅ ring maneja álgebra con (-1)
```

### Template Reutilizable

```lean
-- TEMPLATE PARA LEMAS SOBRE foldl

/-- Lema auxiliar: [DESCRIPCIÓN] con acumulador arbitrario -/
lemma [nombre]_aux (l : List α) ([parámetros]) (acc : β)
  ([hipótesis]) :
  l.foldl op acc REL acc + [expr] := by
  induction l generalizing acc with  -- ✅ NO OLVIDAR: generalizing acc
  | nil => 
    simp [List.foldl]
  | cons h t ih =>
    simp only [List.foldl, List.length]
    have hh : [propiedad_de_h] := [justificación]
    have ih' : t.foldl op (acc OP h) REL ... := by
      apply ih
      [adaptar hipótesis]
    calc t.foldl op (acc OP h)
        REL ... := ih'
      _ = acc + ... := by ring      -- ✅ ring para álgebra
      _ REL acc + ... := by omega   -- ✅ omega para aritmética
      _ = acc + ... := by ring

/-- Lema principal: caso acc = 0 -/
lemma [nombre] (l : List α) ([parámetros]) :
  l.foldl op 0 REL [expr] := by
  have h := [nombre]_aux l [parámetros] 0 [hipótesis]
  simp at h
  exact h
```

### Táctica: Cuándo Usar `ring` vs `omega`

✅ **Usar `ring`**:
- Reorganizar expresiones algebraicas: `(a + b) + c = a + (b + c)`
- Expandir/factorizar: `(n + 1) * m = n * m + m`
- Simplificar con `-1`: `-(a + b) = -a + -b`

✅ **Usar `omega`**:
- Probar desigualdades: `h ≥ m → h + x ≥ m + x`
- Después de `ring` ha reorganizado a forma `acc + ...`
- Comparar expresiones aritméticas lineales

❌ **Evitar**:
- `omega` sin antes usar `ring` para reorganizar
- Asumir que `omega` hará álgebra automáticamente

### Caso de Estudio: adjustDelta_bounded

**Situación**: Probar que `adjustDelta δ ∈ [-3, 3]`

**Estrategia diferente**: Análisis de casos con `split_ifs`

```lean
lemma adjustDelta_bounded (δ : ℤ) :
  -3 ≤ adjustDelta δ ∧ adjustDelta δ ≤ 3 := by
  unfold adjustDelta
  split_ifs with h1 h2
  · -- Caso 1: δ > 3 → adjustDelta δ = δ - 6
    constructor
    · omega  -- -3 ≤ δ - 6 (porque 4 ≤ δ ≤ 9)
    · omega  -- δ - 6 ≤ 3
  · -- Caso 2: δ ≤ 3 ∧ δ < -3 → adjustDelta δ = δ + 6
    constructor
    · omega  -- -3 ≤ δ + 6 (porque -9 ≤ δ ≤ -4)
    · omega  -- δ + 6 ≤ 3
  · -- Caso 3: -3 ≤ δ ≤ 3 → adjustDelta δ = δ
    constructor
    · omega  -- -3 ≤ δ (trivial del caso)
    · omega  -- δ ≤ 3 (trivial del caso)
```

**Lección**: Para funciones definidas con `if-then-else`:
1. ✅ Usar `split_ifs` para separar casos
2. ✅ Omega puede probar cada caso independientemente
3. ✅ No necesitas `generalizing` si no hay recursión

### Referencias de Implementación Completas

**Archivos de referencia con implementaciones probadas**:
- `Documentos_TCN_01/TCN_01_Fundamentos_UPDATED.lean` (líneas 543-620)
- `Documentos_TCN_01/INSTRUCCIONES_APLICACION_LEMAS.md` (explicación detallada)

**Documentación del descubrimiento**:
- `walkthrough_final.md` (sección "Lecciones Técnicas Aprendidas")
- `estado_proyecto.md` (métricas de lemas probados)

---

## 📈 Métricas de Calidad del Código (NUEVA SECCIÓN)

### Para Evaluar el Estado del Proyecto

```markdown
## Reporte de Calidad: [FECHA]

### Errores de Compilación
- Total: [X]
- Bloqueantes: [Y]
- En archivos base: [Z]

### Uso de `sorry`
- Total: [A]
- En teoremas críticos: [B]
- En pruebas auxiliares: [C]

### Complejidad de Archivos
- TCN_03_Matchings.lean: 960 líneas, 0 errores, 0 sorry ✅
- [Otros archivos...]

### Dependencias Bloqueadas
- [ ] TCN_06 ← TCN_03: ✅ DESBLOQUEADO
- [ ] TCN_07 ← TCN_05: [ESTADO]
```

---

## 🎓 Directrices por Archivo

### TCN_01_Fundamentos.lean

**Nivel de estabilidad**: 🔴 CRÍTICO - Base de todo el proyecto

**Modificaciones**:
- Solo con análisis de impacto completo
- Requiere aprobación explícita
- NUNCA agregar `@[ext]` a estructuras

**Tipos de cambios permitidos**:
- Agregar teoremas auxiliares (al final del archivo)
- Agregar docstrings
- Corregir errores matemáticos graves (con justificación)

---

### TCN_02_Reidemeister.lean

**Nivel de estabilidad**: 🟡 ESTABLE - Modificar con precaución

**Modificaciones**:
- Cambios a predicados existentes requieren verificación
- Nuevos predicados/teoremas permitidos

**Tipos de cambios permitidos**:
- Agregar nuevos teoremas sobre R1/R2
- Optimizar predicados decidibles
- Agregar ejemplos y contraejemplos

---

### TCN_03_Matchings.lean

**Nivel de estabilidad**: 🔴 ULTRA-CRÍTICO - 960 líneas, completamente funcional

**Modificaciones**:
- ⚠️ EXTREMA PRECAUCIÓN
- Cualquier cambio requiere branch separado
- Compilación completa después de cada modificación
- NO tocar a menos que sea absolutamente necesario

**Tipos de cambios permitidos**:
- Agregar docstrings
- Agregar comentarios explicativos
- Optimizaciones menores (solo si se verifica exhaustivamente)

**Prohibido**:
- Cambiar signatures de funciones
- Modificar estructuras usadas
- Agregar `@[ext]` a cualquier cosa
- Cambiar tácticas en pruebas existentes

---

### TCN_04_DihedralD6.lean

**Nivel de estabilidad**: 🟢 EN DESARROLLO - Actualmente con `sorry`

**Objetivo actual**: Implementar `actionZMod` y teoremas básicos

**Modificaciones**:
- Permitidas y necesarias
- Seguir enfoque conservador (ver NORMA 5)
- No usar `ext` - usar `cases` en su lugar

**Prioridades**:
1. Implementar `actionZMod`
2. Probar teoremas de grupo (`actionZMod_one`, `actionZMod_mul`)
3. Implementar `actOnPair` y `actOnConfig`
4. Probar propiedades de MulAction

---

### TCN_05_Orbitas.lean

**Nivel de estabilidad**: 🟢 EN DESARROLLO - Depende de TCN_04

**Objetivo**: Teoremas sobre órbitas y estabilizadores

**Modificaciones**:
- Bloqueadas hasta completar TCN_04
- Una vez TCN_04 completo, proceder con implementación

**Recurso disponible**: `TNC_05_1_Teorema_Orbitas_y_estabilizadores.lean` contiene pruebas completas que pueden adaptarse

---

### TCN_06_Representantes.lean y TCN_07_Clasificacion.lean

**Nivel de estabilidad**: 🟡 FUNCIONAL - Dependen de TCN_05

**Modificaciones**:
- Verificar después de cambios en TCN_04/TCN_05
- Probable que compilen sin cambios una vez TCN_04/05 completos

---

## 🚀 Proceso de Actualización de Este Documento

### Cuándo Actualizar (AMPLIADO)
**Actualizar inmediatamente** cuando:
- [NUEVO] Se resuelve un tipo de error recurrente con una solución general
- [NUEVO] Se identifica un patrón de táctica problemática
- [NUEVO] Se establece un protocolo exitoso para correcciones complejas

### Formato de Actualizaciones (ACTUALIZADO)
```markdown
### [NORMA X]: [Título Descriptivo] ([Fecha])

**Contexto**: [Qué problema se estaba resolviendo]

**Análisis**: [Diagnóstico técnico detallado]

**Solución**: [Qué se hizo exactamente]

**Resultado**: [Qué se logró]

**Patrones identificados**: [Para futuras referencias]

**Norma creada/modificada**: [Referencia]

**Verificación**: [Cómo se validó]
```

---

## 📞 Contacto y Resolución de Dudas

### Cuándo Consultar Este Documento

- ✅ Antes de iniciar cualquier modificación
- ✅ Cuando encuentres un error no documentado
- ✅ Al revisar código de otro colaborador
- ✅ Antes de hacer merge a main

### Qué Hacer Si Este Documento No Cubre Tu Caso

1. Analizar el problema cuidadosamente
2. Buscar casos similares en el documento
3. Aplicar principios generales (estabilidad, cambios incrementales)
4. Documentar tu decisión
5. Actualizar este documento con tu caso

---

## ✅ Resumen Ejecutivo - Top 15 Reglas (ACTUALIZADO)

Para referencia rápida, las 15 reglas más importantes:

1. 🛑 **NUNCA** agregar `@[ext]` a `OrderedPair` o `K3Config`
2. 🧪 **SIEMPRE** compilar después de cada cambio  
3. 📝 **SIEMPRE** documentar decisiones no obvias
4. 🔄 **SIEMPRE** hacer cambios incrementales
5. 🎯 **SIEMPRE** verificar archivos dependientes
6. ⚠️ **NUNCA** modificar TCN_03 sin extrema precaución
7. 📊 **SIEMPRE** crear análisis de impacto para cambios a archivos base
8. 🔍 **SIEMPRE** usar `cases` en lugar de `ext` en código nuevo
9. 🛠️ **SIEMPRE** usar `refine` en lugar de `use; simp` para construcciones complejas
10. 🔧 **SIEMPRE** proporcionar argumentos explícitos a lemas con hipótesis
11. 📚 **SIEMPRE** consultar este documento antes de modificar
12. 📈 **SIEMPRE** actualizar este documento con nuevos aprendizajes
13. 🚨 **SIEMPRE** priorizar errores que bloquean múltiples archivos
14. 📋 **SIEMPRE** completar checklist de verificación post-corrección
15. 💡 **SIEMPRE** documentar patrones de error recurrentes para referencia futura

---

## 📄 Firmas y Aprobaciones (ACTUALIZADO)

**Documento creado por**: Dr. Pablo Eduardo Cancino Marentes  
**Fecha de creación**: 2025-12-07  
**Última actualización**: 2025-12-11  
**Versión**: 2.0  
**Estado**: Oficial - Vigente

**Revisiones**:
- [x] Primera implementación completa de TCN_03 según estas normas (2025-12-07)
- [x] Verificación de que TCN_06 y TCN_07 compilan (2025-12-08)
- [x] Corrección de emergencia TCN_06 (Topología) y TCN_04 (Compilación) (2025-12-11)
- [ ] Review después de 30 días de uso

**Aprobado por**:
- [x] Dr. Pablo Eduardo Cancino Marentes
- [ ] [Otro miembro del equipo]

---

**FIN DEL DOCUMENTO NORMATIVO**

*Este documento debe consultarse antes de realizar cualquier modificación al proyecto TME_Nudos*
