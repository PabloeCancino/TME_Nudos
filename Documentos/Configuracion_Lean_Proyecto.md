# Configuración de Lean y Condiciones de Implementación

## 📋 Versión de Lean y Dependencias

### Versión de Lean
- **Lean 4: v4.26.0-rc2** (Release Candidate 2)
  - Archivo: `lean-toolchain`

### Versión de Mathlib
- **Mathlib: v4.26.0-rc2** (debe coincidir con la versión de Lean)
  - Repositorio: `leanprover-community/mathlib`

## ⚙️ Configuraciones Específicas del Proyecto

Las siguientes opciones están configuradas en `lakefile.toml` y **DEBEN** respetarse en cualquier corrección o implementación:

### 1. `pp.unicode.fun = true`
- **Descripción**: Imprime funciones usando sintaxis Unicode
- **Sintaxis requerida**: `fun a ↦ b` en lugar de `fun a => b`
- **Impacto**: Todo código debe usar el símbolo Unicode `↦` para lambdas

**Ejemplo:**
```lean
-- ✅ CORRECTO
map (fun x ↦ x + 1) lista

-- ❌ INCORRECTO (aunque válido en Lean, no coincide con la configuración)
map (fun x => x + 1) lista
```

### 2. `relaxedAutoImplicit = false` ⚠️ **MUY IMPORTANTE**
- **Descripción**: Los argumentos implícitos NO se infieren automáticamente
- **Requisito**: Todos los argumentos implícitos deben declararse explícitamente con `{...}` o `[...]`
- **Impacto**: Evita errores como "unknown identifier" cuando no se declaran variables de tipo

**Ejemplo:**
```lean
-- ❌ INCORRECTO (fallará con relaxedAutoImplicit = false)
def myFunction (x : α) := x

-- ✅ CORRECTO
def myFunction {α : Type*} (x : α) := x
```

**Casos comunes que requieren declaración explícita:**
- Variables de tipo: `{α : Type*}`, `{β : Type}`
- Instancias de typeclass: `[Add α]`, `[Group G]`
- Parámetros de estructuras: `{n : ℕ}`

### 3. `weak.linter.mathlibStandardSet = true`
- **Descripción**: Activa el conjunto de linters estándar de mathlib
- **Requisito**: El código debe cumplir con los estándares de estilo de mathlib
- **Impacto**: Advertencias sobre:
  - Nombres de variables no convencionales
  - Uso innecesario de `have` o `let`
  - Pruebas que pueden simplificarse
  - Importaciones no utilizadas

### 4. `maxSynthPendingDepth = 3`
- **Descripción**: Profundidad máxima de síntesis de instancias de typeclass
- **Límite**: Máximo 3 niveles de profundidad
- **Impacto**: Instancias complejas pueden fallar si exceden esta profundidad
- **Solución**: Declarar instancias intermedias explícitamente si es necesario

## 📁 Estructura del Proyecto

- **Nombre del paquete**: `TME_Nudos`
- **Versión**: 0.1.0
- **Librería principal**: `TMENudos`
  - Directorio: `TMENudos/`
- **Ejecutable**: `check_r2`
  - Archivo raíz: `check_r2.lean`

## ✅ Checklist de Compatibilidad para Correcciones

Antes de proponer cualquier corrección, verifica:

- [ ] **Declaración explícita de variables de tipo**
  - Todas las variables de tipo están declaradas con `{α : Type*}` u otro tipo explícito
  
- [ ] **Sintaxis Unicode para lambdas**
  - Se usa `fun x ↦ ...` en lugar de `fun x => ...`
  
- [ ] **Imports compatibles con Mathlib v4.26.0-rc2**
  - Los nombres de módulos y teoremas existen en esta versión específica
  - Verificar en la documentación de mathlib para v4.26.0-rc2
  
- [ ] **Cadenas de instancias no profundas**
  - Las dependencias de typeclass no requieren más de 3 niveles de síntesis
  - Declarar instancias intermedias si es necesario
  
- [ ] **Cumplimiento con linters de mathlib**
  - No hay advertencias de linters innecesarias
  - El código sigue las convenciones de nomenclatura de mathlib

## 🔧 Ejemplos de Errores Comunes y Soluciones

### Error: "unknown identifier 'α'"
```lean
-- ❌ INCORRECTO
def ejemplo (x : α) := x

-- ✅ CORRECTO
def ejemplo {α : Type*} (x : α) := x
```

### Error: "failed to synthesize instance"
```lean
-- ❌ INCORRECTO (puede fallar si la cadena es muy profunda)
def suma {α : Type*} (x y : α) := x + y

-- ✅ CORRECTO
def suma {α : Type*} [Add α] (x y : α) := x + y
```

### Error de sintaxis con lambdas
```lean
-- Asegúrate de usar el símbolo Unicode correcto
-- ✅ CORRECTO
List.map (fun x ↦ x + 1) [1, 2, 3]
```

## 📚 Referencias

- **Lean 4 Manual**: https://lean-lang.org/lean4/doc/
- **Mathlib Docs**: https://leanprover-community.github.io/mathlib4_docs/
- **Configuración del proyecto**: Ver archivos `lakefile.toml` y `lean-toolchain` en la raíz del proyecto

---

**Última actualización**: 2025-12-07  
**Proyecto**: Teoría Modular Estructural de Nudos (TME_Nudos)
