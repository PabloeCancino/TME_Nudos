# Documentación de Integración Continua (CI/CD)

## Descripción General

Este documento describe la configuración de GitHub Actions implementada para el proyecto TME_Nudos, que proporciona integración continua completa para compilar, probar y verificar el código Lean 4 automáticamente.

## Workflows Configurados

### 1. CI Build (`build.yml`)

**Propósito**: Compilación principal del proyecto y verificación de calidad del código.

**Trigger**: 
- Push a ramas `master` o `main`
- Pull requests a ramas `master` o `main`
- Manual (workflow_dispatch)

**Jobs**:

#### build-and-test
Compila el proyecto completo y ejecuta verificaciones básicas.

**Pasos**:
1. Checkout del código
2. Instalación de elan (gestor de versiones de Lean)
3. Verificación de versión de Lean
4. Cache de dependencias (.lake)
5. Descarga de cache de Mathlib
6. Compilación del proyecto (`lake build`)
7. Ejecución de tests básicos
8. Verificación de ausencia de `sorry` (pruebas incompletas)
9. Verificación de artifacts en el árbol de código fuente
10. Generación de reporte de compilación

#### lint
Ejecuta análisis de estilo y calidad del código.

**Pasos**:
1. Instalación del entorno
2. Ejecución del linter de Lean
3. Reporte de advertencias encontradas

**Timeout**: 30 minutos (build-and-test), 20 minutos (lint)

### 2. Test Suite (`test.yml`)

**Propósito**: Ejecución exhaustiva de tests y verificación de completitud de pruebas.

**Trigger**:
- Push a ramas `master` o `main`
- Pull requests a ramas `master` o `main`
- Manual (workflow_dispatch)

**Job: test**

**Pasos**:
1. Setup del entorno Lean
2. Compilación del proyecto
3. Test del módulo principal (`TMENudos.lean`)
4. Test de módulos individuales (`TCN_*.lean`)
5. Verificación de archivos de test
6. Verificación de completitud de pruebas (búsqueda de `sorry`)
7. Generación de reporte de tests

**Timeout**: 30 minutos

**Verificaciones**:
- ✅ Todos los módulos compilan correctamente
- ✅ No hay pruebas incompletas (`sorry`)
- ✅ Tests específicos pasan exitosamente

### 3. PR Quality Checks (`pr-checks.yml`)

**Propósito**: Verificación de calidad para pull requests.

**Trigger**:
- Pull request abierto, sincronizado o reabierto

**Job: quality**

**Pasos**:
1. Verificación del título del PR (formato convencional)
2. Detección de archivos grandes (>1MB)
3. Búsqueda de patrones sensibles (passwords, secrets, etc.)
4. Verificación de estructura de archivos requeridos
5. Generación de reporte de calidad

### 4. Lean Action CI (`lean_action_ci.yml`)

**Propósito**: Generación de documentación usando acciones oficiales de Lean.

**Trigger**:
- Push
- Pull request
- Manual

**Características**:
- Usa `leanprover/lean-action@v1`
- Genera documentación con `docgen-action`
- Puede publicar en GitHub Pages

### 5. Create Release (`create-release.yml`)

**Propósito**: Creación automática de releases cuando cambia la versión de Lean.

**Trigger**:
- Push a `main`/`master` que modifica `lean-toolchain`

### 6. Update Dependencies (`update.yml`)

**Propósito**: Actualización manual de dependencias de Mathlib.

**Trigger**: Manual (workflow_dispatch)

### 7. Update Lean (`update-lean.yml`)

**Propósito**: Actualización programada de Lean y Mathlib.

**Trigger**:
- Programado: Lunes a las 9:00 AM UTC
- Manual con versión específica

**Características**:
- Actualiza a última versión estable o versión específica
- Intenta compilar el proyecto
- Crea PR automático si la compilación es exitosa
- Reporta fallos para intervención manual

## Caching

Todos los workflows utilizan GitHub Actions Cache para optimizar tiempos:

```yaml
- uses: actions/cache@v4
  with:
    path: .lake
    key: ${{ runner.os }}-lake-${{ hashFiles('lake-manifest.json') }}
    restore-keys: |
      ${{ runner.os }}-lake-
```

**Beneficios**:
- Reduce tiempo de compilación en ~80%
- Reutiliza compilaciones de Mathlib
- Invalida cache automáticamente cuando cambian dependencias

## Badges de Estado

El README incluye badges que muestran el estado de los workflows:

```markdown
[![CI Build](https://github.com/PabloeCancino/TME_Nudos/actions/workflows/build.yml/badge.svg)](...)
[![Test Suite](https://github.com/PabloeCancino/TME_Nudos/actions/workflows/test.yml/badge.svg)](...)
[![Lean Action CI](https://github.com/PabloeCancino/TME_Nudos/actions/workflows/lean_action_ci.yml/badge.svg)](...)
```

## Ejecución Local

Para reproducir las verificaciones de CI localmente:

```bash
# Instalar elan si no está instalado
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Compilar el proyecto
lake build

# Verificar módulo principal
lake env lean TMENudos.lean

# Buscar pruebas incompletas
grep -r "sorry" TMENudos/*.lean
```

## Mejores Prácticas

1. **Commits frecuentes**: Los workflows se ejecutan en cada push, permitiendo detección temprana de problemas
2. **Pull Requests**: Todas las PRs pasan por verificaciones de calidad antes del merge
3. **Cache**: Se reutiliza automáticamente entre ejecuciones para velocidad
4. **Reportes**: Cada workflow genera resúmenes detallados en GitHub Actions Summary
5. **Timeouts**: Configurados para evitar ejecuciones colgadas

## Solución de Problemas

### El build falla con "out of memory"
- Aumentar el timeout o dividir la compilación en etapas
- Usar máquinas con más recursos (runners más grandes)

### Cache no se restaura
- Verificar que `lake-manifest.json` no haya cambiado inesperadamente
- Limpiar cache manualmente desde GitHub Settings > Actions > Caches

### Tests pasan localmente pero fallan en CI
- Verificar versión de Lean (`lean --version`)
- Asegurar que `lake-manifest.json` esté actualizado
- Revisar dependencias en `lakefile.toml`

## Recursos Adicionales

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Lean Community Actions](https://github.com/leanprover/lean-action)

## Mantenimiento

Los workflows se mantienen automáticamente mediante:
- Dependabot para actualizaciones de acciones
- Workflow de actualización semanal de Lean/Mathlib
- Revisión manual de warnings en builds

---

**Última actualización**: Diciembre 2025  
**Mantenedor**: Dr. Pablo Eduardo Cancino Marentes
