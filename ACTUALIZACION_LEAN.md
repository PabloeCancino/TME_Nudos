# Guía de Actualización: Lean y Mathlib

## Estado Actual

**Versión Actual:** Lean 4.26.0-rc2 (según `lean-toolchain`)  
**Versión Objetivo:** Lean 4.27.0  
**Historial:** Lean 4.14 → 4.25 → 4.26 → 4.27

## Estrategia de Actualización

### Opción 1: Actualización Manual (Recomendada para primera vez)

#### Paso 1: Actualizar Lean
```bash
# Editar lean-toolchain
echo "leanprover/lean4:v4.27.0" > lean-toolchain

# Verificar instalación
elan show
lean --version
```

#### Paso 2: Actualizar Mathlib
```bash
# Actualizar dependencias
lake update

# Obtener cache de Mathlib (acelera compilación)
lake exe cache get
```

#### Paso 3: Compilar y Verificar
```bash
# Compilar proyecto
lake build

# Si hay errores, compilar archivo por archivo
lake build TMENudos.ZMod_Helpers
lake build TMENudos.TCN_01_Fundamentos
```

#### Paso 4: Resolver Errores de Compatibilidad
```bash
# Ver errores específicos
lake build 2>&1 | tee build_errors.txt

# Buscar APIs deprecadas
grep -r "deprecated" TMENudos/*.lean
```

### Opción 2: Actualización Automática con GitHub Actions

#### Configuración Inicial

1. **Habilitar GitHub Actions**
   - Ve a tu repositorio en GitHub
   - Settings → Actions → General
   - Permitir "Read and write permissions"

2. **Agregar Workflows**
   - Los archivos ya están en `.github/workflows/`
   - `build.yml`: Compilación automática en cada push
   - `update-lean.yml`: Actualización semanal automática

3. **Ejecutar Manualmente**
   - Actions → Update Lean and Mathlib
   - Run workflow
   - Seleccionar versión (v4.27.0 o latest)

#### Funcionamiento Automático

**Compilación (build.yml):**
- Se ejecuta en cada `git push`
- Compila todo el proyecto
- Reporta errores
- Cachea dependencias

**Actualización (update-lean.yml):**
- Se ejecuta semanalmente (lunes 9 AM)
- Actualiza Lean y Mathlib
- Intenta compilar
- Si compila exitosamente, crea Pull Request
- Si falla, reporta warning

## Proceso de Actualización Paso a Paso

### Semana 1: Preparación
```bash
# 1. Crear branch para actualización
git checkout -b update-lean-4.27

# 2. Backup del estado actual
git tag v-lean-4.26-working

# 3. Actualizar lean-toolchain
echo "leanprover/lean4:v4.27.0" > lean-toolchain

# 4. Actualizar Mathlib
lake update
```

### Semana 2: Compilación y Corrección
```bash
# 5. Intentar compilar
lake build 2>&1 | tee errors_4.27.txt

# 6. Analizar errores
cat errors_4.27.txt | grep "error:" | wc -l

# 7. Corregir errores uno por uno
# (Ver sección "Errores Comunes" abajo)
```

### Semana 3: Verificación
```bash
# 8. Compilación limpia
lake clean
lake build

# 9. Verificar teoremas
grep -n "sorry" TMENudos/*.lean

# 10. Ejecutar tests (si existen)
lake test
```

### Semana 4: Merge
```bash
# 11. Commit cambios
git add .
git commit -m "chore: update to Lean 4.27.0"

# 12. Push y crear PR
git push origin update-lean-4.27

# 13. Merge después de revisión
git checkout master
git merge update-lean-4.27
git push origin master
```

## Errores Comunes y Soluciones

### Error 1: APIs Deprecadas de List
**Síntoma:**
```
Unknown constant `List.get?_eq_none`
Unknown constant `List.get?_map`
```

**Solución:**
- Usar `List.getElem?` en lugar de `List.get?`
- Consultar [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/)

### Error 2: Cambios en Omega
**Síntoma:**
```
omega could not prove the goal
```

**Solución:**
- Agregar bounds explícitos con `have`
- Usar lemas auxiliares de ZMod_Helpers

### Error 3: Cambios en Tactic Syntax
**Síntoma:**
```
unexpected token
too many arguments supplied to `use`
```

**Solución:**
- Usar `refine` en lugar de `use` con múltiples argumentos
- Consultar [Lean 4 tactics](https://leanprover.github.io/theorem_proving_in_lean4/)

## Mantenimiento Continuo

### Estrategia Recomendada

**Frecuencia de Actualización:**
- **Lean:** Cada 2-3 versiones menores (ej: 4.25 → 4.27)
- **Mathlib:** Mensualmente (automático con GitHub Actions)

**Proceso:**
1. GitHub Actions crea PR automáticamente
2. Revisar cambios en PR
3. Si compila: Merge
4. Si no compila: Investigar errores manualmente

### Monitoreo

**Suscribirse a:**
- [Lean 4 Releases](https://github.com/leanprover/lean4/releases)
- [Mathlib Announcements](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4)

**Revisar semanalmente:**
- GitHub Actions status
- Pull Requests automáticos
- Build logs

## Comandos Útiles

### Verificar Versiones
```bash
# Versión de Lean
lean --version

# Versión de Lake
lake --version

# Versiones instaladas
elan show

# Mathlib commit
cat lake-manifest.json | grep mathlib
```

### Actualización Rápida
```bash
# Script de actualización completa
#!/bin/bash
echo "leanprover/lean4:v4.27.0" > lean-toolchain
lake update
lake exe cache get
lake build
```

### Rollback
```bash
# Volver a versión anterior
git checkout lean-toolchain lake-manifest.json
lake build
```

## Checklist de Actualización

- [ ] Backup del estado actual (git tag)
- [ ] Actualizar `lean-toolchain`
- [ ] Ejecutar `lake update`
- [ ] Obtener cache: `lake exe cache get`
- [ ] Compilar: `lake build`
- [ ] Revisar errores
- [ ] Corregir APIs deprecadas
- [ ] Verificar teoremas (no nuevos sorry)
- [ ] Ejecutar tests
- [ ] Commit y push
- [ ] Actualizar documentación

## Recursos

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Zulip Chat](https://leanprover.zulipchat.com/)
- [Migration Guide](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki)

---

*Última actualización: 2025-12-25*  
*Versión actual: Lean 4.26.0-rc2*  
*Próxima versión: Lean 4.27.0*
