# Guía: CI/CD en GitHub y Actualización de Lean

## Archivos Creados

### 1. `.github/workflows/build.yml`
**Propósito:** Compilación automática en cada push

**Funcionalidades:**
- Instala Lean automáticamente
- Compila todo el proyecto
- Cachea dependencias
- Reporta errores
- Verifica sorry statements

**Triggers:**
- Push a master/main
- Pull requests
- Manual (workflow_dispatch)

### 2. `.github/workflows/update-lean.yml`
**Propósito:** Actualización automática de Lean y Mathlib

**Funcionalidades:**
- Actualización semanal automática (lunes 9 AM)
- Actualización manual con versión específica
- Crea Pull Request si compila exitosamente
- Reporta errores si falla

### 3. `ACTUALIZACION_LEAN.md`
**Propósito:** Guía completa de actualización

**Contenido:**
- Proceso manual paso a paso
- Estrategia automática
- Errores comunes y soluciones
- Comandos útiles
- Checklist completa

## Cómo Usar

### Compilar en GitHub (Primera Vez)

1. **Push los archivos**
```bash
git add .github/workflows/*.yml ACTUALIZACION_LEAN.md
git commit -m "feat: add CI/CD workflows"
git push origin master
```

2. **Habilitar Actions**
- Ve a https://github.com/PabloeCancino/TME_Nudos
- Settings → Actions → General
- Permitir "Read and write permissions"

3. **Ver Resultados**
- Actions tab → Verás el workflow ejecutándose
- Badge de estado: [![CI](badge-url)](actions-url)

### Actualizar Lean (Manual)

```bash
# Actualizar a Lean 4.27
echo "leanprover/lean4:v4.27.0" > lean-toolchain
lake update
lake exe cache get
lake build
```

### Actualizar Lean (Automático)

1. **Ir a Actions en GitHub**
2. **Seleccionar "Update Lean and Mathlib"**
3. **Run workflow**
4. **Elegir versión (v4.27.0)**
5. **Esperar PR automático**

## Próximos Pasos

1. ✅ Archivos creados
2. ⏳ Push a GitHub
3. ⏳ Habilitar Actions
4. ⏳ Primera compilación
5. ⏳ Actualizar a Lean 4.27

## Beneficios

- ✅ Compilación automática
- ✅ Detección temprana de errores
- ✅ Actualizaciones sin esfuerzo
- ✅ Historial de builds
- ✅ Badges de estado
