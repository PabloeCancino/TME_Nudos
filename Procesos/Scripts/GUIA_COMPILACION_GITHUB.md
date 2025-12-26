# 🚀 Guía de Compilación en GitHub - TME_Nudos

Esta guía explica cómo compilar tu proyecto Lean en GitHub usando GitHub Actions.

---

## 📋 Tabla de Contenidos

1. [Método Rápido (Recomendado)](#método-rápido-recomendado)
2. [Método Manual](#método-manual)
3. [Verificar Resultados](#verificar-resultados)
4. [Solución de Problemas](#solución-de-problemas)

---

## ⚡ Método Rápido (Recomendado)

### Uso Básico

```powershell
cd C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Procesos\Scripts\
.\quick-compile.ps1
```

Esto hará:
1. ✅ Backup automático a GitHub
2. ✅ Abre el navegador en GitHub Actions
3. ✅ Muestra información del commit

### Opciones Avanzadas

#### Con mensaje personalizado
```powershell
.\Procesos\Scripts\quick-compile.ps1 -Message "Corrección de teoremas en TCN_01"
```

#### Sin abrir navegador
```powershell
.\Procesos\Scripts\quick-compile.ps1 -NoBrowser
```

#### Con monitoreo de compilación (requiere GitHub CLI)
```powershell
.\Procesos\Scripts\quick-compile.ps1 -Watch
```

#### Forzar sobrescritura de GitHub
```powershell
.\Procesos\Scripts\quick-compile.ps1 -Force
```

#### Combinación de opciones
```powershell
.\Procesos\Scripts\quick-compile.ps1 -Message "Fix: dme_mirror theorem" -Watch
```

---

## 🔧 Método Manual

Si prefieres hacer el proceso paso a paso:

### Paso 1: Ejecutar Backup

```powershell
cd C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Procesos\Scripts\
.\github-backup.ps1
```

### Paso 2: Abrir GitHub Actions

Ve a: https://github.com/PabloeCancino/TME_Nudos/actions

### Paso 3: Monitorear Compilación

Verás dos workflows ejecutándose:
- 🔨 **CI Build** - Compilación completa
- 📚 **Lean Action CI** - Compilación + documentación

---

## 📊 Verificar Resultados

### En GitHub Actions

1. **Accede a**: https://github.com/PabloeCancino/TME_Nudos/actions

2. **Busca tu commit** en la lista de workflows

3. **Interpretación de estados**:
   - ✅ **Verde** = Compilación exitosa
   - ❌ **Rojo** = Errores de compilación
   - 🟡 **Amarillo** = En progreso
   - ⚪ **Gris** = En cola

### Ver Logs de Compilación

Si hay errores:

1. Click en el workflow que falló
2. Click en el job "Build Lean Project"
3. Expande el paso "Build project"
4. Verás los errores de Lean con detalles completos

### Ejemplo de Log de Error

```
error: unknown identifier 'dme_mirror'
TMENudos/TCN_01_Fundamentos.lean:123:5
```

---

## 🐛 Solución de Problemas

### Error: "No se encontró github-backup.ps1"

**Solución**: Asegúrate de estar en el directorio correcto:
```powershell
cd C:\Users\pablo\OneDrive\Documentos\TME_Nudos
```

### Error: "Historiales divergentes"

**Causa**: GitHub tiene commits que no están en tu repositorio local.

**Solución**:
```powershell
# Opción 1: Sobrescribir GitHub con tu versión local
.\quick-compile.ps1 -Force

# Opción 2: Integrar cambios de GitHub primero
git pull origin master
.\quick-compile.ps1
```

### Error: "No hay cambios para sincronizar"

**Causa**: No has modificado ningún archivo.

**Solución**: Esto es normal. No necesitas hacer backup si no hay cambios.

### Compilación Falla en GitHub

**Pasos**:

1. **Verifica que compila localmente**:
   ```powershell
   cd C:\Users\pablo\OneDrive\Documentos\TME_Nudos
   lake build
   ```

2. **Si compila localmente pero falla en GitHub**:
   - Verifica que todos los archivos estén en el repositorio
   - Revisa que no haya archivos bloqueados por `.gitignore`

3. **Si no compila localmente**:
   - Corrige los errores primero
   - Luego ejecuta `.\quick-compile.ps1`

---

## 📚 Workflows Disponibles

Tu proyecto tiene configurados estos workflows:

### 1. CI Build (`build.yml`)

**Se ejecuta en**:
- Push a `master` o `main`
- Pull requests
- Manualmente desde GitHub Actions

**Hace**:
- Instala Lean usando `elan`
- Descarga caché de dependencias
- Ejecuta `lake build`
- Verifica `sorry` statements
- Genera reporte de compilación

### 2. Lean Action CI (`lean_action_ci.yml`)

**Se ejecuta en**:
- Cualquier push
- Pull requests
- Manualmente desde GitHub Actions

**Hace**:
- Usa la acción oficial de Lean
- Genera documentación automática
- Puede publicar en GitHub Pages

### 3. Update Lean (`update-lean.yml`)

**Se ejecuta**:
- Manualmente desde GitHub Actions

**Hace**:
- Actualiza la versión de Lean
- Actualiza dependencias

---

## 🎯 Flujo de Trabajo Recomendado

### Para Desarrollo Diario

```powershell
# 1. Trabaja en tu código
# 2. Cuando termines una sesión:
.\quick-compile.ps1 -Message "Descripción de cambios"
```

### Para Cambios Importantes

```powershell
# 1. Verifica que compila localmente
lake build

# 2. Si compila, sube a GitHub
.\quick-compile.ps1 -Message "Feature: nuevo teorema X" -Watch

# 3. Espera confirmación de compilación en GitHub
```

### Para Debugging

```powershell
# 1. Ver qué se subiría sin hacer cambios
.\github-backup.ps1 -DryRun

# 2. Si todo se ve bien, ejecuta
.\quick-compile.ps1
```

---

## 🔍 Monitoreo Avanzado (Opcional)

### Instalar GitHub CLI

Para usar la opción `-Watch`, instala GitHub CLI:

```powershell
winget install GitHub.cli
```

Luego autentícate:

```powershell
gh auth login
```

### Usar Monitoreo

```powershell
.\quick-compile.ps1 -Watch
```

Esto mostrará el estado de compilación en tiempo real en tu terminal.

---

## 📝 Notas Importantes

### Archivos Ignorados

El archivo `.gitignore` excluye automáticamente:
- `Procesos/` - Documentos de trabajo
- `.lake/` - Archivos temporales de Lean
- `build/` - Archivos compilados
- `.vscode/` - Configuración de IDE
- `.gemini/` - Archivos de Gemini

### Seguridad

El script `github-backup.ps1`:
- ✅ NUNCA modifica tu repositorio local
- ✅ Solo sube cambios (backup unidireccional)
- ✅ Aborta si hay conflictos (a menos que uses `-Force`)
- ✅ Respeta automáticamente `.gitignore`
- ✅ Pide confirmación antes de subir cambios

---

## 🆘 Ayuda Adicional

### Ver logs del script

Los logs se guardan en:
```
C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Procesos\Logs\github-backup.log
```

### Comandos Git útiles

```powershell
# Ver estado actual
git status

# Ver últimos commits
git log --oneline -5

# Ver diferencias
git diff

# Ver archivos en staging
git diff --cached --name-only
```

---

## 📞 Contacto

Si encuentras problemas, revisa:
1. Los logs en `Procesos\Logs\github-backup.log`
2. GitHub Actions: https://github.com/PabloeCancino/TME_Nudos/actions
3. La documentación de Lean: https://lean-lang.org/

---

**Última actualización**: 2025-12-25
