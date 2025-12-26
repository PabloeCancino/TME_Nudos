# Scripts de Backup Automático Git

Este directorio contiene scripts para automatizar backups del repositorio TME_Nudos.

## Scripts Disponibles

### 1. `git-backup.ps1` (Completo)

Script principal con todas las funcionalidades:
- ✅ Logging completo
- ✅ Manejo de errores
- ✅ Resolución automática de conflictos
- ✅ Mensajes coloridos
- ✅ Resumen detallado

**Uso básico:**
```powershell
.\git-backup.ps1
```

**Con mensaje personalizado:**
```powershell
.\git-backup.ps1 -Message "feat: completar teorema X"
```

**Forzar backup sin cambios:**
```powershell
.\git-backup.ps1 -Force
```

**Modo verbose:**
```powershell
.\git-backup.ps1 -Verbose
```

### 2. `quick-backup.ps1` (Rápido)

Script simplificado para backups rápidos:
```powershell
.\quick-backup.ps1
```

## Configuración de Backup Automático

### Opción 1: Tarea Programada de Windows

**Ejecutar cada hora:**
1. Abrir "Programador de tareas" (Task Scheduler)
2. Crear tarea básica
3. Nombre: "Git Backup TME_Nudos"
4. Desencadenador: Diariamente, repetir cada 1 hora
5. Acción: Iniciar programa
   - Programa: `powershell.exe`
   - Argumentos: `-ExecutionPolicy Bypass -File "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\git-backup.ps1"`
   - Iniciar en: `C:\Users\pablo\OneDrive\Documentos\TME_Nudos`

**Ejecutar al cerrar sesión:**
1. Mismo proceso pero elegir "Al cerrar sesión" como desencadenador

### Opción 2: Atajo de Teclado

Crear acceso directo:
1. Click derecho en Escritorio → Nuevo → Acceso directo
2. Ubicación: 
   ```
   powershell.exe -ExecutionPolicy Bypass -File "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\quick-backup.ps1"
   ```
3. Nombre: "Backup TME_Nudos"
4. Click derecho en acceso directo → Propiedades → Tecla de método abreviado
5. Asignar: `Ctrl + Alt + B`

### Opción 3: Comando Alias

Añadir a tu perfil de PowerShell (`$PROFILE`):
```powershell
function Backup-TME {
    & "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\git-backup.ps1" @args
}

Set-Alias backup Backup-TME
```

Luego solo escribir `backup` en cualquier terminal.

## Ejemplos de Uso

### Backup al final del día
```powershell
.\git-backup.ps1 -Message "daily: trabajo del $(Get-Date -Format 'yyyy-MM-dd')"
```

### Backup antes de cambio importante
```powershell
.\git-backup.ps1 -Message "checkpoint: antes de refactorizar función X"
```

### Backup silencioso (para automatización)
```powershell
.\quick-backup.ps1
```

## Archivo de Log

Los backups se registran en `backup.log`:
- Ubicación: `C:\Users\pablo\OneDrive\Documentos\TME_Nudos\backup.log`
- Rotación automática al llegar a 5MB
- Formato: `[timestamp] [LEVEL] mensaje`

**Ver últimos backups:**
```powershell
Get-Content backup.log -Tail 20
```

## Solución de Problemas

### "Execution of scripts is disabled"
```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

### Conflictos de merge
El script intenta resolverlos automáticamente con `git pull --rebase`. Si falla:
```powershell
git pull --rebase origin master
# Resolver conflictos manualmente
git add .
git rebase --continue
git push origin master
```

### Ver historial de backups
```powershell
git log --oneline --grep="auto-backup" -10
```

## Mejores Prácticas

1. **Backup frecuente**: Ejecutar al menos al final de cada sesión
2. **Mensajes descriptivos**: Usar `-Message` para cambios importantes
3. **Revisar log**: Verificar `backup.log` ocasionalmente
4. **Tags importantes**: Crear tags manualmente para hitos:
   ```powershell
   git tag -a v1.0 -m "Versión 1.0 estable"
   git push origin v1.0
   ```

## Recuperación de Versión Anterior

```powershell
# Ver historial
git log --oneline -20

# Volver a versión específica (solo lectura)
git checkout <commit-hash>

# Regresar a la última versión
git checkout master

# Deshacer último commit (conservando cambios)
git reset --soft HEAD~1

# Deshacer último commit (descartando cambios)
git reset --hard HEAD~1
```
