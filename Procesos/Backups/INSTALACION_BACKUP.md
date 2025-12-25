# Guía de Configuración de Backup Automático

## 🚀 Instalación Rápida (Recomendado)

### Paso 1: Ejecutar el Script de Configuración

1. **Click derecho** en `setup-auto-backup.ps1`
2. Seleccionar **"Ejecutar con PowerShell como administrador"**
3. Seguir las instrucciones interactivas

### Paso 2: Seleccionar Programación

El script te preguntará la frecuencia de backup:

**Opciones disponibles:**
- `1` - **Cada hora** (8am-8pm) - Ideal para desarrollo activo
- `2` - **Cada 2 horas** (8am-8pm) - Balance entre frecuencia y recursos
- `3` - **Al final del día** (8:00 PM) - Mínimo recomendado
- `4` - **Al iniciar sesión** - Backup al encender PC
- `5` - **Al cerrar sesión** - Backup al apagar PC
- `6` - **Personalizado** - Define tu propia hora

**Recomendación:** Opción 2 (cada 2 horas) es ideal para la mayoría de usuarios.

### Paso 3: Verificar Instalación

El script ejecutará un backup de prueba automáticamente.

---

## 📋 Instalación Manual (Alternativa)

Si prefieres configurar manualmente:

### 1. Abrir Programador de Tareas

- Presiona `Win + R`
- Escribe: `taskschd.msc`
- Presiona Enter

### 2. Crear Nueva Tarea

1. Click derecho en "Biblioteca del Programador de tareas"
2. Seleccionar "Crear tarea básica..."

### 3. Configurar Nombre

- **Nombre:** Git Backup TME_Nudos
- **Descripción:** Backup automático del repositorio a GitHub
- Click "Siguiente"

### 4. Configurar Desencadenador

Selecciona cuándo ejecutar:
- **Diariamente:** Para backups a horas específicas
- **Al iniciar sesión:** Backup al encender PC
- **Al iniciar el equipo:** Backup al arrancar Windows

Click "Siguiente"

### 5. Configurar Repetición (si elegiste Diariamente)

- Hora de inicio: 8:00 AM
- **Marcar:** "Repetir cada"
- **Intervalo:** 1 o 2 horas
- **Durante:** 12 horas
- Click "Siguiente"

### 6. Configurar Acción

- **Acción:** Iniciar un programa
- **Programa:** `powershell.exe`
- **Argumentos:**
  ```
  -ExecutionPolicy Bypass -WindowStyle Hidden -File "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\git-backup.ps1"
  ```
- **Iniciar en:**
  ```
  C:\Users\pablo\OneDrive\Documentos\TME_Nudos
  ```
- Click "Siguiente"

### 7. Configuración Avanzada

Antes de finalizar, marca "Abrir propiedades al hacer clic en Finalizar"

En la ventana de propiedades:

**Pestaña General:**
- ✅ Ejecutar tanto si el usuario inició sesión como si no
- ✅ Ejecutar con los privilegios más altos (solo si necesario)

**Pestaña Condiciones:**
- ✅ Iniciar solo si el equipo está conectado a la red
- ⬜ Iniciar solo si el equipo está en corriente alterna (DESMARCAR)
- ⬜ Detener si el equipo deja de recibir alimentación (DESMARCAR)

**Pestaña Configuración:**
- ✅ Permitir que se ejecute la tarea a petición
- ✅ Ejecutar la tarea lo antes posible después de una inicio programado perdido
- ✅ Si la tarea falla, volver a intentar

Click "Aceptar"

---

## 🔍 Verificar que Funciona

### Ver Estado de la Tarea

```powershell
Get-ScheduledTask -TaskName "Git Backup TME_Nudos" | Get-ScheduledTaskInfo
```

### Ejecutar Manualmente

1. Abrir Programador de Tareas
2. Buscar "Git Backup TME_Nudos"
3. Click derecho → **"Ejecutar"**
4. Verificar `backup.log` para confirmar

### Ver Historial de Ejecuciones

```powershell
Get-Content "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\backup.log" -Tail 20
```

---

## 🛠️ Administración

### Deshabilitar Temporalmente

```powershell
Disable-ScheduledTask -TaskName "Git Backup TME_Nudos"
```

### Habilitar Nuevamente

```powershell
Enable-ScheduledTask -TaskName "Git Backup TME_Nudos"
```

### Modificar Programación

1. Abrir Programador de Tareas
2. Buscar la tarea
3. Click derecho → "Propiedades"
4. Pestaña "Desencadenadores"
5. Editar según necesites

### Desinstalar Completamente

**Opción 1:** Ejecutar `uninstall-auto-backup.ps1` como administrador

**Opción 2:** Manual
```powershell
Unregister-ScheduledTask -TaskName "Git Backup TME_Nudos" -Confirm:$false
```

---

## ⚠️ Solución de Problemas

### La tarea no se ejecuta

1. **Verificar que el script existe:**
   ```powershell
   Test-Path "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\git-backup.ps1"
   ```

2. **Verificar permisos de ejecución:**
   ```powershell
   Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
   ```

3. **Ver último error:**
   ```powershell
   Get-ScheduledTask -TaskName "Git Backup TME_Nudos" | Get-ScheduledTaskInfo
   ```

### Código de salida 1

Revisa `backup.log` para ver el error específico:
```powershell
Get-Content backup.log -Tail 50
```

Errores comunes:
- **Conflictos de merge:** Resolver manualmente con `git pull`
- **Sin conexión a internet:** La tarea reintentará en la siguiente ejecución
- **Cambios en GitHub:** Hacer `git pull` manual primero

### La tarea se ejecuta pero no hace nada

Verifica que haya cambios para commitear:
```powershell
cd C:\Users\pablo\OneDrive\Documentos\TME_Nudos
git status
```

Si no hay cambios, es normal que el backup no haga nada.

---

## 📊 Monitoreo

### Ver Últimos 5 Backups

```powershell
git log --oneline --grep="backup" -5
```

### Estadísticas de Backups

```powershell
# Total de backups automáticos
(git log --oneline --grep="auto-backup" --all).Count

# Backups del último mes
git log --oneline --grep="backup" --since="1 month ago"
```

---

## ✅ Checklist de Instalación Exitosa

- [ ] Script `setup-auto-backup.ps1` ejecutado como administrador
- [ ] Tarea aparece en Programador de Tareas
- [ ] Backup de prueba ejecutado exitosamente
- [ ] Archivo `backup.log` creado con entrada exitosa
- [ ] Commit visible en GitHub con mensaje "auto-backup"

---

## 🎯 Recomendaciones Finales

1. **Revisa `backup.log` semanalmente** para detectar problemas
2. **Haz backups manuales antes de cambios grandes:**
   ```powershell
   .\git-backup.ps1 -Message "checkpoint: antes de refactorización importante"
   ```
3. **Crea tags para versiones importantes:**
   ```powershell
   git tag -a v1.0 -m "Versión 1.0 estable"
   git push origin v1.0
   ```
4. **Usa ramas para experimentos arriesgados**

---

¿Necesitas ayuda adicional? Revisa `BACKUP_README.md` para más información sobre el uso de los scripts de backup.
