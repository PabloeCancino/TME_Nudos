# ============================================================================
# Script de Configuración Automática de Tarea Programada
# ============================================================================
# Descripción: Configura automáticamente la tarea en el Programador de Tareas
# Ejecutar como Administrador
# ============================================================================

# Verificar si se está ejecutando como administrador
$currentPrincipal = New-Object Security.Principal.WindowsPrincipal([Security.Principal.WindowsIdentity]::GetCurrent())
$isAdmin = $currentPrincipal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)

if (-not $isAdmin) {
    Write-Host "⚠️  Este script requiere permisos de administrador" -ForegroundColor Yellow
    Write-Host "Click derecho en el script y selecciona 'Ejecutar como administrador'" -ForegroundColor Yellow
    Write-Host ""
    Read-Host "Presiona Enter para salir"
    exit
}

Write-Host "═══════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  Configuración de Backup Automático - TME_Nudos" -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

# Configuración
$TaskName = "Git Backup TME_Nudos"
$ScriptPath = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\git-backup.ps1"
$WorkingDirectory = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos"

# Verificar que el script existe
if (-not (Test-Path $ScriptPath)) {
    Write-Host "❌ Error: No se encuentra el script en $ScriptPath" -ForegroundColor Red
    Read-Host "Presiona Enter para salir"
    exit
}

# Mostrar opciones de programación
Write-Host "Selecciona la frecuencia de backup:" -ForegroundColor Yellow
Write-Host ""
Write-Host "1. Cada hora (durante horas de trabajo: 8am-8pm)" -ForegroundColor White
Write-Host "2. Cada 2 horas (durante horas de trabajo)" -ForegroundColor White
Write-Host "3. Al final del día (8:00 PM)" -ForegroundColor White
Write-Host "4. Al iniciar sesión" -ForegroundColor White
Write-Host "5. Al cerrar sesión" -ForegroundColor White
Write-Host "6. Personalizado" -ForegroundColor White
Write-Host ""

$opcion = Read-Host "Ingresa el número de opción (1-6)"

# Eliminar tarea existente si existe
$existingTask = Get-ScheduledTask -TaskName $TaskName -ErrorAction SilentlyContinue
if ($existingTask) {
    Write-Host "⚠️  Ya existe una tarea con el nombre '$TaskName'" -ForegroundColor Yellow
    $respuesta = Read-Host "¿Deseas reemplazarla? (s/n)"
    if ($respuesta -eq 's' -or $respuesta -eq 'S') {
        Unregister-ScheduledTask -TaskName $TaskName -Confirm:$false
        Write-Host "✅ Tarea anterior eliminada" -ForegroundColor Green
    }
    else {
        Write-Host "Operación cancelada" -ForegroundColor Yellow
        Read-Host "Presiona Enter para salir"
        exit
    }
}

# Crear acción de la tarea
$Action = New-ScheduledTaskAction `
    -Execute "powershell.exe" `
    -Argument "-ExecutionPolicy Bypass -WindowStyle Hidden -File `"$ScriptPath`"" `
    -WorkingDirectory $WorkingDirectory

# Configurar trigger según la opción
switch ($opcion) {
    "1" {
        # Cada hora de 8am a 8pm
        $Trigger = New-ScheduledTaskTrigger -Daily -At 8:00AM
        $Trigger.Repetition = $(New-ScheduledTaskTrigger -Once -At 8:00AM -RepetitionInterval (New-TimeSpan -Hours 1) -RepetitionDuration (New-TimeSpan -Hours 12)).Repetition
        $descripcion = "Backup cada hora (8am-8pm)"
    }
    "2" {
        # Cada 2 horas de 8am a 8pm
        $Trigger = New-ScheduledTaskTrigger -Daily -At 8:00AM
        $Trigger.Repetition = $(New-ScheduledTaskTrigger -Once -At 8:00AM -RepetitionInterval (New-TimeSpan -Hours 2) -RepetitionDuration (New-TimeSpan -Hours 12)).Repetition
        $descripcion = "Backup cada 2 horas (8am-8pm)"
    }
    "3" {
        # Al final del día
        $Trigger = New-ScheduledTaskTrigger -Daily -At 8:00PM
        $descripcion = "Backup diario a las 8:00 PM"
    }
    "4" {
        # Al iniciar sesión
        $Trigger = New-ScheduledTaskTrigger -AtLogOn
        $descripcion = "Backup al iniciar sesión"
    }
    "5" {
        # Al cerrar sesión (requiere configuración especial)
        Write-Host "⚠️  La opción 'Al cerrar sesión' requiere configuración avanzada" -ForegroundColor Yellow
        Write-Host "Se configurará para ejecutar al final del día (8:00 PM)" -ForegroundColor Yellow
        $Trigger = New-ScheduledTaskTrigger -Daily -At 8:00PM
        $descripcion = "Backup diario a las 8:00 PM"
    }
    "6" {
        # Personalizado
        Write-Host "Ingresa la hora de ejecución (formato 24h, ej: 18:00):" -ForegroundColor Yellow
        $hora = Read-Host "Hora"
        $Trigger = New-ScheduledTaskTrigger -Daily -At $hora
        $descripcion = "Backup diario a las $hora"
    }
    default {
        Write-Host "❌ Opción inválida" -ForegroundColor Red
        Read-Host "Presiona Enter para salir"
        exit
    }
}

# Configurar la tarea
$Settings = New-ScheduledTaskSettingsSet `
    -AllowStartIfOnBatteries `
    -DontStopIfGoingOnBatteries `
    -StartWhenAvailable `
    -RunOnlyIfNetworkAvailable

$Principal = New-ScheduledTaskPrincipal `
    -UserId "$env:USERDOMAIN\$env:USERNAME" `
    -LogonType Interactive `
    -RunLevel Limited

# Registrar la tarea
try {
    Register-ScheduledTask `
        -TaskName $TaskName `
        -Description "Backup automático del repositorio TME_Nudos a GitHub - $descripcion" `
        -Action $Action `
        -Trigger $Trigger `
        -Settings $Settings `
        -Principal $Principal `
        -Force | Out-Null
    
    Write-Host ""
    Write-Host "═══════════════════════════════════════════════════════" -ForegroundColor Green
    Write-Host "✅ Tarea programada creada exitosamente" -ForegroundColor Green
    Write-Host "═══════════════════════════════════════════════════════" -ForegroundColor Green
    Write-Host ""
    Write-Host "Detalles de la tarea:" -ForegroundColor Cyan
    Write-Host "  Nombre: $TaskName" -ForegroundColor White
    Write-Host "  Programación: $descripcion" -ForegroundColor White
    Write-Host "  Script: $ScriptPath" -ForegroundColor White
    Write-Host ""
    Write-Host "Puedes ver y administrar la tarea en:" -ForegroundColor Yellow
    Write-Host "  Programador de tareas → Biblioteca del Programador de tareas" -ForegroundColor White
    Write-Host ""
    
    # Preguntar si ejecutar ahora
    $ejecutar = Read-Host "¿Deseas ejecutar un backup ahora para probar? (s/n)"
    if ($ejecutar -eq 's' -or $ejecutar -eq 'S') {
        Write-Host ""
        Write-Host "🚀 Ejecutando backup de prueba..." -ForegroundColor Cyan
        Start-ScheduledTask -TaskName $TaskName
        Start-Sleep -Seconds 2
        
        # Verificar resultado
        $taskInfo = Get-ScheduledTaskInfo -TaskName $TaskName
        if ($taskInfo.LastTaskResult -eq 0) {
            Write-Host "✅ Backup ejecutado exitosamente" -ForegroundColor Green
        }
        else {
            Write-Host "⚠️  El backup se ejecutó con código: $($taskInfo.LastTaskResult)" -ForegroundColor Yellow
            Write-Host "Revisa el archivo backup.log para más detalles" -ForegroundColor Yellow
        }
    }
    
}
catch {
    Write-Host ""
    Write-Host "❌ Error al crear la tarea: $_" -ForegroundColor Red
    Write-Host ""
}

Write-Host ""
Write-Host "Presiona Enter para cerrar..." -ForegroundColor Gray
Read-Host
