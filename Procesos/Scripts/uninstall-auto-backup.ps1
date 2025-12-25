# Script para desinstalar la tarea programada
# Ejecutar como Administrador

$TaskName = "Git Backup TME_Nudos"

$task = Get-ScheduledTask -TaskName $TaskName -ErrorAction SilentlyContinue

if ($task) {
    Write-Host "Eliminando tarea programada '$TaskName'..." -ForegroundColor Yellow
    Unregister-ScheduledTask -TaskName $TaskName -Confirm:$false
    Write-Host "✅ Tarea eliminada exitosamente" -ForegroundColor Green
}
else {
    Write-Host "⚠️  No se encontró la tarea '$TaskName'" -ForegroundColor Yellow
}

Read-Host "Presiona Enter para cerrar"
