# ============================================================================
# Script de Backup Rápido (versión simplificada)
# ============================================================================
# Uso: .\quick-backup.ps1
# C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Procesos\Scripts\
# ============================================================================

$RepoPath = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\"

Set-Location $RepoPath

$fecha = Get-Date -Format "yyyy-MM-dd HH:mm"

Write-Host "🔄 Backup rápido..." -ForegroundColor Cyan

git add .
git commit -m "backup: $fecha"
git push origin master

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Backup completado: $fecha" -ForegroundColor Green
}
else {
    Write-Host "❌ Error en backup" -ForegroundColor Red
}
