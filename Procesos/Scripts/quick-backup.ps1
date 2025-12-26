# ============================================================================
# Script de Backup Local (solo commits locales, sin push a GitHub)
# ============================================================================
# Uso: .\quick-backup.ps1
# Este script hace commits locales de TODOS tus archivos sin sincronizar
# con GitHub, protegiendo tu trabajo completo en tu PC.
# ============================================================================

$RepoPath = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\"

Set-Location $RepoPath

$fecha = Get-Date -Format "yyyy-MM-dd HH:mm"

Write-Host "� Backup local de todos los archivos..." -ForegroundColor Cyan

# Verificar si hay cambios
$status = git status --porcelain
if ([string]::IsNullOrWhiteSpace($status)) {
    Write-Host "✅ No hay cambios para respaldar" -ForegroundColor Green
    Write-Host "📊 Último backup: " -NoNewline
    git log -1 --format="%cd - %s" --date=format:"%Y-%m-%d %H:%M"
    exit 0
}

# Mostrar resumen de cambios
Write-Host "📝 Cambios detectados:" -ForegroundColor Yellow
$added = ($status | Select-String "^\?\?" | Measure-Object).Count
$modified = ($status | Select-String "^ M" | Measure-Object).Count
$deleted = ($status | Select-String "^ D" | Measure-Object).Count

if ($added -gt 0) { Write-Host "  + $added archivo(s) nuevo(s)" -ForegroundColor Green }
if ($modified -gt 0) { Write-Host "  ~ $modified archivo(s) modificado(s)" -ForegroundColor Yellow }
if ($deleted -gt 0) { Write-Host "  - $deleted archivo(s) eliminado(s)" -ForegroundColor Red }

# Hacer commit local (sin push)
git add .
git commit -m "backup local: $fecha"

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Backup local completado: $fecha" -ForegroundColor Green
    Write-Host "💡 Nota: Este backup es solo local (no se sincronizó con GitHub)" -ForegroundColor Cyan
    
    # Mostrar estadísticas del repositorio
    $totalCommits = (git rev-list --count HEAD)
    Write-Host "📊 Total de backups en historial: $totalCommits" -ForegroundColor Gray
}
else {
    Write-Host "❌ Error al crear backup local" -ForegroundColor Red
    exit 1
}
