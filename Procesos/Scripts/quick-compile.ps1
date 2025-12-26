# ============================================================================
# Quick Compile - TME_Nudos
# ============================================================================
# Descripción: Script rápido para hacer backup y compilar en GitHub
# Uso: .\quick-compile.ps1 [-Message "mensaje"] [-NoBrowser] [-Watch]
#
# Ejemplos:
#   .\quick-compile.ps1                          # Backup y abrir GitHub Actions
#   .\quick-compile.ps1 -Message "Fix teoremas"  # Con mensaje personalizado
#   .\quick-compile.ps1 -NoBrowser               # Sin abrir navegador
#   .\quick-compile.ps1 -Watch                   # Monitorear compilación
# ============================================================================

param(
    [string]$Message = "",
    [switch]$NoBrowser,
    [switch]$Watch,
    [switch]$Force
)

# Configuración
$RepoPath = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos"
$BackupScript = Join-Path $RepoPath "github-backup.ps1"
$GitHubActionsUrl = "https://github.com/PabloeCancino/TME_Nudos/actions"

# Colores
function Write-Success { Write-Host $args -ForegroundColor Green }
function Write-Info { Write-Host $args -ForegroundColor Cyan }
function Write-Warning { Write-Host $args -ForegroundColor Yellow }
function Write-Error { Write-Host $args -ForegroundColor Red }

# Banner
Write-Info "═══════════════════════════════════════════════════════"
Write-Info "  Quick Compile - TME_Nudos"
Write-Info "  $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Write-Info "═══════════════════════════════════════════════════════"

try {
    # Verificar que existe el script de backup
    if (-not (Test-Path $BackupScript)) {
        Write-Error "❌ Error: No se encontró github-backup.ps1"
        Write-Error "   Buscado en: $BackupScript"
        exit 1
    }

    # Paso 1: Ejecutar backup
    Write-Info "`n📤 PASO 1: Ejecutando backup a GitHub..."
    Write-Info "─────────────────────────────────────────────────────"
    
    $backupArgs = @{
        SkipConfirmation = $true
    }
    
    if ($Message) {
        $backupArgs.Message = $Message
    }
    
    if ($Force) {
        $backupArgs.Force = $true
    }
    
    # Ejecutar el script de backup
    & $BackupScript @backupArgs
    
    if ($LASTEXITCODE -ne 0) {
        Write-Error "`n❌ Error en el backup. Abortando."
        exit 1
    }
    
    Write-Success "`n✅ Backup completado exitosamente"
    
    # Paso 2: Obtener información del último commit
    Set-Location $RepoPath
    $commitHash = git rev-parse --short HEAD
    $commitMessage = git log -1 --pretty=%B
    
    Write-Info "`n📊 Información del commit:"
    Write-Info "   Hash: $commitHash"
    Write-Info "   Mensaje: $commitMessage"
    
    # Paso 3: Abrir GitHub Actions (opcional)
    if (-not $NoBrowser) {
        Write-Info "`n🌐 PASO 2: Abriendo GitHub Actions..."
        Write-Info "─────────────────────────────────────────────────────"
        Start-Process $GitHubActionsUrl
        Write-Success "✅ Navegador abierto en GitHub Actions"
    }
    
    # Paso 4: Monitorear compilación (opcional)
    if ($Watch) {
        Write-Info "`n👀 PASO 3: Monitoreando compilación..."
        Write-Info "─────────────────────────────────────────────────────"
        Write-Info "Esperando que GitHub Actions inicie la compilación..."
        Write-Info "(Presiona Ctrl+C para cancelar el monitoreo)"
        
        Start-Sleep -Seconds 5
        
        # Intentar obtener el estado de los workflows usando gh CLI si está disponible
        $ghInstalled = Get-Command gh -ErrorAction SilentlyContinue
        
        if ($ghInstalled) {
            Write-Info "`n📋 Estado de workflows:"
            
            for ($i = 0; $i -lt 10; $i++) {
                try {
                    $runs = gh run list --limit 3 --json status, conclusion, name, createdAt 2>$null | ConvertFrom-Json
                    
                    Clear-Host
                    Write-Info "═══════════════════════════════════════════════════════"
                    Write-Info "  Monitoreo de Compilación - Actualización #$($i + 1)"
                    Write-Info "  $(Get-Date -Format 'HH:mm:ss')"
                    Write-Info "═══════════════════════════════════════════════════════`n"
                    
                    foreach ($run in $runs) {
                        $statusIcon = switch ($run.status) {
                            "completed" { 
                                if ($run.conclusion -eq "success") { "✅" }
                                elseif ($run.conclusion -eq "failure") { "❌" }
                                else { "⚠️" }
                            }
                            "in_progress" { "🔄" }
                            "queued" { "⏳" }
                            default { "❓" }
                        }
                        
                        $color = switch ($run.conclusion) {
                            "success" { "Green" }
                            "failure" { "Red" }
                            default { "Yellow" }
                        }
                        
                        Write-Host "$statusIcon " -NoNewline
                        Write-Host "$($run.name) " -NoNewline -ForegroundColor $color
                        Write-Host "[$($run.status)]" -ForegroundColor Gray
                    }
                    
                    # Verificar si todas las compilaciones terminaron
                    $allCompleted = $runs | Where-Object { $_.status -eq "completed" }
                    if ($allCompleted.Count -eq $runs.Count) {
                        $allSuccess = $runs | Where-Object { $_.conclusion -eq "success" }
                        
                        Write-Info "`n═══════════════════════════════════════════════════════"
                        if ($allSuccess.Count -eq $runs.Count) {
                            Write-Success "✅ ¡Todas las compilaciones completadas exitosamente!"
                        }
                        else {
                            Write-Error "❌ Algunas compilaciones fallaron. Revisa GitHub Actions."
                        }
                        Write-Info "═══════════════════════════════════════════════════════"
                        break
                    }
                    
                    Write-Info "`nActualizando en 10 segundos... (Ctrl+C para cancelar)"
                    Start-Sleep -Seconds 10
                }
                catch {
                    Write-Warning "⚠️  Error al obtener estado de workflows: $_"
                    break
                }
            }
        }
        else {
            Write-Warning "⚠️  GitHub CLI (gh) no está instalado"
            Write-Info "   Para monitoreo automático, instala: winget install GitHub.cli"
            Write-Info "   Por ahora, revisa manualmente en: $GitHubActionsUrl"
        }
    }
    
    # Resumen final
    Write-Info "`n═══════════════════════════════════════════════════════"
    Write-Success "✅ Quick Compile completado"
    Write-Info "─────────────────────────────────────────────────────"
    Write-Info "📍 Siguiente paso:"
    Write-Info "   1. Ve a: $GitHubActionsUrl"
    Write-Info "   2. Verifica que la compilación sea exitosa"
    Write-Info "   3. Revisa los logs si hay errores"
    Write-Info "═══════════════════════════════════════════════════════"
    
}
catch {
    Write-Error "`n❌ Error inesperado: $_"
    Write-Error $_.ScriptStackTrace
    exit 1
}
