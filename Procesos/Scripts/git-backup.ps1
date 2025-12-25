# ============================================================================
# Script de Backup Automático Git para TME_Nudos
# ============================================================================
# Descripción: Realiza commits y push automáticos al repositorio de GitHub
# Uso: .\git-backup.ps1 [-Message "mensaje"] [-Force] [-Verbose]
# ============================================================================

param(
    [string]$Message = "",
    [switch]$Force,
    [switch]$Verbose
)

# Configuración
$RepoPath = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos"
$LogFile = Join-Path $RepoPath "backup.log"
$MaxLogSize = 5MB

# Colores para output
function Write-Success { Write-Host $args -ForegroundColor Green }
function Write-Info { Write-Host $args -ForegroundColor Cyan }
function Write-Warning { Write-Host $args -ForegroundColor Yellow }
function Write-Error { Write-Host $args -ForegroundColor Red }

# Función de logging
function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    
    # Rotar log si es muy grande
    if (Test-Path $LogFile) {
        if ((Get-Item $LogFile).Length -gt $MaxLogSize) {
            Move-Item $LogFile "$LogFile.old" -Force
        }
    }
    
    Add-Content -Path $LogFile -Value $logMessage
    
    if ($Verbose) {
        Write-Host $logMessage
    }
}

# Inicio del script
Write-Info "═══════════════════════════════════════════════════════"
Write-Info "  Git Backup Automático - TME_Nudos"
Write-Info "  $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Write-Info "═══════════════════════════════════════════════════════"
Write-Log "Iniciando backup automático" "INFO"

try {
    # Cambiar al directorio del repositorio
    Set-Location $RepoPath
    Write-Info "📁 Directorio: $RepoPath"
    Write-Log "Cambiado a directorio: $RepoPath" "INFO"
    
    # Verificar que estamos en un repositorio git
    if (-not (Test-Path ".git")) {
        Write-Error "❌ Error: No hay repositorio git en este directorio"
        Write-Log "Error: No es un repositorio git" "ERROR"
        exit 1
    }
    
    # Obtener estado actual
    Write-Info "🔍 Verificando cambios..."
    $status = git status --porcelain
    
    if ([string]::IsNullOrWhiteSpace($status) -and -not $Force) {
        Write-Success "✅ No hay cambios para commitear"
        Write-Log "No hay cambios pendientes" "INFO"
        exit 0
    }
    
    # Mostrar archivos modificados
    if (-not [string]::IsNullOrWhiteSpace($status)) {
        Write-Info "`n📝 Archivos modificados:"
        $status -split "`n" | ForEach-Object {
            Write-Host "   $_" -ForegroundColor Yellow
        }
        $fileCount = ($status -split "`n").Count
        Write-Log "Archivos modificados: $fileCount" "INFO"
    }
    
    # Añadir todos los archivos
    Write-Info "`n➕ Añadiendo archivos..."
    git add .
    Write-Log "Ejecutado: git add ." "INFO"
    
    # Crear mensaje de commit
    if ([string]::IsNullOrWhiteSpace($Message)) {
        $fecha = Get-Date -Format "yyyy-MM-dd HH:mm"
        $Message = "auto-backup: $fecha"
    }
    
    # Hacer commit
    Write-Info "💾 Creando commit..."
    $commitOutput = git commit -m $Message 2>&1
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "✅ Commit creado: $Message"
        Write-Log "Commit exitoso: $Message" "INFO"
        
        # Mostrar resumen del commit
        $commitHash = git rev-parse --short HEAD
        Write-Info "   Hash: $commitHash"
    }
    elseif ($commitOutput -match "nothing to commit") {
        Write-Warning "⚠️  No hay cambios para commitear"
        Write-Log "No hay cambios para commit" "WARN"
        
        if (-not $Force) {
            exit 0
        }
    }
    else {
        Write-Error "❌ Error en commit: $commitOutput"
        Write-Log "Error en commit: $commitOutput" "ERROR"
        exit 1
    }
    
    # Push a GitHub
    Write-Info "`n🚀 Haciendo push a GitHub..."
    $pushOutput = git push origin master 2>&1
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "✅ Push exitoso a origin/master"
        Write-Log "Push exitoso a GitHub" "INFO"
    }
    else {
        Write-Error "❌ Error en push: $pushOutput"
        Write-Log "Error en push: $pushOutput" "ERROR"
        
        # Intentar pull primero si hay conflictos
        if ($pushOutput -match "rejected") {
            Write-Warning "⚠️  Cambios remotos detectados. Intentando pull..."
            Write-Log "Intentando pull por rechazo de push" "WARN"
            
            $pullOutput = git pull --rebase origin master 2>&1
            
            if ($LASTEXITCODE -eq 0) {
                Write-Info "🔄 Pull exitoso, reintentando push..."
                $retryPush = git push origin master 2>&1
                
                if ($LASTEXITCODE -eq 0) {
                    Write-Success "✅ Push exitoso después de pull"
                    Write-Log "Push exitoso después de pull" "INFO"
                }
                else {
                    Write-Error "❌ Error en segundo intento de push"
                    Write-Log "Error en segundo push: $retryPush" "ERROR"
                    exit 1
                }
            }
            else {
                Write-Error "❌ Error en pull: $pullOutput"
                Write-Log "Error en pull: $pullOutput" "ERROR"
                Write-Warning "Resuelve los conflictos manualmente"
                exit 1
            }
        }
        else {
            exit 1
        }
    }
    
    # Resumen final
    Write-Info "`n═══════════════════════════════════════════════════════"
    Write-Success "✅ Backup completado exitosamente"
    Write-Info "   Fecha: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
    Write-Info "   Rama: master"
    Write-Info "   Remote: origin/master"
    Write-Info "═══════════════════════════════════════════════════════"
    Write-Log "Backup completado exitosamente" "INFO"
    
    # Mostrar últimos commits
    Write-Info "`n📜 Últimos 3 commits:"
    git log --oneline -3 | ForEach-Object {
        Write-Host "   $_" -ForegroundColor Gray
    }
    
}
catch {
    Write-Error "❌ Error inesperado: $_"
    Write-Log "Error inesperado: $_" "ERROR"
    exit 1
}
