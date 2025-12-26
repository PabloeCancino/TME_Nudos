# ============================================================================
# Script de Backup a GitHub para TME_Nudos
# ============================================================================
# Descripción: Realiza commits y push a GitHub respetando .gitignore
# Uso: .\github-backup.ps1 [-Message "mensaje"] [-Force] [-Verbose]
#
# IMPORTANTE: Este script sincroniza con GitHub usando el .gitignore local
# Solo sube archivos de código Lean y archivos esenciales del proyecto
# ============================================================================

param(
    [string]$Message = "",
    [switch]$Force,
    [switch]$Verbose
)

# Configuración
$RepoPath = "C:\Users\pablo\OneDrive\Documentos\TME_Nudos"
$LogFile = Join-Path $RepoPath "Procesos\Logs\github-backup.log"
$MaxLogSize = 5MB
$GitIgnorePath = Join-Path $RepoPath ".gitignore"

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
    
    # Crear directorio de logs si no existe
    $logDir = Split-Path $LogFile -Parent
    if (-not (Test-Path $logDir)) {
        New-Item -ItemType Directory -Path $logDir -Force | Out-Null
    }
    
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
Write-Info "  GitHub Backup - TME_Nudos"
Write-Info "  $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Write-Info "═══════════════════════════════════════════════════════"
Write-Log "Iniciando backup a GitHub" "INFO"

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
    
    # Verificar que existe .gitignore
    if (-not (Test-Path $GitIgnorePath)) {
        Write-Warning "⚠️  Advertencia: No se encontró .gitignore"
        Write-Log "Advertencia: .gitignore no encontrado" "WARN"
    }
    else {
        Write-Info "✅ Usando .gitignore: $GitIgnorePath"
        Write-Log "Usando .gitignore local" "INFO"
    }
    
    # Verificar conexión con remoto
    Write-Info "🔗 Verificando conexión con GitHub..."
    $remoteUrl = git remote get-url origin 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Info "   Remote: $remoteUrl"
        Write-Log "Remote URL: $remoteUrl" "INFO"
    }
    else {
        Write-Error "❌ Error: No se pudo obtener URL del remoto"
        Write-Log "Error: No hay remote configurado" "ERROR"
        exit 1
    }
    
    # Obtener estado actual (respetando .gitignore)
    Write-Info "`n🔍 Verificando cambios (respetando .gitignore)..."
    $status = git status --porcelain
    
    if ([string]::IsNullOrWhiteSpace($status) -and -not $Force) {
        Write-Success "✅ No hay cambios para sincronizar con GitHub"
        Write-Log "No hay cambios pendientes" "INFO"
        
        # Mostrar último commit
        Write-Info "`n📊 Último commit en GitHub:"
        git log origin/master --oneline -1 2>&1 | ForEach-Object {
            Write-Host "   $_" -ForegroundColor Gray
        }
        exit 0
    }
    
    # Mostrar archivos que se van a subir
    if (-not [string]::IsNullOrWhiteSpace($status)) {
        Write-Info "`n📝 Archivos a sincronizar con GitHub:"
        $statusLines = $status -split "`n"
        $added = @($statusLines | Where-Object { $_ -match "^\?\?" })
        $modified = @($statusLines | Where-Object { $_ -match "^ M" })
        $deleted = @($statusLines | Where-Object { $_ -match "^ D" })
        
        if ($added.Count -gt 0) {
            Write-Host "`n   ➕ Nuevos ($($added.Count)):" -ForegroundColor Green
            $added | Select-Object -First 5 | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Gray
            }
            if ($added.Count -gt 5) {
                Write-Host "      ... y $($added.Count - 5) más" -ForegroundColor Gray
            }
        }
        
        if ($modified.Count -gt 0) {
            Write-Host "`n   📝 Modificados ($($modified.Count)):" -ForegroundColor Yellow
            $modified | Select-Object -First 5 | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Gray
            }
            if ($modified.Count -gt 5) {
                Write-Host "      ... y $($modified.Count - 5) más" -ForegroundColor Gray
            }
        }
        
        if ($deleted.Count -gt 0) {
            Write-Host "`n   ❌ Eliminados ($($deleted.Count)):" -ForegroundColor Red
            $deleted | Select-Object -First 5 | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Gray
            }
            if ($deleted.Count -gt 5) {
                Write-Host "      ... y $($deleted.Count - 5) más" -ForegroundColor Gray
            }
        }
        
        $fileCount = $statusLines.Count
        Write-Log "Archivos a sincronizar: $fileCount" "INFO"
    }
    
    # Añadir archivos (respetando .gitignore)
    Write-Info "`n➕ Añadiendo archivos (respetando .gitignore)..."
    git add .
    Write-Log "Ejecutado: git add ." "INFO"
    
    # Crear mensaje de commit
    if ([string]::IsNullOrWhiteSpace($Message)) {
        $fecha = Get-Date -Format "yyyy-MM-dd HH:mm"
        $Message = "github-backup: $fecha"
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
    
    # Sincronizar con GitHub
    Write-Info "`n🔄 Sincronizando con GitHub..."
    Write-Info "   1. Obteniendo cambios remotos..."
    
    # Primero hacer fetch para ver si hay cambios remotos
    git fetch origin master 2>&1 | Out-Null
    
    # Verificar si estamos detrás del remoto
    $localCommit = git rev-parse HEAD
    $remoteCommit = git rev-parse origin/master 2>&1
    
    if ($localCommit -ne $remoteCommit) {
        Write-Warning "⚠️  Hay cambios en GitHub que no tienes localmente"
        Write-Info "   2. Integrando cambios remotos..."
        
        $pullOutput = git pull --rebase origin master 2>&1
        
        if ($LASTEXITCODE -ne 0) {
            Write-Error "❌ Error al integrar cambios remotos"
            Write-Error "   $pullOutput"
            Write-Log "Error en pull: $pullOutput" "ERROR"
            Write-Warning "`n⚠️  Resuelve los conflictos manualmente y vuelve a ejecutar el script"
            exit 1
        }
        
        Write-Success "   ✅ Cambios remotos integrados"
        Write-Log "Pull exitoso" "INFO"
    }
    
    # Push a GitHub
    Write-Info "   3. Subiendo cambios a GitHub..."
    $pushOutput = git push origin master 2>&1
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "`n✅ Sincronización exitosa con GitHub"
        Write-Log "Push exitoso a GitHub" "INFO"
    }
    else {
        Write-Error "❌ Error al subir a GitHub: $pushOutput"
        Write-Log "Error en push: $pushOutput" "ERROR"
        exit 1
    }
    
    # Resumen final
    Write-Info "`n═══════════════════════════════════════════════════════"
    Write-Success "✅ Backup a GitHub completado exitosamente"
    Write-Info "   Fecha: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
    Write-Info "   Rama: master"
    Write-Info "   Remote: origin/master"
    Write-Info "═══════════════════════════════════════════════════════"
    Write-Log "Backup a GitHub completado exitosamente" "INFO"
    
    # Mostrar últimos commits
    Write-Info "`n📜 Últimos 3 commits en GitHub:"
    git log origin/master --oneline -3 | ForEach-Object {
        Write-Host "   $_" -ForegroundColor Gray
    }
    
}
catch {
    Write-Error "❌ Error inesperado: $_"
    Write-Log "Error inesperado: $_" "ERROR"
    exit 1
}
