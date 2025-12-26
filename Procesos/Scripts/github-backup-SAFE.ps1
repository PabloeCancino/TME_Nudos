# ============================================================================
# Script de Backup SEGURO a GitHub para TME_Nudos
# ============================================================================
# Descripción: Realiza commits y push a GitHub respetando .gitignore
# Uso: .\github-backup-SAFE.ps1 [-Message "mensaje"] [-Force] [-Verbose] [-DryRun]
#
# IMPORTANTE: Este script sincroniza con GitHub usando el .gitignore local
# Solo sube archivos de código Lean y archivos esenciales del proyecto
# ============================================================================

param(
    [string]$Message = "",
    [switch]$Force,
    [switch]$Verbose,
    [switch]$DryRun,
    [switch]$SkipConfirmation
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

# Función para validar que estamos en el directorio correcto
function Test-RepositoryLocation {
    $currentPath = (Get-Location).Path
    $expectedPath = $RepoPath
    
    if ($currentPath -ne $expectedPath) {
        Write-Error "❌ ERROR CRÍTICO: Directorio incorrecto"
        Write-Error "   Actual: $currentPath"
        Write-Error "   Esperado: $expectedPath"
        return $false
    }
    
    # Verificar que .git está en el directorio correcto
    $gitDir = Join-Path $currentPath ".git"
    if (-not (Test-Path $gitDir)) {
        Write-Error "❌ ERROR CRÍTICO: No hay repositorio .git en $currentPath"
        return $false
    }
    
    # Verificar que .git es un directorio (no un archivo que apunta a otro lugar)
    if (-not (Test-Path $gitDir -PathType Container)) {
        Write-Error "❌ ERROR CRÍTICO: .git no es un directorio válido"
        return $false
    }
    
    return $true
}

# Inicio del script
Write-Info "═══════════════════════════════════════════════════════"
Write-Info "  GitHub Backup SEGURO - TME_Nudos"
Write-Info "  $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
if ($DryRun) {
    Write-Warning "  MODO DRY-RUN: No se harán cambios reales"
}
Write-Info "═══════════════════════════════════════════════════════"
Write-Log "Iniciando backup a GitHub $(if($DryRun){'(DRY-RUN)'})" "INFO"

try {
    # Cambiar al directorio del repositorio
    Set-Location $RepoPath
    Write-Info "📁 Directorio: $RepoPath"
    Write-Log "Cambiado a directorio: $RepoPath" "INFO"
    
    # VALIDACIÓN CRÍTICA: Verificar ubicación
    if (-not (Test-RepositoryLocation)) {
        Write-Error "❌ Abortando por seguridad"
        Write-Log "Abortado: ubicación de repositorio inválida" "ERROR"
        exit 1
    }
    Write-Success "✅ Validación de ubicación exitosa"
    
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
    
    # Verificar que el working directory de git es correcto
    $gitTopLevel = git rev-parse --show-toplevel 2>&1
    $gitTopLevelNormalized = $gitTopLevel -replace '/', '\'
    if ($gitTopLevelNormalized -ne $RepoPath) {
        Write-Error "❌ ERROR CRÍTICO: El repositorio Git apunta a un directorio diferente"
        Write-Error "   Git top-level: $gitTopLevelNormalized"
        Write-Error "   Esperado: $RepoPath"
        Write-Log "Error: Git top-level no coincide" "ERROR"
        exit 1
    }
    Write-Success "✅ Directorio de trabajo Git validado"
    
    # Verificar conexión con remoto
    Write-Info "`n🔗 Verificando conexión con GitHub..."
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
        Write-Info "`n📝 Archivos detectados por Git:"
        $statusLines = $status -split "`n" | Where-Object { $_ -ne "" }
        $added = @($statusLines | Where-Object { $_ -match "^\?\?" })
        $modified = @($statusLines | Where-Object { $_ -match "^ M" })
        $deleted = @($statusLines | Where-Object { $_ -match "^ D" })
        
        if ($added.Count -gt 0) {
            Write-Host "`n   ➕ Nuevos ($($added.Count)):" -ForegroundColor Green
            $added | Select-Object -First 10 | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Gray
            }
            if ($added.Count -gt 10) {
                Write-Host "      ... y $($added.Count - 10) más" -ForegroundColor Gray
            }
        }
        
        if ($modified.Count -gt 0) {
            Write-Host "`n   📝 Modificados ($($modified.Count)):" -ForegroundColor Yellow
            $modified | Select-Object -First 10 | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Gray
            }
            if ($modified.Count -gt 10) {
                Write-Host "      ... y $($modified.Count - 10) más" -ForegroundColor Gray
            }
        }
        
        if ($deleted.Count -gt 0) {
            Write-Host "`n   ❌ Eliminados ($($deleted.Count)):" -ForegroundColor Red
            $deleted | Select-Object -First 10 | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Gray
            }
            if ($deleted.Count -gt 10) {
                Write-Host "      ... y $($deleted.Count - 10) más" -ForegroundColor Gray
            }
        }
        
        $fileCount = $statusLines.Count
        Write-Log "Archivos a sincronizar: $fileCount" "INFO"
        
        # CONFIRMACIÓN DE SEGURIDAD
        if (-not $SkipConfirmation -and -not $DryRun) {
            Write-Warning "`n⚠️  ¿Deseas continuar con estos cambios?"
            $confirmation = Read-Host "Escribe 'SI' para continuar"
            if ($confirmation -ne "SI") {
                Write-Info "❌ Operación cancelada por el usuario"
                Write-Log "Cancelado por el usuario" "INFO"
                exit 0
            }
        }
    }
    
    if ($DryRun) {
        Write-Info "`n🔍 MODO DRY-RUN: Mostrando qué archivos se añadirían..."
        git add --dry-run -A
        Write-Info "`n✅ DRY-RUN completado. No se hicieron cambios."
        exit 0
    }
    
    # Añadir archivos (respetando .gitignore)
    Write-Info "`n➕ Añadiendo archivos al staging area..."
    # Usar -A para añadir, modificar y eliminar archivos
    # Esto es más explícito que "git add ."
    git add -A
    Write-Log "Ejecutado: git add -A" "INFO"
    
    # Verificar qué se añadió realmente
    $stagedFiles = git diff --cached --name-only
    if ([string]::IsNullOrWhiteSpace($stagedFiles)) {
        Write-Warning "⚠️  No hay archivos en staging después de 'git add'"
        Write-Log "No hay archivos staged" "WARN"
        exit 0
    }
    
    Write-Info "`n📋 Archivos en staging area:"
    $stagedFiles -split "`n" | Select-Object -First 10 | ForEach-Object {
        Write-Host "   $_" -ForegroundColor Gray
    }
    $stagedCount = ($stagedFiles -split "`n").Count
    if ($stagedCount -gt 10) {
        Write-Host "   ... y $($stagedCount - 10) más" -ForegroundColor Gray
    }
    
    # Crear mensaje de commit
    if ([string]::IsNullOrWhiteSpace($Message)) {
        $fecha = Get-Date -Format "yyyy-MM-dd HH:mm"
        $Message = "github-backup: $fecha"
    }
    
    # Hacer commit
    Write-Info "`n💾 Creando commit..."
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
        
        # Usar merge en lugar de rebase para ser más seguro
        $pullOutput = git pull --no-rebase origin master 2>&1
        
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
