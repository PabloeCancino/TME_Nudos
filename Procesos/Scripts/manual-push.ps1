# manual-push.ps1
# Script para hacer push manual al repositorio TME_Nudos en GitHub
# Autor: Dr. Pablo Eduardo Cancino Marentes
# Fecha: 2025-12-25

Write-Host "🚀 Push Manual a GitHub - TME_Nudos" -ForegroundColor Cyan
Write-Host "=====================================" -ForegroundColor Cyan
Write-Host ""

# Verificar que estamos en el directorio correcto
$expectedPath = "TME_Nudos"
$currentPath = (Get-Location).Path
if ($currentPath -notlike "*$expectedPath*") {
    Write-Host "⚠️  ADVERTENCIA: No estás en el directorio TME_Nudos" -ForegroundColor Yellow
    Write-Host "   Directorio actual: $currentPath" -ForegroundColor Yellow
    $continue = Read-Host "¿Continuar de todas formas? (s/n)"
    if ($continue -ne "s") {
        Write-Host "❌ Operación cancelada" -ForegroundColor Red
        exit 1
    }
}

# Mostrar estado actual
Write-Host "📊 Estado actual del repositorio:" -ForegroundColor Green
git status --short
Write-Host ""

# Verificar si hay cambios
$changes = git status --porcelain
if ([string]::IsNullOrWhiteSpace($changes)) {
    Write-Host "✅ No hay cambios para hacer commit" -ForegroundColor Green
    Write-Host "   El repositorio está actualizado" -ForegroundColor Gray
    exit 0
}

# Mostrar archivos modificados
Write-Host "📝 Archivos modificados:" -ForegroundColor Yellow
git status --short
Write-Host ""

# Preguntar si desea continuar
$confirm = Read-Host "¿Deseas hacer commit y push de estos cambios? (s/n)"
if ($confirm -ne "s") {
    Write-Host "❌ Operación cancelada por el usuario" -ForegroundColor Red
    exit 1
}

# Solicitar mensaje de commit
Write-Host ""
Write-Host "💬 Ingresa el mensaje del commit:" -ForegroundColor Cyan
Write-Host "   (Presiona Enter para usar mensaje por defecto)" -ForegroundColor Gray
$commitMessage = Read-Host "Mensaje"

if ([string]::IsNullOrWhiteSpace($commitMessage)) {
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm"
    $commitMessage = "update: cambios manuales $timestamp"
    Write-Host "   Usando mensaje por defecto: $commitMessage" -ForegroundColor Gray
}

Write-Host ""
Write-Host "🔄 Ejecutando comandos Git..." -ForegroundColor Cyan

# Paso 1: Add
Write-Host "1️⃣  git add -A" -ForegroundColor Yellow
git add -A
if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ Error en git add" -ForegroundColor Red
    exit 1
}
Write-Host "   ✅ Archivos agregados al staging area" -ForegroundColor Green

# Paso 2: Commit
Write-Host "2️⃣  git commit -m `"$commitMessage`"" -ForegroundColor Yellow
git commit -m "$commitMessage"
if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ Error en git commit" -ForegroundColor Red
    exit 1
}
Write-Host "   ✅ Commit creado exitosamente" -ForegroundColor Green

# Paso 3: Pull (para evitar conflictos)
Write-Host "3️⃣  git pull --rebase origin master" -ForegroundColor Yellow
git pull --rebase origin master
if ($LASTEXITCODE -ne 0) {
    Write-Host "⚠️  Conflictos detectados durante el pull" -ForegroundColor Yellow
    Write-Host "   Resuelve los conflictos manualmente y ejecuta:" -ForegroundColor Yellow
    Write-Host "   git rebase --continue" -ForegroundColor Cyan
    Write-Host "   Luego ejecuta este script nuevamente" -ForegroundColor Cyan
    exit 1
}
Write-Host "   ✅ Repositorio actualizado desde GitHub" -ForegroundColor Green

# Paso 4: Push
Write-Host "4️⃣  git push origin master" -ForegroundColor Yellow
git push origin master
if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ Error en git push" -ForegroundColor Red
    Write-Host "   Posibles causas:" -ForegroundColor Yellow
    Write-Host "   - Problemas de conexión" -ForegroundColor Gray
    Write-Host "   - Permisos insuficientes" -ForegroundColor Gray
    Write-Host "   - Cambios en el repositorio remoto" -ForegroundColor Gray
    exit 1
}
Write-Host "   ✅ Cambios pusheados a GitHub exitosamente" -ForegroundColor Green

Write-Host ""
Write-Host "=====================================" -ForegroundColor Cyan
Write-Host "✅ Push completado exitosamente" -ForegroundColor Green
Write-Host "=====================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "📍 Repositorio: https://github.com/PabloeCancino/TME_Nudos" -ForegroundColor Cyan
Write-Host "🕐 Timestamp: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')" -ForegroundColor Gray
Write-Host ""

# Mostrar último commit
Write-Host "📌 Último commit:" -ForegroundColor Cyan
git log -1 --oneline
Write-Host ""
