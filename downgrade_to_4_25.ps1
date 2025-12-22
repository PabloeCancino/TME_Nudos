# downgrade_to_4_25.ps1
# Script para regresar a Lean 4.25.0

Write-Host "=== Downgrade a Lean 4.25.0 ===" -ForegroundColor Cyan

# 1. Backup
Write-Host "`n[1/5] Creando backups..." -ForegroundColor Yellow
Copy-Item lean-toolchain lean-toolchain.backup -Force
Write-Host "✓ Backup creado" -ForegroundColor Green

# 2. Cambiar versión
Write-Host "`n[2/5] Actualizando lean-toolchain..." -ForegroundColor Yellow
"leanprover/lean4:v4.25.0" | Out-File -FilePath lean-toolchain -Encoding UTF8 -NoNewline
Write-Host "✓ Toolchain actualizado a 4.25.0" -ForegroundColor Green

# 3. Actualizar dependencias
Write-Host "`n[3/5] Actualizando dependencias..." -ForegroundColor Yellow
lake update

# 4. Limpiar build anterior
Write-Host "`n[4/5] Limpiando build anterior..." -ForegroundColor Yellow
lake clean
Write-Host "✓ Build limpiado" -ForegroundColor Green

# 5. Compilar
Write-Host "`n[5/5] Compilando proyecto..." -ForegroundColor Yellow
lake build

Write-Host "`n=== Proceso completado ===" -ForegroundColor Cyan
Write-Host "Verificar con: lake env lean --version" -ForegroundColor Gray