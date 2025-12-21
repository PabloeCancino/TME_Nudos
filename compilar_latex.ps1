# Script de compilación LaTeX optimizado para Fundamentos_TMEN_v3.0.tex
# Uso: .\compilar_latex.ps1

Write-Host "=== Compilación LaTeX con XeLaTeX ===" -ForegroundColor Cyan
Write-Host ""

# Cambiar al directorio del documento
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$docDir = Join-Path $scriptDir "Articulo_K_3"
Set-Location $docDir
Write-Host "Directorio de trabajo: $docDir" -ForegroundColor Gray
Write-Host ""

# Limpiar archivos auxiliares previos
Write-Host "[1/4] Limpiando archivos auxiliares..." -ForegroundColor Yellow
Remove-Item *.aux, *.toc, *.log, *.out -ErrorAction SilentlyContinue

# Primera pasada (genera .aux y .toc)
Write-Host "[2/4] Primera pasada de XeLaTeX..." -ForegroundColor Yellow
xelatex -interaction=nonstopmode "Fundamentos_TMEN_v3.0.tex" | Out-Null

# Segunda pasada (resuelve referencias cruzadas)
Write-Host "[3/4] Segunda pasada de XeLaTeX (referencias cruzadas)..." -ForegroundColor Yellow
xelatex -interaction=nonstopmode "Fundamentos_TMEN_v3.0.tex" | Out-Null

# Verificar resultado
Write-Host "[4/4] Verificando PDF generado..." -ForegroundColor Yellow
if (Test-Path "Fundamentos_TMEN_v3.0.pdf") {
    $pdf = Get-Item "Fundamentos_TMEN_v3.0.pdf"
    Write-Host ""
    Write-Host "✅ PDF generado exitosamente:" -ForegroundColor Green
    Write-Host "   Archivo: $($pdf.Name)" -ForegroundColor White
    Write-Host "   Tamaño:  $([math]::Round($pdf.Length/1KB, 2)) KB" -ForegroundColor White
    Write-Host "   Fecha:   $($pdf.LastWriteTime)" -ForegroundColor White
    
    # Contar páginas (aproximado por tamaño)
    $approxPages = [math]::Round($pdf.Length / 4000)
    Write-Host "   Páginas: ~$approxPages (estimado)" -ForegroundColor White
    
    Write-Host ""
    Write-Host "Para abrir el PDF:" -ForegroundColor Cyan
    Write-Host "   Invoke-Item 'Fundamentos_TMEN_v3.0.pdf'" -ForegroundColor Gray
}
else {
    Write-Host ""
    Write-Host "❌ Error: No se generó el PDF" -ForegroundColor Red
    Write-Host "   Revisa el archivo .log para detalles:" -ForegroundColor Yellow
    Write-Host "   Get-Content 'Fundamentos_TMEN_v3.0.log' -Tail 50" -ForegroundColor Gray
}

Write-Host ""
Write-Host "=== Compilación finalizada ===" -ForegroundColor Cyan

# Regresar al directorio raíz
Set-Location $scriptDir
