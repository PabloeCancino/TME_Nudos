"""
Script para corregir errores comunes de LaTeX en archivo generado por pandoc
"""

import re

def fix_latex_math_errors(filename):
    with open(filename, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    fixes = 0
    
    # Fix 1: Paréntesis alrededor de comandos matemáticos LaTeX
    # (K') → $K'$ o $(K')$ → $(K')$ en modo matemático
    # Buscar patrones como (\deg(K')) que deberían ser $\deg(K')$
    
    patterns = [
        # Paréntesis con comandos LaTeX que necesitan modo matemático
        (r'\(\\deg\(([^)]+)\)([^$]*?)\)', r'$\\deg(\1)\2$'),
        (r'\(\\text\{([^}]+)\}\)', r'$\\text{\1}$'),
        
        # Casos específicos del documento
        (r'configuración \(K\'\) con \(\\deg', r'configuración $K\'$ con $\\deg'),
        (r'preservan \(\\deg\(K\)\)', r'preservan $\\deg(K)$'),
        (r'\(\\deg\(K\'\) \\textless\{\} \\deg\(K\)\)', r'$\\deg(K\') < \\deg(K)$'),
        
        # Símbolos matemáticos mal formateados
        (r'\\textless\{\}', r'<'),
        (r'\\textgreater\{\}', r'>'),
    ]
    
    for pattern, replacement in patterns:
        new_content = re.sub(pattern, replacement, content)
        if new_content != content:
            fixes += len(re.findall(pattern, content))
            content = new_content
    
    # Fix 2: Problemas con itemize y comandos matemáticos
    # Buscar items con fórmulas mal formateadas
    content = re.sub(
        r'configuración \(K\'\) con \(\\\\deg\(K\'\) \\\\textless\{\} \\\\deg\(K\)\)',
        r'configuración $K\'$ con $\\deg(K\') < \\deg(K)$',
        content
    )
    
    content = re.sub(
        r'preservan \(\\\\deg\(K\)\)',
        r'preservan $\\deg(K)$',
        content
    )
    
    if content != original_content:
        # Hacer backup
        with open(filename + '.backup', 'w', encoding='utf-8') as f:
            f.write(original_content)
        
        # Guardar correcciones
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"✅ Archivo corregido:")
        print(f"   - {fixes} patrones corregidos")
        print(f"   - Backup guardado en {filename}.backup")
        return True
    else:
        print("⚠️ No se encontraron patrones para corregir")
        return False

if __name__ == "__main__":
    filename = r"C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Articulo_K_3\Fundamentos_TMEN_v3.0.tex"
    fix_latex_math_errors(filename)
