"""
Script para actualizar el artículo de Fundamentos Axiomáticos
de notación racional a Teoría Modular Estructural de Nudos (TMEN)

Cambios aplicados:
1. Notación fraccionaria → pares ordenados
2. Indexación 1..2n → 0..(2n-1)
3. Terminología "racional" → "modular" o "TMEN"
4. Añadir referencias a Lean donde corresponda
"""

import re
from pathlib import Path

def actualizar_articulo(ruta_entrada, ruta_salida):
    """Aplica todas las actualizaciones sistemáticas al artículo"""
    
    with open(ruta_entrada, 'r', encoding='utf-8') as f:
        contenido = f.read()
    
    print("📝 Aplicando actualizaciones...")
    
    # 1. CAMBIOS EN NOTACIÓN MATEMÁTICA
    # Reemplazar frac{o_i}{u_i} → (o_i, u_i)
    contenido = re.sub(r'\\frac\{o_i\}\{u_i\}', r'(o_i, u_i)', contenido)
    contenido = re.sub(r'\\frac\{o_(\d+)\}\{u_(\d+)\}', r'(o_\1, u_\1)', contenido)
    contenido = re.sub(r'\\frac\{o_([a-z])\}\{u_([a-z])\}', r'(o_\1, u_\1)', contenido)
    contenido = re.sub(r'\\frac\{u_i\}\{o_i\}', r'(u_i, o_i)', contenido)
    contenido = re.sub(r'\\frac\{u_(\d+)\}\{o_(\d+)\}', r'(u_\1, o_\1)', contenido)
    
    # 2. INDEXACIÓN: {1, 2, ..., 2n} → {0, 1, ..., 2n-1}
    contenido = re.sub(r'\{1,\s*2,\s*\\ldots,\s*2n\}', r'{0, 1, \\ldots, 2n-1}', contenido)
    contenido = re.sub(r'\{1,2,\\dots,2n\}', r'{0, 1, \\ldots, 2n-1}', contenido)
    contenido = re.sub(r'\\mathcal\{R\}_\{2n\}\s*=\s*\{1,\s*2,\s*\\dots,\s*2n\}',
                      r'\\mathbb{Z}_{2n} = \\{0, 1, \\ldots, 2n-1\\}', contenido)
    
    # 3. TERMINOLOGÍA
    # Cambiar "configuración racional" → "configuración modular" (selectivo)
    contenido = re.sub(r'configuración racional de nudos', 
                      r'configuración modular', contenido)
    contenido = re.sub(r'configuraciones racionales',
                      r'configuraciones modulares', contenido, count=10)  # Primeras apariciones
    
    # Cambiar mathcal{C}_{rat} → mathcal{C}
    contenido = re.sub(r'\\mathcal\{C\}_\{\\mathrm\{rat\}\}', r'\\mathcal{C}', contenido)
    
    # Cambiar "cruce racional" → "par ordenado de cruce"
    contenido = re.sub(r'cruce racional',  r'par ordenado de cruce', contenido)
    
    # 4. SÍMBOLOS ESTRUCTURALES
    # Actualizar mathcal{R}_{2n} → mathbb{Z}_{2n}
    contenido = re.sub(r'\\mathcal\{R\}_\{2n\}', r'\\mathbb{Z}_{2n}', contenido)
    
    # 5. CASOS ESPECÍFICOS DE NOTACIÓN
    # Actualizar definiciones que usan la notación vieja
    contenido = re.sub(
        r'K\s*=\s*\\left\\{.*?\\right\\}',
        lambda m: m.group(0).replace('\\frac{', '(').replace('}{', ', ').replace('}', ')'),
        contenido,
        flags=re.DOTALL
    )
    
    # 6. GUARDAR
    with open(ruta_salida, 'w', encoding='utf-8') as f:
        f.write(contenido)
    
    print(f"✅ Artículo actualizado guardado en: {ruta_salida}")
    print(f"📊 Tamaño: {len(contenido)} caracteres")
    
    return contenido

if __name__ == "__main__":
    ruta_original = r"C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Articulo_K_3\Fundamentos Axiomáticos de la Teoría Racional de Nudos. ver.final2.md"
    ruta_nueva = r"C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Articulo_K_3\Fundamentos_TMEN_v3.0.md"
    
    actualizar_articulo(ruta_original, ruta_nueva)
    print("\n🎉 Actualización completada!")
