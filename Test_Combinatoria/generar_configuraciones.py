import json
from itertools import permutations
from pathlib import Path
from datetime import datetime

def generar_configuraciones_nudos(n_valores=[3]):
    """
    Genera todas las configuraciones posibles de nudos para los valores de n especificados.
    
    Args:
        n_valores: Lista de valores de n para generar
    
    Returns:
        Lista de configuraciones en formato JSON plano
    """
    configuraciones = []
    id_global = 1
    
    for n in n_valores:
        print(f"Generando configuraciones para n={n} (2n={2*n} elementos)...")
        
        elementos = list(range(1, 2*n + 1))
        num_caso = 1
        
        # Generar todas las permutaciones
        for perm in permutations(elementos):
            fila_superior = list(perm[:n])
            fila_inferior = list(perm[n:])
            pares_ordenados = [[fila_superior[j], fila_inferior[j]] for j in range(n)]
            
            configuraciones.append({
                "id": id_global,
                "num_cruces": n,
                "num_caso": num_caso,
                "configuracion_Racional": str(pares_ordenados).replace(" ", "")
            })
            
            id_global += 1
            num_caso += 1
        
        total_configs = num_caso - 1
        print(f"  [OK] Generadas {total_configs:,} configuraciones")
    
    return configuraciones

def guardar_json(datos, nombre_archivo="configuraciones_nudos.json"):
    """Guarda las configuraciones en formato JSON."""
    ruta = Path(nombre_archivo)
    
    with open(ruta, 'w', encoding='utf-8') as f:
        json.dump(datos, f, indent=4, ensure_ascii=False)
    
    tamano_kb = ruta.stat().st_size / 1024
    print(f"\n[OK] Archivo guardado: {ruta.absolute()}")
    print(f"  Tamaño: {tamano_kb:.2f} KB")
    
    return ruta

def mostrar_ejemplos(datos, num_ejemplos=10):
    """Muestra ejemplos de configuraciones."""
    print(f"\n{'='*70}")
    print(f"EJEMPLOS DE CONFIGURACIONES (primeras {num_ejemplos})")
    print('='*70)
    
    for config in datos[:num_ejemplos]:
        print(f"\n  ID: {config['id']}")
        print(f"  Num. Cruces: {config['num_cruces']}")
        print(f"  Num. Caso: {config['num_caso']}")
        print(f"  configuracion_Racional: \"{config['configuracion_Racional']}\"")

def generar_resumen(datos):
    """Genera un resumen de las configuraciones."""
    print(f"\n{'='*70}")
    print("RESUMEN DE CONFIGURACIONES GENERADAS")
    print('='*70)
    
    # Contar por número de cruces
    por_cruces = {}
    for config in datos:
        n = config['num_cruces']
        if n not in por_cruces:
            por_cruces[n] = 0
        por_cruces[n] += 1
    
    total_general = 0
    for n in sorted(por_cruces.keys()):
        total = por_cruces[n]
        total_general += total
        factorial = 1
        for k in range(1, 2*n + 1):
            factorial *= k
        print(f"n={n}: {total:>8,} configuraciones (= {2*n}! = {factorial:,})")
    
    print(f"\n{'Total general:':<15} {total_general:>8,} configuraciones")
    print('='*70)

# ============================================
# EJECUCIÓN PRINCIPAL
# ============================================

if __name__ == "__main__":
    print("="*70)
    print("GENERADOR DE CONFIGURACIONES DE NUDOS - TME_Nudos")
    print("="*70)
    print()
    
    # Generar para n=1, 2, 3
    datos = generar_configuraciones_nudos()
    
    # Guardar en JSON
    archivo = guardar_json(datos)
    
    # Mostrar ejemplos
    mostrar_ejemplos(datos, num_ejemplos=10)
    
    # Resumen final
    generar_resumen(datos)
    
    print(f"\n[OK] Proceso completado exitosamente")
    print(f"[OK] Total de configuraciones generadas: {len(datos):,}")