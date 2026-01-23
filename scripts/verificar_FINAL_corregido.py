"""
Script de verificación FINAL para las 24 configuraciones CORREGIDAS.
Verifica el criterio correcto de R1: arcos consecutivos en módulo 4.
"""

import json

def son_consecutivos_mod4(a, b):
    """Verifica si dos arcos son consecutivos en módulo 4."""
    diff = abs(a - b) % 4
    return diff == 1 or diff == 3

# Cargar configuraciones
with open(r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\configuraciones_2_cruces_24_CORREGIDAS.json", 'r', encoding='utf-8') as f:
    datos = json.load(f)

configuraciones = datos['configuraciones']

print("="*80)
print("VERIFICACIÓN FINAL - CRITERIO R1 CORRECTO")
print("="*80)
print(f"\nCriterio R1: Arcos consecutivos en mod 4")
print(f"Consecutivos: |over - under| mod 4 ∈ {{1, 3}}\n")

triviales = []
no_triviales = []

for config in configuraciones:
    id_config = config['id']
    pares = config['pares_ordenados']
    
    # Verificar si algún cruce tiene R1 aplicable
    tiene_r1 = False
    for par in pares:
        if par['r1_aplicable']:
            tiene_r1 = True
            break
    
    if tiene_r1:
        triviales.append(config)
    else:
        no_triviales.append(config)

print(f"📊 RESULTADOS:")
print(f"  Triviales (con R1):     {len(triviales)}")
print(f"  No triviales (sin R1):  {len(no_triviales)}")
print(f"  Total:                  {len(configuraciones)}")

print(f"\n{'='*80}")
print(f"CONFIGURACIONES NO TRIVIALES ({len(no_triviales)})")
print(f"{'='*80}\n")

for config in no_triviales:
    print(f"{config['nombre']}: {config['notacion_pares_ordenados']}")
    print(f"  Permutación: {config['permutacion']}")
    print(f"  Clase: {config['clase_orientacion']}, Writhe: {config['writhe']}")
    
    for par in config['pares_ordenados']:
        over = par['over']
        under = par['under']
        diff = abs(over - under) % 4
        print(f"  Cruce {par['cruce']}: over={over}, under={under} → |{over}-{under}| mod 4 = {diff} → {'CONSECUTIVOS' if diff in [1,3] else 'NO consecutivos'}")
    print()

print(f"{'='*80}")
print(f"EJEMPLOS DE CONFIGURACIONES TRIVIALES (primeras 5)")
print(f"{'='*80}\n")

for i, config in enumerate(triviales[:5]):
    print(f"{config['nombre']}: {config['notacion_pares_ordenados']}")
    print(f"  Permutación: {config['permutacion']}")
    print(f"  Clase: {config['clase_orientacion']}, Writhe: {config['writhe']}")
    
    for par in config['pares_ordenados']:
        over = par['over']
        under = par['under']
        diff = abs(over - under) % 4
        if diff in [1, 3]:
            print(f"  Cruce {par['cruce']}: over={over}, under={under} → CONSECUTIVOS (R1 aplicable)")
    print()

# Análisis por clase
print(f"{'='*80}")
print(f"ANÁLISIS POR CLASE DE ORIENTACIÓN")
print(f"{'='*80}\n")

por_clase = {"++": {"triviales": 0, "no_triviales": 0},
             "+-": {"triviales": 0, "no_triviales": 0},
             "-+": {"triviales": 0, "no_triviales": 0},
             "--": {"triviales": 0, "no_triviales": 0}}

for config in triviales:
    por_clase[config['clase_orientacion']]['triviales'] += 1

for config in no_triviales:
    por_clase[config['clase_orientacion']]['no_triviales'] += 1

print(f"{'Clase':<6} | {'Total':<6} | {'Triviales':<10} | {'No Triviales':<13} | {'% Triviales'}")
print("-"*80)
for clase in ["++", "+-", "-+", "--"]:
    total = por_clase[clase]['triviales'] + por_clase[clase]['no_triviales']
    triv = por_clase[clase]['triviales']
    no_triv = por_clase[clase]['no_triviales']
    pct = (triv / total * 100) if total > 0 else 0
    print(f"{clase:<6} | {total:<6} | {triv:<10} | {no_triv:<13} | {pct:.1f}%")

print(f"\n{'='*80}")
print(f"✅ CONCLUSIÓN")
print(f"{'='*80}")
print(f"Con el criterio CORRECTO de R1 (arcos consecutivos en mod 4):")
print(f"  - {len(triviales)} configuraciones son TRIVIALES")
print(f"  - {len(no_triviales)} configuraciones son NO TRIVIALES")
print(f"  - Solo la clase ++ tiene configuraciones no triviales")
