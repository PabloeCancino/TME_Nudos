"""
Verificar que todas las configuraciones de una clase de equivalencia
se normalizan a la misma configuración canónica.
"""

from clasificador_ime import ClasificadorIME, ConfiguracionRacional
import json
from collections import defaultdict

# Cargar datos
with open('configuraciones_nudos_k3.json', 'r') as f:
    configuraciones = json.load(f)

clasificador = ClasificadorIME('configuraciones_nudos_k3.json')

print("=" * 70)
print("VERIFICACION DE NORMALIZACION - Clase del Trebol")
print("=" * 70)

# Clase del trébol: IME = [3, 3, 3]
ids_trebol = [1, 22, 26, 40, 81, 95, 99, 120, 123, 144]  # Primeros 10

print(f"\nAnalizando primeros 10 IDs de la Clase 1 (Trebol)...")
print(f"IME esperado: [3, 3, 3]")
print(f"Configuracion canonica esperada: [[1, 4], [2, 5], [3, 6]]")
print("\n" + "-" * 70)

configuraciones_normalizadas = defaultdict(list)

for config_dict in configuraciones[:200]:  # Analizar primeras 200
    config_id = config_dict.get("id")
    
    # Parsear configuración
    config_str = config_dict.get("configuracion_Racional", "[]")
    pares = json.loads(config_str.replace("'", '"'))
    
    # Normalizar
    config_obj = ConfiguracionRacional(pares, normalizar=True)
    config_normalizada = config_obj.pares
    ime = config_obj.calcular_ime()
    
    # Si es de la clase del trébol
    if ime == [3, 3, 3]:
        key = str(config_normalizada)
        configuraciones_normalizadas[key].append(config_id)
        
        if config_id in ids_trebol[:5]:  # Mostrar solo primeros 5
            print(f"\nID {config_id}:")
            print(f"  Original:    {pares}")
            print(f"  Normalizada: {config_normalizada}")
            print(f"  IME: {ime}")

print("\n" + "=" * 70)
print("RESUMEN DE CONFIGURACIONES NORMALIZADAS PARA IME=[3,3,3]")
print("=" * 70)

for config_norm, ids in configuraciones_normalizadas.items():
    print(f"\nConfiguracion normalizada: {config_norm}")
    print(f"  IDs que se normalizan a esta: {ids[:15]}" + (" ..." if len(ids) > 15 else ""))
    print(f"  Total: {len(ids)}")

if len(configuraciones_normalizadas) == 1:
    print("\n[OK] CORRECTO: Todas se normalizan a la MISMA configuracion")
else:
    print(f"\n[ATENCION] Hay {len(configuraciones_normalizadas)} configuraciones normalizadas diferentes!")
    print("Esto podria indicar que son nudos diferentes o que la normalizacion es incompleta")
