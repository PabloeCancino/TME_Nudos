"""
Buscar la configuración canónica [[1,4],[5,2],[3,6]] en el JSON
"""

import json

with open('configuraciones_nudos_k3.json', 'r') as f:
    configuraciones = json.load(f)

# Buscar la configuración canónica
config_canonica = [[1,4],[5,2],[3,6]]
config_str_canonica = str(config_canonica).replace(" ", "")

print("Buscando la configuracion canonica del trebol:")
print(f"  {config_canonica}")
print()

encontrado = False
for cfg in configuraciones:
    config_str = cfg.get("configuracion_Racional", "")
    if config_str == config_str_canonica:
        print(f"[OK] ENCONTRADA!")
        print(f"  ID: {cfg['id']}")
        print(f"  Configuracion: {config_str}")
        encontrado = True
        break

if not encontrado:
    print("[X] No encontrada en el JSON!")
    print()
    print("Buscando configuraciones similares con IME [3,3,3]...")
    
    from clasificador_ime import ConfiguracionRacional
    
    for cfg in configuraciones[:50]:
        config_str = cfg.get("configuracion_Racional", "[]")
        pares = json.loads(config_str.replace("'", '"'))
        
        try:
            obj = ConfiguracionRacional(pares, normalizar=False)
            if obj.calcular_ime() == [3, 3, 3]:
                print(f"  ID {cfg['id']}: {pares}")
        except:
            pass
