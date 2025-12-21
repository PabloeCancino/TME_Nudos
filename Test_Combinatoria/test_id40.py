"""
Verificar normalización del ID 40
"""

from clasificador_ime import ConfiguracionRacional

# ID 40 del JSON
config_id_40 = [[1,4],[3,6],[5,2]]

print("ID 40 - Test de normalizacion")
print("=" * 60)
print(f"Configuracion original: {config_id_40}")
print()

# Analizar elemento mínimo de cada par
print("Elementos minimos:")
for i, par in enumerate(config_id_40):
    print(f"  Par {i}: {par} -> min = {min(par)}")

print()

# Normalizar
obj = ConfiguracionRacional(config_id_40, normalizar=True)

print(f"Configuracion normalizada: {obj.pares}")
print(f"Configuracion esperada:    [[1, 4], [5, 2], [3, 6]]")
print()

if obj.pares == [[1, 4], [5, 2], [3, 6]]:
    print("[OK] CORRECTO! La normalizacion funciona bien")
else:
    print("[ERROR] La normalizacion NO funciona correctamente")
    print(f"  Esperado: [[1, 4], [5, 2], [3, 6]]")
    print(f"  Obtenido: {obj.pares}")

print()
print(f"IME: {obj.calcular_ime()}")
print(f"Es reducible: {obj.es_reducible()}")
