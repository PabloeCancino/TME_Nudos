"""
Test de R1 con distancia cíclica
"""

from clasificador_ime import ConfiguracionRacional

print("Test de R1 - Distancia Ciclica")
print("=" * 60)

# Caso 1: [6, 1] en mod 6 (n=3)
config1 = [[6, 1], [2, 4], [5, 3]]
print("\nCaso 1: [[6, 1], [2, 4], [5, 3]]")
print("  Par [6, 1] en espacio mod 6:")
print("  Distancia lineal: |6-1| = 5")
print("  Distancia ciclica: min(5, 6-5) = min(5, 1) = 1")
print("  ¿Deberia ser R1? SI")

obj1 = ConfiguracionRacional(config1, normalizar=False)
print(f"  ¿Mi codigo lo detecta? {obj1.es_reducible()}")

if obj1.es_reducible():
    print("  [OK] CORRECTO!")
else:
    print("  [ERROR] No lo detecto!")

# Caso 2: [1, 2] - R1 obvio
config2 = [[1, 2], [3, 6], [4, 5]]
print("\nCaso 2: [[1, 2], [3, 6], [4, 5]]")
print("  Par [1, 2]:")
print("  Distancia: |1-2| = 1")
print("  ¿Deberia ser R1? SI")

obj2 = ConfiguracionRacional(config2, normalizar=False)
print(f"  ¿Mi codigo lo detecta? {obj2.es_reducible()}")

if obj2.es_reducible():
    print("  [OK] CORRECTO!")
else:
    print("  [ERROR] No lo detecto!")

# Caso 3: NO es R1
config3 = [[1, 4], [5, 2], [3, 6]]
print("\nCaso 3: [[1, 4], [5, 2], [3, 6]] (trebol)")
print("  Ninguna distancia ciclica es 1")
print("  ¿Deberia ser R1? NO")

obj3 = ConfiguracionRacional(config3, normalizar=False)
print(f"  ¿Mi codigo lo detecta como reducible? {obj3.es_reducible()}")

if not obj3.es_reducible():
    print("  [OK] CORRECTO - No es reducible!")
else:
    print("  [ERROR] Lo marco como reducible!")
