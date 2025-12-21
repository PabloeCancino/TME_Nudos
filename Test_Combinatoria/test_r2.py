"""
Verificar detección de R2 en la configuración específica
"""

from clasificador_ime import ConfiguracionRacional

config = [[1, 4], [2, 6], [3, 5]]

print("Configuracion:", config)
print()

# Analizar
obj = ConfiguracionRacional(config, normalizar=False)

print("Par 0 [1,4]: min=1, max=4")
print("Par 1 [2,6]: min=2, max=6")
print("Par 2 [3,5]: min=3, max=5")
print()

# Verificar adyacencia entre pares 1 y 2
print("Verificando R2 entre pares 1 y 2:")
print(f"  Adyacencia over: |2-3| = {abs(2-3)} (debe ser 1) -> {'SI' if abs(2-3)==1 else 'NO'}")
print(f"  Adyacencia under: |6-5| = {abs(6-5)} (debe ser 1) -> {'SI' if abs(6-5)==1 else 'NO'}")
print()

# Verificar interlazado
a1, b1 = min(2, 6), max(2, 6)  # [2, 6]
a2, b2 = min(3, 5), max(3, 5)  # [3, 5]

print(f"  Intervalos:")
print(f"    Par 1: [{a1}, {b1}]")
print(f"    Par 2: [{a2}, {b2}]")
print()

# Patrones de interlazado
patron1 = a1 < a2 < b1 < b2
patron2 = a2 < a1 < b2 < b1

print(f"  Patron 1 (a1 < a2 < b1 < b2): {a1} < {a2} < {b1} < {b2} = {patron1}")
print(f"  Patron 2 (a2 < a1 < b2 < b1): {a2} < {a1} < {b2} < {b1} = {patron2}")
print()

# ¿Están interlazados según mi función?
interlazados = obj._estan_interlazados(1, 2)
print(f"  ¿Estan interlazados segun mi codigo? {interlazados}")
print()

# Verificar si es reducible
print(f"¿Es reducible segun mi codigo? {obj.es_reducible()}")
print()

# Análisis geométrico
print("ANALISIS GEOMETRICO:")
print(f"  El intervalo [{a1},{b1}] CONTIENE al intervalo [{a2},{b2}]? {a1 < a2 and b2 < b1}")
print(f"  Esto forma un 'bigon' (dos cruces que se cancelan)")
