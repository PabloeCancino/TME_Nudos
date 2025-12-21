"""
Test para verificar que la normalización NO cambia el orden interno de los pares
"""

from clasificador_ime import ConfiguracionRacional

# Test crítico: verificar que [2,5] NO se convierte en [5,2]
config_original = [[1, 4], [5, 2], [3, 6]]

print("Configuración original:", config_original)
print()

config = ConfiguracionRacional(config_original, normalizar=True)
print("Configuración normalizada:", config.pares)
print()

# Verificar cada par
for i, (orig, norm) in enumerate(zip(config_original, config.pares)):
    print(f"Par {i}: Original = {orig}")
    
# Verificar específicamente el par [5, 2]
par_problematico = [5, 2]
print(f"\nBuscando el par {par_problematico} en la normalizada...")
encontrado = False
for par in config.pares:
    if par == par_problematico:
        print(f"  [OK] Encontrado: {par}")

        encontrado = True
        break

if not encontrado:
    print(f"  [ERROR] El par {par_problematico} fue modificado!")

    print(f"  Los pares normalizados son: {config.pares}")
