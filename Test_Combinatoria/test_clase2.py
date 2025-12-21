"""
Verificar Clase 2 - Deberia ser REDUCIBLE por R2
"""

from clasificador_ime import ConfiguracionRacional

config = [[1, 4], [2, 6], [3, 5]]

print("Clase 2 - Verificacion de R2")
print("=" * 60)
print(f"Configuracion: {config}")
print()

# Crear objeto
obj = ConfiguracionRacional(config, normalizar=False)

print("Analisis de pares:")
for i, (o, u) in enumerate(config):
    print(f"  Par {i}: [{o}, {u}] -> intervalo [{min(o,u)}, {max(o,u)}]")
print()

# Verificar cada par de pares
print("Verificando adyacencias:")
for i in range(len(config)):
    for j in range(i+1, len(config)):
        oi, ui = config[i]
        oj, uj = config[j]
        
        ady_over = abs(oi - oj) == 1
        ady_under = abs(ui - uj) == 1
        
        print(f"\nPares {i} y {j}:")
        print(f"  Adyacencia over: |{oi}-{oj}| = {abs(oi-oj)} -> {'SI' if ady_over else 'NO'}")
        print(f"  Adyacencia under: |{ui}-{uj}| = {abs(ui-uj)} -> {'SI' if ady_under else 'NO'}")
        
        if ady_over and ady_under:
            # Verificar bigon
            ai, bi = min(oi, ui), max(oi, ui)
            aj, bj = min(oj, uj), max(oj, uj)
            
            contiene_i_a_j = (ai < aj and bj < bi)
            contiene_j_a_i = (aj < ai and bi < bj)
            
            print(f"  Intervalo {i}: [{ai}, {bi}]")
            print(f"  Intervalo {j}: [{aj}, {bj}]")
            print(f"  ¿{i} contiene {j}? {ai} < {aj} and {bj} < {bi} = {contiene_i_a_j}")
            print(f"  ¿{j} contiene {i}? {aj} < {ai} and {bi} < {bj} = {contiene_j_a_i}")
            
            if contiene_i_a_j or contiene_j_a_i:
                print(f"  [R2 DETECTADO] Forma un bigon!")

print()
print(f"¿Es reducible segun mi codigo? {obj.es_reducible()}")
print()

if not obj.es_reducible():
    print("[ERROR] Mi codigo NO detecto el R2!")
    print("Deberia ser REDUCIBLE")
else:
    print("[OK] Correctamente detectado como REDUCIBLE")
