"""
Análisis de la topología de K_3_5 usando la matriz de incidencia.
"""

import numpy as np
from collections import deque

# Matriz de incidencia de K_3_5
# Filas: vértices (cruces)
# Columnas: aristas (arcos)
# Valor: multiplicidad de incidencia

matriz_incidencia = np.array([
    [2, 1, 1, 0, 0, 0],  # v_1
    [0, 1, 0, 1, 1, 1],  # v_2
    [0, 0, 1, 1, 1, 1]   # v_3
])

print("="*80)
print("ANÁLISIS DE TOPOLOGÍA: K_3_5")
print("="*80)

print("\n📊 MATRIZ DE INCIDENCIA:")
print("\n     a_1  a_2  a_3  a_4  a_5  a_6")
for i, fila in enumerate(matriz_incidencia, 1):
    print(f"v_{i}   {fila[0]}    {fila[1]}    {fila[2]}    {fila[3]}    {fila[4]}    {fila[5]}")

print("\n🔍 INTERPRETACIÓN DE LA MATRIZ:")
print("-"*80)

# Analizar cada vértice
print("\nVértice v_1:")
print("  - a_1: incidencia 2 → BUCLE (arco que sale y regresa al mismo vértice)")
print("  - a_2: incidencia 1 → arco normal")
print("  - a_3: incidencia 1 → arco normal")
print("  Total: v_1 tiene un bucle (a_1) y dos arcos normales (a_2, a_3)")

print("\nVértice v_2:")
print("  - a_2: incidencia 1 → conecta con v_1")
print("  - a_4: incidencia 1 → arco normal")
print("  - a_5: incidencia 1 → arco normal")
print("  - a_6: incidencia 1 → arco normal")
print("  Total: v_2 tiene 4 arcos incidentes")

print("\nVértice v_3:")
print("  - a_3: incidencia 1 → conecta con v_1")
print("  - a_4: incidencia 1 → conecta con v_2")
print("  - a_5: incidencia 1 → conecta con v_2")
print("  - a_6: incidencia 1 → conecta con v_2")
print("  Total: v_3 tiene 4 arcos incidentes")

# Construir grafo de arcos
print("\n🔗 CONSTRUCCIÓN DEL GRAFO DE ARCOS:")
print("-"*80)

# Determinar qué arcos están conectados
conexiones = []
for j in range(6):  # Para cada arco
    vertices_incidentes = []
    for i in range(3):  # Para cada vértice
        if matriz_incidencia[i, j] > 0:
            vertices_incidentes.append(i+1)
    
    if len(vertices_incidentes) == 1:
        print(f"Arco a_{j+1}: BUCLE en vértice v_{vertices_incidentes[0]}")
    elif len(vertices_incidentes) == 2:
        print(f"Arco a_{j+1}: conecta v_{vertices_incidentes[0]} ↔ v_{vertices_incidentes[1]}")
    conexiones.append(vertices_incidentes)

# Construir grafo de adyacencia de arcos
print("\n🌐 GRAFO DE ADYACENCIA DE ARCOS:")
print("-"*80)

# Dos arcos están conectados si comparten un vértice
grafo_arcos = {i: [] for i in range(6)}

for i in range(6):
    for j in range(6):
        if i != j:
            # Verificar si comparten algún vértice
            vertices_i = set()
            vertices_j = set()
            
            for v in range(3):
                if matriz_incidencia[v, i] > 0:
                    vertices_i.add(v)
                if matriz_incidencia[v, j] > 0:
                    vertices_j.add(v)
            
            if vertices_i & vertices_j:  # Si comparten vértice
                grafo_arcos[i].append(j)

for arco, vecinos in grafo_arcos.items():
    print(f"a_{arco+1} → {[f'a_{v+1}' for v in vecinos]}")

# BFS para componentes conexas
print("\n🔍 COMPONENTES CONEXAS (BFS):")
print("-"*80)

visitados = set()
componentes = []

for arco in range(6):
    if arco not in visitados:
        componente = []
        cola = deque([arco])
        visitados.add(arco)
        
        while cola:
            actual = cola.popleft()
            componente.append(actual)
            
            for vecino in grafo_arcos[actual]:
                if vecino not in visitados:
                    visitados.add(vecino)
                    cola.append(vecino)
        
        componentes.append(sorted(componente))

print(f"\nNúmero de componentes: {len(componentes)}")
for i, comp in enumerate(componentes, 1):
    arcos_str = [f'a_{a+1}' for a in comp]
    print(f"Componente {i}: {arcos_str}")

# Clasificación
print("\n✅ CLASIFICACIÓN:")
print("-"*80)
if len(componentes) == 1:
    print("  Tipo: NUDO (1 componente)")
else:
    print(f"  Tipo: ENLACE ({len(componentes)} componentes)")

# Análisis de cruces
print("\n🎯 ANÁLISIS DE CRUCES:")
print("-"*80)
cruces = [
    {"id": 1, "over": 0, "under": 3},
    {"id": 2, "over": 1, "under": 4},
    {"id": 3, "over": 2, "under": 5}
]

for cruce in cruces:
    over, under = cruce['over'], cruce['under']
    diff = abs(over - under) % 6
    consecutivos = diff in [1, 5]
    print(f"V_{cruce['id']}({over},{under}): |{over}-{under}| = {diff} → {'✅ R1' if consecutivos else '❌ No R1'}")

# Guardar resultados
resultado = {
    "nombre": "K_3_5",
    "cruces": cruces,
    "matriz_incidencia": matriz_incidencia.tolist(),
    "num_componentes": len(componentes),
    "componentes": [[f"a_{a+1}" for a in comp] for comp in componentes],
    "clasificacion": "enlace" if len(componentes) > 1 else "nudo"
}

import json
with open(r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\analisis_K3_5_topologia.json", 'w', encoding='utf-8') as f:
    json.dump(resultado, f, indent=2, ensure_ascii=False)

print(f"\n✅ Análisis guardado en: analisis_K3_5_topologia.json")
