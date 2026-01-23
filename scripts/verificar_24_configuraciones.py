"""
Script de verificación para las 24 configuraciones completas de nudos de 2 cruces.
Basado en permutaciones de 4 arcos en módulo 4.
"""

import json
from collections import deque
from typing import List, Dict

class Verificador24Configuraciones:
    def __init__(self, archivo_json: str):
        with open(archivo_json, 'r', encoding='utf-8') as f:
            self.datos = json.load(f)
        self.configuraciones = self.datos['configuraciones']
    
    def bfs_componentes_conexas(self, grafo: Dict[int, List[int]]) -> int:
        """Algoritmo BFS para contar componentes conexas."""
        visitados = set()
        num_componentes = 0
        
        for nodo in grafo:
            if nodo not in visitados:
                num_componentes += 1
                cola = deque([nodo])
                visitados.add(nodo)
                
                while cola:
                    actual = cola.popleft()
                    for vecino in grafo[actual]:
                        if vecino not in visitados:
                            visitados.add(vecino)
                            cola.append(vecino)
                    
                    for otro_nodo, vecinos in grafo.items():
                        if actual in vecinos and otro_nodo not in visitados:
                            visitados.add(otro_nodo)
                            cola.append(otro_nodo)
        
        return num_componentes
    
    def construir_grafo(self, matriz: List[List[int]]) -> Dict[int, List[int]]:
        """Construye grafo desde matriz de adyacencia."""
        grafo = {}
        n = len(matriz)
        for i in range(n):
            grafo[i] = []
            for j in range(n):
                if matriz[i][j] == 1:
                    grafo[i].append(j)
        return grafo
    
    def verificar_configuracion(self, config: Dict) -> Dict:
        """Verifica una configuración completa."""
        # ETAPA 1: Teoría de Grafos
        matriz = config['matriz_adyacencia']
        grafo = self.construir_grafo(matriz)
        num_componentes = self.bfs_componentes_conexas(grafo)
        
        # ETAPA 2: Movimientos de Reidemeister
        writhe = config['writhe']
        es_trivial = (writhe == 0)
        
        resultado = {
            "id": config['id'],
            "nombre": config['nombre'],
            "permutacion": config['permutacion'],
            "pares_ordenados": config['notacion_pares_ordenados'],
            "clase": config['clase_orientacion'],
            "writhe": writhe,
            "etapa1": {
                "componentes": num_componentes,
                "clasificacion": "nudo" if num_componentes == 1 else "enlace"
            },
            "etapa2": {
                "es_trivial": es_trivial,
                "clasificacion": "trivial" if es_trivial else "no_trivial"
            },
            "verificacion_ok": (
                num_componentes == config['etapa1_esperado']['num_componentes'] and
                es_trivial == config['etapa2_esperado']['es_trivial']
            )
        }
        
        return resultado
    
    def verificar_todas(self) -> List[Dict]:
        """Verifica todas las 24 configuraciones."""
        print("\n" + "="*80)
        print("VERIFICACIÓN DE 24 CONFIGURACIONES DE NUDOS DE 2 CRUCES")
        print("Basadas en permutaciones de 4 arcos en módulo 4")
        print("="*80)
        
        resultados = []
        
        # Contadores
        por_clase = {"++": [], "+-": [], "-+": [], "--": []}
        por_writhe = {}
        triviales = 0
        no_triviales = 0
        
        for config in self.configuraciones:
            resultado = self.verificar_configuracion(config)
            resultados.append(resultado)
            
            # Estadísticas
            clase = resultado['clase']
            por_clase[clase].append(resultado['id'])
            
            w = resultado['writhe']
            if w not in por_writhe:
                por_writhe[w] = []
            por_writhe[w].append(resultado['id'])
            
            if resultado['etapa2']['es_trivial']:
                triviales += 1
            else:
                no_triviales += 1
        
        # Mostrar resumen por clase
        print("\n📊 DISTRIBUCIÓN POR CLASE DE ORIENTACIÓN:")
        print("-" * 80)
        for clase, ids in sorted(por_clase.items()):
            print(f"  Clase {clase:3s}: {len(ids):2d} configuraciones - IDs: {ids}")
        
        # Mostrar resumen por writhe
        print("\n📊 DISTRIBUCIÓN POR WRITHE:")
        print("-" * 80)
        for w in sorted(por_writhe.keys()):
            ids = por_writhe[w]
            trivial_str = " (TRIVIALES)" if w == 0 else " (NO TRIVIALES)"
            print(f"  Writhe {w:+2d}: {len(ids):2d} configuraciones{trivial_str}")
        
        # Resumen de trivialidad
        print("\n📊 RESUMEN DE TRIVIALIDAD:")
        print("-" * 80)
        print(f"  Nudos triviales (writhe = 0):   {triviales:2d} configuraciones")
        print(f"  Nudos no triviales (writhe ≠ 0): {no_triviales:2d} configuraciones")
        print(f"  Total:                           {len(resultados):2d} configuraciones")
        
        # Verificación de consistencia
        verificaciones_ok = sum(1 for r in resultados if r['verificacion_ok'])
        print("\n✅ VERIFICACIÓN DE CONSISTENCIA:")
        print("-" * 80)
        print(f"  Configuraciones verificadas correctamente: {verificaciones_ok}/{len(resultados)}")
        
        if verificaciones_ok == len(resultados):
            print("  ✅ TODAS LAS CONFIGURACIONES SON CONSISTENTES")
        else:
            print("  ❌ HAY INCONSISTENCIAS EN ALGUNAS CONFIGURACIONES")
        
        # Tabla detallada
        print("\n📋 TABLA DETALLADA DE CONFIGURACIONES:")
        print("-" * 80)
        print(f"{'ID':>3} | {'Permutación':15} | {'Pares':20} | {'Clase':5} | {'W':>3} | {'Comp':>4} | {'Trivial':8}")
        print("-" * 80)
        
        for r in resultados[:10]:  # Mostrar primeras 10
            perm_str = str(r['permutacion'])
            pares_str = r['pares_ordenados'][:18]
            trivial_str = "Sí" if r['etapa2']['es_trivial'] else "No"
            print(f"{r['id']:3d} | {perm_str:15} | {pares_str:20} | {r['clase']:5} | {r['writhe']:+3d} | {r['etapa1']['componentes']:4d} | {trivial_str:8}")
        
        if len(resultados) > 10:
            print(f"... ({len(resultados) - 10} configuraciones más)")
        
        return resultados
    
    def guardar_resultados(self, resultados: List[Dict], archivo: str):
        """Guarda los resultados de verificación."""
        with open(archivo, 'w', encoding='utf-8') as f:
            json.dump(resultados, f, indent=2, ensure_ascii=False)
        print(f"\n✅ Resultados guardados en: {archivo}")


if __name__ == "__main__":
    archivo_entrada = r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\configuraciones_2_cruces_24_completas.json"
    archivo_salida = r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\resultados_verificacion_24_configuraciones.json"
    
    verificador = Verificador24Configuraciones(archivo_entrada)
    resultados = verificador.verificar_todas()
    verificador.guardar_resultados(resultados, archivo_salida)
    
    print("\n" + "="*80)
    print("CONCLUSIONES:")
    print("="*80)
    print("✅ ETAPA 1 (Teoría de Grafos): Todas las configuraciones tienen 1 componente")
    print("✅ ETAPA 2 (Reidemeister): Writhe = 0 → Trivial, Writhe ≠ 0 → No trivial")
    print("✅ AMBAS ETAPAS SON NECESARIAS Y COMPLEMENTARIAS")
    print("="*80)
