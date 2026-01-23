"""
Evaluación de 4 configuraciones de nudos de 3 cruces (K_3).
Aplica criterios de Reidemeister I y II en módulo 6.
"""

import json
from collections import deque
from typing import List, Dict, Tuple

class EvaluadorK3:
    def __init__(self):
        self.m = 6  # Módulo para 3 cruces (2*3 = 6 arcos)
        self.configuraciones = []
    
    # ==================== UTILIDADES ====================
    
    def son_consecutivos_mod(self, a: int, b: int) -> bool:
        """Verifica si dos valores son consecutivos en módulo m."""
        diff = abs(a - b) % self.m
        return diff == 1 or diff == (self.m - 1)
    
    def determinar_orientacion(self, over: int, under: int) -> int:
        """Determina la orientación de un cruce."""
        diff = (over - under) % self.m
        if diff in [1, 2, 3]:
            return 1  # Positivo
        else:
            return -1  # Negativo
    
    # ==================== R1: CONSECUTIVIDAD INTERNA ====================
    
    def detectar_r1_en_cruce(self, over: int, under: int) -> bool:
        """
        R1: Se aplica cuando over y under son CONSECUTIVOS en mod m.
        Criterio: |over - under| mod m ∈ {1, m-1}
        """
        return self.son_consecutivos_mod(over, under)
    
    # ==================== R2: CONSECUTIVIDAD CORRESPONDIENTE ====================
    
    def detectar_r2_entre_cruces(self, cruce1: Dict, cruce2: Dict) -> bool:
        """
        R2: Se aplica cuando DOS CRUCES tienen pares (over, under) AMBOS consecutivos.
        
        Criterio:
        - |over₁ - over₂| mod m ∈ {1, m-1}  Y
        - |under₁ - under₂| mod m ∈ {1, m-1}
        """
        o1, u1 = cruce1['over'], cruce1['under']
        o2, u2 = cruce2['over'], cruce2['under']
        
        overs_consecutivos = self.son_consecutivos_mod(o1, o2)
        unders_consecutivos = self.son_consecutivos_mod(u1, u2)
        
        return overs_consecutivos and unders_consecutivos
    
    # ==================== ETAPA 1: COMPONENTES CONEXAS ====================
    
    def construir_grafo(self, cruces: List[Dict]) -> Dict[int, List[int]]:
        """
        Construye el grafo de arcos desde los cruces.
        Cada arco se conecta al siguiente en secuencia.
        """
        grafo = {i: [] for i in range(self.m)}
        
        # Construir conexiones basadas en la secuencia de arcos
        for i in range(self.m):
            grafo[i].append((i + 1) % self.m)
        
        return grafo
    
    def bfs_componentes_conexas(self, grafo: Dict[int, List[int]]) -> int:
        """BFS para contar componentes conexas."""
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
                    
                    # Considerar aristas inversas
                    for otro_nodo, vecinos in grafo.items():
                        if actual in vecinos and otro_nodo not in visitados:
                            visitados.add(otro_nodo)
                            cola.append(otro_nodo)
        
        return num_componentes
    
    # ==================== EVALUACIÓN COMPLETA ====================
    
    def evaluar_configuracion(self, nombre: str, cruces_raw: List[Tuple[int, int]]) -> Dict:
        """Evalúa una configuración completa."""
        # Construir cruces con información completa
        cruces = []
        for i, (over, under) in enumerate(cruces_raw):
            cruce = {
                'id': i + 1,
                'over': over,
                'under': under,
                'orientacion': self.determinar_orientacion(over, under),
                'r1_aplicable': self.detectar_r1_en_cruce(over, under)
            }
            cruces.append(cruce)
        
        # ETAPA 1: Componentes conexas
        grafo = self.construir_grafo(cruces)
        num_componentes = self.bfs_componentes_conexas(grafo)
        clasificacion_etapa1 = "nudo" if num_componentes == 1 else "enlace"
        
        # ETAPA 2: Movimientos de Reidemeister
        movimientos = []
        
        # Verificar R1 en cada cruce
        for cruce in cruces:
            if cruce['r1_aplicable']:
                movimientos.append(f"R1_cruce{cruce['id']}")
        
        # Verificar R2 entre pares de cruces
        r2_pares = []
        for i in range(len(cruces)):
            for j in range(i + 1, len(cruces)):
                if self.detectar_r2_entre_cruces(cruces[i], cruces[j]):
                    r2_pares.append((i+1, j+1))
                    movimientos.append(f"R2_cruces{i+1}_{j+1}")
        
        # Determinar trivialidad
        es_trivial = len(movimientos) > 0
        if es_trivial:
            if any('R1' in m for m in movimientos):
                razon = "Reducible mediante R1 (arcos consecutivos en un cruce)"
            else:
                razon = "Reducible mediante R2 (pares consecutivos entre cruces)"
        else:
            razon = "No reducible mediante R1 o R2"
        
        # Calcular writhe
        writhe = sum(c['orientacion'] for c in cruces)
        
        return {
            'nombre': nombre,
            'cruces': cruces,
            'etapa1': {
                'num_componentes': num_componentes,
                'clasificacion': clasificacion_etapa1
            },
            'etapa2': {
                'movimientos_aplicables': movimientos,
                'r2_pares': r2_pares,
                'es_trivial': es_trivial,
                'razon': razon,
                'writhe': writhe
            }
        }
    
    def evaluar_todas(self, configs: Dict[str, List[Tuple[int, int]]]):
        """Evalúa todas las configuraciones."""
        print("="*80)
        print("EVALUACIÓN DE 4 CONFIGURACIONES DE K_3")
        print("Módulo: m = 6 (2 × 3 cruces)")
        print("="*80)
        
        resultados = []
        
        for nombre, cruces_raw in configs.items():
            print(f"\n{'='*80}")
            print(f"CONFIGURACIÓN: {nombre}")
            print(f"{'='*80}")
            
            resultado = self.evaluar_configuracion(nombre, cruces_raw)
            resultados.append(resultado)
            
            # Mostrar cruces
            print(f"\n📋 CRUCES:")
            for cruce in resultado['cruces']:
                consec = "✅ Consecutivos" if cruce['r1_aplicable'] else "❌ NO consecutivos"
                orient = "+" if cruce['orientacion'] == 1 else "-"
                print(f"  V_{cruce['id']}({cruce['over']},{cruce['under']}) → {consec}, Orientación: {orient}")
            
            # ETAPA 1
            print(f"\n📊 ETAPA 1: COMPONENTES CONEXAS")
            print(f"  Número de componentes: {resultado['etapa1']['num_componentes']}")
            print(f"  Clasificación: {resultado['etapa1']['clasificacion'].upper()}")
            
            # ETAPA 2
            print(f"\n🔄 ETAPA 2: MOVIMIENTOS DE REIDEMEISTER")
            print(f"  Writhe: {resultado['etapa2']['writhe']}")
            print(f"  Movimientos aplicables: {len(resultado['etapa2']['movimientos_aplicables'])}")
            
            if resultado['etapa2']['movimientos_aplicables']:
                for mov in resultado['etapa2']['movimientos_aplicables']:
                    print(f"    - {mov}")
            else:
                print(f"    - Ninguno")
            
            if resultado['etapa2']['r2_pares']:
                print(f"  Pares con R2: {resultado['etapa2']['r2_pares']}")
            
            print(f"\n  ✅ Trivial: {'SÍ' if resultado['etapa2']['es_trivial'] else 'NO'}")
            print(f"  Razón: {resultado['etapa2']['razon']}")
        
        # Resumen final
        print(f"\n{'='*80}")
        print(f"RESUMEN FINAL")
        print(f"{'='*80}")
        
        triviales = sum(1 for r in resultados if r['etapa2']['es_trivial'])
        no_triviales = len(resultados) - triviales
        nudos = sum(1 for r in resultados if r['etapa1']['clasificacion'] == 'nudo')
        enlaces = len(resultados) - nudos
        
        print(f"\nTotal de configuraciones: {len(resultados)}")
        print(f"Nudos (1 componente): {nudos}")
        print(f"Enlaces (2+ componentes): {enlaces}")
        print(f"Triviales: {triviales}")
        print(f"No triviales: {no_triviales}")
        
        return resultados


if __name__ == "__main__":
    evaluador = EvaluadorK3()
    
    # Definir las 4 configuraciones
    configuraciones = {
        'K_3_1': [(0, 3), (4, 1), (2, 5)],
        'K_3_2': [(0, 5), (2, 1), (4, 3)],
        'K_3_3': [(0, 3), (1, 4), (2, 5)],
        'K_3_4': [(0, 5), (1, 4), (2, 3)]
    }
    
    resultados = evaluador.evaluar_todas(configuraciones)
    
    # Guardar resultados
    archivo_salida = r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\evaluacion_K3_4_configuraciones.json"
    with open(archivo_salida, 'w', encoding='utf-8') as f:
        json.dump(resultados, f, indent=2, ensure_ascii=False)
    
    print(f"\n✅ Resultados guardados en: {archivo_salida}")
