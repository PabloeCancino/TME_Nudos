"""
Generador FINAL CORREGIDO de las 24 configuraciones de nudos de 2 cruces.
Basado en permutaciones de 4 arcos en módulo 4 (clases de equivalencia 0,1,2,3).

CRITERIOS CORRECTOS:
- R1: Se aplica cuando over y under son CONSECUTIVOS en mod 4 en UN MISMO cruce
- R2: Se aplica cuando DOS CRUCES tienen pares (over, under) consecutivos:
      [o(n), u(m)], [o(n±1), u(m±1)]
"""

import json
import itertools
from typing import List, Dict, Tuple

class GeneradorConfiguracionesFinalCorregido:
    def __init__(self):
        self.configuraciones = []
        
    def generar_todas_permutaciones(self) -> List[Tuple[int, int, int, int]]:
        """Genera todas las permutaciones de (0,1,2,3). Total: 4! = 24"""
        arcos = [0, 1, 2, 3]
        return list(itertools.permutations(arcos))
    
    def son_consecutivos_mod4(self, a: int, b: int) -> bool:
        """Verifica si dos valores son consecutivos en módulo 4."""
        diff = abs(a - b) % 4
        return diff == 1 or diff == 3
    
    def determinar_orientacion_cruce(self, over: int, under: int) -> int:
        """Determina la orientación de un cruce."""
        diff = (over - under) % 4
        if diff in [1, 2]:
            return 1  # Positivo
        else:
            return -1  # Negativo
    
    def detectar_r1_en_cruce(self, over: int, under: int) -> bool:
        """
        R1: Se aplica cuando over y under son CONSECUTIVOS en mod 4.
        """
        return self.son_consecutivos_mod4(over, under)
    
    def detectar_r2_entre_cruces(self, cruce1: Dict, cruce2: Dict) -> bool:
        """
        R2: Se aplica cuando DOS CRUCES tienen pares (over, under) consecutivos.
        
        Patrones:
        - [o(n), u(m)], [o(n+1), u(m+1)]
        - [o(n), u(m)], [o(n-1), u(m+1)]
        - [o(n), u(m)], [o(n+1), u(m-1)]
        - [o(n), u(m)], [o(n-1), u(m-1)]
        """
        o1, u1 = cruce1['over'], cruce1['under']
        o2, u2 = cruce2['over'], cruce2['under']
        
        # Verificar si los overs son consecutivos
        overs_consecutivos = self.son_consecutivos_mod4(o1, o2)
        
        # Verificar si los unders son consecutivos
        unders_consecutivos = self.son_consecutivos_mod4(u1, u2)
        
        # R2 se aplica si AMBOS son consecutivos
        return overs_consecutivos and unders_consecutivos
    
    def construir_pares_ordenados(self, perm: Tuple[int, int, int, int]) -> List[Dict]:
        """Construye los pares ordenados para los 2 cruces."""
        cruce1 = {
            "cruce": 1,
            "over": perm[0],
            "under": perm[1],
            "par": [perm[0], perm[1]],
            "orientacion": self.determinar_orientacion_cruce(perm[0], perm[1]),
            "r1_aplicable": self.detectar_r1_en_cruce(perm[0], perm[1])
        }
        
        cruce2 = {
            "cruce": 2,
            "over": perm[2],
            "under": perm[3],
            "par": [perm[2], perm[3]],
            "orientacion": self.determinar_orientacion_cruce(perm[2], perm[3]),
            "r1_aplicable": self.detectar_r1_en_cruce(perm[2], perm[3])
        }
        
        return [cruce1, cruce2]
    
    def calcular_writhe(self, pares: List[Dict]) -> int:
        """Calcula el writhe total (suma de orientaciones)."""
        return sum(p["orientacion"] for p in pares)
    
    def determinar_trivialidad(self, pares: List[Dict]) -> Tuple[bool, str, List[str]]:
        """
        Determina si la configuración es trivial.
        
        Criterios:
        1. Si algún cruce tiene R1 aplicable → Trivial
        2. Si los dos cruces tienen R2 aplicable → Trivial
        3. Caso contrario → No trivial
        """
        movimientos = []
        
        # Verificar R1 en cada cruce
        if pares[0]["r1_aplicable"]:
            movimientos.append("R1_cruce1")
        if pares[1]["r1_aplicable"]:
            movimientos.append("R1_cruce2")
        
        # Si algún cruce tiene R1, es trivial
        if movimientos:
            return True, "Reducible mediante R1 (arcos consecutivos en un cruce)", movimientos
        
        # Verificar R2 entre cruces
        if self.detectar_r2_entre_cruces(pares[0], pares[1]):
            movimientos.append("R2")
            return True, "Reducible mediante R2 (pares consecutivos entre cruces)", movimientos
        
        return False, "No reducible mediante R1 o R2", []
    
    def construir_matriz_adyacencia(self, perm: Tuple[int, int, int, int]) -> List[List[int]]:
        """Construye la matriz de adyacencia del grafo."""
        matriz = [
            [0, 1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, 0, 1],
            [1, 0, 0, 0]
        ]
        return matriz
    
    def clasificar_por_orientaciones(self, pares: List[Dict]) -> str:
        """Clasifica la configuración por sus orientaciones."""
        o1 = pares[0]["orientacion"]
        o2 = pares[1]["orientacion"]
        
        if o1 == 1 and o2 == 1:
            return "++"
        elif o1 == 1 and o2 == -1:
            return "+-"
        elif o1 == -1 and o2 == 1:
            return "-+"
        else:
            return "--"
    
    def generar_configuracion(self, idx: int, perm: Tuple[int, int, int, int]) -> Dict:
        """Genera una configuración completa a partir de una permutación."""
        pares = self.construir_pares_ordenados(perm)
        writhe = self.calcular_writhe(pares)
        clase_orientacion = self.clasificar_por_orientaciones(pares)
        es_trivial, razon, movimientos = self.determinar_trivialidad(pares)
        
        # Información adicional sobre R2
        r2_info = {
            "overs_consecutivos": self.son_consecutivos_mod4(pares[0]['over'], pares[1]['over']),
            "unders_consecutivos": self.son_consecutivos_mod4(pares[0]['under'], pares[1]['under']),
            "r2_aplicable": self.detectar_r2_entre_cruces(pares[0], pares[1])
        }
        
        config = {
            "id": idx + 1,
            "nombre": f"K_(2,{idx+1})",
            "permutacion": list(perm),
            "notacion_pares_ordenados": f"{{({perm[0]},{perm[1]}), ({perm[2]},{perm[3]})}}",
            "pares_ordenados": pares,
            "clase_orientacion": clase_orientacion,
            "writhe": writhe,
            "r2_info": r2_info,
            "matriz_adyacencia": self.construir_matriz_adyacencia(perm),
            "etapa1_esperado": {
                "num_componentes": 1,
                "es_grafo_euleriano": True,
                "clasificacion": "nudo"
            },
            "etapa2_esperado": {
                "es_trivial": es_trivial,
                "razon": razon,
                "writhe": writhe,
                "clasificacion_final": "nudo_trivial" if es_trivial else "nudo_no_trivial",
                "movimientos_aplicables": movimientos
            }
        }
        
        return config
    
    def generar_todas_configuraciones(self) -> List[Dict]:
        """Genera las 24 configuraciones completas."""
        permutaciones = self.generar_todas_permutaciones()
        
        for idx, perm in enumerate(permutaciones):
            config = self.generar_configuracion(idx, perm)
            self.configuraciones.append(config)
        
        return self.configuraciones
    
    def generar_resumen_estadistico(self) -> Dict:
        """Genera estadísticas sobre las configuraciones."""
        total = len(self.configuraciones)
        triviales = sum(1 for c in self.configuraciones if c["etapa2_esperado"]["es_trivial"])
        no_triviales = total - triviales
        
        # Distribución de writhe
        writhe_dist = {}
        for c in self.configuraciones:
            w = c["writhe"]
            writhe_dist[w] = writhe_dist.get(w, 0) + 1
        
        # Distribución de clases de orientación
        clase_dist = {}
        for c in self.configuraciones:
            clase = c["clase_orientacion"]
            clase_dist[clase] = clase_dist.get(clase, 0) + 1
        
        # Distribución de movimientos
        con_r1 = sum(1 for c in self.configuraciones 
                     if any("R1" in m for m in c["etapa2_esperado"]["movimientos_aplicables"]))
        con_r2 = sum(1 for c in self.configuraciones 
                     if "R2" in c["etapa2_esperado"]["movimientos_aplicables"])
        con_r1_o_r2 = sum(1 for c in self.configuraciones
                          if len(c["etapa2_esperado"]["movimientos_aplicables"]) > 0)
        
        return {
            "total_configuraciones": total,
            "nudos_triviales": triviales,
            "nudos_no_triviales": no_triviales,
            "distribucion_writhe": writhe_dist,
            "distribucion_clases": clase_dist,
            "con_r1_aplicable": con_r1,
            "con_r2_aplicable": con_r2,
            "con_r1_o_r2": con_r1_o_r2
        }
    
    def guardar_json(self, archivo: str):
        """Guarda las configuraciones en un archivo JSON."""
        datos = {
            "descripcion": "24 configuraciones de nudos de 2 cruces basadas en permutaciones de 4 arcos en módulo 4",
            "notacion": "Permutaciones de (0,1,2,3) generan 4! = 24 configuraciones",
            "criterios_reidemeister": {
                "R1": "Se aplica cuando over y under son CONSECUTIVOS en mod 4 en UN MISMO cruce: |over - under| mod 4 ∈ {1, 3}",
                "R2": "Se aplica cuando DOS CRUCES tienen pares (over, under) AMBOS consecutivos: |o1-o2| mod 4 ∈ {1,3} Y |u1-u2| mod 4 ∈ {1,3}"
            },
            "configuraciones": self.configuraciones,
            "resumen_estadistico": self.generar_resumen_estadistico()
        }
        
        with open(archivo, 'w', encoding='utf-8') as f:
            json.dump(datos, f, indent=2, ensure_ascii=False)
        
        print(f"✅ Archivo guardado: {archivo}")
        print(f"📊 Total de configuraciones: {len(self.configuraciones)}")


if __name__ == "__main__":
    generador = GeneradorConfiguracionesFinalCorregido()
    generador.generar_todas_configuraciones()
    
    # Guardar en archivo
    archivo_salida = r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\configuraciones_2_cruces_24_FINAL.json"
    generador.guardar_json(archivo_salida)
    
    # Mostrar resumen
    resumen = generador.generar_resumen_estadistico()
    print("\n" + "="*70)
    print("RESUMEN ESTADÍSTICO (CON R1 Y R2 CORRECTOS)")
    print("="*70)
    print(f"Total de configuraciones: {resumen['total_configuraciones']}")
    print(f"Nudos triviales: {resumen['nudos_triviales']}")
    print(f"Nudos no triviales: {resumen['nudos_no_triviales']}")
    print(f"Configuraciones con R1 aplicable: {resumen['con_r1_aplicable']}")
    print(f"Configuraciones con R2 aplicable: {resumen['con_r2_aplicable']}")
    print(f"Configuraciones con R1 o R2: {resumen['con_r1_o_r2']}")
    print(f"\nDistribución de writhe: {resumen['distribucion_writhe']}")
    print(f"Distribución de clases: {resumen['distribucion_clases']}")
    
    # Mostrar ejemplos de R2
    print("\n" + "="*70)
    print("EJEMPLOS DE CONFIGURACIONES CON R2 APLICABLE")
    print("="*70)
    count = 0
    for c in generador.configuraciones:
        if "R2" in c['etapa2_esperado']['movimientos_aplicables']:
            print(f"\n{c['nombre']}: {c['notacion_pares_ordenados']}")
            print(f"  Permutación: {c['permutacion']}")
            p1, p2 = c['pares_ordenados']
            print(f"  Cruce 1: over={p1['over']}, under={p1['under']}")
            print(f"  Cruce 2: over={p2['over']}, under={p2['under']}")
            print(f"  Overs consecutivos: {c['r2_info']['overs_consecutivos']}")
            print(f"  Unders consecutivos: {c['r2_info']['unders_consecutivos']}")
            print(f"  → R2 APLICABLE")
            count += 1
            if count >= 5:
                break
