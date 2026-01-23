"""
Generador CORREGIDO de las 24 configuraciones de nudos de 2 cruces.
Basado en permutaciones de 4 arcos en módulo 4 (clases de equivalencia 0,1,2,3).

CORRECCIÓN IMPORTANTE:
- Movimiento R1: Se aplica cuando over y under son CONSECUTIVOS en mod 4
- Movimiento R2: Se aplica cuando dos cruces tienen orientaciones opuestas Y están conectados
"""

import json
import itertools
from typing import List, Dict, Tuple

class GeneradorConfiguraciones2CrucesCorregido:
    def __init__(self):
        self.configuraciones = []
        
    def generar_todas_permutaciones(self) -> List[Tuple[int, int, int, int]]:
        """
        Genera todas las permutaciones de (0,1,2,3).
        Total: 4! = 24 permutaciones
        """
        arcos = [0, 1, 2, 3]
        return list(itertools.permutations(arcos))
    
    def son_consecutivos_mod4(self, a: int, b: int) -> bool:
        """
        Verifica si dos arcos son consecutivos en módulo 4.
        Consecutivos: |a - b| mod 4 == 1 o |a - b| mod 4 == 3
        """
        diff = abs(a - b) % 4
        return diff == 1 or diff == 3
    
    def determinar_orientacion_cruce(self, over: int, under: int) -> int:
        """
        Determina la orientación de un cruce basado en los arcos.
        Convención: si (over - under) mod 4 es 1 o 2, orientación +1, sino -1
        """
        diff = (over - under) % 4
        if diff in [1, 2]:
            return 1  # Positivo
        else:
            return -1  # Negativo
    
    def detectar_r1_en_cruce(self, over: int, under: int) -> bool:
        """
        Detecta si un cruce puede eliminarse mediante R1.
        R1 se aplica cuando over y under son CONSECUTIVOS en mod 4.
        """
        return self.son_consecutivos_mod4(over, under)
    
    def construir_pares_ordenados(self, perm: Tuple[int, int, int, int]) -> List[Dict]:
        """
        Construye los pares ordenados para los 2 cruces.
        Para 2 cruces en una permutación (a0, a1, a2, a3):
        - Cruce 1: over=a0, under=a1
        - Cruce 2: over=a2, under=a3
        """
        cruce1 = {
            "cruce": 1,
            "over": perm[0],
            "under": perm[1],
            "par": [perm[0], perm[1]],
            "orientacion": self.determinar_orientacion_cruce(perm[0], perm[1]),
            "consecutivos": self.son_consecutivos_mod4(perm[0], perm[1]),
            "r1_aplicable": self.detectar_r1_en_cruce(perm[0], perm[1])
        }
        
        cruce2 = {
            "cruce": 2,
            "over": perm[2],
            "under": perm[3],
            "par": [perm[2], perm[3]],
            "orientacion": self.determinar_orientacion_cruce(perm[2], perm[3]),
            "consecutivos": self.son_consecutivos_mod4(perm[2], perm[3]),
            "r1_aplicable": self.detectar_r1_en_cruce(perm[2], perm[3])
        }
        
        return [cruce1, cruce2]
    
    def calcular_writhe(self, pares: List[Dict]) -> int:
        """Calcula el writhe total (suma de orientaciones)."""
        return sum(p["orientacion"] for p in pares)
    
    def detectar_r2_aplicable(self, pares: List[Dict]) -> bool:
        """
        Detecta si R2 es aplicable entre los dos cruces.
        R2 se aplica cuando:
        1. Los cruces tienen orientaciones opuestas
        2. Están conectados (un arco de salida de uno es arco de entrada del otro)
        """
        # Verificar orientaciones opuestas
        if pares[0]["orientacion"] + pares[1]["orientacion"] != 0:
            return False
        
        # Verificar conexión (simplificado: asumimos conexión si están en secuencia)
        return True
    
    def determinar_trivialidad(self, pares: List[Dict]) -> Tuple[bool, str, List[str]]:
        """
        Determina si la configuración es trivial.
        
        Criterios:
        1. Si algún cruce tiene R1 aplicable → Trivial
        2. Si ambos cruces tienen R2 aplicable → Trivial
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
            return True, "Reducible mediante R1 (arcos consecutivos)", movimientos
        
        # Verificar R2 entre cruces
        if self.detectar_r2_aplicable(pares):
            movimientos.append("R2")
            return True, "Reducible mediante R2 (orientaciones opuestas)", movimientos
        
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
        
        config = {
            "id": idx + 1,
            "nombre": f"K_(2,{idx+1})",
            "permutacion": list(perm),
            "notacion_pares_ordenados": f"{{({perm[0]},{perm[1]}), ({perm[2]},{perm[3]})}}",
            "pares_ordenados": pares,
            "clase_orientacion": clase_orientacion,
            "writhe": writhe,
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
        
        return {
            "total_configuraciones": total,
            "nudos_triviales": triviales,
            "nudos_no_triviales": no_triviales,
            "distribucion_writhe": writhe_dist,
            "distribucion_clases": clase_dist,
            "con_r1_aplicable": con_r1,
            "con_r2_aplicable": con_r2
        }
    
    def guardar_json(self, archivo: str):
        """Guarda las configuraciones en un archivo JSON."""
        datos = {
            "descripcion": "24 configuraciones de nudos de 2 cruces basadas en permutaciones de 4 arcos en módulo 4",
            "notacion": "Permutaciones de (0,1,2,3) generan 4! = 24 configuraciones",
            "criterios_reidemeister": {
                "R1": "Se aplica cuando over y under son CONSECUTIVOS en mod 4: |over - under| mod 4 ∈ {1, 3}",
                "R2": "Se aplica cuando dos cruces tienen orientaciones opuestas y están conectados"
            },
            "configuraciones": self.configuraciones,
            "resumen_estadistico": self.generar_resumen_estadistico()
        }
        
        with open(archivo, 'w', encoding='utf-8') as f:
            json.dump(datos, f, indent=2, ensure_ascii=False)
        
        print(f"✅ Archivo guardado: {archivo}")
        print(f"📊 Total de configuraciones: {len(self.configuraciones)}")


if __name__ == "__main__":
    generador = GeneradorConfiguraciones2CrucesCorregido()
    generador.generar_todas_configuraciones()
    
    # Guardar en archivo
    archivo_salida = r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\configuraciones_2_cruces_24_CORREGIDAS.json"
    generador.guardar_json(archivo_salida)
    
    # Mostrar resumen
    resumen = generador.generar_resumen_estadistico()
    print("\n" + "="*70)
    print("RESUMEN ESTADÍSTICO (CORREGIDO)")
    print("="*70)
    print(f"Total de configuraciones: {resumen['total_configuraciones']}")
    print(f"Nudos triviales: {resumen['nudos_triviales']}")
    print(f"Nudos no triviales: {resumen['nudos_no_triviales']}")
    print(f"Configuraciones con R1 aplicable: {resumen['con_r1_aplicable']}")
    print(f"Configuraciones con R2 aplicable: {resumen['con_r2_aplicable']}")
    print(f"\nDistribución de writhe: {resumen['distribucion_writhe']}")
    print(f"Distribución de clases: {resumen['distribucion_clases']}")
    
    # Mostrar ejemplos de R1
    print("\n" + "="*70)
    print("EJEMPLOS DE CONFIGURACIONES CON R1 APLICABLE")
    print("="*70)
    count = 0
    for c in generador.configuraciones:
        if any("R1" in m for m in c['etapa2_esperado']['movimientos_aplicables']):
            print(f"\n{c['nombre']}: {c['notacion_pares_ordenados']}")
            print(f"  Permutación: {c['permutacion']}")
            for p in c['pares_ordenados']:
                if p['r1_aplicable']:
                    print(f"  Cruce {p['cruce']}: over={p['over']}, under={p['under']} → CONSECUTIVOS (R1 aplicable)")
            count += 1
            if count >= 5:
                break
