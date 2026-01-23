"""
Generador de las 24 configuraciones de nudos de 2 cruces.
Basado en permutaciones de 4 arcos en módulo 4 (clases de equivalencia 0,1,2,3).
"""

import json
import itertools
from typing import List, Dict, Tuple

class GeneradorConfiguraciones2Cruces:
    def __init__(self):
        self.configuraciones = []
        
    def generar_todas_permutaciones(self) -> List[Tuple[int, int, int, int]]:
        """
        Genera todas las permutaciones de (0,1,2,3).
        Total: 4! = 24 permutaciones
        """
        arcos = [0, 1, 2, 3]
        return list(itertools.permutations(arcos))
    
    def determinar_orientacion_cruce(self, a1: int, a2: int) -> int:
        """
        Determina la orientación de un cruce basado en los arcos.
        Convención: si (a1 - a2) mod 4 es 1 o 2, orientación +1, sino -1
        """
        diff = (a1 - a2) % 4
        if diff in [1, 2]:
            return 1  # Positivo
        else:
            return -1  # Negativo
    
    def construir_pares_ordenados(self, perm: Tuple[int, int, int, int]) -> List[Dict]:
        """
        Construye los pares ordenados para los 2 cruces.
        Para 2 cruces en una permutación (a0, a1, a2, a3):
        - Cruce 1: (a0, a1)
        - Cruce 2: (a2, a3)
        """
        cruce1 = {
            "cruce": 1,
            "par": [perm[0], perm[1]],
            "orientacion": self.determinar_orientacion_cruce(perm[0], perm[1])
        }
        
        cruce2 = {
            "cruce": 2,
            "par": [perm[2], perm[3]],
            "orientacion": self.determinar_orientacion_cruce(perm[2], perm[3])
        }
        
        return [cruce1, cruce2]
    
    def calcular_writhe(self, pares: List[Dict]) -> int:
        """Calcula el writhe total (suma de orientaciones)."""
        return sum(p["orientacion"] for p in pares)
    
    def construir_matriz_adyacencia(self, perm: Tuple[int, int, int, int]) -> List[List[int]]:
        """
        Construye la matriz de adyacencia del grafo.
        Para simplificar, usamos una matriz 4x4 donde cada arco puede conectar al siguiente.
        """
        # Matriz básica de ciclo
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
        else:  # o1 == -1 and o2 == -1
            return "--"
    
    def es_trivial(self, pares: List[Dict]) -> bool:
        """Determina si la configuración es trivial (writhe = 0)."""
        return self.calcular_writhe(pares) == 0
    
    def generar_configuracion(self, idx: int, perm: Tuple[int, int, int, int]) -> Dict:
        """Genera una configuración completa a partir de una permutación."""
        pares = self.construir_pares_ordenados(perm)
        writhe = self.calcular_writhe(pares)
        clase_orientacion = self.clasificar_por_orientaciones(pares)
        es_trivial = self.es_trivial(pares)
        
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
                "num_componentes": 1,  # Asumimos 1 componente para simplificar
                "es_grafo_euleriano": True,
                "clasificacion": "nudo"
            },
            "etapa2_esperado": {
                "es_trivial": es_trivial,
                "writhe": writhe,
                "clasificacion_final": "nudo_trivial" if es_trivial else "nudo_no_trivial",
                "movimientos_aplicables": ["R2"] if es_trivial else []
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
        
        return {
            "total_configuraciones": total,
            "nudos_triviales": triviales,
            "nudos_no_triviales": no_triviales,
            "distribucion_writhe": writhe_dist,
            "distribucion_clases": clase_dist
        }
    
    def guardar_json(self, archivo: str):
        """Guarda las configuraciones en un archivo JSON."""
        datos = {
            "descripcion": "24 configuraciones de nudos de 2 cruces basadas en permutaciones de 4 arcos en módulo 4",
            "notacion": "Permutaciones de (0,1,2,3) generan 4! = 24 configuraciones",
            "configuraciones": self.configuraciones,
            "resumen_estadistico": self.generar_resumen_estadistico()
        }
        
        with open(archivo, 'w', encoding='utf-8') as f:
            json.dump(datos, f, indent=2, ensure_ascii=False)
        
        print(f"✅ Archivo guardado: {archivo}")
        print(f"📊 Total de configuraciones: {len(self.configuraciones)}")


if __name__ == "__main__":
    generador = GeneradorConfiguraciones2Cruces()
    generador.generar_todas_configuraciones()
    
    # Guardar en archivo
    archivo_salida = r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\configuraciones_2_cruces_24_completas.json"
    generador.guardar_json(archivo_salida)
    
    # Mostrar resumen
    resumen = generador.generar_resumen_estadistico()
    print("\n" + "="*70)
    print("RESUMEN ESTADÍSTICO")
    print("="*70)
    print(f"Total de configuraciones: {resumen['total_configuraciones']}")
    print(f"Nudos triviales (writhe=0): {resumen['nudos_triviales']}")
    print(f"Nudos no triviales: {resumen['nudos_no_triviales']}")
    print(f"\nDistribución de writhe: {resumen['distribucion_writhe']}")
    print(f"Distribución de clases: {resumen['distribucion_clases']}")
    
    # Mostrar primeras 5 configuraciones como ejemplo
    print("\n" + "="*70)
    print("PRIMERAS 5 CONFIGURACIONES (EJEMPLO)")
    print("="*70)
    for i in range(min(5, len(generador.configuraciones))):
        c = generador.configuraciones[i]
        print(f"\n{c['nombre']}: {c['notacion_pares_ordenados']}")
        print(f"  Permutación: {c['permutacion']}")
        print(f"  Clase: {c['clase_orientacion']}, Writhe: {c['writhe']}, Trivial: {c['etapa2_esperado']['es_trivial']}")
