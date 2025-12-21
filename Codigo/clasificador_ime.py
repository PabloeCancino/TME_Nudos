"""
Sistema de Clasificación de Nudos mediante IME (Invariante Modular Estructural)

Basado en la teoría formalizada en TMENudos/Basic.lean
Autor: Dr. Pablo Eduardo Cancino Marentes

Este módulo implementa:
1. Cálculo del IME desde configuraciones racionales
2. Detección de equivalencia exacta (mismo nudo bajo isotopía)
3. Métricas de similitud estructural
4. Clasificación por familias
5. Detección automática de nudos reducibles
"""

import json
from typing import List, Tuple, Dict, Optional, Set
from dataclasses import dataclass
from collections import defaultdict
from pathlib import Path



@dataclass
class ResultadoClasificacion:
    """Resultado de la clasificación de un nudo."""
    ime: List[int]
    ime_normalizado: List[int]
    n_cruces: int
    es_reducible: bool
    familia: str
    configuracion_original: List[List[int]]
    equivalentes_encontrados: List[Dict]
    similares: List[Dict]  # Lista de nudos similares con score


class ConfiguracionRacional:
    """
    Representa una configuración racional de nudos.
    
    Una configuración racional es un conjunto de pares ordenados [[o1,u1], [o2,u2], ..., [on,un]]
    donde {o1,...,on,u1,...,un} = {1,2,...,2n} (cobertura del espacio de recorrido).
    """
    
    def __init__(self, pares_ordenados: List[List[int]]):
        """
        Inicializa una configuración racional.
        
        Args:
            pares_ordenados: Lista de pares [o_i, u_i] representando cruces
            
        Raises:
            ValueError: Si la configuración no es válida
        """
        self.pares = pares_ordenados
        self.n = len(pares_ordenados)
        
        if not self._validar_configuracion():
            raise ValueError(
                f"Configuración inválida: las posiciones deben cubrir exactamente {{1,2,...,{2*self.n}}}"
            )
    
    def _validar_configuracion(self) -> bool:
        """
        Valida que la configuración cubre el espacio de recorrido.
        
        Returns:
            True si es válida, False en caso contrario
        """
        if self.n == 0:
            return True
        
        posiciones = set()
        for o, u in self.pares:
            if o == u:
                return False  # over_pos ≠ under_pos
            posiciones.add(o)
            posiciones.add(u)
        
        esperado = set(range(1, 2 * self.n + 1))
        return posiciones == esperado
    
    def calcular_ime(self) -> List[int]:
        """
        Calcula el Invariante Modular Estructural (IME).
        
        Según Basic.lean (línea 275-280):
        IME(K) = [ratio_val(c1), ratio_val(c2), ..., ratio_val(cn)]
        donde ratio_val(ci) = (ui - oi) mod 2n
        
        Returns:
            Lista de razones modulares
        """
        ime = []
        modulo = 2 * self.n
        
        for o, u in self.pares:
            # Razón modular: [o,u] = (u - o) mod 2n
            ratio = (u - o) % modulo
            ime.append(ratio)
        
        return ime
    
    def calcular_ime_normalizado(self) -> List[int]:
        """
        Calcula el IME en forma canónica (normalizado bajo rotaciones).
        
        Dos configuraciones que difieren solo por rotación cíclica tienen
        el mismo IME normalizado. La forma canónica es la rotación
        lexicográficamente mínima.
        
        Returns:
            IME normalizado (forma canónica)
        """
        ime = self.calcular_ime()
        if not ime:
            return []
        
        # Generar todas las rotaciones cíclicas
        rotaciones = [ime[i:] + ime[:i] for i in range(len(ime))]
        
        # Retornar la lexicográficamente mínima
        return min(rotaciones)
    
    def es_reducible(self) -> bool:
        """
        Detecta si el nudo es reducible (puede simplificarse por movimientos de Reidemeister).
        
        Un nudo es reducible si:
        - Tiene cruces R1: |o - u| = 1 (bucle)
        - Tiene pares R2: cruces consecutivos que se cancelan
        
        Returns:
            True si es reducible, False si es irreducible
        """
        # Detectar cruces R1 (bucles)
        for o, u in self.pares:
            if abs(o - u) == 1:
                return True
        
        # Detectar pares R2 (bigones)
        # Un par (ca, cb) es R2 si:
        # - Ady(oa, ob) y Ady(ua, ub)
        # - Los cruces están interlazados
        for i in range(len(self.pares)):
            for j in range(i + 1, len(self.pares)):
                oi, ui = self.pares[i]
                oj, uj = self.pares[j]
                
                # Verificar adyacencia
                ady_over = abs(oi - oj) == 1
                ady_under = abs(ui - uj) == 1
                
                if ady_over and ady_under:
                    # Verificar interlazado
                    if self._estan_interlazados(i, j):
                        return True
        
        return False
    
    def _estan_interlazados(self, i: int, j: int) -> bool:
        """
        Verifica si dos cruces están interlazados.
        
        Según Basic.lean (línea 368-373):
        Dos cruces están interlazados si:
        ai < aj < bi < bj  OR  aj < ai < bj < bi
        donde [ai, bi] = [min(oi,ui), max(oi,ui)]
        
        Args:
            i, j: Índices de los cruces
            
        Returns:
            True si están interlazados
        """
        oi, ui = self.pares[i]
        oj, uj = self.pares[j]
        
        ai, bi = min(oi, ui), max(oi, ui)
        aj, bj = min(oj, uj), max(oj, uj)
        
        patron1 = ai < aj < bi < bj
        patron2 = aj < ai < bj < bi
        
        return patron1 or patron2
    
    def get_familia(self) -> str:
        """
        Determina la familia del nudo basándose en características estructurales.
        
        Returns:
            Nombre de la familia
        """
        n = self.n
        ime = self.calcular_ime()
        
        if n == 0:
            return "Unknot"
        
        if self.es_reducible():
            return f"Reducible-{n}"
        
        # Detectar familias especiales
        if all(r == ime[0] for r in ime):
            return f"Uniforme-{n}"  # Todos tienen la misma razón
        
        if ime == sorted(ime):
            return f"Monotona-Creciente-{n}"
        
        if ime == sorted(ime, reverse=True):
            return f"Monotona-Decreciente-{n}"
        
        # Familia general
        return f"General-{n}"
    
    def to_dict(self) -> Dict:
        """Exporta la configuración como diccionario."""
        return {
            "n_cruces": self.n,
            "configuracion": self.pares,
            "ime": self.calcular_ime(),
            "ime_normalizado": self.calcular_ime_normalizado(),
            "es_reducible": self.es_reducible(),
            "familia": self.get_familia()
        }


class ClasificadorIME:
    """
    Clasificador de nudos racionales basado en el IME.
    
    Implementa:
    - Detección de equivalencia exacta
    - Cálculo de similitud estructural
    - Clasificación por familias
    """
    
    def __init__(self, base_datos_path: Optional[str] = None):
        """
        Inicializa el clasificador.
        
        Args:
            base_datos_path: Ruta al JSON con configuraciones conocidas
        """
        self.base_datos = []
        if base_datos_path:
            self.cargar_base_datos(base_datos_path)
    
    def cargar_base_datos(self, path: str):
        """Carga la base de datos de configuraciones conocidas."""
        with open(path, 'r', encoding='utf-8') as f:
            self.base_datos = json.load(f)
        print(f"[OK] Base de datos cargada: {len(self.base_datos)} configuraciones")

    
    def clasificar(self, pares_ordenados: List[List[int]]) -> ResultadoClasificacion:
        """
        Clasifica un nudo dado su configuración racional.
        
        Args:
            pares_ordenados: Lista de pares [[o1,u1], [o2,u2], ...]
            
        Returns:
            Resultado de la clasificación
        """
        config = ConfiguracionRacional(pares_ordenados)
        ime = config.calcular_ime()
        ime_norm = config.calcular_ime_normalizado()
        
        # Buscar equivalentes exactos en la base de datos
        equivalentes = self._buscar_equivalentes(ime_norm)
        
        # Calcular similares (top 5)
        similares = self._calcular_similares(ime, n_top=5)
        
        return ResultadoClasificacion(
            ime=ime,
            ime_normalizado=ime_norm,
            n_cruces=config.n,
            es_reducible=config.es_reducible(),
            familia=config.get_familia(),
            configuracion_original=pares_ordenados,
            equivalentes_encontrados=equivalentes,
            similares=similares
        )
    
    def clasificar_desde_json(self, config_dict: Dict) -> ResultadoClasificacion:
        """
        Clasifica desde un diccionario JSON con formato del proyecto.
        
        Args:
            config_dict: Diccionario con clave "configuracion_Racional"
            
        Returns:
            Resultado de la clasificación
        """
        # Parsear la configuración racional
        config_str = config_dict.get("configuracion_Racional", "[]")
        pares = json.loads(config_str.replace("'", '"'))
        
        return self.clasificar(pares)
    
    def _buscar_equivalentes(self, ime_normalizado: List[int]) -> List[Dict]:
        """
        Busca configuraciones equivalentes (mismo IME normalizado).
        
        Args:
            ime_normalizado: IME en forma canónica
            
        Returns:
            Lista de configuraciones equivalentes encontradas
        """
        equivalentes = []
        
        for config_dict in self.base_datos:
            try:
                config_str = config_dict.get("configuracion_Racional", "[]")
                pares = json.loads(config_str.replace("'", '"'))
                
                config = ConfiguracionRacional(pares)
                if config.calcular_ime_normalizado() == ime_normalizado:
                    equivalentes.append({
                        "id": config_dict.get("id"),
                        "num_cruces": config_dict.get("num_cruces"),
                        "configuracion": config_str,
                        "ime": config.calcular_ime()
                    })
            except:
                continue
        
        return equivalentes
    
    def _calcular_similares(self, ime: List[int], n_top: int = 5) -> List[Dict]:
        """
        Calcula los nudos más similares estructuralmente.
        
        Usa múltiples métricas:
        1. Distancia L1 entre IMEs (normalizadas)
        2. Similitud del número de cruces
        3. Similitud de distribución de razones
        
        Args:
            ime: IME del nudo a comparar
            n_top: Número de similares a retornar
            
        Returns:
            Lista de nudos similares con scores
        """
        if not self.base_datos or not ime:
            return []
        
        similitudes = []
        
        for config_dict in self.base_datos:
            try:
                config_str = config_dict.get("configuracion_Racional", "[]")
                pares = json.loads(config_str.replace("'", '"'))
                
                config = ConfiguracionRacional(pares)
                ime_otro = config.calcular_ime()
                
                # Calcular score de similitud
                score = self._calcular_score_similitud(ime, ime_otro)
                
                similitudes.append({
                    "id": config_dict.get("id"),
                    "num_cruces": config_dict.get("num_cruces"),
                    "configuracion": config_str,
                    "ime": ime_otro,
                    "score_similitud": score
                })
            except:
                continue
        
        # Ordenar por score (mayor = más similar) y tomar top N
        similitudes.sort(key=lambda x: x["score_similitud"], reverse=True)
        return similitudes[:n_top]
    
    def _calcular_score_similitud(self, ime1: List[int], ime2: List[int]) -> float:
        """
        Calcula un score de similitud entre dos IMEs.
        
        Score compuesto:
        - 40% penalización por diferencia en número de cruces
        - 60% similitud de distribución de razones (distancia normalizada)
        
        Args:
            ime1, ime2: IMEs a comparar
            
        Returns:
            Score entre 0.0 y 1.0 (1.0 = idénticos)
        """
        n1, n2 = len(ime1), len(ime2)
        
        if n1 == 0 and n2 == 0:
            return 1.0
        
        # Componente 1: Similitud en número de cruces
        max_n = max(n1, n2)
        min_n = min(n1, n2)
        score_cruces = min_n / max_n if max_n > 0 else 0.0
        
        # Componente 2: Similitud de distribución
        # Normalizar IMEs para comparación justa
        if n1 > 0 and n2 > 0:
            # Padding con ceros para igualar longitud
            ime1_pad = ime1 + [0] * (max_n - n1)
            ime2_pad = ime2 + [0] * (max_n - n2)
            
            # Distancia L1 normalizada
            distancia = sum(abs(a - b) for a, b in zip(ime1_pad, ime2_pad))
            max_distancia = sum(max(a, b) for a, b in zip(ime1_pad, ime2_pad))
            
            score_distribucion = 1.0 - (distancia / max_distancia) if max_distancia > 0 else 1.0
        else:
            score_distribucion = 0.0
        
        # Score compuesto
        return 0.4 * score_cruces + 0.6 * score_distribucion
    
    def agrupar_por_familias(self, configuraciones: List[List[List[int]]]) -> Dict[str, List]:
        """
        Agrupa configuraciones por familias.
        
        Args:
            configuraciones: Lista de configuraciones
            
        Returns:
            Diccionario {familia: [configuraciones]}
        """
        familias = defaultdict(list)
        
        for pares in configuraciones:
            try:
                config = ConfiguracionRacional(pares)
                familia = config.get_familia()
                familias[familia].append({
                    "configuracion": pares,
                    "ime": config.calcular_ime(),
                    "ime_normalizado": config.calcular_ime_normalizado()
                })
            except:
                continue
        
        return dict(familias)


def calcular_ime(pares_ordenados: List[List[int]]) -> List[int]:
    """
    Función auxiliar para calcular el IME directamente.
    
    Args:
        pares_ordenados: Lista de pares [[o1,u1], [o2,u2], ...]
        
    Returns:
        IME (lista de razones modulares)
    """
    config = ConfiguracionRacional(pares_ordenados)
    return config.calcular_ime()


def son_equivalentes(pares1: List[List[int]], pares2: List[List[int]]) -> bool:
    """
    Verifica si dos configuraciones son equivalentes (mismo nudo).
    
    Args:
        pares1, pares2: Configuraciones a comparar
        
    Returns:
        True si representan el mismo nudo
    """
    try:
        config1 = ConfiguracionRacional(pares1)
        config2 = ConfiguracionRacional(pares2)
        
        return config1.calcular_ime_normalizado() == config2.calcular_ime_normalizado()
    except:
        return False
