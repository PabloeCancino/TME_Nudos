"""
Script de Demostración del Clasificador IME

Ejemplos de uso del sistema de clasificación de nudos mediante IME.
Demuestra todas las funcionalidades principales.
"""

from clasificador_ime import (
    ClasificadorIME,
    ConfiguracionRacional,
    calcular_ime,
    son_equivalentes
)
import json
from pathlib import Path


def ejemplo_1_calcular_ime():
    """Ejemplo 1: Calcular IME de una configuración simple."""
    print("=" * 70)
    print("EJEMPLO 1: Cálculo del IME")
    print("=" * 70)
    
    # Nudo trébol (3 cruces)
    trebol = [[1, 4], [2, 5], [3, 6]]
    
    print(f"\nConfiguración (trébol): {trebol}")
    
    ime = calcular_ime(trebol)
    print(f"IME calculado: {ime}")
    
    config = ConfiguracionRacional(trebol)
    print(f"IME normalizado: {config.calcular_ime_normalizado()}")
    print(f"¿Es reducible?: {config.es_reducible()}")
    print(f"Familia: {config.get_familia()}")


def ejemplo_2_detectar_equivalencia():
    """Ejemplo 2: Detectar nudos equivalentes bajo rotación."""
    print("\n" + "=" * 70)
    print("EJEMPLO 2: Detección de Equivalencia")
    print("=" * 70)
    
    # Trébol en diferentes rotaciones
    trebol_1 = [[1, 4], [2, 5], [3, 6]]
    trebol_2 = [[3, 6], [4, 1], [5, 2]]  # Rotado
    trebol_3 = [[5, 2], [6, 3], [1, 4]]  # Otra rotación
    
    print(f"\nConfiguración 1: {trebol_1}")
    print(f"Configuración 2: {trebol_2}")
    print(f"Configuración 3: {trebol_3}")
    
    print(f"\nIME 1: {calcular_ime(trebol_1)}")
    print(f"IME 2: {calcular_ime(trebol_2)}")
    print(f"IME 3: {calcular_ime(trebol_3)}")
    
    # Verificar equivalencia
    print(f"\nConfig 1 == Config 2?: {son_equivalentes(trebol_1, trebol_2)}")
    print(f"Config 1 == Config 3?: {son_equivalentes(trebol_1, trebol_3)}")
    print(f"Config 2 == Config 3?: {son_equivalentes(trebol_2, trebol_3)}")

    
    # Mostrar IME normalizado (debe ser igual para todos)
    config1 = ConfiguracionRacional(trebol_1)
    config2 = ConfiguracionRacional(trebol_2)
    config3 = ConfiguracionRacional(trebol_3)
    
    print(f"\nIME Normalizado 1: {config1.calcular_ime_normalizado()}")
    print(f"IME Normalizado 2: {config2.calcular_ime_normalizado()}")
    print(f"IME Normalizado 3: {config3.calcular_ime_normalizado()}")


def ejemplo_3_clasificacion_completa():
    """Ejemplo 3: Clasificación completa de una configuración."""
    print("\n" + "=" * 70)
    print("EJEMPLO 3: Clasificación Completa")
    print("=" * 70)
    
    # Base de datos
    db_path = Path(__file__).parent / "configuraciones_nudos.json"
    
    if not db_path.exists():
        print(f"\n[!] Base de datos no encontrada: {db_path}")
        print("Continuando sin base de datos...")

        clasificador = ClasificadorIME()
    else:
        clasificador = ClasificadorIME(str(db_path))
    
    # Clasificar una configuración
    config_test = [[1, 6], [2, 7], [3, 8], [4, 5]]
    
    print(f"\nConfiguración a clasificar: {config_test}")
    
    resultado = clasificador.clasificar(config_test)
    
    print(f"\n{'-' * 70}")
    print("RESULTADO DE LA CLASIFICACION:")
    print(f"{'-' * 70}")

    print(f"  IME: {resultado.ime}")
    print(f"  IME Normalizado: {resultado.ime_normalizado}")
    print(f"  Número de cruces: {resultado.n_cruces}")
    print(f"  ¿Es reducible?: {resultado.es_reducible}")
    print(f"  Familia: {resultado.familia}")
    
    if resultado.equivalentes_encontrados:
        print(f"\n  [OK] Equivalentes encontrados: {len(resultado.equivalentes_encontrados)}")
        for eq in resultado.equivalentes_encontrados[:3]:
            print(f"    - ID: {eq['id']}, Config: {eq['configuracion'][:50]}...")
    else:
        print("  [X] No se encontraron equivalentes en la base de datos")

    
    if resultado.similares:
        print(f"\n  Top 3 nudos similares:")
        for sim in resultado.similares[:3]:
            print(f"    - ID: {sim['id']}, Score: {sim['score_similitud']:.3f}")
            print(f"      IME: {sim['ime']}")


def ejemplo_4_detectar_reducibilidad():
    """Ejemplo 4: Detectar nudos reducibles."""
    print("\n" + "=" * 70)
    print("EJEMPLO 4: Detección de Reducibilidad")
    print("=" * 70)
    
    # Nudo con bucle R1 (reducible)
    con_bucle = [[1, 2], [3, 6], [4, 5]]
    
    # Nudo irreducible
    irreducible = [[1, 4], [2, 5], [3, 6]]
    
    print(f"\nConfiguración con bucle R1: {con_bucle}")
    config1 = ConfiguracionRacional(con_bucle)
    print(f"  IME: {config1.calcular_ime()}")
    print(f"  ¿Es reducible?: {config1.es_reducible()}")
    print(f"  Familia: {config1.get_familia()}")
    
    print(f"\nConfiguración irreducible (trébol): {irreducible}")
    config2 = ConfiguracionRacional(irreducible)
    print(f"  IME: {config2.calcular_ime()}")
    print(f"  ¿Es reducible?: {config2.es_reducible()}")
    print(f"  Familia: {config2.get_familia()}")


def ejemplo_5_clasificacion_por_familias():
    """Ejemplo 5: Agrupar nudos por familias."""
    print("\n" + "=" * 70)
    print("EJEMPLO 5: Clasificación por Familias")
    print("=" * 70)
    
    configuraciones = [
        [[1, 4], [2, 5], [3, 6]],           # Trébol (irreducible)
        [[1, 6], [2, 7], [3, 8], [4, 5]],   # 4 cruces
        [[1, 2], [3, 6], [4, 5]],           # Reducible (bucle)
        [[3, 6], [4, 1], [5, 2]],           # Trébol rotado
        [[1, 8], [2, 9], [3, 10], [4, 5], [6, 7]],  # 5 cruces
    ]
    
    clasificador = ClasificadorIME()
    familias = clasificador.agrupar_por_familias(configuraciones)
    
    print(f"\nNúmero de familias encontradas: {len(familias)}\n")
    
    for familia, configs in familias.items():
        print(f"  Familia '{familia}':")
        print(f"    - Miembros: {len(configs)}")
        for i, config in enumerate(configs, 1):
            print(f"      {i}. Config: {config['configuracion']}")
            print(f"         IME: {config['ime']}")


def ejemplo_6_procesar_json():
    """Ejemplo 6: Procesar configuraciones desde JSON."""
    print("\n" + "=" * 70)
    print("EJEMPLO 6: Procesamiento desde JSON")
    print("=" * 70)
    
    db_path = Path(__file__).parent / "configuraciones_nudos.json"
    
    if not db_path.exists():
        print(f"\n[!] Base de datos no encontrada: {db_path}")

        return
    
    with open(db_path, 'r', encoding='utf-8') as f:
        datos = json.load(f)
    
    clasificador = ClasificadorIME(str(db_path))
    
    print(f"\nProcesando primeras 5 configuraciones del JSON...\n")
    
    for i, config_dict in enumerate(datos[:5], 1):
        resultado = clasificador.clasificar_desde_json(config_dict)
        
        print(f"{i}. ID: {config_dict.get('id')}, Cruces: {resultado.n_cruces}")
        print(f"   IME: {resultado.ime}")
        print(f"   Normalizado: {resultado.ime_normalizado}")
        print(f"   Reducible: {resultado.es_reducible}, Familia: {resultado.familia}")
        print()


def main():
    """Ejecuta todos los ejemplos."""
    print("\n" + "=" * 70)
    print("=" + " " * 68 + "=")
    print("=" + "  SISTEMA DE CLASIFICACION DE NUDOS MEDIANTE IME".center(68) + "=")
    print("=" + "  (Invariante Modular Estructural)".center(68) + "=")
    print("=" + " " * 68 + "=")
    print("=" * 70)

    
    try:
        ejemplo_1_calcular_ime()
        ejemplo_2_detectar_equivalencia()
        ejemplo_3_clasificacion_completa()
        ejemplo_4_detectar_reducibilidad()
        ejemplo_5_clasificacion_por_familias()
        ejemplo_6_procesar_json()
        
        print("\n" + "=" * 70)
        print("[OK] Todos los ejemplos completados exitosamente")
        print("=" * 70)
        
    except Exception as e:
        print(f"\n[ERROR] Error durante la ejecucion: {e}")

        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
