"""
Script de Analisis para configuraciones_nudos_k3.json

Este script analiza todas las configuraciones en el archivo k3,
calcula sus IMEs, detecta equivalencias y genera un reporte.
"""

from clasificador_ime import ClasificadorIME, ConfiguracionRacional, calcular_ime
import json
from pathlib import Path
from collections import defaultdict


def analizar_base_datos_k3():
    """Analiza todas las configuraciones en configuraciones_nudos_k3.json"""
    
    # Rutas de archivos
    base_dir = Path(__file__).parent
    archivo_entrada = base_dir / "configuraciones_nudos_k3.json"
    archivo_salida = base_dir / "resultados_clasificacion_k3.json"
    
    print("=" * 70)
    print("ANALISIS DE CONFIGURACIONES K3 - Sistema IME")
    print("=" * 70)
    print(f"\nArchivo de entrada: {archivo_entrada}")
    print(f"Archivo de salida: {archivo_salida}")
    
    # Verificar que existe el archivo
    if not archivo_entrada.exists():
        print(f"\n[ERROR] No se encuentra el archivo: {archivo_entrada}")
        return
    
    # Cargar datos
    print("\n[1/4] Cargando configuraciones...")
    with open(archivo_entrada, 'r', encoding='utf-8') as f:
        configuraciones = json.load(f)
    
    print(f"  Total de configuraciones: {len(configuraciones)}")
    
    # Crear clasificador (con la misma base de datos para buscar equivalentes)
    print("\n[2/4] Inicializando clasificador...")
    clasificador = ClasificadorIME(str(archivo_entrada))
    
    # Analizar cada configuración
    print("\n[3/4] Analizando configuraciones...")
    resultados = []
    equivalencias = defaultdict(list)  # {ime_normalizado: [ids]}
    configuraciones_normalizadas = {}  # {ime_normalizado: configuracion_normalizada}
    familias = defaultdict(int)  # {familia: count}
    
    for i, config_dict in enumerate(configuraciones, 1):
        if i % 100 == 0:
            print(f"  Procesadas: {i}/{len(configuraciones)}")
        
        try:
            # Clasificar
            resultado = clasificador.clasificar_desde_json(config_dict)
            
            # Obtener configuración normalizada
            config_str = config_dict.get("configuracion_Racional", "[]")
            pares = json.loads(config_str.replace("'", '"'))
            config_obj = ConfiguracionRacional(pares, normalizar=True)
            config_normalizada = config_obj.pares
            
            # Guardar resultado
            resultado_dict = {
                "id": config_dict.get("id"),
                "num_cruces": resultado.n_cruces,
                "configuracion_original": config_dict.get("configuracion_Racional"),
                "configuracion_normalizada": config_normalizada,
                "ime": resultado.ime,
                "ime_normalizado": resultado.ime_normalizado,
                "es_reducible": resultado.es_reducible,
                "familia": resultado.familia,
                "num_equivalentes": len(resultado.equivalentes_encontrados),
                "ids_equivalentes": [eq["id"] for eq in resultado.equivalentes_encontrados]
            }
            resultados.append(resultado_dict)
            
            # Agrupar por IME normalizado (para detectar equivalencias)
            ime_key = str(resultado.ime_normalizado)
            equivalencias[ime_key].append(config_dict.get("id"))
            
            # Guardar configuración normalizada representativa de esta clase
            if ime_key not in configuraciones_normalizadas:
                configuraciones_normalizadas[ime_key] = config_normalizada
            
            # Contar familias
            familias[resultado.familia] += 1
            
        except Exception as e:
            print(f"  [ERROR] Config ID {config_dict.get('id')}: {e}")
            continue

    
    print(f"  [OK] Procesadas: {len(resultados)}/{len(configuraciones)} configuraciones")
    
    # Generar estadísticas
    print("\n[4/4] Generando estadisticas...")
    
    estadisticas = {
        "total_configuraciones": len(resultados),
        "total_familias": len(familias),
        "distribucion_familias": dict(familias),
        "clases_equivalencia": len([ids for ids in equivalencias.values() if len(ids) > 1]),
        "configuraciones_unicas": len([ids for ids in equivalencias.values() if len(ids) == 1])
    }
    
    # Guardar resultados
    print(f"\nGuardando resultados en: {archivo_salida}")
    salida = {
        "estadisticas": estadisticas,
        "configuraciones": resultados
    }
    
    with open(archivo_salida, 'w', encoding='utf-8') as f:
        json.dump(salida, f, indent=2, ensure_ascii=False)
    
    print(f"[OK] Resultados guardados")
    
    # Mostrar resumen
    print("\n" + "=" * 70)
    print("RESUMEN DE ANALISIS")
    print("=" * 70)
    print(f"\nTotal analizadas: {estadisticas['total_configuraciones']}")
    print(f"Configuraciones unicas (IME): {estadisticas['configuraciones_unicas']}")
    print(f"Clases de equivalencia: {estadisticas['clases_equivalencia']}")
    print(f"\nDistribucion por familias:")
    for familia, count in sorted(familias.items(), key=lambda x: -x[1])[:10]:
        print(f"  {familia}: {count}")
    
    # Mostrar algunos ejemplos de equivalencias
    print(f"\n{'-' * 70}")
    print("EJEMPLOS DE NUDOS EQUIVALENTES (misma clase de isotopia)")
    print(f"{'-' * 70}")
    
    ejemplos_mostrados = 0
    for ime_key, ids in equivalencias.items():
        if len(ids) > 1 and ejemplos_mostrados < 5:
            config_normalizada = configuraciones_normalizadas[ime_key]
            print(f"\nClase {ejemplos_mostrados + 1} {config_normalizada}: IME = {ime_key}")
            print(f"  IDs equivalentes: {ids[:10]}" + (" ..." if len(ids) > 10 else ""))
            print(f"  Total en esta clase: {len(ids)}")
            ejemplos_mostrados += 1

    
    print("\n" + "=" * 70)
    print("[OK] Analisis completado exitosamente")
    print("=" * 70)


def mostrar_configuracion_especifica(config_id: int):
    """Muestra analisis detallado de una configuracion especifica"""
    
    base_dir = Path(__file__).parent
    archivo_entrada = base_dir / "configuraciones_nudos_k3.json"
    
    with open(archivo_entrada, 'r', encoding='utf-8') as f:
        configuraciones = json.load(f)
    
    # Buscar configuracion
    config_dict = None
    for cfg in configuraciones:
        if cfg.get("id") == config_id:
            config_dict = cfg
            break
    
    if not config_dict:
        print(f"[ERROR] No se encontro configuracion con ID {config_id}")
        return
    
    # Clasificar
    clasificador = ClasificadorIME(str(archivo_entrada))
    resultado = clasificador.clasificar_desde_json(config_dict)
    
    # Mostrar detalles
    print("\n" + "=" * 70)
    print(f"ANALISIS DETALLADO - Configuracion ID: {config_id}")
    print("=" * 70)
    print(f"\nConfiguracion: {config_dict.get('configuracion_Racional')}")
    print(f"\nIME: {resultado.ime}")
    print(f"IME Normalizado: {resultado.ime_normalizado}")
    print(f"Numero de cruces: {resultado.n_cruces}")
    print(f"Es reducible: {resultado.es_reducible}")
    print(f"Familia: {resultado.familia}")
    
    if resultado.equivalentes_encontrados:
        print(f"\n[OK] Equivalentes encontrados: {len(resultado.equivalentes_encontrados)}")
        print("\nPrimeros 5 equivalentes:")
        for i, eq in enumerate(resultado.equivalentes_encontrados[:5], 1):
            print(f"  {i}. ID: {eq['id']}")
            print(f"     Config: {eq['configuracion']}")
            print(f"     IME: {eq['ime']}")
    else:
        print("\n[X] No se encontraron equivalentes")
    
    if resultado.similares:
        print(f"\nTop 3 configuraciones similares:")
        for i, sim in enumerate(resultado.similares[:3], 1):
            print(f"  {i}. ID: {sim['id']}, Score: {sim['score_similitud']:.3f}")
            print(f"     IME: {sim['ime']}")


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1:
        # Si se pasa un ID como argumento, mostrar solo esa configuracion
        try:
            config_id = int(sys.argv[1])
            mostrar_configuracion_especifica(config_id)
        except ValueError:
            print("[ERROR] El ID debe ser un numero entero")
    else:
        # Analizar toda la base de datos
        analizar_base_datos_k3()
