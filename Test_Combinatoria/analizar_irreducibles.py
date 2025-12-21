"""
Análisis FILTRADO - Solo configuraciones IRREDUCIBLES

Este script muestra la verdad: solo los nudos que NO pueden 
simplificarse mediante movimientos de Reidemeister.
"""

from clasificador_ime import ClasificadorIME, ConfiguracionRacional
import json
from pathlib import Path
from collections import defaultdict


def analizar_solo_irreducibles():
    """Analiza solo las configuraciones IRREDUCIBLES"""
    
    base_dir = Path(__file__).parent
    archivo_entrada = base_dir / "configuraciones_nudos_k3.json"
    
    print("=" * 70)
    print("ANALISIS DE CONFIGURACIONES IRREDUCIBLES - Sistema IME")
    print("=" * 70)
    print(f"\nArchivo de entrada: {archivo_entrada}")
    
    if not archivo_entrada.exists():
        print(f"\n[ERROR] No se encuentra el archivo: {archivo_entrada}")
        return
    
    # Cargar datos
    print("\n[1/3] Cargando configuraciones...")
    with open(archivo_entrada, 'r', encoding='utf-8') as f:
        configuraciones = json.load(f)
    
    print(f"  Total de configuraciones: {len(configuraciones)}")
    
    # Analizar y separar
    print("\n[2/3] Clasificando en reducibles e irreducibles...")
    
    clases_irreducibles = defaultdict(list)  # {ime_normalizado: [configs irreducibles]}
    clases_reducibles = defaultdict(list)    # {ime_normalizado: [configs reducibles]}
    
    total_irreducibles = 0
    total_reducibles = 0
    
    for i, config_dict in enumerate(configuraciones, 1):
        if i % 100 == 0:
            print(f"  Procesadas: {i}/{len(configuraciones)}")
        
        try:
            config_str = config_dict.get("configuracion_Racional", "[]")
            pares = json.loads(config_str.replace("'", '"'))
            
            config_obj = ConfiguracionRacional(pares, normalizar=True)
            config_normalizada = config_obj.pares
            ime = config_obj.calcular_ime()
            ime_normalizado = config_obj.calcular_ime_normalizado()
            es_reducible = config_obj.es_reducible()
            
            ime_key = str(ime_normalizado)
            
            info = {
                "id": config_dict.get("id"),
                "configuracion_original": pares,
                "configuracion_normalizada": config_normalizada,
                "ime": ime
            }
            
            if es_reducible:
                clases_reducibles[ime_key].append(info)
                total_reducibles += 1
            else:
                clases_irreducibles[ime_key].append(info)
                total_irreducibles += 1
                
        except Exception as e:
            print(f"  [ERROR] Config ID {config_dict.get('id')}: {e}")
            continue
    
    print(f"  [OK] Procesadas: {len(configuraciones)} configuraciones")
    
    # Generar reporte
    print("\n[3/3] Generando reporte...")
    
    print("\n" + "=" * 70)
    print("ESTADISTICAS GENERALES")
    print("=" * 70)
    print(f"\nTotal configuraciones: {len(configuraciones)}")
    print(f"  IRREDUCIBLES: {total_irreducibles} ({100*total_irreducibles/len(configuraciones):.1f}%)")
    print(f"  REDUCIBLES:   {total_reducibles} ({100*total_reducibles/len(configuraciones):.1f}%)")
    print(f"\nNudos unicos (IME) irreducibles: {len(clases_irreducibles)}")
    print(f"Clases con al menos 1 reducible: {len(clases_reducibles)}")
    
    # Mostrar SOLO las clases irreducibles
    print("\n" + "=" * 70)
    print("NUDOS IRREDUCIBLES - REPRESENTANTES CANONICOS")
    print("=" * 70)
    
    if len(clases_irreducibles) == 0:
        print("\n[ATENCION] NO hay configuraciones irreducibles en los datos!")
        print("Todas las configuraciones pueden simplificarse con movimientos R1 o R2")
    else:
        for i, (ime_key, configs) in enumerate(sorted(clases_irreducibles.items()), 1):
            # Tomar la primera irreducible como representante canónico
            representante = configs[0]
            
            # Contar cuántas reducibles tienen el mismo IME
            reducibles_mismo_ime = len(clases_reducibles.get(ime_key, []))
            
            print(f"\nClase {i} {representante['configuracion_normalizada']}: IME = {ime_key}")
            print(f"  Configuraciones IRREDUCIBLES: {len(configs)}")
            print(f"  IDs irreducibles: {[c['id'] for c in configs[:10]]}" + 
                  (" ..." if len(configs) > 10 else ""))
            if reducibles_mismo_ime > 0:
                print(f"  (+ {reducibles_mismo_ime} configuraciones REDUCIBLES con mismo IME)")
    
    # Mostrar clases que SOLO tienen reducibles
    print("\n" + "=" * 70)
    print("CLASES QUE SOLO CONTIENEN REDUCIBLES")
    print("=" * 70)
    
    clases_solo_reducibles = {k: v for k, v in clases_reducibles.items() 
                              if k not in clases_irreducibles}
    
    if len(clases_solo_reducibles) == 0:
        print("\n[OK] Todas las clases de IME tienen al menos 1 irreducible")
    else:
        print(f"\n[ATENCION] Hay {len(clases_solo_reducibles)} clases IME sin representante irreducible:")
        for i, (ime_key, configs) in enumerate(sorted(clases_solo_reducibles.items())[:5], 1):
            representante = configs[0]
            print(f"\n  {i}. IME = {ime_key}")
            print(f"     Ejemplo: {representante['configuracion_normalizada']}")
            print(f"     Total reducibles: {len(configs)}")
    
    print("\n" + "=" * 70)
    print("[OK] Analisis completado")
    print("=" * 70)


if __name__ == "__main__":
    analizar_solo_irreducibles()
