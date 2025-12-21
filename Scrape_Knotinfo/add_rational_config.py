"""
Script para agregar el campo 'configuracion_Racional' a cada registro del DB_knotinfo.json
basado en la conversión de notación Dowker-Thistlethwaite a configuración racional.
"""

import json
import ast


def dt_to_rational_config(dt_notation_str):
    """
    Convierte notación DT a configuración racional.
    
    Args:
        dt_notation_str: String con la notación DT, ej: "[4, 6, 2]"
    
    Returns:
        String con la configuración racional, ej: "[[1,4],[3,0],[5,2]]"
    """
    # Si el campo es NULL o vacío, devolver NULL
    if not dt_notation_str or dt_notation_str == "NULL":
        return "NULL"
    
    try:
        # Parsear la lista DT
        dt = ast.literal_eval(dt_notation_str)
        
        if not dt or not isinstance(dt, list):
            return "NULL"
        
        n = len(dt)
        modulo = 2 * n
        
        config = []
        
        # Aplicar el algoritmo de conversión
        for i, a in enumerate(dt, start=1):
            # posición impar 2i-1 pasa a índice modular p = (2i-1) - 1
            p = (2 * i - 1 - 1) % modulo
            # posición par a_i pasa a índice modular q = a_i - 1
            q = (a - 1) % modulo
            config.append([p, q])
        
        # Aplicar rotación shift=1 para mejor presentación
        shift = 1
        config_rotada = [[(p + shift) % modulo, (q + shift) % modulo] for [p, q] in config]
        
        # Formatear como string JSON
        return json.dumps(config_rotada, separators=(',', ':'))
    
    except Exception as e:
        print(f"Error procesando DT notation '{dt_notation_str}': {e}")
        return "NULL"


def add_rational_config_to_db(input_file, output_file):
    """
    Lee el archivo JSON, agrega el campo configuracion_Racional después de dt_notation,
    y guarda el resultado.
    """
    print(f"Leyendo {input_file}...")
    
    with open(input_file, 'r', encoding='utf-8') as f:
        knots = json.load(f)
    
    print(f"Total de registros: {len(knots)}")
    
    # Procesar cada registro
    for i, knot in enumerate(knots, start=1):
        if i % 100 == 0:
            print(f"Procesando registro {i}/{len(knots)}...")
        
        # Obtener la notación DT
        dt_notation = knot.get("dt_notation", "NULL")
        
        # Calcular configuración racional
        config_racional = dt_to_rational_config(dt_notation)
        
        # Crear un nuevo diccionario con el campo insertado en la posición correcta
        new_knot = {}
        for key, value in knot.items():
            new_knot[key] = value
            # Insertar configuracion_Racional justo después de dt_notation
            if key == "dt_notation":
                new_knot["configuracion_Racional"] = config_racional
        
        # Reemplazar el registro original
        knots[i - 1] = new_knot
    
    print(f"Guardando en {output_file}...")
    
    # Guardar con formato bonito
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(knots, f, indent=4, ensure_ascii=False)
    
    print("¡Completado!")


if __name__ == "__main__":
    input_file = r"E:\Nudos_LEAN\Scrape_Knotinfo\DB_knotinfo.json"
    output_file = r"E:\Nudos_LEAN\Scrape_Knotinfo\DB_knotinfo_updated.json"
    
    add_rational_config_to_db(input_file, output_file)
    
    # Mostrar un ejemplo
    print("\n--- Ejemplo del primer registro ---")
    with open(output_file, 'r', encoding='utf-8') as f:
        data = json.load(f)
        if data:
            first = data[0]
            print(f"ID: {first['id']}")
            print(f"DT Notation: {first['dt_notation']}")
            print(f"Configuración Racional: {first['configuracion_Racional']}")
