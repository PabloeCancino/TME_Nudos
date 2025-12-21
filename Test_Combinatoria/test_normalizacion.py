"""
Script de prueba para verificar la normalización de configuraciones
"""

from clasificador_ime import ConfiguracionRacional, calcular_ime


def test_normalizacion():
    """Prueba la función de normalización"""
    
    print("=" * 70)
    print("PRUEBA DE NORMALIZACION DE CONFIGURACIONES")
    print("=" * 70)
    
    # Caso 1: Ejemplo básico
    print("\n[Caso 1] Ejemplo basico:")
    config_original = [[1,4],[6,3],[2,5]]
    print(f"  Original: {config_original}")
    
    config = ConfiguracionRacional(config_original, normalizar=True)
    print(f"  Normalizada: {config.pares}")
    print(f"  IME: {config.calcular_ime()}")

    
    # Caso 2: Trébol
    print("\n[Caso 2] Trébol:")
    trebol_original = [[5,2],[3,6],[1,4]]
    print(f"  Original: {trebol_original}")
    
    config_trebol = ConfiguracionRacional(trebol_original, normalizar=True)
    print(f"  Normalizada: {config_trebol.pares}")
    print(f"  IME: {config_trebol.calcular_ime()}")
    
    # Caso 3: Verificar que diferentes ordenamientos dan el mismo IME normalizado
    print("\n[Caso 3] Diferentes ordenamientos del mismo nudo:")
    
    config_1 = [[1,4],[2,5],[3,6]]
    config_2 = [[3,6],[1,4],[2,5]]
    config_3 = [[2,5],[3,6],[1,4]]
    
    c1 = ConfiguracionRacional(config_1, normalizar=True)
    c2 = ConfiguracionRacional(config_2, normalizar=True)
    c3 = ConfiguracionRacional(config_3, normalizar=True)
    
    print(f"  Config 1 original: {config_1}")
    print(f"  Config 1 normalizada: {c1.pares}")
    print(f"  IME: {c1.calcular_ime()}")
    
    print(f"\n  Config 2 original: {config_2}")
    print(f"  Config 2 normalizada: {c2.pares}")
    print(f"  IME: {c2.calcular_ime()}")
    
    print(f"\n  Config 3 original: {config_3}")
    print(f"  Config 3 normalizada: {c3.pares}")
    print(f"  IME: {c3.calcular_ime()}")
    
    # Verificar que todas tienen la misma forma normalizada
    print(f"\n  Todas normalizadas son iguales? {c1.pares == c2.pares == c3.pares}")
    print(f"  Todos los IME son iguales? {c1.calcular_ime() == c2.calcular_ime() == c3.calcular_ime()}")
    
    print("\n" + "=" * 70)

    print("[OK] Pruebas completadas")
    print("=" * 70)


if __name__ == "__main__":
    test_normalizacion()
