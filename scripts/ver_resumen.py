import json

# Cargar archivo
with open(r"c:\Users\pablo\OneDrive\Documentos\TME_Nudos\data\configuraciones_2_cruces_24_FINAL.json", 'r', encoding='utf-8') as f:
    datos = json.load(f)

resumen = datos['resumen_estadistico']

print("="*70)
print("RESUMEN FINAL CON R1 Y R2 CORRECTOS")
print("="*70)
print(f"Triviales: {resumen['nudos_triviales']}")
print(f"No triviales: {resumen['nudos_no_triviales']}")
print(f"Con R1: {resumen['con_r1_aplicable']}")
print(f"Con R2: {resumen['con_r2_aplicable']}")
print(f"Con R1 o R2: {resumen['con_r1_o_r2']}")
