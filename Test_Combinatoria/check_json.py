import json

with open('configuraciones_nudos_k3.json', 'r') as f:
    data = json.load(f)

print("Primeras 5 configuraciones del JSON:")
for d in data[:5]:
    print(f"ID {d['id']}: {d['configuracion_Racional']}")
