# Manual Push - Guía de Uso

## Script: manual-push.ps1

Script interactivo para hacer push manual al repositorio TME_Nudos en GitHub.

## Ubicación

```
C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Procesos\Scripts\manual-push.ps1
```

## Uso

### Opción 1: Desde el directorio raíz del proyecto

```powershell
cd C:\Users\pablo\OneDrive\Documentos\TME_Nudos
.\Procesos\Scripts\manual-push.ps1
```

### Opción 2: Ejecutar directamente

```powershell
C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Procesos\Scripts\manual-push.ps1
```

## Flujo del Script

1. **Verificación de directorio**
   - Confirma que estás en TME_Nudos
   - Opción de continuar si no lo estás

2. **Mostrar estado**
   - Lista archivos modificados
   - Muestra cambios pendientes

3. **Confirmación**
   - Pregunta si deseas continuar
   - Opción de cancelar

4. **Mensaje de commit**
   - Solicita mensaje personalizado
   - Usa mensaje por defecto si no ingresas nada
   - Formato: "update: cambios manuales YYYY-MM-DD HH:mm"

5. **Ejecución Git**
   - `git add -A` - Agrega todos los cambios
   - `git commit -m "mensaje"` - Crea commit
   - `git pull --rebase origin master` - Actualiza desde GitHub
   - `git push origin master` - Sube cambios

6. **Reporte final**
   - Muestra resultado de cada paso
   - Link al repositorio
   - Timestamp
   - Último commit

## Características

### ✅ Seguridad
- Confirmación antes de cada acción
- Verificación de errores en cada paso
- Pull antes de push para evitar conflictos

### ✅ Información
- Muestra archivos modificados
- Reporta progreso de cada paso
- Indica errores claramente

### ✅ Flexibilidad
- Mensaje de commit personalizado
- Mensaje por defecto automático
- Opción de cancelar en cualquier momento

## Ejemplos de Uso

### Ejemplo 1: Push con mensaje personalizado

```powershell
PS> .\Procesos\Scripts\manual-push.ps1

🚀 Push Manual a GitHub - TME_Nudos
=====================================

📊 Estado actual del repositorio:
 M TMENudos/TCN_01_Fundamentos.lean
 M README.md

📝 Archivos modificados:
 M TMENudos/TCN_01_Fundamentos.lean
 M README.md

¿Deseas hacer commit y push de estos cambios? (s/n): s

💬 Ingresa el mensaje del commit:
   (Presiona Enter para usar mensaje por defecto)
Mensaje: fix: corregir teorema gap_mirror

🔄 Ejecutando comandos Git...
1️⃣  git add -A
   ✅ Archivos agregados al staging area
2️⃣  git commit -m "fix: corregir teorema gap_mirror"
   ✅ Commit creado exitosamente
3️⃣  git pull --rebase origin master
   ✅ Repositorio actualizado desde GitHub
4️⃣  git push origin master
   ✅ Cambios pusheados a GitHub exitosamente

=====================================
✅ Push completado exitosamente
=====================================

📍 Repositorio: https://github.com/PabloeCancino/TME_Nudos
🕐 Timestamp: 2025-12-25 19:25:30

📌 Último commit:
abc1234 fix: corregir teorema gap_mirror
```

### Ejemplo 2: Push con mensaje por defecto

```powershell
PS> .\Procesos\Scripts\manual-push.ps1

...
💬 Ingresa el mensaje del commit:
   (Presiona Enter para usar mensaje por defecto)
Mensaje: [Enter]
   Usando mensaje por defecto: update: cambios manuales 2025-12-25 19:25
...
```

### Ejemplo 3: Cancelar operación

```powershell
PS> .\Procesos\Scripts\manual-push.ps1

...
¿Deseas hacer commit y push de estos cambios? (s/n): n
❌ Operación cancelada por el usuario
```

## Manejo de Errores

### Error: Conflictos durante pull

```
⚠️  Conflictos detectados durante el pull
   Resuelve los conflictos manualmente y ejecuta:
   git rebase --continue
   Luego ejecuta este script nuevamente
```

**Solución:**
1. Resolver conflictos en los archivos marcados
2. `git add <archivos-resueltos>`
3. `git rebase --continue`
4. Ejecutar script nuevamente

### Error: Push rechazado

```
❌ Error en git push
   Posibles causas:
   - Problemas de conexión
   - Permisos insuficientes
   - Cambios en el repositorio remoto
```

**Solución:**
1. Verificar conexión a internet
2. Verificar credenciales de GitHub
3. Ejecutar `git pull --rebase` manualmente
4. Intentar nuevamente

## Comandos Equivalentes Manuales

Si prefieres ejecutar los comandos manualmente:

```powershell
# 1. Agregar cambios
git add -A

# 2. Crear commit
git commit -m "tu mensaje aquí"

# 3. Actualizar desde GitHub
git pull --rebase origin master

# 4. Subir cambios
git push origin master
```

## Notas

- El script está en `Procesos/Scripts/` que está excluido del repositorio público
- Los cambios se suben a la rama `master`
- Se usa `--rebase` para mantener un historial limpio
- El script verifica errores en cada paso

## Alternativas

### quick-backup.ps1
Para backups automáticos con timestamp:
```powershell
.\Procesos\Scripts\quick-backup.ps1
```

### git-backup.ps1
Para backups programados:
```powershell
.\Procesos\Scripts\git-backup.ps1
```

---

*Guía creada: 2025-12-25*  
*Script: manual-push.ps1*
