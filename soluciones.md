# Apunte: Optimizando la máquina virtual #

## Opcional 6 ##

Para poder ignorar un valor y no introducirlo al entorno, habría que quitar el SHIFT (y consecuentemente el DROP) al momento de compilar un término si la variable comienza con "_".
Pero esto trae el problema de que podemos no agregar los valores al entorno pero de todas formas quedan en el stack. Y si el código está dentro de una función, cuyo stack debe terminar con 1 sólo valor y luego la RA, este invariante ya no se cumplirá.
