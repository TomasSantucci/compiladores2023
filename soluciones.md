# Apunte: Compilación a máquina virtual

## e - comparación de ack en C y la Macchina

Resultados en C: 0,6 s

Resultados en la Macchina (con TAILCALL): 4m59s

La gran discrepancia que se obtiene se debe principalmente a: en C el código se compila directamente 
a intrucciones assembler las cuales son rápidas. En cambio en la macchina se traduce a instrucciones
de una máquina virtual que deben ser ejecutadas una a una con un programa hecho en Haskell que no es
de bajo nivel como C.

# Apunte: Optimizando la máquina virtual

## 3

Verificamos la mejora en uso de memoria con el test 003-fib.
Se consigue un tamaño máximo del stack de 4, sin importar el índice de fibonacci que se quiera calcular.

## Opcional 6

Para poder ignorar un valor y no introducirlo al entorno, habría que quitar el SHIFT (y consecuentemente el DROP) al momento de compilar un término si la variable comienza con "_".
Pero esto trae el problema de que podemos no agregar los valores al entorno pero de todas formas quedan en el stack. Y si el código está dentro de una función, cuyo stack debe terminar con 1 sólo valor y luego la RA, este invariante ya no se cumplirá.

## Opcional 8

Con la máquina optimizada obtenemos un bytecode que contiene el siguiente fragmento:

FUNCTION len=5; ACCESS 1; ACCESS 0; TAILCALL; FIX;

Sin usar tailcalls:

FUNCTION len=5; ACCESS 1; ACCESS 0; CALL; RETURN; FIX;

En este último, cada vez que se llega a la operación CALL se agrega la RA correspondiente, al stack.
Luego se vuelve a repetir el mismo fragmento y de esta forma se va utilizando cada vez más memoria.

Con la operación TAILCALL sucede otra cosa. Cada vez que se ejecuta la operación TAILCALL, se salta al
código correspondiente (el mismo desde el principio) pero no se agrega ninguna RA porque se usará la misma
que ya se guardó antes. De esta forma obtenemos un uso de memoria constante.