# lambda_comp
Lambda calculus to C compiler.

Project for the MPRI course "Functional Programming and type systems".

The code can be found at https://github.com/fondation451/lambda_comp.

### Compilation

To compile this program, you need an installation of OCaml with the Menhir library.

Then :

```
make
```

### Cleaning directory

```
make clean
```

### Execution

```
# Direct Compilation
./joujou file.lambda

# Debug Compilation
./joujou --debug file.lambda

# Typing Compilation
./joujou --typing file.lambda
```

To run the automatic test :

```
make test
```

## The Implementation

The mandatories tasks have been implemented (CPS and Defunctionalisation).
The new instruction `ifzero` has been implemented too and follow the syntax :
```
ifzero $var then $term else $term
```

Some optional tasks have been implemented too.
* Elimination of variable to variable bindings. It is implemented in the file Defun.ml by the functions `eliminate` and `subs`.
* Typing of the lambda calculus. The algorithm used is the Algorithm W. It works fine on every example except bool.lambda. Unfortunately, we haven't been able to find out the reason. It is implemented in the files type.ml and type.mli. In the directory bad_test, you can find pretty naive example of ill-typed lambda calculus program. Typing is not done in the usual compilation process. In order to activate typing, you need to add the `--typing` option during compilation.
* Mutually recursive function. The syntax has been extend with new key words : `mutual` and `and`. It allows to express mutually recursive function. It has been done by adding begining and ending tag of mutual definition so that the CPS and the Defun round are not modified. It works fine with simple mutual definition, but when we write imbricate mutual definition (see the test file mutual2.lambda), it doesn't work. That is due to a problem in the computation of the free variable in TAIL. It has not been fixed yet. To see an example of mutual definition which works, you should look at mutual1.lambda.

The new tests which have been added are :
* cps1.lambda, cps2.lambda, cps3.lambda
* inner_def.lambda to test inner definitions of functions
* rec1.lambda, fib.lambda, triangle.lambda to test recursive functions
* mutual1.lambda, mutual2.lambda to test mutual definition of recursive functions

## Authors

* **Nicolas ASSOUAD** - *Initial work* - [fondation451](https://github.com/fondation451)
