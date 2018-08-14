A Haskell library for Elgot Monads
=====

This library has been developed under assistance of Dr. Sergey Goncharov at Friedrich-Alexander University
Erlangen-Nuremburg. See here for more details:

   - https://www.fau.eu/
   - https://www8.cs.fau.de/sergey

Elgot monads are monads equipped with an unguarded iterative computation.

The idea of iterative computations with side effects is explained here:

https://www.ioc.ee/~tarmo/tday-veskisilla/uustalu-slides.pdf

Imagine a function @f: X -> T (Y + X)@ where @T@ is a monad. Elgot monads
have an iteration operator with @iteration: X -> T (Y + X) -> T Y@.

An imperative way to think about this is a while loop whith a certain
condition. After each loop the condition is reevaluated and the loop either
continues or ends with the least fixpoint. The loop itself has side effects.

For example:
```
@while(b, p) (x) =
    if b(x)
        then
			do x <- p(x);
			while (b,p) (x)
	else
            η(x)@
```

Elgot monads are guarded if after each iteration step a monadic side-effect takes place.

This package includes the module "Algebra.ProcessAlgebra" which introduces the process algebra CCS by Robin Milner
https://en.wikipedia.org/wiki/Calculus_of_communicating_systems .

Processes can behave as follows:

	* produce an outgoing or wait for an ingoing action.
	* have a choice with which subsequent process to continue.
	* parallelize different processes.
	* rename actions.
	* hide actions.

In addition to all basic process operations the choice operation is improved by
the possibility to add a probability to each subprocess.
