# sierra-lean represents Sierra programs in Lean 4

## Design considerations

* Create specs as Lean 4 *code* or should we simply directly add them to the environment, without
generating Lean *files*?
* What's the best way to get the semantics of all the libfuncs?
* Need a substitution calculus (example: `rename([1]) -> ([2])`)
* Use custom reader monad and output existential closure?
