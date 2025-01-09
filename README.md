![Aegis logo](./images/logo_dark.png#gh-light-mode-only)
![Aegis logo](./images/logo_white.png#gh-dark-mode-only)

Aegis is a tool for the verification of Cairo code.

## Usage

```lean
import Aegis.Commands

-- Load a Sierra file
aegis_load_file "../foo.sierra"

-- Provide the specification of the function double
aegis_spec "foo::foo::double" :=
  fun _ a ρ => ρ = a + a

-- Prove the correctness of the specification
aegis_prove "foo::foo::double" :=
  fun _ a ρ => by
  rintro rfl
  rfl

-- Check that we have verified all functions exported by the Sierra file, otherwise
-- print an error message listing the missing proofs
aegis_complete
```

Further example usage can be found in `Aegis.Tests.Commands`.

An incomplete verification of Cairo's corelib can be found [here](https://github.com/lindy-labs/corelib_verification).

When loading your own Cairo code, it is advisable to compile it to Sierra in the following way:
* Use the `-r` option in order to keep reasonable names for identifiers instead of numbers.
* Remove all `#[inline(always)]` decorators to make the verification easier.

## To-Dos

* A few Libfuncs are not implemented yet, a list can be found in `libfuncs_todo`
* There is no mechanism yet for giving and using polymorphic specifications for polymorphic Cairo functions
* A few libfunc specifications might be improved in the future to streamline proofs

## Contributions

Feel free to contribute PRs if you find bugs or if you want to add e.g. additional tests or libfunc implementations.

## Contact

For any questions about Aegis, contact [javra](mailto:javra@lindylabs.net).

