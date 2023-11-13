<img src="./images/logo_white.png" alt="" width="500" >

Aegis is a tool for the verification of Cairo code.

## Usage

```lean
import Aegis.Commands

-- Load a Sierra file
aegis_load_file "Aegis/Tests/foo.sierra"

-- Provide the specification of the function double
aegis_spec "foo::foo::double" :=
  fun _ a ρ => ρ = a * a

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

## To-Dos

* A few Libfuncs are not implemented yet, a list can be found in `libfuncs_todo`
* There is no mechanism yet for giving and using polymorphic specifications for polymorphic Cairo functions
* A few libfunc specifications might be improved in the future to streamline proofs

## Contact

For any questions about Aegis, contact [javra](mailto:jakob@lindylabs.net).

