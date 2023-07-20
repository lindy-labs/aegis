# sierra-lean represents Sierra programs in Lean 4

## Usage

```lean
import SierraLean.Commands

-- Load a Sierra file
sierra_load_file "SierraLean/Tests/foo.sierra"

-- Provide the specification of the function double
sierra_spec "foo::foo::double" := fun _ a ρ => ρ = a * a

-- Prove the correctness of the specification
sierra_sound "foo::foo::double" := fun _ a ρ => by
  rintro rfl
  rfl

-- Check that we have verified all functions exported by the Sierra file, otherwise
-- print an error message listing the missing proofs
sierra_complete
```

Further example usage can be found in `SierraLean.Tests.Commands`.

## To-Dos

* A few Libfuncs are not implemented yet, a list can be found in `libfuncs_todo`
* There is no mechanism yet for giving and using polymorphic specifications for polymorphic Cairo functions
* A few libfunc specifications might be improved in the future to streamline proofs
