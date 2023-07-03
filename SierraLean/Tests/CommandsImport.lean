import SierraLean.Tests.Commands

sierra_spec "test::bar" := fun _ a b ρ => (ρ : Bool) = xor a b

sierra_sound "test::bar" := fun _ a b ρ => by
  aesop
