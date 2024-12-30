import Aegis.Tests.Commands
import Aegis.Tactic

aegis_spec "test::bar" := fun _ a b ρ => (ρ : Bool) = xor a b

aegis_prove "test::bar" := fun _ a b ρ => by
  aesop
