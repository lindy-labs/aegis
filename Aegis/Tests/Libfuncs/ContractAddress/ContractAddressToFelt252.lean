import Aegis.Commands

namespace Sierra.Test.ContractAddress.ContractAddressToFelt252

aegis_load_file "../../e2e_libfuncs/contract_address_aegis/contract_address_to_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "test::foo" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_complete
