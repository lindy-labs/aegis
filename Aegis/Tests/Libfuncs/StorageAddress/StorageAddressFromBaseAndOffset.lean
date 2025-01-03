import Aegis.Commands

namespace Sierra.Test.StorageAddress.StorageAddressFromBasAndOffset

aegis_load_file "../../e2e_libfuncs/storage_address_aegis/storage_address_from_base_and_offset.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.cast + b.toNat

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_complete
