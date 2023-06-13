import SierraLean.Tests.Commands

sierra_load_string "type F = felt252;

libfunc c5 = felt252_const<5>;
libfunc call_bar = function_call<user@bar>;

c5() -> ([1]);
return([1]);
call_bar([2]) -> ([3]);
return([3]);

bar@0([0]: F) -> (F);
bazz@2([2]: F) -> (F);"

sierra_spec "bazz" := fun _ _ ρ => ρ = 5

sierra_sound "bazz" := fun _ a ρ => by
  rintro ⟨r, rfl, rfl⟩
  rfl

sierra_complete
