import Aegis.Commands
import Aegis.Macros

open Sierra Lean

aegis_load_file "Aegis/Tests/issue2249.sierra"

aegis_info "issue2249::issue2249::simple_test"


#eval translate (HashMap.ofList [(id!"felt252", id!"felt252"),
(id!"Box<issue2249::issue2249::Node>", id!"Box<issue2249::issue2249::Node>"),
(id!"Unit", id!"Struct<ut@Tuple>"),
(id!"core::option::Option::<core::box::Box::<issue2249::issue2249::Node>>", id!"Enum<ut@core::option::Option::<core::box::Box::<issue2249::issue2249::Node>>, Box<issue2249::issue2249::Node>, Unit>"),
(id!"issue2249::issue2249::Node", id!"Struct<ut@issue2249::issue2249::Node, felt252, core::option::Option::<core::box::Box::<issue2249::issue2249::Node>>>"),
(id!"Tuple<issue2249::issue2249::Node>", id!"Struct<ut@Tuple, issue2249::issue2249::Node>"),
(id!"core::panics::Panic", id!"Struct<ut@core::panics::Panic>"),
(id!"Array<felt252>", id!"Array<felt252>"),
(id!"Tuple<core::panics::Panic, Array<felt252>>", id!"Struct<ut@Tuple, core::panics::Panic, Array<felt252>>"),
(id!"core::panics::PanicResult::<(issue2249::issue2249::Node,)>", id!"Enum<ut@core::panics::PanicResult::<(issue2249::issue2249::Node,)>, Tuple<issue2249::issue2249::Node>, Tuple<core::panics::Panic, Array<felt252>>>"),
(id!"Snapshot<Box<issue2249::issue2249::Node>>", id!"Snapshot<Box<issue2249::issue2249::Node>>"),
(id!"Snapshot<core::option::Option::<core::box::Box::<issue2249::issue2249::Node>>>", id!"Snapshot<core::option::Option::<core::box::Box::<issue2249::issue2249::Node>>>"),
(id!"NonZero<felt252>", id!"NonZero<felt252>")])
   [] (id!"Box<issue2249::issue2249::Node>")


aegis_spec "issue2249::issue2249::simple_test" :=
  fun _ ρ => by
  simp only [SierraType.toType] at ρ
  exact True

aegis_prove "issue2249::issue2249::simple_test" :=
  fun _ ρ => by
  sorry

aegis_complete
