import SierraLean.Commands

namespace Sierra

sierra_load_file "SierraLean/Tests/ternary_add.sierra"

sierra_spec "ternary_add" := fun a b c ρ =>
  @Eq.{1} Sierra.F ρ
    (@HAdd.hAdd.{0, 0, 0} Sierra.F Sierra.F Sierra.F
      (@instHAdd.{0} Sierra.F
        (@Distrib.toAdd.{0} Sierra.F
          (@NonUnitalNonAssocSemiring.toDistrib.{0} Sierra.F
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Sierra.F
              (@NonAssocRing.toNonUnitalNonAssocRing.{0} Sierra.F
                (@Ring.toNonAssocRing.{0} Sierra.F (@CommRing.toRing.{0} Sierra.F (ZMod.commRing Sierra.PRIME))))))))
      (@HAdd.hAdd.{0, 0, 0} Sierra.F Sierra.F Sierra.F
        (@instHAdd.{0} Sierra.F
          (@Distrib.toAdd.{0} Sierra.F
            (@NonUnitalNonAssocSemiring.toDistrib.{0} Sierra.F
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Sierra.F
                (@NonAssocRing.toNonUnitalNonAssocRing.{0} Sierra.F
                  (@Ring.toNonAssocRing.{0} Sierra.F (@CommRing.toRing.{0} Sierra.F (ZMod.commRing Sierra.PRIME))))))))
        a b)
      c)

sierra_sound "ternary_add" := _
