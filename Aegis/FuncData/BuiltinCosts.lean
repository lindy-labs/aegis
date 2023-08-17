import Aegis.FuncDataUtil

open Qq Lean
namespace Sierra

/- Make `Identifier` and `Parameter` quotable. -/
mutual

partial def Parameter.quote : Parameter → Q(Parameter)
| .identifier i => q(.identifier $(Identifier.quote i))
| .const n => q(.const $n)
| .usertype i => q(.usertype $(Identifier.quote i))
| .userfunc i => q(.userfunc $(Identifier.quote i))
| .libfunc i => q(.libfunc $(Identifier.quote i))
| .tuple ps => ParameterList.quote ps

partial def ParameterList.quote : List Parameter → Q(List Parameter)
| [] => q([])
| p::ps => q($(Parameter.quote p) :: $(ParameterList.quote ps))

partial def Identifier.quote : Identifier → Q(Identifier)
| .ref n => q(.ref $n)
| .name n ps tl => q(.name $n $(ParameterList.quote ps) $(OptionIdentifier.quote tl))

partial def OptionIdentifier.quote : Option Identifier → Q(Option Identifier)
| .none => q(.none)
| .some i => q(.some $(Identifier.quote i))

end

instance : ToExpr Identifier := ⟨Identifier.quote, q(Identifier)⟩
instance : ToExpr Parameter := ⟨Parameter.quote, q(Parameter)⟩

namespace FuncData

variable (currentFunc : Identifier) (metadataRef : FVarId)

def get_builtin_costs : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.BuiltinCosts]
                 condition := fun (ρ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   q($ρ = ($m).costs $currentFunc) }]

def builtinCostsLibfuncs : Identifier → Option FuncData
| .name "get_builtin_costs" [] .none => get_builtin_costs currentFunc metadataRef
| _ => .none
