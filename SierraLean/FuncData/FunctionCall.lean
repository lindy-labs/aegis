import SierraLean.FuncDataUtil

open Qq Lean

namespace Sierra.FuncData

def function_call (i : Identifier) (userfuncs : HashMap Identifier FuncData)
  (specs : HashMap Identifier Name) : FuncData where
  inputTypes := (userfuncs.find! i).inputTypes
  branches := (userfuncs.find! i).branches.map fun bd =>
    { bd with condition := 
                match specs.find? i with
                | .none => bd.condition
                | .some n => OfInputs.abstract fun ioExprs => mkAppN (mkConst n) ioExprs.toArray }

def functionCallLibfuncs (userfuncs : HashMap Identifier FuncData)
  (specs : HashMap Identifier Name) : Identifier → Option FuncData
| .name "function_call" [.userfunc i] =>
  if userfuncs.contains i then function_call i userfuncs specs else .none
| _ => .none