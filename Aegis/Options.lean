import Lean.Data.Options

open Lean Lean.Meta Lean.Option

namespace Sierra.Options

register_option aegis.normalize : Bool :=
  let descr := "Set whether to normalize conjunctions and disjunctions in the proof goal."
  { defValue := true, group := "aesop", descr := descr }

register_option aegis.contract : Bool :=
  let descr := "Set whether the proof goal of `aegis_prove` should contract equalities."
  { defValue := true, group := "aesop", descr := descr }

register_option aegis.filterUnused : Bool :=
  let descr := "Set whether to filter out intermediate variables which do not actually appear in the proof goal."
  { defValue := true, group := "aesop", descr := descr }

end Sierra.Options

namespace Lean.Option

-- TODO Isn't there a function that does this already?
def isEnabled [Monad m] [MonadOptions m] (opt : Lean.Option Bool) : m Bool :=
  return opt.get (← getOptions)

def withEnabled [Monad m] [MonadWithOptions m] (opt : Lean.Option Bool) (k : m α) :
    m α := do
  withOptions (λ opts => opt.set opts true) k
