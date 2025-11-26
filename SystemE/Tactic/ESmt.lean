import Lean

import Smt.Tactic.Smt
import SystemE.Tactic.Attr

namespace Smt

open Lean hiding Command
open Elab Tactic

namespace Tactic

syntax (name := esmt) "esmt" smtHints : tactic

#check Tactic.evalRunTac
#check Tactic.evalTactic
#check Tactic.elabTerm

#check smtHintElem
@[tactic esmt]
def evalESmt : Tactic := fun stx => withMainContext do
  -- evalTactic (← `(tactic | dsimp at *))

  let axioms := euclidExtension.getState (← getEnv)
  let userHints ← elabHints ⟨stx[1]⟩

  let lemmaNames : Array Name := euclidExtension.getState (← getEnv)
  let axioms : Array (TSyntax `term) := lemmaNames.map (fun x => ⟨mkIdent x⟩)
  -- Manually build: smt [ax1, ax2, ax3, ...]
  evalTactic (← `(tactic| smt [$[$axioms:term],*]))
-- unexpected token ',*'; expected ']'
