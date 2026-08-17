module DGamma.CP4ProgressProof

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNumeric
import DGamma.CP4ProgressPrecedence
import DGamma.CP4ProgressNoDeadlockFinal
import Decidable.Equality

%default total

||| Complete constructive inhabitant of the approved CP4 Theorem-66 alias.
||| Preservation supplies endpoint well-formedness, lifecycle framing carries
||| precedence acyclicity, unloading descent supplies no-deadlock, and the
||| amortized target potential supplies Equation 61.
public export
0 progressTheoremProof : progressTheorem name key value world error
progressTheoremProof nameEq keyEq bound first last trace lifecycle aligned
  wellFormed acyclic programs continuations =
  let finalWellFormed = alignedTraceWellFormedEnd nameEq keyEq trace aligned
        wellFormed
      finalAcyclic = lifecycleTracePrecedenceAcyclic nameEq keyEq trace lifecycle
        aligned acyclic
      noDeadlock = progressNoDeadlockAt nameEq keyEq last finalWellFormed
        finalAcyclic
      numeric = actorTraceEquation61 nameEq keyEq bound
  in MkProgressResult noDeadlock
    (\actor, turns, count => numeric actor trace lifecycle aligned programs
      continuations turns count)
    (maximalQuietFromNoDeadlock nameEq keyEq last noDeadlock)
