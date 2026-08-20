module DGamma.CP4DeletionIndependenceRestriction

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryModelTrace
import Decidable.Equality

%default total

||| Definition 60 is hereditary under a trace occurrence embedding.  The
||| proof-free generator projection lives in `Metatheory`; this public alias
||| gives the deletion development its standard `OccurrenceEmbedding` shape.
public export
0 restrictTraceIndependent :
  (embedding : OccurrenceEmbedding segment whole) ->
  TraceIndependent name key world error value keyEq whole ->
  TraceIndependent name key world error value keyEq segment
restrictTraceIndependent embedding independent =
  traceIndependentUnderEmbedding embedding independent
