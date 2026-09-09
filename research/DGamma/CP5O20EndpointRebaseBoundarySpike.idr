module DGamma.CP5O20EndpointRebaseBoundarySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Identity name transport preserves an arbitrary provider word. This
||| structural proof is used for all four native lifecycle constructors.
export
0 o20IdentityProviderWord :
  {name : Type} -> (providers : List name) ->
  (map (renameForward (identityNameBijection {name})) providers = providers)
o20IdentityProviderWord [] = Refl
o20IdentityProviderWord (provider :: rest) = cong (provider ::) (o20IdentityProviderWord rest)
