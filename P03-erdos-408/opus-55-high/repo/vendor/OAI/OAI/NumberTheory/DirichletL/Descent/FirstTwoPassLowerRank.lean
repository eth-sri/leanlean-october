module

public import OAI.NumberTheory.DirichletL.Descent.CanonicalLowerMoments
public import OAI.NumberTheory.DirichletL.Descent.FirstTwoPassParentEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicFullEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicOriginalBranches
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveParents
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)

end SevenEighths.InverseMoment

end

end OAI
