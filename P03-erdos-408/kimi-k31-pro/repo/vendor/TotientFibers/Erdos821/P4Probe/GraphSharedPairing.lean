module

public import Erdos821.P4Probe.SharedPairingTask
public import Erdos821.P4Probe.PatternMasses
public import Erdos821.P4Probe.BigAveraging

@[expose] public section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

local instance graphSharedSiteDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (BigSite P M) := Classical.decEq _

end
end Erdos821.P4Probe
