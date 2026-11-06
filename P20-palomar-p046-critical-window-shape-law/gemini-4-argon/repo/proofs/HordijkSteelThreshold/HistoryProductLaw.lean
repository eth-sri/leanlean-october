module

public import proofs.HordijkSteelThreshold.NestedColumnHistory
public import proofs.HordijkSteelThreshold.ColumnEventProduct

@[expose] public section

namespace HordijkSteelThreshold

noncomputable def columnHistoryWeight (q : ENNReal) (sizes : ℕ → ℕ) (T d : ℕ) : ENNReal :=
  if d = 0 then q ^ sizes 0
  else if T < d then 1 - q ^ sizes T
  else q ^ sizes d - q ^ sizes (d - 1)

end HordijkSteelThreshold
