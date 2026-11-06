module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.ProbeHighRowFamily


def adaptiveRowExponent (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedRowCount δ (1/2-q/δ)+Δ/4+159*ε+εm+slotMesh+7*ν
  else 1-δ+78*ε+εm

end SevenEighths.ProbeHighRowFamily

end

end OAI
