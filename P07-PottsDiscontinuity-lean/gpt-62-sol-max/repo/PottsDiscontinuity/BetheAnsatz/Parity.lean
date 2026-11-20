module

public import PottsDiscontinuity.BetheAnsatz.Defs

@[expose] public section

namespace PottsDiscontinuity.Bethe

/-- The central index of an odd symmetric root tuple. -/
def oddCenter {n : ℕ} (h : ¬ Even n) : Fin n :=
  ⟨n / 2, by
    grind⟩

/-- The Bethe eigenvalue in the parity-appropriate branch. -/
noncomputable def parityEigenvalue {n : ℕ} (N : ℕ) (c : ℝ) (p : Fin n → ℝ) : ℂ :=
  if h : Even n then BetheAnsatz.eigenvalueRegular c p
  else BetheAnsatz.eigenvalueZero N c p (oddCenter h)

end PottsDiscontinuity.Bethe
