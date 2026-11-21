module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData
public import DedekindZetaZeroFree.Eisenstein.Induction.ConvergenceChamberAndConstantTerms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPChamberL2Defect

open MeasureTheory
open scoped ENNReal

abbrev chamber : Set ℂ := KPEisensteinChamber.chamber

theorem chamber_isOpen : IsOpen chamber := by
  exact isOpen_lt continuous_const Complex.continuous_re

section ScalarFormula
variable {G Q X H A : Type*} [Group G] [Fintype A]
  [AddCommGroup H] [Module ℂ H]

def series (lift : Q → G) (representative : X → G)
    (realize : ℂ → H →ₗ[ℂ] (G → ℂ)) (f : ℂ → H) (s : ℂ) (x : X) : ℂ :=
  ∑' q, realize s (f s) (lift q * representative x)

end ScalarFormula




section CuspOutput
variable {Y A W : Type*} [MeasurableSpace Y] [Fintype A]
  [NormedAddCommGroup W]

end CuspOutput


end DedekindZetaZeroFree.KPChamberL2Defect

end
