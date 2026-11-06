module

public import ArithmeticHeights.Absolute
public import ArithmeticHeights.Arakelov
public import ArithmeticHeights.Plucker

public section

open Module

namespace Submodule

open exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)} [NumberField K]

noncomputable def arakelovMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovMulHeight (V.pluckerPoint rfl)

theorem arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint (hV : finrank K V = k) :
    V.arakelovMulHeight = Projectivization.arakelovMulHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem arakelovMulHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (plucker k v) := by
  have hV : finrank K (span K (Set.range v)) = k :=
    (finrank_span_eq_card hv).trans (Fintype.card_fin k)
  rw [arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint hV, pluckerPoint_span_range hv hV,
    Projectivization.arakelovMulHeight_mk]

end Submodule
end
