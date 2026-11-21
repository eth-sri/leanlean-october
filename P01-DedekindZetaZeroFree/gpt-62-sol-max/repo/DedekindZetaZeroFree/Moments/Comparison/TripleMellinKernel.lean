module

public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section







def comparisonRealPower (Z : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log Z : ℂ))


end
end DedekindZetaZeroFree
