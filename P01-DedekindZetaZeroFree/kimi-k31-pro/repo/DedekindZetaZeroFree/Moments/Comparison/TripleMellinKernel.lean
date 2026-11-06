module

public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section

def comparisonA : ℝ := 9 / 10

def comparisonB : ℝ := 133 / 1000



def comparisonX (Z : ℝ) : ℝ := Z ^ comparisonA

def comparisonY (Z : ℝ) : ℝ := Z ^ comparisonB



def comparisonRealPower (Z : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log Z : ℂ))

def comparisonTripleVerticalIntegral (σξ σw σz : ℝ)
    (κ : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
    ∫ t : ℝ × ℝ × ℝ,
      κ ((σξ : ℂ) + (t.1 : ℂ) * Complex.I)
        ((σw : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((σz : ℂ) + (t.2.2 : ℂ) * Complex.I)

end
end DedekindZetaZeroFree
