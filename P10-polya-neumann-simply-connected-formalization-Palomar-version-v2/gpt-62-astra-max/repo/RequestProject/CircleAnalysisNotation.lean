module

public import Mathlib.Analysis.Fourier.AddCircle
public import RequestProject.PlanarNotation

/-! Notation in the angular coordinate: `∫ₚ` integrates over one period in dθ,
whereas `angleCoeff` gives a Fourier coefficient with the mean normalization. -/

public section

namespace PolyaNeumann

scoped notation3 "∫ₚ " (...) ", " r:60:(scoped f => intervalIntegral f 0 anglePeriod MeasureTheory.volume) => r
scoped notation "angleCoeff" => fourierCoeffOn Real.two_pi_pos
scoped notation "fourierScale" => (Real.sqrt anglePeriod : ℂ)

end PolyaNeumann
