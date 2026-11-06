module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.Calibration
public import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic

@[expose] public section

namespace OAI


open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow


theorem calibrationForSet_coprime_iff  S   hS 
     a  : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded  S 
     hS   a 
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := (OAI.SevenEighths.ProbePhysical.calibrationForSet_coprime_iff S hS a).mpr fun P hP ha => hmask P hP (Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)))

end SevenEighths.ProbePhysical


end OAI
