module

public import OAI.NumberTheory.DirichletL.Detector.Calibration
public import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : ActualEisensteinCubic.O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (by grind)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (by grind)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : ActualEisensteinCubic.O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  simp_all

end SevenEighths.ProbePhysical
end

end OAI
