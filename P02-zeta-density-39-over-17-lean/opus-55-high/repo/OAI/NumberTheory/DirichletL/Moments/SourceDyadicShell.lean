module
public import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondActiveDyadic
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceDyadicShell
open CenteredMomentSectorLocalization CenteredMomentSourceLowerSupport
local notation "O" => ActualEisensteinCubic.O

section
variable (C I:Ideal O) (hC:C≠0)
include C I hC
lemma residual_window_bounds (L U:ℝ) (n:ℤ)
    (hL:L≤(Ideal.absNorm (C*I):ℝ)) (hU:(Ideal.absNorm (C*I):ℝ)≤U)
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    L/(Ideal.absNorm C:ℝ)≤dyadicScale n ∧
      dyadicScale n≤4*U/(Ideal.absNorm C:ℝ) := by
  pm_408 hc
  have hs:=dyadicWeight_support n hw
  simp only [map_mul,Nat.cast_mul] at hL hU
  constructor
  · apply (div_le_iff₀ hc).mpr
    exact hL.trans (by nlinarith [hs.2])
  · apply (le_div_iff₀ hc).mpr
    nlinarith [hs.1]

lemma raw_window_lower (a H:ℝ) (ha:0<a) (n:ℤ)
    (hL:a*H≤(Ideal.absNorm (C*I):ℝ))
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale n/a := by
  pm_408 hc
  have hs:=(dyadicWeight_support n hw).2.le
  simp only [map_mul,Nat.cast_mul] at hL
  apply (div_le_div_iff₀ hc ha).mpr
  nlinarith
end

end SevenEighths.CenteredMomentSourceDyadicShell

end

end OAI
