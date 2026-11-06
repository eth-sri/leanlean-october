module
public import OAI.NumberTheory.DirichletL.Detector.PhysicalMellinCoefficient
public import OAI.NumberTheory.DirichletL.Detector.RadialSpectral
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ProbeCompleted ProbeRow SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

section
variable (S : Finset (Ideal O)) (hbad : fixedBadPrimes⊆S)
include S hbad
lemma supported_of_source_exclusions (I : Ideal O) (hI : I≠0)
    (hS : ∀P∈S,¬P∣I) : Supported I := by
  refine ⟨hI,?_⟩
  pm_7811
  pm_3439
  intro hb
  exact hS P (hbad hb) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)

lemma spectralSummand_support
    (D I J : Ideal O) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) :
    Squarefree I ∧ Supported I ∧ Supported J := by
  pm_7626 hI I
  pm_7626 hJ J
  have hsf : Squarefree I := by
    by_contra hn
    exact h (by simp [spectralSummand,columnWeight,squarefreeGaussCoefficient,hn])
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hex : ∀P∈S,¬P∣I*J ^3 := by
    pm_3823
  refine ⟨hsf,supported_of_source_exclusions S hbad I hI ?_,
    supported_of_source_exclusions S hbad J hJ ?_⟩
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_left hd _)
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_right (hd.trans (dvd_pow_self J (by decide : 3≠0))) _)
end

end SevenEighths.ProbePhysical
end

end OAI
