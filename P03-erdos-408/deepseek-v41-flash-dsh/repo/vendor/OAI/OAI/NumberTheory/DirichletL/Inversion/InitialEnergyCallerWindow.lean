module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerPool
public import OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge SevenEighths.InverseInitialEnergyCallerPool
namespace SevenEighths.InverseInitialEnergyCallerWindow
local notation "Eis" => ActualEisensteinCubic.O

def originalSource (Z r b : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported (Z r b : ℝ) :
    ∀n∈originalSource Z r b,Squarefree n→Supported n := by
  intro n hn _
  exact (Finset.mem_filter.mp hn).2

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j c : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hc : Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (admissible_of_dvd hP hj),
        admissible_supported (admissible_of_dvd hc (idealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive

end SevenEighths.InverseInitialEnergyCallerWindow

end

end OAI
