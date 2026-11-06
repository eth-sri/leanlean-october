module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerPool
public import OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge SevenEighths.InverseInitialEnergyCallerPool
namespace SevenEighths.InverseInitialEnergyCallerWindow


def originalSource (Z r b : ℝ)  :=
  (idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported  Z r b  :
    ∀n∈originalSource Z r b,Squarefree n→Supported n := fun n hn a => (Finset.mem_filter.mp hn).right

theorem residual_window_eq  W   {P j c} 
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
     Z r z G  (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
     {P j c}  (hP : Admissible P) (hj : j∣P)
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
