module
public import TraceAlternatives.PhysicalUniversalActualDensity
public import TraceAlternatives.NativeCubeRows34
public import LaterPairs.NativeSharpRow5Suffix

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density

theorem density_universal_row4 {σ ε : ℝ}
    (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(1261710*(1-σ)/(1447460*σ-465509)+ε) :=
  density_of_pair_universal_fraction TaoTrudgianYang2025.exponentPair_BTTY3 hε

theorem density_universal_row5 {σ ε : ℝ}
    (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3066*(1-σ)/(3616*σ-1215)+ε) :=
  density_of_pair_universal_fraction TaoTrudgianYang2025.exponentPair_BATY2 hε

