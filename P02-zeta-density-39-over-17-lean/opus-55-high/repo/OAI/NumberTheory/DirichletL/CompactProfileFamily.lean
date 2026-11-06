module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.CompactProfileFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
section
variable (F : E → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
include F hF
theorem section_deriv_smooth :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  pc_241

theorem section_iteratedDeriv_smooth (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih
end

export OAI.CubicReflectionKernel (tsupport_iteratedDeriv_subset)

set_option hygiene false in
macro "pf_188" : tactic => `(tactic| (
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc))
section
variable (F : E → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K) (hsupp : ∀ σ, Function.support (F σ) ⊆ K)
include F hF K hK hsupp
theorem compact_family_deriv_integrable (σ : E) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by pf_188

theorem compact_family_deriv_L1_bound (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by pm_3064

theorem compact_family_fourier_power_bound (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by pf_46

theorem compact_family_fourier_weighted_bound (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by pf_47
end

end SevenEighths.CompactProfileFamily

end OAI
