module

public import DedekindZetaZeroFree.Analysis.Jets.Seminorms
public import DedekindZetaZeroFree.Analysis.Jets.LocallyUniformLimits

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesGlobalLimits
open Filter Topology Set
open scoped ContDiff
lemma global_smooth_jet_limit (F : ℕ → ℂ → ℂ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hC : ∀ (n : ℕ) (R : ℝ), UniformCauchySeqOn
      (fun i => iteratedFDeriv ℝ n (F i)) atTop (Metric.closedBall (0 : ℂ) R)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧ ∀ (n : ℕ) (R : ℝ),
      TendstoUniformlyOn (fun i => iteratedFDeriv ℝ n (F i))
        (iteratedFDeriv ℝ n G) atTop (Metric.closedBall (0 : ℂ) R) := by
  classical
  have hex (n : ℕ) (x : ℂ) : ∃ q : (ℂ [×n]→L[ℝ] ℂ),
      Tendsto (fun i => iteratedFDeriv ℝ n (F i) x) atTop (𝓝 q) := cauchySeq_tendsto_of_complete ((hC n (‖x‖+1)).cauchySeq (by
      simp))
  choose Q hQ using hex
  have hu (n : ℕ) (R : ℝ) : TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ n (F i)) (Q n) atTop (Metric.closedBall (0 : ℂ) R) :=
    (hC n R).tendstoUniformlyOn_of_tendsto (fun x _ => hQ n x)
  have hl (n : ℕ) : TendstoLocallyUniformlyOn
      (fun i => iteratedFDeriv ℝ n (F i)) (Q n) atTop univ := by
    intro u hu' x hx
    refine ⟨Metric.ball 0 (‖x‖+1), ?_, ?_⟩
    · simp
      exact Metric.isOpen_ball.mem_nhds (by
        simp)
    · exact ((hu n (‖x‖+1)) u hu').mono (fun i hi y hy =>
        hi y (Metric.ball_subset_closedBall hy))
  let G := fun x => (Q 0 x).curry0
  have hp : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) G (fun x n => Q n x) univ := by
    apply KPCplxPrincipalSeriesJetLimits.taylorSeries_locallyUniform_limit atTop univ isOpen_univ
      F (fun i => ftaylorSeries ℝ (F i)) G (fun x n => Q n x)
      (fun i => (hF i).ftaylorSeries.hasFTaylorSeriesUpToOn univ) _ hl
    intro x hx
    simpa only [G, ContinuousMultilinearMap.curry0, continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_eq_comp, Function.comp_def, LinearIsometryEquiv.apply_symm_apply]
      using ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.tendsto (Q 0 x) |>.comp (hQ 0 x))
  have hqeq : ∀ n x, Q n x = iteratedFDeriv ℝ n G x := fun n x => hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp) uniqueDiffOn_univ (mem_univ x) |>.trans
      (congrFun iteratedFDerivWithin_univ x)
  refine ⟨G, (contDiffOn_univ.mp hp.contDiffOn), ?_⟩
  intro n R
  rw [← (funext (hqeq n))]
  exact hu n R
end DedekindZetaZeroFree.KPCplxPrincipalSeriesGlobalLimits
