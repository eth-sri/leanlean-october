module
public import GuthMaynard.Improvement.UnequalHeightReduction
public import GuthMaynard.Improvement.SparseAffineInput
public import GuthMaynard.Improvement.UniformReduction
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open GuthMaynard.NativeMoment

/-- Apply the verified sparse affine theorem to the actual adaptive source
smoothing, uniformly even in the internal epsilon parameter. -/
theorem adaptive_sparse_affine (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T δ : ℝ) (hT : 8 ≤ T) (f : 𝓢(ℝ, ℝ)) (R K : ℕ),
      (∀ x, 0 ≤ f x) → GMAffineSourceSupported f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f →
      0 < K → (K:ℝ) ≤ T^4 →
      gmAffineJ (unequalAdaptive T δ K R f (by linarith)) K ≤
        B*T^ε*((K:ℝ)^6*(∫ x, f x)^2+(K:ℝ)^4*(∫ x, f x^2)) := by
  obtain ⟨B,hB,hbound⟩ := sparse_affine_all_heights
    (fun β n => 2*D β n) (fun β n => mul_nonneg (by norm_num) (hD β n)) hε
  refine ⟨16*B,by positivity,?_⟩
  intro T δ hT f R K hf hs hp hK hKT
  have hTp : 0 < T := by linarith
  let Q := T ^ gmAffineIterationEta δ
  pm_4907 hQ Q hTp
  let S := gmAffineSecondPoissonCutoff T Q K R/Q
  have hS : 0 < S := div_pos (gmAffineSecondPoissonCutoff_pos hTp hQ) hQ
  have hTS : T ≤ S := gmAffineSecondPoissonSmoothingScale_ge hQ
  let ft := gmAffineTildeSchwartz S hS f
  have hft : ∀ x, 0 ≤ ft x := gmAffineTildeSchwartz_nonneg S hS f hf
  have hwidth : 2/S ≤ (1/4:ℝ) := (div_le_iff₀ hS).mpr (by linarith only [hT,hTS])
  have hsft : GMAffineSupportedOn (1/4:ℝ) (9/4) ft :=
    (gmAffineTildeSchwartz_supportedOn hS f hs).mono (by linarith) (by linarith)
  have hpft : GMAffineHeightFourierMassFamilyAtDepth T (fun β n => 2*D β n) 0 ft := by
    have h := gmAffineTildeSchwartz_heightFourierMassFamilyAtDepth_succ hTp.le hS D hD f hf hp
    pm_124 GMAffineHeightFourierMassFamilyAtDepth Nat.zero_add pow_zero pow_one one_mul h
  have hmain := hbound T ft K (by linarith) hft hsft hpft hK hKT
  have hw := gmAffineTildeSchwartz_weighted_norms_le_sixteen hS f hf (le_refl K)
  pm_738 hb hmain.trans hw
  pm_314 ft S Q unequalAdaptive mul_assoc mul_left_comm mul_comm hb

end GuthMaynard.Improvement
