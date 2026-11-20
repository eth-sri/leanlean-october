module

public import NearlyMinimax.LiftL2
public import NearlyMinimax.LocalizationL2

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.FieldLiftCovariance

open LiftL2 (IndependentL2 IidL2)

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {M : Measure W}

abbrev KernelMap (p k : ℕ) :=
  LiftL2.KernelMap p k

/-- The actual raw kernel is a continuous linear function of its
multilinear coefficient map, with values in the observation L² space.
The finite coordinate expansion proves this even for unbounded features. -/
def rawKernelOperator {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X) : KernelMap p k →L[ℝ] Lp ℝ 2 μ :=
  ∑ σ : Fin k → Fin p,
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
      (fun i => Pi.single (σ i) 1)).smulRight
      ((LiftL2.coordinate_monomial_memLp_two e σ X hX).toLp
        (fun ω => ∏ i, X (e i) ω (σ i)))

section
variable {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)

section
variable (H : KernelMap p k)

/-- This operator is precisely the real raw kernel, modulo almost-everywhere equality. -/
theorem raw_kernel_operator_eq_toLp :
    rawKernelOperator e X hX H =
      (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hX).toLp
        (fun ω => H (fun i => X (e i) ω)) := by
  let F (σ : Fin k → Fin p) (ω : Ω) := ∏ i, X (e i) ω (σ i)
  let c (σ : Fin k → Fin p) := H (fun i => Pi.single (σ i) 1)
  have hF (σ) : MemLp (F σ) 2 μ := LiftL2.coordinate_monomial_memLp_two e σ X hX
  let G (σ) := c σ • (hF σ).toLp (F σ)
  have hterms : ∀ᵐ ω ∂μ, ∀ σ, G σ ω = c σ * F σ ω := Filter.eventually_all.mpr fun σ => by
    filter_upwards [Lp.coeFn_smul (c σ) ((hF σ).toLp (F σ)), (hF σ).coeFn_toLp] with ω hs hp
    simp [G, hs, hp, smul_eq_mul]
  rw [show rawKernelOperator e X hX H = ∑ σ, G σ by simp [rawKernelOperator, G, c, F]]
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ G, hterms,
    (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hX).coeFn_toLp] with ω hs ht hH
  simp only [ContinuousMultilinearMap.coe_coe] at hH
  rw [hs, hH]
  simp_rw [ht]
  exact (LiftL2.multilinear_coordinate_expansion H.toMultilinearMap _).symm

/-- The genuine raw-kernel energy equals the operator's squared Hilbert norm. -/
theorem raw_kernel_operator_norm_sq :
    ‖rawKernelOperator e X hX H‖ ^ 2 =
      ∫ ω, H (fun i => X (e i) ω) ^ 2 ∂μ := by
  rw [raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_norm_sq_eq_integral_sq _

end

/-- Bochner integration commutes with the actual raw-kernel operator. -/
theorem raw_kernel_integral_commute
    (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) :
    rawKernelOperator e X hX (∫ w, ν w • H w ∂M) =
      ∫ w, ν w • rawKernelOperator e X hX (H w) ∂M := by
  rw [← (rawKernelOperator e X hX).integral_comp_comm hH]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => map_smul _ _ _)

/-- Raw support separation becomes genuine L² orthogonality, before centering. -/
theorem raw_kernel_operator_inner_zero (H G : KernelMap p k)
    (hdisjoint : ∀ᵐ ω ∂μ,
      H (fun i => X (e i) ω) * G (fun i => X (e i) ω) = 0) :
    ⟪rawKernelOperator e X hX H,
      rawKernelOperator e X hX G⟫ = 0 := by
  simpa [raw_kernel_operator_eq_toLp] using LocalizationL2.toLp_inner_eq_zero_of_disjoint _ _ hdisjoint

end

/-- Evaluation of a factorial lift is continuous linear in the coefficient kernel. -/
private def kernelStatisticCLM {n p k : ℕ} (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) :
    KernelMap p k →L[ℝ] ℝ :=
  (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) •
    ∑ e : Fin k ↪ Fin n, ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
      (fun i => X (e i) ω)

section
variable {n p k : ℕ}
    (X : Fin n → Ω → Fin p → ℝ)

private theorem kernelStatisticCLM_apply (ω : Ω) (H : KernelMap p k) :
    kernelStatisticCLM X ω H = LiftL2.kernelStatistic H X ω := by
  simp [kernelStatisticCLM, LiftL2.kernelStatistic, LiftL2.kernelSum, smul_eq_mul]

section
variable (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) (ω : Ω)
include hH

theorem weighted_kernel_statistic_integrable :
    Integrable (fun w => ν w * LiftL2.kernelStatistic (H w) X ω) M := by
  simpa only [Function.comp_apply, map_smul, smul_eq_mul, kernelStatisticCLM_apply] using
    (kernelStatisticCLM X ω).integrable_comp hH

theorem kernel_statistic_integral_commute :
    (∫ w, ν w * LiftL2.kernelStatistic (H w) X ω ∂M) =
      LiftL2.kernelStatistic (∫ w, ν w • H w ∂M) X ω := by
  simpa only [map_smul, smul_eq_mul, kernelStatisticCLM_apply] using
    (kernelStatisticCLM X ω).integral_comp_comm hH

end

end

/-- Spatial integration commutes with the entire centered Taylor lift. -/
theorem centered_expansion_integral_commute {n p R : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ)
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M) (ω : Ω) :
    (∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) X ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M) X ω := by
  simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ => weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) ω)]
  exact Finset.sum_congr rfl (fun r _ => kernel_statistic_integral_commute X ν (fun w => H w r) (hH r) ω)

/-- Symmetry of the genuine multilinear fields is preserved by integration. -/
theorem integrated_kernel_symmetric {p k : ℕ}
    (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M)
    (hsym : ∀ w (σ : Equiv.Perm (Fin k)) v,
      H w (fun i => v (σ i)) = H w v)
    (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin p → ℝ) :
    (∫ w, ν w • H w ∂M) (fun i => v (σ i)) = (∫ w, ν w • H w ∂M) v := by
  simpa only [ContinuousMultilinearMap.integral_apply hH] using integral_congr_ae (Filter.Eventually.of_forall (fun w => by
      simp only [smul_apply, hsym w σ v]))

section
variable {n p R : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
include hH

/-- Actual coefficient integration yields a square-integrable centered
random variable; centering and integrability are proved from the input L²
observations, rather than required as covariance hypotheses. -/
theorem integrated_centered_lift_moment_facts
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    MemLp (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M) 2 μ ∧
      (∫ ω, ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M ∂μ) = 0 := by
  simp_rw [centered_expansion_integral_commute (fun j ω => X j ω - m) ν H hH]
  obtain ⟨hX0, hzero⟩ := LiftL2.centerObservations_l2 X m
    hX hmean
  exact ⟨LiftL2.centeredKernelExpansion_memLp_two _ _ _ hX0.toIndependentL2,
    LiftL2.centeredKernelExpansion_expectation _ _ _ hX0.toIndependentL2 hzero⟩

end

/-- U6's second spatial inequality for actual raw kernels. Distinct spatial
blocks are checked before centering; their L² orthogonality is proved from
disjoint raw support. This gains the block mass, without bounding responses. -/
theorem integrated_centered_lift_variance_localized [IsFiniteMeasure M] {n p R q : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (hHmeas : ∀ r, AEStronglyMeasurable (fun w => H w r) M)
    (hsym : ∀ w r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H w r (fun i => v (σ i)) = H w r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M,
      ‖rawKernelOperator (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR))
        X hX.toIndependentL2 (H w r)‖ ≤ C r)
    (hdisjoint : ∀ r w v, b w ≠ b v → ∀ᵐ ω ∂μ,
      H w r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) *
      H v r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    variance (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
          ∫ ω, H w r (fun i => X
            (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ ∂M := by
  let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  let K (r : Fin R) (w : W) := rawKernelOperator (e r) X hX.toIndependentL2 (H w r)
  let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
  have hKmeas (r : Fin R) :=
    (rawKernelOperator (e r) X hX.toIndependentL2).continuous.comp_aestronglyMeasurable (hHmeas r)
  have horth (r : Fin R) (w v : W) (h : b w ≠ b v) :=
    raw_kernel_operator_inner_zero (e r) X hX.toIndependentL2 (H w r) (H v r) (hdisjoint r w v h)
  have hl := LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν K hKmeas
    C hC hbound horth δ (fun r => by dsimp [δ]; positivity) L hL
  have hfirst := LiftL2.centered_expansion_variance_le_raw_power 0
    (fun r => ∫ w, ν w • H w r ∂M)
    (fun r => integrated_kernel_symmetric ν (fun w => H w r) (hH r)
      (fun w => hsym w r)) X m hR hX hmean Λ hΛ hΛn
  simp_rw [centered_expansion_integral_commute (fun j ω => X j ω - m) ν H hH]
  have heq (r : Fin R) :
      (∫ ω, (∫ w, ν w • H w r ∂M) (fun i => X (e r i) ω) ^ 2 ∂μ) =
        ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
    rw [← raw_kernel_operator_norm_sq (e r) X hX.toIndependentL2,
      raw_kernel_integral_commute (e r) X hX.toIndependentL2 ν (fun w => H w r) (hH r)]
  refine hfirst.trans ((Finset.sum_congr rfl (fun r _ => congrArg (δ r * ·) (heq r))).trans_le ?_)
  simpa only [K, raw_kernel_operator_norm_sq] using hl

end NearlyMinimax.FieldLiftCovariance
