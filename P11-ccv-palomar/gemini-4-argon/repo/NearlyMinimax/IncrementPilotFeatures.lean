module
public import NearlyMinimax.LiftL2
public import NearlyMinimax.LocalizationL2
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.PairWindowGeometry
public import NearlyMinimax.PopulationMomentDerivatives
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
section
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax.FieldLiftCovariance
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {M : Measure W}
abbrev KernelMap (p k : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
def rawKernelOperator {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) : KernelMap p k →L[ℝ] Lp ℝ 2 μ :=
  ∑ σ : Fin k → Fin p,
    (ContinuousMultilinearMap.apply ℝ (fun _ => Fin p → ℝ) ℝ
      (fun i => Pi.single (σ i) 1)).smulRight
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
        (fun ω => ∏ i, X (e i) ω (σ i)))
theorem raw_kernel_operator_eq_toLp {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H : KernelMap p k) :
    rawKernelOperator e X hind hmeas hL2 H =
      (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).toLp
        (fun ω => H (fun i => X (e i) ω)) := by
  have heq : rawKernelOperator e X hind hmeas hL2 H =
      ∑ σ : Fin k → Fin p, H (fun i => Pi.single (σ i) 1) •
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
          (fun ω => ∏ i, X (e i) ω (σ i))) := by
    simp [rawKernelOperator]
  rw [heq]
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun σ => H (fun i => Pi.single (σ i) 1) •
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
        (fun ω => ∏ i, X (e i) ω (σ i))))
  have hterms : ∀ᵐ ω ∂μ, ∀ σ,
      (H (fun i => Pi.single (σ i) 1) •
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
          (fun ω => ∏ i, X (e i) ω (σ i)))) ω =
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) := by
    apply Filter.eventually_all.mpr
    intro σ
    filter_upwards [Lp.coeFn_smul (H (fun i => Pi.single (σ i) 1))
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
        (fun ω => ∏ i, X (e i) ω (σ i))),
      (LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).coeFn_toLp] with ω hs hp
    rw [hs, Pi.smul_apply, hp, smul_eq_mul]
  filter_upwards [hsum, hterms,
    (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).coeFn_toLp]
    with ω hs ht hH
  change ((LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).toLp
    (fun ω => H (fun i => X (e i) ω))) ω = H (fun i => X (e i) ω) at hH
  rw [hs, hH]
  calc
    _ = ∑ σ : Fin k → Fin p,
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) :=
      Finset.sum_congr rfl (fun σ _ => ht σ)
    _ = H (fun i => X (e i) ω) :=
      (LiftL2.multilinear_coordinate_expansion H.toMultilinearMap _).symm
theorem raw_kernel_operator_norm_sq {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H : KernelMap p k) :
    ‖rawKernelOperator e X hind hmeas hL2 H‖ ^ 2 =
      ∫ ω, H (fun i => X (e i) ω) ^ 2 ∂μ := by
  rw [raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_norm_sq_eq_integral_sq _
theorem weighted_kernel_statistic_integrable {n p k : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) (ω : Ω) :
    Integrable (fun w => ν w * LiftL2.kernelStatistic (H w) X ω) M := by
  classical
  let d := (↑k.factorial * (n.descFactorial k : ℝ))⁻¹
  have hi (e : Fin k ↪ Fin n) : Integrable (fun w => ν w * H w (fun i => X (e i) ω)) M := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
        (fun i => X (e i) ω)).integrable_comp hH
  have hsum := integrable_finsetSum Finset.univ (fun e _ => (hi e).const_mul d)
  convert hsum using 1
  funext w
  simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  dsimp [d]
  ring
theorem centered_expansion_integral_commute {n p R : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ)
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M) (ω : Ω) :
    (∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) X ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M) X ω := by
  simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ => weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) ω)]
  have h_kernel_statistic_integral_commute {k : ℕ} (H : W → KernelMap p k) (hH : Integrable (fun w => ν w • H w) M) : (∫ w, ν w * LiftL2.kernelStatistic (H w) X ω ∂M) =
      LiftL2.kernelStatistic (∫ w, ν w • H w ∂M) X ω := by
    classical
    let d := (↑k.factorial * (n.descFactorial k : ℝ))⁻¹
    have hi (e : Fin k ↪ Fin n) : Integrable (fun w => ν w * H w (fun i => X (e i) ω)) M := by
      simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
          (fun i => X (e i) ω)).integrable_comp hH
    have heval (v : Fin k → Fin p → ℝ) :
        (∫ w, ν w • H w ∂M) v = ∫ w, ν w * H w v ∂M := by
      rw [ContinuousMultilinearMap.integral_apply hH]
      rfl
    have halg : (fun w => ν w * LiftL2.kernelStatistic (H w) X ω) =
        (fun w => d * ∑ e : Fin k ↪ Fin n, ν w * H w (fun i => X (e i) ω)) := by
      funext w
      simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      dsimp [d]
      ring
    rw [halg, integral_const_mul, integral_finsetSum _ (fun e _ => hi e)]
    change d * ∑ e : Fin k ↪ Fin n, (∫ w, ν w * H w (fun i => X (e i) ω) ∂M) =
      d * ∑ e : Fin k ↪ Fin n, (∫ w, ν w • H w ∂M) (fun i => X (e i) ω)
    simp_rw [heval]
  exact Finset.sum_congr rfl (fun r _ => (h_kernel_statistic_integral_commute (fun w => H w r) (hH r)))
theorem integrated_kernel_symmetric 
    (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M)
    (hsym : ∀ w (σ : Equiv.Perm (Fin k)) v,
      H w (fun i => v (σ i)) = H w v)
    (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin p → ℝ) :
    (∫ w, ν w • H w ∂M) (fun i => v (σ i)) = (∫ w, ν w • H w ∂M) v := by
  rw [ContinuousMultilinearMap.integral_apply hH,
    ContinuousMultilinearMap.integral_apply hH]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun w => by
    simp only [smul_apply, hsym w σ v]))
theorem integrated_centered_lift_moment_facts {n p R : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    MemLp (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M) 2 μ ∧
      (∫ ω, ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M ∂μ) = 0 := by
  have heq : (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M)
        (fun j ω => X j ω - m) := by
    funext ω
    exact centered_expansion_integral_commute _ ν H hH ω
  rw [heq]
  obtain ⟨hi, hm, _, hlp, hzero⟩ := LiftL2.centerObservations_l2 X m
    hind hmeas hid hL2 hmean
  exact ⟨LiftL2.centeredKernelExpansion_memLp_two _ _ _ hi hm hlp,
    LiftL2.centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero⟩
theorem centered_expansion_variance_le_raw_power {n p R : ℕ}
    (H )
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (LiftL2.centeredKernelExpansion 0 H (fun j ω => X j ω - m)) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, H r (fun i => X
          (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  obtain ⟨hi, hm, hid', hlp, hzero⟩ := LiftL2.centerObservations_l2 X m
    hind hmeas hid hL2 hmean
  rw [LiftL2.centeredKernelExpansion_variance 0 H hsym _ hR hi hm hid' hlp hzero]
  apply Finset.sum_le_sum
  intro r _
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  have hc := LiftL2.independent_centering_square_le_l2 μ (H r)
    (fun i => X (e i)) (fun i => hmeas (e i)) (hind.precomp e.injective)
    (fun i j => hid (e i) (e j)) (fun i a => hL2 (e i) a) m
    (fun i a => hmean (e i) a)
  have hb := LiftL2.descFactorial_lower_bound hR (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((r.val + 1).factorial : ℝ) := by positivity
  have hpow : 0 < Λ ^ (r.val + 1) := pow_pos hΛ _
  have hd := (inv_le_inv₀ (mul_pos hfac (hpow.trans_le hb)) (mul_pos hfac hpow)).2
    (mul_le_mul_of_nonneg_left hb hfac.le)
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (mul_le_mul_of_nonneg_right hd (integral_nonneg (fun _ => sq_nonneg _)))
theorem integrated_centered_lift_variance_localized [IsFiniteMeasure M] {n p R q : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (hHmeas : ∀ r, AEStronglyMeasurable (fun w => H w r) M)
    (hsym : ∀ w r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H w r (fun i => v (σ i)) = H w r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M,
      ‖rawKernelOperator (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR))
        X hind hmeas hL2 (H w r)‖ ≤ C r)
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
  let K (r : Fin R) (w : W) := rawKernelOperator (e r) X hind hmeas hL2 (H w r)
  let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
  have hKmeas (r : Fin R) : AEStronglyMeasurable (K r) M :=
    (rawKernelOperator (e r) X hind hmeas hL2).continuous.comp_aestronglyMeasurable (hHmeas r)
  have h_raw_kernel_operator_inner_zero {k : ℕ} (e : Fin k ↪ Fin n) (H : KernelMap p k) (G : KernelMap p k) (hdisjoint : ∀ᵐ ω ∂μ, H (fun i => X (e i) ω) * G (fun i => X (e i) ω) = 0) : ⟪rawKernelOperator e X hind hmeas hL2 H,
      rawKernelOperator e X hind hmeas hL2 G⟫ = 0 := by
    rw [raw_kernel_operator_eq_toLp, raw_kernel_operator_eq_toLp]
    exact LocalizationL2.toLp_inner_eq_zero_of_disjoint _ _ hdisjoint
  have horth (r : Fin R) (w v : W) (h : b w ≠ b v) : ⟪K r w, K r v⟫ = 0 :=
    h_raw_kernel_operator_inner_zero (e r) (H w r) (H v r) (hdisjoint r w v h)
  have hl := LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν K hKmeas
    C hC hbound horth δ (fun r => by dsimp [δ]; positivity) L hL
  have h_integrated_centered_lift_variance_le_raw : variance (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, (∫ w, ν w • H w r ∂M)
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
    have heq : (fun ω => ∫ w,
        ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) =
        LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M)
          (fun j ω => X j ω - m) := by
      funext ω
      exact centered_expansion_integral_commute _ ν H hH ω
    rw [heq]
    exact centered_expansion_variance_le_raw_power _
      (fun r => integrated_kernel_symmetric ν (fun w => H w r) (hH r)
        (fun w => hsym w r)) X m hR hind hmeas hid hL2 hmean Λ hΛ hΛn
  have heq (r : Fin R) :
      (∫ ω, (∫ w, ν w • H w r ∂M) (fun i => X (e r i) ω) ^ 2 ∂μ) =
        ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
    have h_raw_kernel_integral_commute : rawKernelOperator (e r) X hind hmeas hL2 (∫ w, ν w • (fun w => H w r) w ∂M) =
      ∫ w, ν w • rawKernelOperator (e r) X hind hmeas hL2 ((fun w => H w r) w) ∂M := by
      have hH  := hH r
      rw [← (rawKernelOperator (e r) X hind hmeas hL2).integral_comp_comm hH]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => map_smul _ _ _)
    rw [← raw_kernel_operator_norm_sq (e r) X hind hmeas hL2,
      h_raw_kernel_integral_commute]
  have hfirst' : variance (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      ∑ r : Fin R, δ r * ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
    apply (h_integrated_centered_lift_variance_le_raw).trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t => δ r * t) (heq r)
  apply hfirst'.trans
  convert hl using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    change ν w ^ 2 * ∑ r : Fin R,
      δ r * (∫ ω, H w r (fun i => X (e r i) ω) ^ 2 ∂μ) =
        ν w ^ 2 * ∑ r : Fin R, δ r * ‖K r w‖ ^ 2
    apply congrArg (fun t => ν w ^ 2 * t)
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t => δ r * t)
      (raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r)).symm)
end NearlyMinimax.FieldLiftCovariance
namespace NearlyMinimax
open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
def dyadicFeaturePolynomial  (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, (C (2 ^ j) * (X i - C (x i))) ^ (γ.val i).val
def PolynomialCoefficientContinuous {X σ : Type*} [TopologicalSpace X]
    (P : X → MvPolynomial σ ℝ) : Prop := ∀ e, Continuous (fun x => (P x).coeff e)
theorem polynomialCoefficientContinuous_const {X σ : Type*} [TopologicalSpace X]
    (P : MvPolynomial σ ℝ) : PolynomialCoefficientContinuous (fun _ : X => P) :=
  fun _ => continuous_const
theorem polynomialCoefficientContinuous_C {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] (g : X → ℝ) (hg : Continuous g) :
    PolynomialCoefficientContinuous (fun x => C (g x) : X → MvPolynomial σ ℝ) := by
  intro e
  simp only [coeff_C]
  by_cases he : 0 = e
  · simpa only [he, if_true] using hg
  · simp only [he, if_false]
    exact continuous_const
theorem polynomialCoefficientContinuous_mul {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] (P Q : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous (fun x => P x * Q x) := by
  intro e
  simp only [coeff_mul]
  apply continuous_finset_sum
  intro v hv
  exact (hP v.1).mul (hQ v.2)
theorem polynomialCoefficientContinuous_sub {X σ : Type*} [TopologicalSpace X]
    (P Q : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous (fun x => P x - Q x) := by
  intro e
  simp only [coeff_sub]
  exact (hP e).sub (hQ e)
theorem polynomialCoefficientContinuous_pow {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] (P : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (n : ℕ) :
    PolynomialCoefficientContinuous (fun x => P x ^ n) := by
  induction n with
  | zero => exact polynomialCoefficientContinuous_const 1
  | succ n hn =>
    simp_rw [pow_succ]
    exact polynomialCoefficientContinuous_mul _ _ hn hP
theorem polynomialCoefficientContinuous_prod {X σ ι : Type*} [TopologicalSpace X]
    [DecidableEq σ] (s : Finset ι) (P : ι → X → MvPolynomial σ ℝ)
    (hP : ∀ i ∈ s, PolynomialCoefficientContinuous (P i)) :
    PolynomialCoefficientContinuous (fun x => ∏ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialCoefficientContinuous_const (X := X) (1 : MvPolynomial σ ℝ)
  | @insert i s hi hs =>
    simp_rw [Finset.prod_insert hi]
    exact polynomialCoefficientContinuous_mul _ _ (hP i (Finset.mem_insert_self i s))
      (hs (fun j hj => hP j (Finset.mem_insert_of_mem hj)))
theorem dyadicFeaturePolynomial_coeff_continuous  (j )
    (γ : AnchoredIndex d ℓ) (e ) :
    Continuous (fun x : Covariate d => (dyadicFeaturePolynomial j x γ).coeff e) := by
  apply polynomialCoefficientContinuous_prod Finset.univ
    (fun i (x : Covariate d) => (C ((2 : ℝ) ^ j) * (X i - C (x i))) ^ (γ.val i).val) ?_ e
  intro i hi
  apply polynomialCoefficientContinuous_pow
  apply polynomialCoefficientContinuous_mul
  · exact polynomialCoefficientContinuous_const _
  · apply polynomialCoefficientContinuous_sub
    · exact polynomialCoefficientContinuous_const _
    · exact polynomialCoefficientContinuous_C _ (continuous_apply i)
abbrev PilotBasisIndex (q d ℓ : ℕ) := (Fin q × PolynomialBox d ℓ) × Bool
def pilotGlobalMonomial  (γ : PolynomialBox d ℓ) (x : Covariate d) : ℝ :=
  ∏ i, (x i) ^ (γ i).val
def pilotBasisFeature {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) : ℝ :=
  if cell z.1 = a.1.1 then pilotGlobalMonomial a.1.2 z.1 * (if a.2 then z.2 else 1) else 0
theorem pilotBasisFeature_measurable {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    Measurable (pilotBasisFeature cell a) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun (hc.comp measurable_fst) measurable_const
  · exact ((continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)).measurable.comp measurable_fst).mul
      (by cases a.2 <;> first | exact measurable_const | exact measurable_snd)
  · exact measurable_const
theorem observationLaw_cube_ae  (C θ) (hθ : Admissible C θ) :
    ∀ᵐ z ∂observationLaw θ, z.1 ∈ unitCube d :=
  (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)
theorem pilotBasisFeature_memLp_two {q d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : Covariate d → Fin q) (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    MemLp (pilotBasisFeature cell a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  apply ((memLp_const (1 : ℝ)).add (by simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm)).mono' (pilotBasisFeature_measurable cell hc a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  rw [Real.norm_eq_abs]
  have h_pilotBasisFeature_abs_bound : |pilotBasisFeature cell a z| ≤
      (Prod.fst ⁻¹' {x | cell x = a.1.1}).indicator
        (fun z => 1 + |z.2|) z := by
    have h_pilotGlobalMonomial_abs_le_one : |pilotGlobalMonomial a.1.2 z.1| ≤ 1 := by
      unfold pilotGlobalMonomial
      rw [Finset.abs_prod]
      simp only [abs_pow]
      have hcoord (i : Fin d) : |z.1 i| ≤ 1 := by
        rw [abs_of_nonneg (hz i).1]
        exact (hz i).2
      calc
        _ ≤ ∏ _i : Fin d, 1 ^ (a.1.2 _i).val :=
          Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
            (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord i) _)
        _ = 1 := by simp
    have hmono := h_pilotGlobalMonomial_abs_le_one
    by_cases h : cell z.1 = a.1.1
    · rw [pilotBasisFeature, if_pos h, abs_mul]
      simp only [mem_preimage, mem_setOf_eq, h, indicator_of_mem]
      cases a.2
      · simpa using hmono.trans (le_add_of_nonneg_right (abs_nonneg z.2))
      · simp only [↓reduceIte]
        exact (mul_le_mul_of_nonneg_right hmono (abs_nonneg z.2)).trans (by linarith)
    · simp [pilotBasisFeature, h]
  apply h_pilotBasisFeature_abs_bound.trans
  by_cases h : cell z.1 = a.1.1 <;> simp [h] <;> positivity
def pilotRawVector {q d ℓ : ℕ} (cell : Covariate d → Fin q) (z : Observation d) :
    Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ :=
  fun a => pilotBasisFeature cell ((Fintype.equivFin (PilotBasisIndex q d ℓ)).symm a) z
abbrev LocalPilotIndex (d ℓ : ℕ) :=
  Sum (AnchoredIndex d ℓ × AnchoredIndex d ℓ) (Sum (AnchoredIndex d ℓ) (AnchoredIndex d ℓ))
def dyadicPilotScale (d j : ℕ) : ℝ := (2 ^ j) ^ d
theorem dyadicPilotScale_pos (d j ) : 0 < dyadicPilotScale d j := by
  unfold dyadicPilotScale
  positivity
def dyadicPilotCell  (j : ℕ) (x : Covariate d) : Set (Covariate d) :=
  {z | regularGridCell (2 ^ j) (by positivity) z =
    regularGridCell (2 ^ j) (by positivity) x}
theorem dyadicPilotCell_measurable {d : ℕ} (j : ℕ) (x : Covariate d) :
    MeasurableSet (dyadicPilotCell j x) :=
  measurableSet_eq_fun (regular_grid_cell_measurable _ _) measurable_const
theorem dyadicAnchoredFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : Measurable (fun z => dyadicAnchoredFeature j x z γ) := by
  exact ((anchoredMonomial_continuous γ).comp (continuous_pi (fun i =>
    continuous_const.mul ((continuous_apply i).sub continuous_const)))).measurable
def dyadicPilotScalar  (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicAnchoredFeature j x z.1 γ * dyadicAnchoredFeature j x z.1 δ
  | Sum.inr (Sum.inl γ) => z.2 * dyadicAnchoredFeature j x z.1 γ
  | Sum.inr (Sum.inr γ) => dyadicAnchoredFeature j x z.1 γ
def dyadicPilotFeature  (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  dyadicPilotScale d j * (Prod.fst ⁻¹' dyadicPilotCell j x).indicator
    (dyadicPilotScalar j x a) z
theorem dyadicPilotScalar_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : Measurable (dyadicPilotScalar j x a) := by
  cases a with
  | inl a =>
    exact ((dyadicAnchoredFeature_measurable j x a.1).comp measurable_fst).mul
      ((dyadicAnchoredFeature_measurable j x a.2).comp measurable_fst)
  | inr a =>
    cases a with
    | inl γ =>
      exact measurable_snd.mul
        ((dyadicAnchoredFeature_measurable j x γ).comp measurable_fst)
    | inr γ => exact (dyadicAnchoredFeature_measurable j x γ).comp measurable_fst
theorem dyadicPilotFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : Measurable (dyadicPilotFeature j x a) :=
  measurable_const.mul ((dyadicPilotScalar_measurable j x a).indicator
    (measurable_fst (dyadicPilotCell_measurable j x)))
theorem dyadicPilotFeature_abs_bound {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) (hx : x ∈ unitCube d)
    (hz : z.1 ∈ unitCube d) :
    |dyadicPilotFeature j x a z| ≤ dyadicPilotScale d j *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator
        (fun z : Observation d => 1 + |z.2|) z := by
  by_cases hc : z.1 ∈ dyadicPilotCell j x
  · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
    simp only [dyadicPilotFeature, indicator_of_mem hc', abs_mul,
      abs_of_pos (dyadicPilotScale_pos d j)]
    have h_dyadicPilotScalar_abs_bound : |dyadicPilotScalar j x a z| ≤ 1 + |z.2| := by
      have h_dyadicAnchoredFeature_abs_le_one (γ : AnchoredIndex d ℓ) : |dyadicAnchoredFeature j x z.1 γ| ≤ 1 := by
        apply anchoredMonomial_abs_le_one
        intro i
        have hr := regular_grid_same_cell_radius (2 ^ j) (by positivity) z.1 x hz hx hc i
        have hk : 0 < (2 : ℝ) ^ j := by positivity
        have he : (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by simp
        rw [he] at hr
        rw [abs_mul, abs_of_pos hk]
        exact (mul_le_mul_of_nonneg_left hr hk.le).trans_eq (by field_simp)
      have hb := h_dyadicAnchoredFeature_abs_le_one
      cases a with
      | inl a =>
        change |dyadicAnchoredFeature j x z.1 a.1 * dyadicAnchoredFeature j x z.1 a.2| ≤ _
        rw [abs_mul]
        apply (mul_le_mul (hb a.1) (hb a.2) (abs_nonneg _) (by norm_num)).trans
        simp only [one_mul]
        exact le_add_of_nonneg_right (abs_nonneg z.2)
      | inr a =>
        cases a with
        | inl γ =>
          change |z.2 * dyadicAnchoredFeature j x z.1 γ| ≤ _
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left (hb γ) (abs_nonneg z.2)).trans (by linarith)
        | inr γ => exact (hb γ).trans (le_add_of_nonneg_right (abs_nonneg z.2))
    exact mul_le_mul_of_nonneg_left h_dyadicPilotScalar_abs_bound
      (dyadicPilotScale_pos d j).le
  · simp [dyadicPilotFeature, hc]
theorem dyadicPilotFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    MemLp (dyadicPilotFeature j x a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hd : MemLp (fun z : Observation d => dyadicPilotScale d j * (1 + |z.2|))
      2 (observationLaw θ) := ((memLp_const (1 : ℝ)).add (by simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm)).const_mul _
  apply hd.mono' (dyadicPilotFeature_measurable j x a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  rw [Real.norm_eq_abs]
  apply (dyadicPilotFeature_abs_bound j x a z hx hz).trans
  by_cases hc : z.1 ∈ dyadicPilotCell j x <;> simp [hc]
  exact mul_nonneg (dyadicPilotScale_pos d j).le (by positivity)
def dyadicPilotMomentConstant  (C : ModelConstants d) : ℝ :=
  2 * (1 + responseSecondBound C) * C.densityUpper
theorem dyadicPilotFeature_second_le  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  have hd : Integrable (fun z : Observation d => dyadicPilotScale d j ^ 2 *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator (fun z : Observation d => (1 + |z.2|) ^ 2) z)
      (observationLaw θ) :=
    (((memLp_const (1 : ℝ)).add (by simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm)).integrable_sq.indicator
      (measurable_fst (dyadicPilotCell_measurable j x))).const_mul _
  have hfirst : (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotScale d j ^ 2 *
        ((2 * (1 + responseSecondBound C)) * (designLaw θ).real (dyadicPilotCell j x)) := by
    apply (integral_mono_ae (dyadicPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq hd ?_).trans
    · rw [integral_const_mul]
      have h_observationLaw_localized_response_energy_le (A : Set (Covariate d)) (hA : MeasurableSet A) : (∫ z, (Prod.fst ⁻¹' A).indicator
          (fun z : Observation d => (1 + |z.2|) ^ 2) z ∂observationLaw θ) ≤
          2 * (1 + responseSecondBound C) * (designLaw θ).real A := by
        let := observationLaw_isProbability C θ hθ
        have hi : Integrable (fun z : Observation d => (1 + |z.2|) ^ 2)
            (observationLaw θ) := ((memLp_const (1 : ℝ)).add (by simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm)).integrable_sq
        have hd : Integrable (fun z : Observation d => 2 * (1 + z.2 ^ 2))
            (observationLaw θ) :=
          ((integrable_const (1 : ℝ)).add
            (observationLaw_response_memLp_two C θ hθ).integrable_sq).const_mul 2
        have hb := integral_mono (hi.indicator (measurable_fst hA))
          (hd.indicator (measurable_fst hA)) (fun z => by
            apply Set.indicator_le_indicator
            have hab := sq_nonneg (1 - |z.2|)
            nlinarith [sq_abs z.2])
        have heq : (fun z : Observation d => (Prod.fst ⁻¹' A).indicator
            (fun z => 2 * (1 + z.2 ^ 2)) z) =
            (fun z => 2 * ((Prod.fst ⁻¹' A).indicator (fun _ => (1 : ℝ)) z +
              (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z)) := by
          funext z
          by_cases hz : z.1 ∈ A <;> simp [hz]
        rw [heq, integral_const_mul,
          integral_add ((integrable_const (1 : ℝ)).indicator (measurable_fst hA))
            ((observationLaw_response_memLp_two C θ hθ).integrable_sq.indicator
              (measurable_fst hA))] at hb
        have hI : (∫ z, (Prod.fst ⁻¹' A).indicator (fun _ : Observation d => (1 : ℝ)) z
            ∂observationLaw θ) = (designLaw θ).real A := by
          rw [integral_indicator_const (1 : ℝ) (measurable_fst hA)]
          simp only [smul_eq_mul, mul_one]
          exact (observationLaw_fst_measurePreserving C θ hθ).measureReal_preimage
            hA.nullMeasurableSet
        rw [hI] at hb
        have hb2 := observationLaw_localized_second_integral_le C θ hθ A hA
        nlinarith
      exact mul_le_mul_of_nonneg_left (h_observationLaw_localized_response_energy_le _ (dyadicPilotCell_measurable j x)) (sq_nonneg _)
    · filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
      have hb := dyadicPilotFeature_abs_bound j x a z hx hz
      by_cases hc : z.1 ∈ dyadicPilotCell j x
      · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
        simp only [indicator_of_mem hc'] at hb ⊢
        change dyadicPilotFeature j x a z ^ 2 ≤ dyadicPilotScale d j ^ 2 * (1 + |z.2|) ^ 2
        simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      · simp [dyadicPilotFeature, hc]
  have hmass : (designLaw θ).real (dyadicPilotCell j x) ≤ C.densityUpper / dyadicPilotScale d j := by
    convert regularGridProbability_cap C θ hθ ((2 : ℕ) ^ j) (by positivity)
      (regularGridCell ((2 : ℕ) ^ j) (by positivity) x) using 1 <;>
      simp only [dyadicPilotCell, regularGridProbability, Set.preimage, Set.mem_singleton_iff,
        dyadicPilotScale, Nat.cast_pow, Nat.cast_ofNat]
  apply hfirst.trans
  have hfactor : 0 ≤ dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C)) := by
    have := responseSecondBound_pos C
    positivity
  have hm := mul_le_mul_of_nonneg_left hmass hfactor
  have heq : dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C)) *
      (C.densityUpper / dyadicPilotScale d j) =
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    unfold dyadicPilotMomentConstant
    field_simp [ne_of_gt (dyadicPilotScale_pos d j)] <;> ring
  rw [heq] at hm
  simpa only [mul_assoc] using hm
def dyadicPilotPopulation  (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    LocalPilotIndex d ℓ → ℝ := fun a => ∫ z, dyadicPilotFeature j x a z ∂observationLaw θ
def gridAffine {d : ℕ} (k : ℕ) (c : Fin d → Fin k) (w : Covariate d) : Covariate d :=
  regularGridCorner k c + (k : ℝ)⁻¹ • w
def gridClosedBox {d : ℕ} (k : ℕ) (c : Fin d → Fin k) : Set (Covariate d) :=
  Icc (regularGridCorner k c) (regularGridCorner k c + fun _ => (k : ℝ)⁻¹)
def gridAffineEquiv  (k ) (hk : 0 < k) (c : Fin d → Fin k) :
    Covariate d ≃ᵐ Covariate d :=
  ((Homeomorph.smul (Units.mk0 ((k : ℝ)⁻¹) (by positivity))).trans
    (Homeomorph.addLeft (regularGridCorner k c))).toMeasurableEquiv
@[simp] theorem gridAffineEquiv_apply {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) (w : Covariate d) : gridAffineEquiv k hk c w = gridAffine k c w := rfl
theorem gridAffine_preimage_box  (k ) (hk : 0 < k) (c ) :
    gridAffine k c ⁻¹' gridClosedBox k c = unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  ext w
  change ((∀ i, regularGridCorner k c i ≤ regularGridCorner k c i + (k : ℝ)⁻¹ * w i) ∧
    (∀ i, regularGridCorner k c i + (k : ℝ)⁻¹ * w i ≤ regularGridCorner k c i + (k : ℝ)⁻¹)) ↔
    ∀ i, 0 ≤ w i ∧ w i ≤ 1
  constructor
  · intro hw i
    constructor
    · exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hkr)).mp (by linarith [hw.1 i])
    · apply (mul_le_mul_iff_of_pos_left (inv_pos.mpr hkr)).mp
      simpa using (show (k : ℝ)⁻¹ * w i ≤ (k : ℝ)⁻¹ by linarith [hw.2 i])
  · intro hw
    constructor <;> intro i
    · linarith [mul_nonneg (inv_nonneg.mpr hkr.le) (hw i).1]
    · have := mul_le_mul_of_nonneg_left (hw i).2 (inv_nonneg.mpr hkr.le)
      linarith
theorem gridClosedBox_subset_cube  (k ) (hk : 0 < k)
    (c ) : gridClosedBox k c ⊆ unitCube d := by
  intro z hz i
  refine ⟨(regular_grid_corner_mem_cube k hk c i).1.trans (hz.1 i), ?_⟩
  apply (hz.2 i).trans
  change (c i : ℝ) / k + (k : ℝ)⁻¹ ≤ 1
  have he : (c i : ℝ) / k + (k : ℝ)⁻¹ = ((c i : ℝ) + 1) / k := by ring
  rw [he]
  exact (div_le_one (by exact_mod_cast hk)).2 (by exact_mod_cast (c i).isLt)
theorem gridAffine_map_cubeVolume  (k ) (hk : 0 < k) (c ) :
    (cubeVolume d).map (gridAffine k c) =
      ENNReal.ofReal ((k : ℝ) ^ d) • volume.restrict (gridClosedBox k c) := by
  let e := gridAffineEquiv k hk c
  have hpre : e ⁻¹' gridClosedBox k c = unitCube d := gridAffine_preimage_box k hk c
  have h := e.restrict_map (volume : Measure (Covariate d)) (gridClosedBox k c)
  rw [hpre] at h
  change ((volume.restrict (unitCube d)).map e) = _
  rw [← h]
  change ((volume : Measure (Covariate d)).map (gridAffine k c)).restrict _ = _
  have h_gridAffine_map_volume : (volume : Measure (Covariate d)).map (gridAffine k c) =
      ENNReal.ofReal (↑k ^ d) • volume := by
    have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
    rw [show gridAffine k c = (fun z => regularGridCorner k c + z) ∘
      (fun w => (k : ℝ)⁻¹ • w) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_addHaar_smul volume (inv_ne_zero hkr.ne'),
      Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
    simp [Module.finrank_pi, abs_of_nonneg (pow_nonneg hkr.le d)]
  rw [h_gridAffine_map_volume, Measure.restrict_smul]
theorem gridAffine_ae_pullback {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
    {P : Covariate d → Prop} (hP : ∀ᵐ z ∂cubeVolume d, P z) :
    ∀ᵐ w ∂cubeVolume d, P (gridAffine k c w) := by
  apply ae_of_ae_map (gridAffineEquiv k hk c).measurable.aemeasurable
  change ∀ᵐ z ∂(cubeVolume d).map (gridAffine k c), P z
  rw [gridAffine_map_cubeVolume k hk c]
  exact Measure.ae_smul_measure
    (ae_restrict_of_ae_restrict_of_subset (gridClosedBox_subset_cube k hk c) hP) _
def gridNormalizedAnchor  (k ) (hk : 0 < k) (x : Covariate d) : Covariate d :=
  fun i => k * (x i - regularGridCorner k (regularGridCell k hk x) i)
theorem gridNormalizedAnchor_mem_cube  (k hk x) (hx : x ∈ unitCube d) : gridNormalizedAnchor k hk x ∈ unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  intro i
  constructor
  · exact mul_nonneg hkr.le (sub_nonneg.mpr (regular_grid_cell_corner_le k hk x hx i))
  · change (k : ℝ) * (x i - regularGridCorner k (regularGridCell k hk x) i) ≤ 1
    exact (mul_le_mul_of_nonneg_left ((abs_le.mp (regular_grid_cell_radius k hk x hx i)).2) hkr.le).trans_eq (by field_simp)
theorem dyadicAnchoredFeature_affine {d ℓ : ℕ} (j : ℕ) (x w : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature j x
      (gridAffine (↑2 ^ j) (regularGridCell _ (by positivity) x) w) γ =
      anchoredFeature (gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x) w γ := by
  unfold dyadicAnchoredFeature anchoredFeature
  congr 1
  funext i
  simp only [gridAffine, gridNormalizedAnchor, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring
theorem regular_grid_cell_integral  (k hk) (c : Fin d → Fin k)
    (f : Covariate d → ℝ) :
    ↑k ^ d * (∫ z in (regularGridCell k hk) ⁻¹' {c}, f z ∂cubeVolume d) =
      ∫ w, f (gridAffine k c w) ∂cubeVolume d := by
  have h_regular_grid_fiber_restrict : (cubeVolume d).restrict ((regularGridCell k hk) ⁻¹' {c}) =
      volume.restrict (gridClosedBox k c) := by
    rw [cubeVolume, Measure.restrict_restrict
      ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
    have h_regular_grid_fiber_ae_box : ((regularGridCell k hk) ⁻¹' {c} ∩ unitCube d) =ᵐ[volume] gridClosedBox k c := by
      have hfaces : ∀ᵐ z : Covariate d ∂volume,
          ∀ i, z i ≠ regularGridCorner k c i + (k : ℝ)⁻¹ := by
        rw [ae_all_iff]
        intro i
        apply ae_iff.mpr
        simp only [not_not]
        change (volume : Measure (Covariate d))
          ((fun z : Covariate d => z i) ⁻¹' {regularGridCorner k c i + (k : ℝ)⁻¹}) = 0
        rw [volume_pi]
        exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) (measure_singleton _)
      filter_upwards [hfaces] with z hz
      apply propext
      constructor
      · intro hzcell
        have hc : regularGridCell k hk z = c := hzcell.1
        constructor <;> intro i
        · simpa only [hc] using regular_grid_cell_corner_le k hk z hzcell.2 i
        · have h := (abs_le.mp (regular_grid_cell_radius k hk z hzcell.2 i)).2
          simp only [hc] at h
          change z i ≤ regularGridCorner k c i + (k : ℝ)⁻¹
          simpa only [one_div] using (by linarith : z i ≤ regularGridCorner k c i + 1 / k)
      · intro hzbox
        refine ⟨?_, gridClosedBox_subset_cube k hk c hzbox⟩
        change regularGridCell k hk z = c
        funext i
        have h_regular_grid_index_eq_of_box (c : Fin k) (z) (hlo : (c : ℝ) / k ≤ z) (hhi : z < (c : ℝ) / k + (k : ℝ)⁻¹) : regularGridIndex k hk z = c := by
          have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
          have hf : ⌊(k : ℝ) * z⌋₊ = c.val := by
            apply (Nat.floor_eq_iff (mul_nonneg hkr.le ((div_nonneg (Nat.cast_nonneg _) hkr.le).trans hlo))).2
            constructor
            · have h := (div_le_iff₀ hkr).mp hlo
              nlinarith
            · have h := mul_lt_mul_of_pos_left hhi hkr
              have he : (k : ℝ) * ((c : ℝ) / k + (k : ℝ)⁻¹) = (c : ℝ) + 1 := by field_simp
              rwa [he] at h
          apply Fin.ext
          change min ⌊↑k * z⌋₊ (k - 1) = c.val
          rw [hf, min_eq_left (by have := c.isLt; omega)]
        apply h_regular_grid_index_eq_of_box (c i) (z i) (hzbox.1 i)
        exact lt_of_le_of_ne (hzbox.2 i) (hz i)
    exact Measure.restrict_congr_set h_regular_grid_fiber_ae_box
  rw [h_regular_grid_fiber_restrict]
  have h_gridAffine_integral : (∫ w, f (gridAffine k c w) ∂cubeVolume d) =
      (k : ℝ) ^ d * ∫ z in gridClosedBox k c, f z := by
    have h := integral_map_equiv (μ := cubeVolume d) (gridAffineEquiv k hk c) f
    simp only [gridAffineEquiv_apply] at h
    rw [← h]
    change (∫ z, f z ∂(cubeVolume d).map (gridAffine k c)) = _
    rw [gridAffine_map_cubeVolume k hk c, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
    rfl
  exact h_gridAffine_integral.symm
def dyadicNormalizedAnchor  (j : ℕ) (x : Covariate d) : Covariate d :=
  gridNormalizedAnchor (2 ^ j) (by positivity) x
def dyadicCellAffine  (j : ℕ) (x w : Covariate d) : Covariate d :=
  gridAffine (2 ^ j) (regularGridCell _ (by positivity) x) w
def dyadicNormalizedDensity  (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ := θ.density ∘ dyadicCellAffine j x
def dyadicKnownGram  (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂cubeVolume d
def dyadicPopulationGram  (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ
def dyadicPreconditionedGram  (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (dyadicKnownGram j x)⁻¹ * dyadicPopulationGram θ j x
theorem admissible_designLaw_setIntegral  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (s : Set (Covariate d)) (hs : MeasurableSet s) (f : Covariate d → ℝ) :
    (∫ z in s, f z ∂designLaw θ) = ∫ z in s, θ.density z * f z ∂cubeVolume d := by
  unfold designLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hθ.1.ennreal_ofReal.aemeasurable) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hθ.2.2.1] with z hz
  rw [ENNReal.toReal_ofReal (C.densityLower_pos.le.trans hz.1)]
  rfl
theorem dyadicKnownGram_eq_normalized {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicKnownGram (ℓ := ℓ) j x = anchoredGram (dyadicNormalizedAnchor j x) := by
  ext γ δ
  have h := regular_grid_cell_integral (2 ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicKnownGram, dyadicPilotScale,
    dyadicPilotCell, Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine,
    anchoredGram, dyadicNormalizedAnchor] using h
theorem dyadicPopulationGram_eq_normalized  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j ) (x : Covariate d) :
    dyadicPopulationGram (ℓ := ℓ) θ j x =
      anchoredDensityGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  ext γ δ
  change dyadicPilotScale d j * (∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ) = _
  rw [admissible_designLaw_setIntegral C θ hθ _ (dyadicPilotCell_measurable j x)]
  have h := regular_grid_cell_integral (↑2 ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => θ.density z * (dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ))
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicPilotScale, dyadicPilotCell,
    Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine, anchoredDensityGram,
    dyadicNormalizedAnchor, dyadicNormalizedDensity, Function.comp_apply, dyadicCellAffine] using h
theorem dyadicNormalizedDensity_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    Measurable (dyadicNormalizedDensity θ j x) :=
  hθ.1.comp (gridAffineEquiv _ (by positivity) _).measurable
theorem dyadicNormalizedDensity_bounds  (C : ModelConstants d)
    (θ ) (hθ : Admissible C θ) (j x) :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper :=
  gridAffine_ae_pullback _ (by positivity) _ hθ.2.2.1
theorem dyadicKnownGram_posDef {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (dyadicKnownGram (ℓ := ℓ) j x).PosDef := by
  rw [dyadicKnownGram_eq_normalized]
  exact anchoredGram_posDef _
def pilotPolynomialLinear  (c : Fin q) (P : MvPolynomial (Fin d) ℝ)
    (response : Bool) : (Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ) →L[ℝ] ℝ :=
  ∑ β : PolynomialBox d ℓ, P.coeff (polynomialBoxExponent β) •
    ContinuousLinearMap.proj ((Fintype.equivFin (PilotBasisIndex q d ℓ)) ((c, β), response))
theorem pilotPolynomialLinear_raw_apply {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (c : Fin q) (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ)
    (response : Bool) (z : Observation d) :
    pilotPolynomialLinear (ℓ := ℓ) c P response (pilotRawVector cell z) =
      if cell z.1 = c then eval z.1 P * (if response then z.2 else 1) else 0 := by
  simp only [pilotPolynomialLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, pilotRawVector, Equiv.symm_apply_apply, smul_eq_mul,
    pilotBasisFeature]
  by_cases h : cell z.1 = c
  · simp only [h, ite_true, ← mul_assoc, ← Finset.sum_mul]
    rw [polynomial_box_evaluation P hP]
    rfl
  · simp [h]
abbrev DyadicPilotLabelIndex (d j : ℕ) := Fin d → Fin (2 ^ j)
def dyadicPilotLabel  (j ) (x : Covariate d) :
    Fin (Fintype.card (DyadicPilotLabelIndex d j)) :=
  Fintype.equivFin (DyadicPilotLabelIndex d j)
    (regularGridCell (2 ^ j) (by positivity) x)
theorem dyadicPilotLabel_measurable  (j ) :
    Measurable (dyadicPilotLabel (d := d) j) :=
  (measurable_of_countable _).comp (regular_grid_cell_measurable _ _)
theorem dyadicPilotLabel_eq_iff {d : ℕ} (j : ℕ) (x z : Covariate d) :
    dyadicPilotLabel j z = dyadicPilotLabel j x ↔ z ∈ dyadicPilotCell j x :=
  (Fintype.equivFin (DyadicPilotLabelIndex d j)).injective.eq_iff
def dyadicPilotPolynomial  (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : MvPolynomial (Fin d) ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ
  | Sum.inr (Sum.inl γ) => dyadicFeaturePolynomial j x γ
  | Sum.inr (Sum.inr γ) => dyadicFeaturePolynomial j x γ
def dyadicPilotResponse  (a : LocalPilotIndex d ℓ) : Bool :=
  match a with
  | Sum.inl _ => false
  | Sum.inr (Sum.inl _) => true
  | Sum.inr (Sum.inr _) => false
def dyadicPilotCoordinate  (j ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) :
    (Fin (Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))) → ℝ) →L[ℝ] ℝ :=
  dyadicPilotScale d j • pilotPolynomialLinear (dyadicPilotLabel j x)
    (dyadicPilotPolynomial j x a) (dyadicPilotResponse a)
theorem dyadicPilotCoordinate_raw_apply {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) :
    dyadicPilotCoordinate j x a (pilotRawVector (dyadicPilotLabel j) z) =
      dyadicPilotFeature j x a z := by
  have h_dyadicFeaturePolynomial_degree (γ : AnchoredIndex d ℓ) : (dyadicFeaturePolynomial j x γ).totalDegree ≤ ℓ := by
    apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
    apply (Finset.sum_le_sum _).trans γ.property.2
    intro i hi
    have hlinear : (C (2 ^ j) * (X i - C (x i))).totalDegree ≤ 1 := by
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, zero_add]
      exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hlinear)
  have h_dyadicFeaturePolynomial_eval (j : ℕ) (x : Covariate d) (z : Covariate d) (γ : AnchoredIndex d ℓ) : eval z (dyadicFeaturePolynomial j x γ) = dyadicAnchoredFeature j x z γ := by
    simp only [dyadicFeaturePolynomial, map_prod, map_pow, map_mul, map_sub, eval_C, eval_X,
      dyadicAnchoredFeature, anchoredMonomial]
  have h_dyadicPilotPolynomial_degree : (dyadicPilotPolynomial j x a).totalDegree ≤ 2 * ℓ := by
    cases a with
    | inl a =>
      exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add (h_dyadicFeaturePolynomial_degree a.1)
          (h_dyadicFeaturePolynomial_degree a.2)).trans_eq (by omega))
    | inr a =>
      cases a <;> exact (h_dyadicFeaturePolynomial_degree _).trans (by omega)
  rw [dyadicPilotCoordinate, ContinuousLinearMap.smul_apply,
    pilotPolynomialLinear_raw_apply _ _ _ h_dyadicPilotPolynomial_degree]
  have h_dyadicPilotPolynomial_scalar : eval z.1 (dyadicPilotPolynomial j x a) * (if dyadicPilotResponse a then z.2 else 1) =
      dyadicPilotScalar j x a z := by
    cases a with
    | inl a => simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
        h_dyadicFeaturePolynomial_eval]
    | inr a =>
      cases a <;> simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
        h_dyadicFeaturePolynomial_eval, mul_comm]
  simp only [smul_eq_mul, dyadicPilotLabel_eq_iff, h_dyadicPilotPolynomial_scalar,
    dyadicPilotFeature]
  by_cases h : z.1 ∈ dyadicPilotCell j x
  · have he := (dyadicPilotLabel_eq_iff j x z.1).mpr h
    simp [h, he]
  · have he : dyadicPilotLabel j z.1 ≠ dyadicPilotLabel j x :=
      fun he => h ((dyadicPilotLabel_eq_iff j x z.1).mp he)
    simp [h, he]
def dyadicResponseMoment  (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * θ.regression z ∂designLaw θ
def dyadicConstantMoment  (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ ∂designLaw θ
theorem observationLaw_integral_design  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (g : Covariate d → ℝ)
    (hg : Measurable g) : (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
  have hp := observationLaw_fst_measurePreserving C θ hθ
  rw [← hp.map_eq]
  exact (integral_map hp.aemeasurable hg.aestronglyMeasurable).symm
theorem dyadicPilotPopulation_constant {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inr γ)) = dyadicConstantMoment θ j x γ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
      (fun z => dyadicAnchoredFeature j x z γ) z.1 ∂observationLaw θ) = _
  rw [observationLaw_integral_design C θ hθ _
    ((dyadicAnchoredFeature_measurable j x γ).indicator (dyadicPilotCell_measurable j x)),
    integral_indicator (dyadicPilotCell_measurable j x)]
  rfl
theorem dyadicPilotPopulation_response  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inl γ)) = dyadicResponseMoment θ j x γ := by
  let := observationLaw_isProbability C θ hθ
  unfold dyadicPilotPopulation
  rw [observationLaw_integral_conditioning C θ hθ _
    ((dyadicPilotFeature_memLp_two C θ hθ j x hx (Sum.inr (Sum.inl γ))).integrable (by norm_num))]
  have heq : (fun z => ∫ u, dyadicPilotFeature j x (Sum.inr (Sum.inl γ))
      (z, θ.regression z + u) ∂θ.errors z) =ᵐ[designLaw θ]
      (fun z => dyadicPilotScale d j * (dyadicPilotCell j x).indicator
        (fun z => dyadicAnchoredFeature j x z γ * θ.regression z) z) := by
    filter_upwards [hθ.2.2.2.2.2.2.2] with z hz
    by_cases hcell : z ∈ dyadicPilotCell j x
    · have hm  := hz.1
      have hi : (fun u => dyadicPilotFeature j x (Sum.inr (Sum.inl γ)) (z, θ.regression z + u)) =
          (fun u => dyadicPilotScale d j * ((θ.regression z + u) * dyadicAnchoredFeature j x z γ)) := by
        funext u
        simp [dyadicPilotFeature, dyadicPilotScalar, hcell]
      rw [hi, integral_const_mul, integral_mul_const]
      simp only [indicator_of_mem hcell]
      rw [integral_add (integrable_const _) hm, integral_const, hz.2.2.2.1]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, add_zero]
      ring
    · simp [dyadicPilotFeature, hcell]
  rw [integral_congr_ae heq, integral_const_mul, integral_indicator (dyadicPilotCell_measurable j x)]
  rfl
theorem dyadicResponseMoment_eq_normalized  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j x) :
    dyadicResponseMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) := by
  funext γ
  unfold dyadicResponseMoment
  rw [admissible_designLaw_setIntegral C θ hθ _ (dyadicPilotCell_measurable j x)]
  have h := regular_grid_cell_integral (2 ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => θ.density z * (dyadicAnchoredFeature j x z γ * θ.regression z))
  change (((2 ^ j : ℕ) : ℝ)) ^ d * (∫ z in dyadicPilotCell j x,
    θ.density z * (dyadicAnchoredFeature j x z γ * θ.regression z) ∂cubeVolume d) = _ at h
  change dyadicPilotScale d j * (∫ z in dyadicPilotCell j x,
    θ.density z * (dyadicAnchoredFeature j x z γ * θ.regression z) ∂cubeVolume d) = _
  rw [show dyadicPilotScale d j = (((2 ^ j : ℕ) : ℝ)) ^ d by simp [dyadicPilotScale]]
  rw [h]
  unfold anchoredVectorMoment dyadicNormalizedDensity dyadicCellAffine dyadicNormalizedAnchor
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    dsimp only [Function.comp_apply]
    rw [dyadicAnchoredFeature_affine]
    ring)
theorem dyadicConstantMoment_eq_normalized  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j x) :
    dyadicConstantMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (fun _ => 1) := by
  funext γ
  unfold dyadicConstantMoment
  rw [admissible_designLaw_setIntegral C θ hθ _ (dyadicPilotCell_measurable j x)]
  have h := regular_grid_cell_integral (2 ^ j) (by positivity)
    (regularGridCell _ (by positivity) x) (fun z => θ.density z * dyadicAnchoredFeature j x z γ)
  change (((2 ^ j : ℕ) : ℝ)) ^ d * (∫ z in dyadicPilotCell j x,
    θ.density z * dyadicAnchoredFeature j x z γ ∂cubeVolume d) = _ at h
  change dyadicPilotScale d j * (∫ z in dyadicPilotCell j x,
    θ.density z * dyadicAnchoredFeature j x z γ ∂cubeVolume d) = _
  rw [show dyadicPilotScale d j = (((2 ^ j : ℕ) : ℝ)) ^ d by simp [dyadicPilotScale]]
  rw [h]
  unfold anchoredVectorMoment dyadicNormalizedDensity dyadicCellAffine dyadicNormalizedAnchor
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    dsimp only [Function.comp_apply]
    rw [dyadicAnchoredFeature_affine]
    simp)
end NearlyMinimax
end
section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
def localPilotRow  (a : LocalPilotIndex d ℓ) : AnchoredIndex d ℓ :=
  match a with
  | Sum.inl (γ, _) => γ
  | Sum.inr (Sum.inl γ) => γ
  | Sum.inr (Sum.inr γ) => γ
def localPilotReplaceRow  (a : LocalPilotIndex d ℓ)
    (β : AnchoredIndex d ℓ) : LocalPilotIndex d ℓ :=
  match a with
  | Sum.inl (_, δ) => Sum.inl (β, δ)
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl β)
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr β)
def preconditionedPilotFeature  (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z
def preconditionedPilotPopulation  (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (a : LocalPilotIndex d ℓ) : ℝ :=
  ∫ z, preconditionedPilotFeature j x a z ∂observationLaw θ
theorem preconditionedPilotFeature_measurable  (j )
    (x : Covariate d) (a : LocalPilotIndex d ℓ) : Measurable (preconditionedPilotFeature j x a) :=
  Finset.measurable_sum Finset.univ (fun β _ =>
    measurable_const.mul (dyadicPilotFeature_measurable j x _))
theorem preconditionedPilotFeature_memLp_two  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    MemLp (preconditionedPilotFeature j x a) 2 (observationLaw θ) :=
  memLp_finsetSum Finset.univ (fun β _ =>
    (dyadicPilotFeature_memLp_two C θ hθ j x hx (localPilotReplaceRow a β)).const_mul _)
theorem preconditionedPilotPopulation_eq_sum  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) (a ) :
    preconditionedPilotPopulation θ j x a =
      ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
        dyadicPilotPopulation θ j x (localPilotReplaceRow a β) := by
  let := observationLaw_isProbability C θ hθ
  unfold preconditionedPilotPopulation preconditionedPilotFeature
  rw [integral_finsetSum _ (fun β _ =>
    ((dyadicPilotFeature_memLp_two C θ hθ j x hx _).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul, dyadicPilotPopulation]
theorem dyadicKnownGram_inverse_uniform_bound  :
    ∃ L, 0 < L ∧ ∀ j, ∀ x ∈ unitCube d, ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L := by
  obtain ⟨L, hL, hbound⟩ := anchoredGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
  refine ⟨L, hL, ?_⟩
  intro j x hx
  rw [dyadicKnownGram_eq_normalized]
  exact hbound _ (gridNormalizedAnchor_mem_cube _ _ x hx)
theorem preconditionedPilotFeature_second_le  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ)
    (L : ℝ) (hL : 0 ≤ L) (hB : ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L) :
    (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ) : ℝ) ^ 2 * L ^ 2 *
        dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  let B := (dyadicKnownGram (ℓ := ℓ) j x)⁻¹
  let f (β : AnchoredIndex d ℓ) (z : Observation d) := B (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z
  have hlp (β : AnchoredIndex d ℓ) : MemLp (f β) 2 (observationLaw θ) :=
    (dyadicPilotFeature_memLp_two C θ hθ j x hx _).const_mul _
  have hs : Integrable (fun z => (Fintype.card (AnchoredIndex d ℓ) : ℝ) *
      ∑ β, f β z ^ 2) (observationLaw θ) :=
    (integrable_finsetSum Finset.univ (fun β _ => (hlp β).integrable_sq)).const_mul _
  have hfirst : (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ) : ℝ) * ∑ β, ∫ z, f β z ^ 2 ∂observationLaw θ := by
    have h := integral_mono (preconditionedPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq hs
      (fun z => by simpa [preconditionedPilotFeature, f, B] using
        sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun β => f β z))
    rwa [integral_const_mul, integral_finsetSum _ (fun β _ => (hlp β).integrable_sq)] at h
  have hb (β : AnchoredIndex d ℓ) : |B (localPilotRow a) β| ≤ L := by
    calc
      _ = ‖B (localPilotRow a) β‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B‖ := matrix_real_entry_norm_le B (localPilotRow a) β
      _ ≤ L := hB
  have hcoord (β : AnchoredIndex d ℓ) : (∫ z, f β z ^ 2 ∂observationLaw θ) ≤
      L ^ 2 * dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    simp only [f, mul_pow, integral_const_mul]
    have h_dyadicPilotMomentConstant_pos : 0 < dyadicPilotMomentConstant C := by
      have := C.one_lt_densityUpper
      have := responseSecondBound_pos C
      unfold dyadicPilotMomentConstant
      positivity
    exact (mul_le_mul_of_nonneg_left (dyadicPilotFeature_second_le C θ hθ j x hx _)
      (sq_nonneg _)).trans
      (by have hc := h_dyadicPilotMomentConstant_pos
          have hk := dyadicPilotScale_pos d j
          nlinarith [mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb β) 2) (mul_nonneg hc.le hk.le)])
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun β _ => hcoord β))
    (Nat.cast_nonneg _)).trans_eq
  simp [pow_two, mul_assoc]
def pilotInverseBound (d ℓ : ℕ) : ℝ :=
  Classical.choose (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))
theorem pilotInverseBound_pos (d ℓ ) : 0 < pilotInverseBound d ℓ :=
  (Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))).1
def preconditionedPilotMomentConstant  (C : ModelConstants d) (ℓ : ℕ) : ℝ :=
  max 1 ((Fintype.card (AnchoredIndex d ℓ) : ℝ) ^ 2 * pilotInverseBound d ℓ ^ 2 *
    dyadicPilotMomentConstant C)
theorem preconditionedPilotMomentConstant_pos {d : ℕ} (C : ModelConstants d) (ℓ : ℕ) :
    0 < preconditionedPilotMomentConstant C ℓ := zero_lt_one.trans_le (le_max_left _ _)
end NearlyMinimax
end
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax.KernelMomentBounds
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem pi_norm_sq_le_sum_sq {p : ℕ} (v : Fin p → ℝ) : ‖v‖ ^ 2 ≤ ∑ a, (v a) ^ 2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (by apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr; intro a; have hs := Finset.single_le_sum (fun a _ => sq_nonneg (v a)) (Finset.mem_univ a); simpa only [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hs) 2).trans_eq (Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _)))
theorem vector_memLp_two {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ) : MemLp X 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_finsetSum Finset.univ (fun a _ => (hL2 a).integrable_sq)).mono' (hm.norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pi_norm_sq_le_sum_sq (X ω)
theorem factorial_kernel_budget {p k : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ)
    (X : Fin k → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (E a c Λ : ℝ) (hE : 0 ≤ E) (ha : 0 ≤ a) (hc : 0 ≤ c) (hΛ : 0 < Λ)
    (henergy : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ E)
    (hderiv : ‖H‖ ≤ a * (k.factorial : ℝ) * c ^ k) :
    ((↑k.factorial * Λ ^ k)⁻¹) * (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
      a ^ 2 * ↑k.factorial * (c ^ 2 * E / Λ) ^ k := by
  have hfac : 0 < ↑k.factorial := by positivity
  have h_multilinear_second_le : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤ ‖H‖ ^ 2 * E ^ k := by
    have hnorm (i : Fin k) := (vector_memLp_two (X i) (hm i) (hL2 i)).norm
    have hind' : iIndepFun (fun i ω => ‖X i ω‖ ^ 2) μ :=
      hind.comp (fun _ => fun v : Fin p → ℝ => ‖v‖ ^ 2)
        (fun _ => measurable_norm.pow_const 2)
    have hmeas' (i : Fin k) : Measurable (fun ω => ‖X i ω‖ ^ 2) := (hm i).norm.pow_const 2
    have hd := LiftL2.independent_finset_product_integrable hind' hmeas'
      (fun i => (hnorm i).integrable_sq) Finset.univ
    have hraw := (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap
      (Function.Embedding.refl (Fin k)) X hind hm hL2).integrable_sq
    have hcomp : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
        ‖H‖ ^ 2 * ∫ ω, ∏ i : Fin k, ‖X i ω‖ ^ 2 ∂μ := by
      rw [← integral_const_mul]
      apply integral_mono hraw (hd.const_mul (‖H‖ ^ 2))
      intro ω
      change H (fun i => X i ω) ^ 2 ≤ ‖H‖ ^ 2 * ∏ i : Fin k, ‖X i ω‖ ^ 2
      simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.prod_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (H.le_opNorm (fun i => X i ω)) 2
    have heq := hind'.integral_fun_prod_eq_prod_integral (fun i => (hmeas' i).aestronglyMeasurable)
    rw [heq] at hcomp
    apply hcomp.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    calc
      _ ≤ ∏ _i : Fin k, E := Finset.prod_le_prod₀
        (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => henergy i)
      _ = E ^ k := by simp
  have h := mul_le_mul_of_nonneg_left
    ((h_multilinear_second_le).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hderiv 2) (pow_nonneg hE k)))
    (show 0 ≤ (↑k.factorial * Λ ^ k)⁻¹ by positivity)
  apply h.trans_eq
  simp only [div_pow, mul_pow]
  field_simp [ne_of_gt hfac, ne_of_gt hΛ] <;> ring
theorem vector_second_le_sum_coordinates {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ ∑ a, ∫ ω, X ω a ^ 2 ∂μ := by
  have h := integral_mono ((vector_memLp_two X hm hL2).norm.integrable_sq) (integrable_finsetSum Finset.univ (fun a _ => (hL2 a).integrable_sq)) (fun ω => pi_norm_sq_le_sum_sq (X ω))
  rwa [integral_finsetSum _ (fun a _ => (hL2 a).integrable_sq)] at h
end NearlyMinimax.KernelMomentBounds
namespace NearlyMinimax
open MeasureTheory Set ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {d ℓ n : ℕ}
theorem regular_grid_index_parent (k hk x) :
    (regularGridIndex (2 * k) (by omega) x).val / 2 = (regularGridIndex k hk x).val := by
  have hre : ((2 * k : ℕ) : ℝ) * x = k * x * (2 : ℕ) := by push_cast; ring
  have : ⌊((2 * k : ℕ) : ℝ) * x⌋₊ / 2 = ⌊(k : ℝ) * x⌋₊ := by
    rw [hre, Nat.mul_cast_floor_div_cancel (by decide : (2 : ℕ) ≠ 0)]
  simp only [regularGridIndex, Fin.val_mk]
  omega
theorem dyadicPilotCell_subset_parent  (j : ℕ) (x : Covariate d) :
    dyadicPilotCell j x ⊆ dyadicPilotCell (j - 1) x := by
  cases j with
  | zero => simp
  | succ j =>
    intro z hz
    have h_regular_grid_cell_parent_eq (k : ℕ) (hk : 0 < k) (h : regularGridCell (2 * k) (by omega) z = regularGridCell (2 * k) (by omega) x) : regularGridCell k hk z = regularGridCell k hk x := by
      funext i
      apply Fin.ext
      have hi := congrArg (fun c => (c i).val / 2) h
      change (regularGridIndex (2 * k) (by omega) (z i)).val / 2 =
        (regularGridIndex (2 * k) (by omega) (x i)).val / 2 at hi
      rw [regular_grid_index_parent k hk, regular_grid_index_parent k hk] at hi
      exact hi
    apply h_regular_grid_cell_parent_eq (2 ^ j) (by positivity)
    change regularGridCell (2 ^ (j + 1)) (by positivity) z =
      regularGridCell (2 ^ (j + 1)) (by positivity) x at hz
    have h_regular_grid_same_cell_congr {k : ℕ} {l : ℕ} (h : k = l) (hk : 0 < k) (hl : 0 < l) : (regularGridCell k hk z = regularGridCell k hk x) ↔
        (regularGridCell l hl z = regularGridCell l hl x) := by
      subst l
      rfl
    exact (h_regular_grid_same_cell_congr (by rw [pow_succ]; omega) (by positivity) (by positivity)).mp hz
def anchoredFinIndex  (i : Fin (anchoredDimension d ℓ)) : AnchoredIndex d ℓ :=
  (Fintype.equivFin (AnchoredIndex d ℓ)).symm i
def dyadicIncrementFeature  (j : ℕ) (x : Covariate d)
    (v : incrementVariables (anchoredDimension d ℓ)) (z : Observation d) : ℝ :=
  match v with
  | Sum.inl m => match m with
    | Sum.inl it =>
      preconditionedPilotFeature j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2)) z
    | Sum.inr it =>
      if j = 0 then (if it.2.1 = it.2.2 then 1 else 0) else
        preconditionedPilotFeature (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2)) z
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      preconditionedPilotFeature (if pri.1 then j - 1 else j) x
        (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
          else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2))) z
def dyadicIncrementRawVector  (j : ℕ) (x : Covariate d) (z : Observation d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => dyadicIncrementFeature j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) z
def dyadicIncrementRawMean  (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => ∫ z, dyadicIncrementRawVector j x z a ∂observationLaw θ
theorem dyadicIncrementFeature_measurable  (j : ℕ) (x : Covariate d)
    (v : incrementVariables (anchoredDimension d ℓ)) : Measurable (dyadicIncrementFeature j x v) := by
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_measurable j x _
    | inr v =>
      change Measurable (fun z => if j = 0 then
        (if v.2.1 = v.2.2 then 1 else 0) else
        preconditionedPilotFeature (j - 1) x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z)
      split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_measurable _ x _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    change Measurable (fun z => if parent && (j == 0) then 0 else
      preconditionedPilotFeature (if parent then j - 1 else j) x
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
          else Sum.inr (Sum.inl (anchoredFinIndex i))) z)
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_measurable _ x _
theorem dyadicIncrementRawVector_measurable  (j : ℕ) (x : Covariate d) :
    Measurable (dyadicIncrementRawVector (ℓ := ℓ) j x) :=
  measurable_pi_iff.mpr (fun _ => dyadicIncrementFeature_measurable j x _)
theorem dyadicIncrementFeature_memLp_two  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) (v : incrementVariables (anchoredDimension d ℓ)) :
    MemLp (dyadicIncrementFeature j x v) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_memLp_two C θ hθ j x hx _
    | inr v =>
      change MemLp (fun z => if j = 0 then
        (if v.2.1 = v.2.2 then 1 else 0) else
        preconditionedPilotFeature (j - 1) x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z) 2 (observationLaw θ)
      split_ifs <;> first | exact memLp_const _ | exact preconditionedPilotFeature_memLp_two C θ hθ _ x hx _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    change MemLp (fun z => if parent && (j == 0) then 0 else
      preconditionedPilotFeature (if parent then j - 1 else j) x
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
          else Sum.inr (Sum.inl (anchoredFinIndex i))) z) 2 (observationLaw θ)
    split_ifs <;> first | exact memLp_const _ | exact preconditionedPilotFeature_memLp_two C θ hθ _ x hx _
def dyadicFinPilotGram  (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (dyadicPreconditionedGram θ j x)
def dyadicFinPilotMoments  (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun response i => preconditionedPilotPopulation θ j x
    (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
      else Sum.inr (Sum.inl (anchoredFinIndex i)))
def dyadicIncrementPopulation  (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    incrementVariables (anchoredDimension d ℓ) → ℝ :=
  incrementValuation (dyadicFinPilotGram θ j x)
    (if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)
    (dyadicFinPilotMoments θ j x)
    (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
theorem dyadicIncrementRawMean_eq_population  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      dyadicIncrementPopulation θ j x
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  have h_preconditionedPilotPopulation_gram (j) (x) (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) (δ : AnchoredIndex d ℓ) : preconditionedPilotPopulation θ j x (Sum.inl (γ, δ)) =
      dyadicPreconditionedGram θ j x γ δ := by
    rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
    have h_dyadicPilotPopulation_gram (j : ℕ) (x : Covariate d) (γ : AnchoredIndex d ℓ) (δ : AnchoredIndex d ℓ) : dyadicPilotPopulation θ j x (Sum.inl (γ, δ)) = dyadicPopulationGram θ j x γ δ := by
      unfold dyadicPilotPopulation dyadicPilotFeature
      rw [integral_const_mul]
      change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
          (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) z.1
            ∂observationLaw θ) = dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
              dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ
      have hg : Measurable (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) :=
        (dyadicAnchoredFeature_measurable j x γ).mul (dyadicAnchoredFeature_measurable j x δ)
      rw [observationLaw_integral_design C θ hθ _
        (hg.indicator (dyadicPilotCell_measurable j x)), integral_indicator (dyadicPilotCell_measurable j x)]
    simp only [localPilotRow, localPilotReplaceRow, h_dyadicPilotPopulation_gram,
      dyadicPreconditionedGram, Matrix.mul_apply]
  funext a
  have h_dyadicIncrementFeature_integral (v : incrementVariables (anchoredDimension d ℓ)) : (∫ z, dyadicIncrementFeature j x v z ∂observationLaw θ) =
      dyadicIncrementPopulation θ j x v := by
    let := observationLaw_isProbability C θ hθ
    cases v with
    | inl v =>
      cases v with
      | inl v =>
        rcases v with ⟨i, t⟩
        simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
          anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex,
          preconditionedPilotPopulation] using
          h_preconditionedPilotPopulation_gram j x hx (anchoredFinIndex i) (anchoredFinIndex t)
      | inr v =>
        by_cases hj : j = 0
        · simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
            RoughRegime.CombinedPolynomial.entryValuation, hj, Matrix.one_apply]
        · simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
            RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
            anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex, hj,
            preconditionedPilotPopulation] using
            h_preconditionedPilotPopulation_gram (j - 1) x hx
              (anchoredFinIndex v.2.1) (anchoredFinIndex v.2.2)
    | inr v =>
      rcases v with ⟨parent, response, i⟩
      cases parent <;> cases response <;> by_cases hj : j = 0
      all_goals simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
        dyadicFinPilotMoments, hj, preconditionedPilotPopulation]
  exact h_dyadicIncrementFeature_integral _
theorem dyadicFinPilotGram_eq_normalized  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicFinPilotGram (ℓ := ℓ) θ j x =
      anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  unfold dyadicFinPilotGram dyadicPreconditionedGram anchoredFinNormalizedGram
  rw [dyadicKnownGram_eq_normalized, dyadicPopulationGram_eq_normalized C θ hθ]
theorem dyadicIncrementRawVector_sample_facts  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) :
    iIndepFun (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector (ℓ := ℓ) j x (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))) ∧
    (∀ i t, IdentDistrib
      (fun z => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))
      (fun z => dyadicIncrementRawVector (ℓ := ℓ) j x (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a ∂sampleLaw θ n) =
      dyadicIncrementRawMean θ j x a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := dyadicIncrementRawVector_measurable (ℓ := ℓ) j x
  have hp (i : Fin n) : MeasurePreserving (fun z : Fin n → Observation d => z i)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i), ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib (fun z : Fin n → Observation d => z i)
        (fun z : Fin n → Observation d => z t) (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
    exact ht.comp hm
  · intro i a
    exact (dyadicIncrementFeature_memLp_two C θ hθ j x hx _).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
      ((dyadicIncrementFeature_measurable j x
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a)).aestronglyMeasurable)
theorem dyadicIncrementRawVector_sample_second_le  (C θ) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) (i ) :
    (∫ z : Fin n → Observation d, ‖dyadicIncrementRawVector (ℓ := ℓ) j x (z i)‖ ^ 2 ∂sampleLaw θ n) ≤
      Fintype.card (incrementVariables (anchoredDimension d ℓ)) *
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  have h_preconditionedPilotFeature_uniform_second_le (j) (x) (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) : (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
    have h_pilotInverseBound_le  := (Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))).2 j x hx
    apply (preconditionedPilotFeature_second_le C θ hθ j x hx a (pilotInverseBound d ℓ)
      (pilotInverseBound_pos d ℓ).le h_pilotInverseBound_le).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (dyadicPilotScale_pos d j).le
  let := observationLaw_isProbability C θ hθ
  unfold sampleLaw
  rw [integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
    (((dyadicIncrementRawVector_measurable (ℓ := ℓ) j x).norm.pow_const 2).aestronglyMeasurable)]
  let := observationLaw_isProbability C θ hθ
  apply (KernelMomentBounds.vector_second_le_sum_coordinates (dyadicIncrementRawVector j x)
    (dyadicIncrementRawVector_measurable j x) (fun _ => dyadicIncrementFeature_memLp_two C θ hθ j x hx _)).trans
  have h_dyadicIncrementFeature_second_le (v : incrementVariables (anchoredDimension d ℓ)) : (∫ z, dyadicIncrementFeature j x v z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
    let := observationLaw_isProbability C θ hθ
    have hC := preconditionedPilotMomentConstant_pos C ℓ
    have hroot : 1 ≤ preconditionedPilotMomentConstant C ℓ := le_max_left _ _
    have hK : 1 ≤ dyadicPilotScale d j := by
      exact one_le_pow₀ (one_le_pow₀ (by norm_num))
    have hnon  :=
      mul_nonneg hC.le (dyadicPilotScale_pos d j).le
    have h_dyadicPilotScale_parent_le : dyadicPilotScale d (j - 1) ≤ dyadicPilotScale d j := by
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)) d
    have hparent (a : LocalPilotIndex d ℓ) :=
      (h_preconditionedPilotFeature_uniform_second_le (j - 1) x hx a).trans
        (mul_le_mul_of_nonneg_left h_dyadicPilotScale_parent_le hC.le)
    cases v with
    | inl v =>
      cases v with
      | inl v =>
        rcases v with ⟨i, t⟩
        exact h_preconditionedPilotFeature_uniform_second_le j x hx _
      | inr v =>
        dsimp only [dyadicIncrementFeature]
        split_ifs <;> first
          | simpa using (mul_le_mul hroot hK (by norm_num : (0 : ℝ) ≤ 1) hC.le)
          | simpa using hnon
          | exact hparent _
    | inr v =>
      rcases v with ⟨parent, response, i⟩
      cases parent with
      | false =>
        cases response
        all_goals first
          | simpa [dyadicIncrementFeature] using h_preconditionedPilotFeature_uniform_second_le j x hx
              (Sum.inr (Sum.inl (anchoredFinIndex i)))
          | simpa [dyadicIncrementFeature] using h_preconditionedPilotFeature_uniform_second_le j x hx
              (Sum.inr (Sum.inr (anchoredFinIndex i)))
      | true =>
        cases response <;> by_cases hj : j = 0
        all_goals first
          | simpa [dyadicIncrementFeature, hj] using hnon
          | simpa [dyadicIncrementFeature, hj] using hparent
              (Sum.inr (Sum.inl (anchoredFinIndex i)))
          | simpa [dyadicIncrementFeature, hj] using hparent
              (Sum.inr (Sum.inr (anchoredFinIndex i)))
  exact (Finset.sum_le_sum (fun a _ => (h_dyadicIncrementFeature_second_le _))).trans_eq
    (by simp [mul_assoc])
end NearlyMinimax
