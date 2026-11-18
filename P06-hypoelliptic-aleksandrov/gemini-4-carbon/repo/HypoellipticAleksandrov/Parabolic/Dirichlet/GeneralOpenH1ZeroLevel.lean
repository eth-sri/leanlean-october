module

public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.LocallyFinite
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Composition
public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.W1p.Truncation
public import PDEFoundation.Sobolev.H1.Algebra

@[expose] public noncomputable section

namespace PDE
open Filter MeasureTheory Set
open scoped Topology


/-- Weak gradients on an open set glue from a ball around every point. -/
theorem HasWeakGradientOn.of_ballwise
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} {Df : Vec d → Vec d}
    (hf : MeasureTheory.LocallyIntegrableOn f U MeasureTheory.volume)
    (hDf : ∀ i : Fin d,
      MeasureTheory.LocallyIntegrableOn (fun x => Df x i) U MeasureTheory.volume)
    (hlocal : ∀ x ∈ U, ∃ R : ℝ, 0 < R ∧
      euclideanClosedBall x R ⊆ U ∧
      HasWeakGradientOn (euclideanBall x R) f Df) :
    HasWeakGradientOn U f Df := by
  intro i φ hφSmooth hφCompact hφU
  let K := tsupport φ
  have hKClosed : IsClosed K := by simpa using isClosed_tsupport φ
  choose R hRpos hRsub hweak using fun x : K => hlocal x.1 (hφU x.2)
  let V : K → Set (Vec d) := fun x => euclideanBall x.1 (R x)
  have hVOpen : ∀ x, IsOpen (V x) := fun x => isOpen_euclideanBall _ _
  have hKCover : K ⊆ ⋃ x, V x := by
    intro x hx
    exact mem_iUnion_of_mem ⟨x, hx⟩ (center_mem_euclideanBall x (hRpos ⟨x, hx⟩))
  obtain ⟨ρ, hρV⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      (ι := K) (modelWithCornersSelf ℝ (Vec d)) hKClosed V hVOpen hKCover
  let active : Set K := {x | (Function.support (ρ x) ∩ K).Nonempty}
  have hactiveFinite : active.Finite := by
    exact ρ.locallyFinite.finite_nonempty_inter_compact (hφCompact.isCompact)
  let J := hactiveFinite.toFinset
  let ψ : K → Vec d → ℝ := fun x y => φ y * ρ x y
  have hsumψ : (∑ x ∈ J, ψ x) = φ := by
    funext y
    by_cases hy : y ∈ K
    · have hfin : ρ.finsupport y ⊆ J := by
        intro x hx
        rw [SmoothPartitionOfUnity.mem_finsupport] at hx
        have hxactive : x ∈ active := ⟨y, hx, hy⟩
        exact hactiveFinite.mem_toFinset.mpr hxactive
      rw [Finset.sum_apply]
      rw [← Finset.mul_sum]
      rw [ρ.sum_finsupport' (x₀ := y) hy hfin, mul_one]
    · have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [ψ, hφy]
  have hψSmooth (x : K) : ContDiff ℝ (⊤ : ℕ∞) (ψ x) := by
    exact hφSmooth.mul (ρ x).contMDiff.contDiff
  have hψCompact (x : K) : HasCompactSupport (ψ x) := by
    simpa only [ψ, Pi.mul_def] using hφCompact.mul_right (f' := ρ x)
  have hψV (x : K) : tsupport (ψ x) ⊆ V x := by
    exact (tsupport_mul_subset_right (f := φ) (g := ρ x)).trans (hρV x)
  have hVU (x : K) : V x ⊆ U := by
    exact (euclideanBall_subset_euclideanClosedBall _ _).trans (hRsub x)
  have hlocalIdentity (x : K) :
      ∫ y in U, f y * (fderiv ℝ (ψ x) y) (basisVec i) ∂volume =
        -∫ y in U, Df y i * ψ x y ∂volume := by
    have hleftZero (y : Vec d) (hy : y ∉ V x) :
        f y * (fderiv ℝ (ψ x) y) (basisVec i) = 0 := by
      have hy' : y ∉ tsupport (ψ x) := fun h => hy (hψV x h)
      have heq : ψ x =ᶠ[nhds y] 0 :=
        (isClosed_tsupport (ψ x)).isOpen_compl.eventually_mem hy' |>.mono
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      rw [heq.fderiv_eq]
      simp
    have hrightZero (y : Vec d) (hy : y ∉ V x) : Df y i * ψ x y = 0 := by
      simp [image_eq_zero_of_notMem_tsupport (fun h => hy (hψV x h))]
    have hleftZeroU (y : Vec d) (hy : y ∉ U) :
        f y * (fderiv ℝ (ψ x) y) (basisVec i) = 0 :=
      hleftZero y (fun h => hy (hVU x h))
    have hrightZeroU (y : Vec d) (hy : y ∉ U) : Df y i * ψ x y = 0 :=
      hrightZero y (fun h => hy (hVU x h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleftZeroU,
      setIntegral_eq_integral_of_forall_compl_eq_zero hrightZeroU,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hleftZero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hrightZero]
    exact hweak x i (ψ x) (hψSmooth x) (hψCompact x) (hψV x)
  have hleftIntegrable (x : K) :
      Integrable (fun y => f y * (fderiv ℝ (ψ x) y) (basisVec i)) (volumeOn U) := by
    let g : Vec d → ℝ := fun y => (fderiv ℝ (ψ x) y) (basisVec i)
    have hgCont : Continuous g :=
      (hψSmooth x).continuous_fderiv (by simp) |>.clm_apply continuous_const
    have hgCompact :=
      (hψCompact x).fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hgU : tsupport g ⊆ U :=
      (closure_minimal (by
        intro y hy
        apply (tsupport_fderiv_subset ℝ)
        exact subset_tsupport _ (fun hz => hy (by simp [g, hz])))
        (isClosed_tsupport (ψ x))).trans ((hψV x).trans (hVU x))
    simpa only [IntegrableOn, volumeOn, g] using
      ((hf.integrableOn_compact_subset hgU hgCompact.isCompact).mul_continuousOn hgCont.continuousOn hgCompact.isCompact).of_forall_sdiff_eq_zero hU.measurableSet fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy.2]
  have hrightIntegrable (x : K) :
      Integrable (fun y => Df y i * ψ x y) (volumeOn U) := by
    simpa only [IntegrableOn, volumeOn] using
      (((hDf i).integrableOn_compact_subset ((hψV x).trans (hVU x)) (hψCompact x).isCompact).mul_continuousOn (hψSmooth x).continuous.continuousOn (hψCompact x).isCompact).of_forall_sdiff_eq_zero hU.measurableSet fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy.2]
  have hsumIdentity :
      (∑ x ∈ J, ∫ y in U, f y * (fderiv ℝ (ψ x) y) (basisVec i) ∂volume) =
        ∑ x ∈ J, -∫ y in U, Df y i * ψ x y ∂volume := by
    apply Finset.sum_congr rfl
    intro x _
    exact hlocalIdentity x
  rw [← MeasureTheory.integral_finsetSum _ (fun x _ => hleftIntegrable x),
    Finset.sum_neg_distrib] at hsumIdentity
  rw [← MeasureTheory.integral_finsetSum _ (fun x _ => hrightIntegrable x)] at hsumIdentity
  have hderivSum (y : Vec d) :
      ∑ x ∈ J, (fderiv ℝ (ψ x) y) (basisVec i) =
        (fderiv ℝ φ y) (basisVec i) := by
    rw [← hsumψ]
    rw [fderiv_sum (fun x _ =>
      (hψSmooth x).contDiffAt.differentiableAt (by simp))]
    rw [sum_apply]
  have hvalueSum (y : Vec d) : ∑ x ∈ J, ψ x y = φ y := by
    simpa using congrFun hsumψ y
  calc
    ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x, ∑ y ∈ J, f x * (fderiv ℝ (ψ y) x) (basisVec i) ∂volumeOn U := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change f x * (fderiv ℝ φ x) (basisVec i) =
          ∑ y ∈ J, f x * (fderiv ℝ (ψ y) x) (basisVec i)
        rw [← Finset.mul_sum, hderivSum]
    _ = -∫ x, ∑ y ∈ J, Df x i * ψ y x ∂volumeOn U := hsumIdentity
    _ = -∫ x in U, Df x i * φ x ∂volume := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∑ y ∈ J, Df x i * ψ y x) = Df x i * φ x
        rw [← Finset.mul_sum, hvalueSum]

section
open scoped ENNReal

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The `p = 2` weak chain rule, stated directly on the representative-level
`H¹` carrier.  This is an exact transport of the generic finite-exponent
theorem. -/
theorem hasWeakGradient_comp_contDiff_of_deriv_bounded
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    HasWeakGradientOn U
      (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  simpa using
    W1pFunction.hasWeakGradient_comp_contDiff_of_deriv_bounded
      hU (by norm_num) (by norm_num) u.toW1pFunction hG hM hderiv

/-- Compose an `H¹` representative with a `C¹` real function whose derivative
is bounded by `M`. -/
noncomputable def compContDiffOfDerivBounded
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    H1Function U :=
  (u.toW1pFunction.compContDiffOfDerivBounded
    hU (by norm_num) (by norm_num)
    hG hM hderiv).toH1Function

@[simp]
theorem compContDiffOfDerivBounded_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    (u.compContDiffOfDerivBounded
      hU hG hM hderiv).toFun =
        fun x => G (u.toFun x) :=
  rfl

@[simp]
theorem compContDiffOfDerivBounded_grad
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    (u.compContDiffOfDerivBounded
      hU hG hM hderiv).grad =
        fun x i =>
          deriv G (u.toFun x) * u.grad x i :=
  rfl

end H1Function

end
end PDE

namespace PDE.H1Function
open Filter MeasureTheory Set
open scoped ENNReal Topology


private theorem tendsto_eLpNorm_two_zero_of_ae_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hboundMem : MemLp bound (2 : ℝ≥0∞) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (2 : ℝ≥0∞) μ) atTop (𝓝 0) := by
  let G : ℕ → α → ℝ≥0∞ := fun n x => ‖F n x‖ₑ ^ (2 : ℝ)
  let B : α → ℝ≥0∞ := fun x => ‖bound x‖ₑ ^ (2 : ℝ)
  have hGMeas : ∀ n, AEMeasurable (G n) μ := fun n => (hF n).enorm.pow_const _
  have hGBound : ∀ n, G n ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hbound n] with x hx
    exact ENNReal.rpow_le_rpow (by
      simpa using ENNReal.ofReal_le_ofReal hx) (by norm_num)
  have hGZero : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto 0).comp hx
    simpa only [Function.comp_def, G, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const :
        Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp henorm
  have hint : Tendsto (fun n => ∫⁻ x, G n x ∂μ) atTop (𝓝 0) := by
    simpa using
      tendsto_lintegral_of_dominated_convergence' B hGMeas hGBound ((lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num) (memLp_iff.mp hboundMem)).ne) hGZero
  simpa only [Function.comp_def, G, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : 2 ≠ ∞) (hF _), ENNReal.toReal_ofNat, one_div,
      ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)] using
    ((ENNReal.continuous_rpow_const :
      Continuous (fun a : ℝ≥0∞ => a ^ ((2 : ℝ)⁻¹))).tendsto 0).comp hint

/-- The positive part above a nonnegative constant belongs to `H¹` on an
arbitrary open set, with the strict-superlevel representative of its weak
gradient. -/
theorem exists_h1PositivePartSubConst_of_isOpen
    {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : IsOpen U) (u : PDE.H1Function U) (c : ℝ) (hc : 0 ≤ c) :
    ∃ v : PDE.H1Function U,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      v.grad = (fun x => {y | c < u.toFun y}.indicator u.grad x)  := by
  have hasWeakGradient_comp_contDiff_of_deriv_bounded_of_isOpen {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
      PDE.HasWeakGradientOn U (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by
    have hcompMem :
        MemLp (fun x => G (u.toFun x)) 2 (volume.restrict U) := by
      simpa only [Function.comp_def, PDE.volumeOn] using
        (PDE.lipschitzWith_of_abs_deriv_le hM (hG.differentiable (by norm_num)) hderiv).comp_memLp hG0 u.memL2
    have hgradMem (i : Fin d) :
        MemLp (fun x => deriv G (u.toFun x) * u.grad x i)
          2 (volume.restrict U) := by
      refine MemLp.of_le_mul (c := M) (u.gradMemL2 i) ?_ ?_
      · exact
          ((hG.continuous_deriv (by norm_num)).comp_aestronglyMeasurable
            u.memL2.aestronglyMeasurable).mul
            (u.gradMemL2 i).aestronglyMeasurable
      · filter_upwards with x
        simp [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (hderiv (u.toFun x)) (abs_nonneg (u.grad x i))
    apply PDE.HasWeakGradientOn.of_ballwise hU (locallyIntegrableOn_of_locallyIntegrable_restrict (hcompMem.locallyIntegrable (by norm_num)))
      (fun i => locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hgradMem i).locallyIntegrable (by norm_num)))
    intro x hx
    rcases Metric.isOpen_iff.1 hU x hx with ⟨δ, hδ, hball⟩
    let R : ℝ := δ / 2
    have hR : 0 < R := by
      dsimp only [R]
      positivity
    have hclosed :=
      (PDE.euclideanClosedBall_subset_supClosedBall hR.le).trans
        ((Metric.closedBall_subset_ball (by
          dsimp only [R]
          linarith)).trans hball)
    refine ⟨R, hR, hclosed, ?_⟩
    let uR :=
      u.restrict (PDE.isOpen_euclideanBall x R)
        ((PDE.euclideanBall_subset_euclideanClosedBall x R).trans hclosed)
    simpa only [uR, restrict_toFun, restrict_grad] using
      PDE.H1Function.hasWeakGradient_comp_contDiff_of_deriv_bounded
        (PDE.isOpenBoundedConvexDomain_euclideanBall x hR)
        uR hG hM hderiv
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδPos : ∀ n, 0 < δ n := by
    intro n
    dsimp only [δ]
    positivity
  have hδTendsto : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f : PDE.Vec d → ℝ := fun x => max (u.toFun x - c) 0
  let Du : PDE.Vec d → PDE.Vec d :=
    fun x => {y | c < u.toFun y}.indicator u.grad x
  let valueSeq : ℕ → PDE.Vec d → ℝ :=
    fun n x => PDE.smoothPositivePartApprox c (δ n) (u.toFun x)
  let gradSeq : ℕ → PDE.Vec d → PDE.Vec d :=
    fun n x i =>
      PDE.smoothPositivePartStep c (δ n) (u.toFun x) * u.grad x i
  have hDuCoord : ∀ x i,
      Du x i = (if c < u.toFun x then 1 else 0) * u.grad x i := by
    intro x i
    by_cases hx : c < u.toFun x <;> simp [Du, hx]
  have hvalueSeqAesm : ∀ n,
      AEStronglyMeasurable (valueSeq n) (PDE.volumeOn U) := by
    intro n
    exact
      (PDE.smoothPositivePartApprox_contDiff_one c (δ n)).continuous
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable
  have hgradSeqAesm : ∀ i n,
      AEStronglyMeasurable (fun x => gradSeq n x i) (PDE.volumeOn U) := by
    intro i n
    exact
      ((PDE.smoothPositivePartStep_continuous c (δ n))
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable).mul
        (u.gradMemL2 i).aestronglyMeasurable
  have hvalueTendsto : ∀ x,
      Tendsto (fun n => valueSeq n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have htwo : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
      simpa using hδTendsto.const_mul 2
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) htwo
    rw [Real.norm_eq_abs]
    exact PDE.abs_smoothPositivePartApprox_sub_le
      (hδPos n) (u.toFun x)
  have hgradTendsto : ∀ i x,
      Tendsto (fun n => gradSeq n x i) atTop (𝓝 (Du x i)) := by
    intro i x
    simpa only [gradSeq, hDuCoord x i] using (PDE.tendsto_smoothPositivePartStep (c := c) hδPos hδTendsto (u.toFun x)).mul_const (u.grad x i)
  have hfAesm : AEStronglyMeasurable f (PDE.volumeOn U) :=
    (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
  have hfMem : PDE.MemL2On U f := by
    refine MemLp.of_le u.memL2 hfAesm ?_
    filter_upwards with x
    simp [f]
    rcases le_or_gt (u.toFun x - c) 0 with hnonpos | hpos
    · simp [max_eq_right hnonpos, abs_nonneg]
    · rw [max_eq_left hpos.le, abs_of_pos hpos]
      calc
        u.toFun x - c ≤ u.toFun x := sub_le_self _ hc
        _ ≤ |u.toFun x| := le_abs_self _
  have hDuAesm : ∀ i,
      AEStronglyMeasurable (fun x => Du x i) (PDE.volumeOn U) := by
    intro i
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (hgradSeqAesm i)
      (Filter.Eventually.of_forall (hgradTendsto i))
  have hDuMem : PDE.GradMemL2On U Du := by
    intro i
    refine MemLp.of_le (u.gradMemL2 i) (hDuAesm i) ?_
    filter_upwards with x
    rw [hDuCoord x i]
    split_ifs
    · simpa using (le_rfl : ‖u.grad x i‖ ≤ ‖u.grad x i‖)
    · simpa [norm_zero] using norm_nonneg (u.grad x i)
  have hvalueSeqBound : ∀ n x, ‖valueSeq n x‖ ≤ ‖u.toFun x‖ := by
    intro n
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (PDE.smoothPositivePartApprox_nonneg (c := c) (hδPos n) (u.toFun x))]
    rcases le_or_gt (u.toFun x) c with hx | hx
    · rw [PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) hx]
      exact abs_nonneg _
    · calc
        PDE.smoothPositivePartApprox c (δ n) (u.toFun x)
            ≤ |u.toFun x - c| :=
          le_trans (le_abs_self _)
            (PDE.abs_smoothPositivePartApprox_le c (δ n) (u.toFun x))
        _ = u.toFun x - c := abs_of_pos (sub_pos.2 hx)
        _ ≤ u.toFun x := sub_le_self _ hc
        _ ≤ |u.toFun x| := le_abs_self _
  have hvalueSeqMem : ∀ n, PDE.MemL2On U (valueSeq n) := by
    intro n
    exact MemLp.of_le u.memL2 (hvalueSeqAesm n)
      (Filter.Eventually.of_forall (hvalueSeqBound n))
  have hgradSeqBound : ∀ n i x, ‖gradSeq n x i‖ ≤ ‖u.grad x i‖ := by
    intro n i x
    change ‖PDE.smoothPositivePartStep c (δ n) (u.toFun x) * u.grad x i‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |PDE.smoothPositivePartStep c (δ n) (u.toFun x)| * ‖u.grad x i‖
          ≤ 1 * ‖u.grad x i‖ :=
        mul_le_mul_of_nonneg_right
          (PDE.abs_smoothPositivePartStep_le_one c (δ n) (u.toFun x))
          (norm_nonneg (u.grad x i))
      _ = ‖u.grad x i‖ := one_mul _
  have hgradSeqMem : ∀ n, PDE.GradMemL2On U (gradSeq n) := by
    intro n i
    exact MemLp.of_le (u.gradMemL2 i) (hgradSeqAesm i n)
      (Filter.Eventually.of_forall (hgradSeqBound n i))
  have hweakSeq : ∀ n,
      PDE.HasWeakGradientOn U (valueSeq n) (gradSeq n) := by
    intro n
    simpa only [valueSeq, gradSeq, PDE.deriv_smoothPositivePartApprox] using
      hasWeakGradient_comp_contDiff_of_deriv_bounded_of_isOpen (PDE.smoothPositivePartApprox_contDiff_one c (δ n)) (PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) hc)
        zero_le_one (PDE.abs_deriv_smoothPositivePartApprox_le c (δ n))
  have hvalueConv : Tendsto
      (fun n => eLpNorm (valueSeq n - f) 2 (PDE.volumeOn U))
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_ae_dominated
      (bound := fun x => 2 * u.toFun x)
    · intro n
      exact (hvalueSeqAesm n).sub hfAesm
    · exact u.memL2.const_mul 2
    · intro n
      filter_upwards with x
      rw [Pi.sub_apply, norm_mul]
      exact (norm_sub_le _ _).trans (by
        rw [mul_comm]
        calc
          ‖valueSeq n x‖ + ‖f x‖ ≤ ‖u.toFun x‖ + ‖u.toFun x‖ := add_le_add
            (hvalueSeqBound n x) (by
              change ‖max (u.toFun x - c) 0‖ ≤ ‖u.toFun x‖
              rcases le_or_gt (u.toFun x - c) 0 with hx | hx
              · simp [hx]
              · rw [max_eq_left hx.le, Real.norm_eq_abs, abs_of_pos hx]
                exact (sub_le_self _ hc).trans (le_abs_self _))
          _ = ‖u.toFun x‖ * ‖(2 : ℝ)‖ := by norm_num; ring)
    · filter_upwards with x
      exact tendsto_sub_nhds_zero_iff.2 (hvalueTendsto x)
  have hgradConv : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => gradSeq n x i - Du x i)
        2 (PDE.volumeOn U)) atTop (𝓝 0) := by
    intro i
    apply tendsto_eLpNorm_two_zero_of_ae_dominated
      (bound := fun x => (2 : ℝ) * u.grad x i)
    · intro n
      exact (hgradSeqAesm i n).sub (hDuAesm i)
    · exact (u.gradMemL2 i).const_mul 2
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact (norm_sub_le _ _).trans (by
        rw [mul_comm]
        calc
          ‖gradSeq n x i‖ + ‖Du x i‖ ≤
              ‖u.grad x i‖ + ‖u.grad x i‖ := add_le_add
            (hgradSeqBound n i x) (by
              rw [hDuCoord x i]
              split_ifs <;> simp)
          _ = ‖u.grad x i‖ * ‖(2 : ℝ)‖ := by norm_num; ring)
    · filter_upwards with x
      exact tendsto_sub_nhds_zero_iff.2 (hgradTendsto i x)
  exact ⟨⟨f, Du, hfMem, hDuMem, (PDE.HasWeakGradientOn.of_tendsto_eLpNorm hfMem hDuMem hvalueSeqMem hgradSeqMem hweakSeq hvalueConv hgradConv)⟩, rfl, rfl⟩



/-- On an arbitrary open set, the selected weak gradient of an `H¹`
representative vanishes almost everywhere on its zero set. -/
theorem grad_ae_zero_on_zero_set_of_isOpen
    {d : ℕ} {U : Set (PDE.Vec d)} (hU : IsOpen U)
    (u : PDE.H1Function U) :
    ∀ᵐ x ∂(PDE.volumeOn U), u.toFun x = 0 → u.grad x = 0 := by
  obtain ⟨v₁, hv₁Fun, hv₁Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hU u 0 (by norm_num)
  obtain ⟨v₂, hv₂Fun, hv₂Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hU (-u) 0 (by norm_num)
  let v := v₁ - v₂
  have hvFun : v.toFun = u.toFun := by
    simp only [v, sub_toFun]
    funext x
    rw [hv₁Fun, hv₂Fun]
    simp only [neg_toFun, sub_zero]
    rcases le_total (u.toFun x) 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
  have hgradAE : ∀ᵐ x ∂(PDE.volumeOn U), v.grad x = u.grad x := by
    have hcoord : ∀ i : Fin d,
        (fun x => v.grad x i) =ᵐ[PDE.volumeOn U] (fun x => u.grad x i) := by
      intro i
      refine PDE.HasWeakPartialDerivOn.ae_eq hU
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((v.gradMemL2 i).locallyIntegrable (by norm_num)))
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((u.gradMemL2 i).locallyIntegrable (by norm_num)))
        (v.hasWeakGradient i) ?_
      rw [hvFun]
      exact u.hasWeakGradient i
    filter_upwards [(ae_all_iff.mpr hcoord)] with x hx
    funext i
    exact hx i
  filter_upwards [hgradAE] with x hx hux
  have hv₁Zero : v₁.grad x = 0 := by
    rw [hv₁Grad]
    change {y | 0 < u.toFun y}.indicator u.grad x = 0
    rw [indicator_of_notMem]
    simp [hux, lt_self_iff_false]
  have hv₂Zero : v₂.grad x = 0 := by
    rw [hv₂Grad]
    change {y | 0 < (-u).toFun y}.indicator (-u).grad x = 0
    rw [indicator_of_notMem]
    simp [neg_toFun, hux, lt_self_iff_false]
  rw [← hx]
  simp only [v, sub_grad]
  rw [hv₁Zero, hv₂Zero, sub_zero]

end PDE.H1Function

