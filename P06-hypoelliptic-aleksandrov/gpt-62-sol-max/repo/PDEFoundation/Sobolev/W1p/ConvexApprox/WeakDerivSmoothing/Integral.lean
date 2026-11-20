module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing.Affine

/-!
# Averaging weak derivatives over a convex smoothing kernel

Compact local integrability and Fubini give the exact smoothing derivative identity.
-/

@[expose] public section

open scoped ENNReal Pointwise

open MeasureTheory

namespace PDE

/-- The affine sample transports Lebesgue measure by a constant Jacobian,
independently of the center and the kernel variable. -/
private theorem map_convexApproxSample_volume {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (convexApproxSample x0 z r ε) volume =
      ENNReal.ofReal |((1 - ε) ^ Module.finrank ℝ (Vec d))⁻¹| • volume := by
  let b := ε • (x0 - r • z)
  let addB (y : Vec d) := y + b
  have hb : Measurable addB := by unfold addB; fun_prop
  have hm : Measurable (fun y : Vec d => (1 - ε) • y) := by fun_prop
  change Measure.map (addB ∘ fun y : Vec d => (1 - ε) • y) volume = _
  rw [← Measure.map_map hb hm, Measure.map_addHaar_smul volume (sub_ne_zero.mpr hε.ne'),
    Measure.map_smul _ hb.aemeasurable]
  rw [(measurePreserving_add_right volume b).map_eq]

/-- The joint sample law is dominated by the same Jacobian times the mass of the kernel carrier. -/
private theorem map_jointSample_le {d : ℕ} (K L : Set (Vec d)) (x0 : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (fun p : Vec d × Vec d => convexApproxSample x0 p.2 r ε p.1)
      ((volume.restrict K).prod (volume.restrict L)) ≤
      (ENNReal.ofReal |((1 - ε) ^ Module.finrank ℝ (Vec d))⁻¹| * volume.restrict L Set.univ) • volume := by
  let S (p : Vec d × Vec d) := convexApproxSample x0 p.2 r ε p.1
  have hS : Measurable S := by unfold S convexApproxSample; fun_prop
  refine Measure.le_iff.mpr fun A hA => ?_
  change Measure.map S _ A ≤ _
  rw [Measure.map_apply hS hA, Measure.prod_apply_symm (hS hA), Measure.smul_apply, smul_eq_mul]
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal |((1 - ε) ^ Module.finrank ℝ (Vec d))⁻¹| * volume A)
    fun z => ?_).trans_eq (by rw [lintegral_const]; ac_rfl)
  have hm : Measurable (convexApproxSample x0 z r ε) := by unfold convexApproxSample; fun_prop
  change volume.restrict K ((convexApproxSample x0 z r ε) ⁻¹' A) ≤ _
  calc
    _ ≤ volume ((convexApproxSample x0 z r ε) ⁻¹' A) := Measure.restrict_apply_le _ _
    _ = _ := by
      rw [← Measure.map_apply hm hA, map_convexApproxSample_volume x0 z r ε hε,
        Measure.smul_apply, smul_eq_mul]

private theorem integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {u ρ ψ : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume) (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Integrable (fun p : Vec d × Vec d =>
      ρ p.2 * Set.indicator U u (convexApproxSample x0 p.2 r ε p.1) * ψ p.1)
      ((volume.restrict (tsupport ψ)).prod (volume.restrict (tsupport ρ))) := by
  let K := tsupport ψ ×ˢ tsupport ρ
  let S (p : Vec d × Vec d) := convexApproxSample x0 p.2 r ε p.1
  let W := S '' K
  let μ := (volume.restrict (tsupport ψ)).prod (volume.restrict (tsupport ρ))
  have hK : IsCompact K := hc.isCompact.prod hρ.compactSupport.isCompact
  have hS : Continuous S := by unfold S convexApproxSample; fun_prop
  have hW : IsCompact W := hK.image hS
  have hWU : W ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact convexApproxSample_mem_of_isOpenBoundedConvexDomain hU (hs hp.1) hball hr
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hρ.support_subset_closedBall hp.2)
      hε0 hε1.le
  -- Truncate the profile only outside the compact image of the test and kernel supports.
  have hi := (hu.integrableOn_compact_subset hWU hW).integrable_indicator hW.measurableSet
  let : IsFiniteMeasure (volume.restrict (tsupport ρ)) :=
    isFiniteMeasure_restrict.mpr hρ.compactSupport.isCompact.measure_lt_top.ne
  have hsample : Integrable (fun p => W.indicator u (S p)) μ :=
    (hi.of_measure_le_smul (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (map_jointSample_le (tsupport ψ) (tsupport ρ) x0 r ε hε1)).comp_measurable hS.measurable
  obtain ⟨Cρ, hCρ⟩ := hρ.compactSupport.exists_bound_of_continuous hρ.continuous
  obtain ⟨Cψ, hCψ⟩ := hc.exists_bound_of_continuous hψ
  refine ((hsample.bdd_mul (hρ.continuous.measurable.comp measurable_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hCρ p.2)).mul_bdd
    (hψ.measurable.comp measurable_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hCψ p.1)).congr ?_
  change ∀ᵐ p ∂μ, ρ p.2 * W.indicator u (S p) * ψ p.1 =
    ρ p.2 * U.indicator u (S p) * ψ p.1
  dsimp only [μ]
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  have hmem : S p ∈ W := Set.mem_image_of_mem _ hp
  simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem (hWU hmem)]

namespace HasWeakPartialDerivOn

section
variable {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {i : Fin d}
  {u gi ρ : Vec d → ℝ} (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
  (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
  (hu : HasWeakPartialDerivOn U i u gi) (hρ : IsConvexApproxKernel ρ) {x0 : Vec d} {r ε : ℝ}
  (hball : Metric.closedBall x0 r ⊆ U)
include hU huLoc hgiLoc hu hρ hball

/-- Convex-domain smoothing commutes with a weak partial derivative, with the
exact factor `1 - ε` contributed by the affine sampling map. -/
theorem convexApproxSmoothing
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (PDE.convexApproxSmoothing ρ u x0 r ε)
      (fun x =>
        (1 - ε) *
          PDE.convexApproxSmoothing ρ gi x0 r ε x) := by
  intro φ hφSmooth hφCompact hφU
  let dφ (x : Vec d) := fderiv ℝ φ x (basisVec i)
  let S (z x : Vec d) := convexApproxSample x0 z r ε x
  have hρmeas := hρ.compactSupport.isCompact.measurableSet
  have hnorm {z} (hz : z ∈ tsupport ρ) : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hρ.support_subset_closedBall hz
  have hmap {z x} (hz : z ∈ tsupport ρ) (hx : x ∈ U) : S z x ∈ U :=
    convexApproxSample_mem_of_isOpenBoundedConvexDomain hU hx hball hr (hnorm hz) hε0 hε1.le
  -- The same Fubini identity applies to the value and to the derivative pairing.
  have hFubini (v ψ : Vec d → ℝ) (hv : LocallyIntegrableOn v U volume)
      (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
      (∫ x in U, PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x) =
      ∫ z in tsupport ρ, ρ z * ∫ x in U, v (S z x) * ψ x := by
    let F (x z : Vec d) := ρ z * Set.indicator U v (S z x) * ψ x
    have hRestr {g : Vec d → ℝ} (hg : ∀ x ∉ tsupport ψ, g x = 0) :
        (∫ x in U, g x) = ∫ x in tsupport ψ, g x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hs fun x hx => hg x hx.2
    have hψ0 {x} (hx : x ∉ tsupport ψ) : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    calc
      _ = ∫ x in tsupport ψ, PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x :=
        hRestr fun x hx => by rw [hψ0 hx, mul_zero]
      _ = ∫ x in tsupport ψ, ∫ z in tsupport ρ, F x z := by
        apply setIntegral_congr_fun (isClosed_tsupport (f := ψ)).measurableSet
        intro x hx
        dsimp only [PDE.convexApproxSmoothing]
        rw [← integral_mul_const]
        apply setIntegral_congr_fun hρmeas
        intro z hz
        simp only [F, convexApproxIntegrand, Set.indicator_of_mem (hmap hz (hs hx)), S]
      _ = ∫ z in tsupport ρ, ∫ x in tsupport ψ, F x z :=
        integral_integral_swap (f := F)
          (integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
            hU hv hρ hψ hc hs hball hr hε0 hε1)
      _ = _ := by
        apply setIntegral_congr_fun hρmeas
        intro z hz
        dsimp only
        rw [← hRestr (g := fun x => F x z) (fun x hx => by simp [F, hψ0 hx]), ← integral_const_mul]
        exact setIntegral_congr_fun hU.measurableSet fun x hx => by
          simp only [F, Set.indicator_of_mem (hmap hz hx), mul_assoc]
  have hdφ : tsupport dφ ⊆ U := (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hφU
  have hcφ : Continuous dφ := (hφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  change (∫ x in U, PDE.convexApproxSmoothing ρ u x0 r ε x * dφ x) =
    -∫ x in U, ((1 - ε) * PDE.convexApproxSmoothing ρ gi x0 r ε x) * φ x
  simp_rw [mul_assoc (1 - ε), integral_const_mul,
    hFubini u dφ huLoc hcφ (hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)) hdφ,
    hFubini gi φ hgiLoc hφSmooth.continuous hφCompact hφU]
  rw [← neg_mul, ← integral_const_mul]
  apply setIntegral_congr_fun hρmeas
  intro z hz
  have hw := (hu.comp_convexApproxSample hU hball hr (hnorm hz) hε0 hε1)
    φ hφSmooth hφCompact hφU
  change (∫ x in U, u (S z x) * dφ x) = -∫ x in U, ((1 - ε) * gi (S z x)) * φ x at hw
  simp_rw [mul_assoc (1 - ε), integral_const_mul] at hw
  dsimp only
  rw [hw]
  ring

/-- The globally smooth representative has the same weak partial derivative
as convex-approximation smoothing on the domain. -/
theorem convexApproxSmoothRepresentative
    (hr : 0 < r) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (PDE.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x =>
        (1 - ε) *
          PDE.convexApproxSmoothRepresentative
            U ρ gi x0 r ε x) := by
  intro φ hφSmooth hφCompact hφU
  have hweak :=
    hu.convexApproxSmoothing
      hU huLoc hgiLoc hρ hball hr.le hε0.le hε1
  have hleft :
      (∫ x in U,
          PDE.convexApproxSmoothRepresentative
              U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hU.measurableSet ?_
    intro x hx
    change
      PDE.convexApproxSmoothRepresentative
            U ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i) =
        PDE.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hr hε0 hε1]
  have hright :
      (∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothing ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume) =
        ∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothRepresentative
                U ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hU.measurableSet ?_
    intro x hx
    change
      ((1 - ε) *
          PDE.convexApproxSmoothing ρ gi x0 r ε x) *
          φ x =
        ((1 - ε) *
            PDE.convexApproxSmoothRepresentative
              U ρ gi x0 r ε x) *
          φ x
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hr hε0 hε1]
  calc
    (∫ x in U,
        PDE.convexApproxSmoothRepresentative U ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume :=
      hleft
    _ = -∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothing ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume :=
      hweak φ hφSmooth hφCompact hφU
    _ = -∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothRepresentative
                U ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume := by
      rw [hright]

end

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

end HasWeakGradientOn

end PDE
