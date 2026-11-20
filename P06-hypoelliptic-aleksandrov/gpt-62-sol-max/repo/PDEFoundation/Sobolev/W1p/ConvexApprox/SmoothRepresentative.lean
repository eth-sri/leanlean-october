module

public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Measure.ConvolutionContraction
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth representatives for convex-domain approximation

This file defines the globally smooth representative of convex approximation.
It also records the measurable change of variables, exact `L^p` bounds, and
integrability lemmas needed by the later density and weak-derivative modules.
-/

@[expose] public section

open scoped ENNReal Pointwise Convolution

namespace PDE

open MeasureTheory

noncomputable section

/-- A globally smooth representative of convex-domain approximation. -/
noncomputable def convexApproxSmoothRepresentative
    {d : ℕ} (U : Set (Vec d)) (ρ u : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) : Vec d → ℝ :=
  fun x =>
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0)

section
variable {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ}

theorem contDiff_convexApproxSmoothRepresentative {p : ENNReal}
    (hU : MeasurableSet U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (convexApproxSmoothRepresentative
        U ρ u x0 r ε) := by
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hU]
    exact hu
  have huLocallyIntegrable := huIndicator.locallyIntegrable hp
  have hconv :=
    HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume)
      (f := scaledConvexApproxKernel ρ (ε * r))
      (g := Set.indicator U u)
      (hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport hεr)
      (contDiff_scaledConvexApproxKernel hρ (ε * r))
      huLocallyIntegrable
  have haffine :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec d =>
          (1 - ε) • x + ε • x0) := by
    exact
      ((contDiff_id :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun x : Vec d => x)).const_smul (1 - ε)).add contDiff_const
  exact hconv.comp haffine

theorem
    convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    convexApproxSmoothRepresentative U ρ u x0 r ε x =
      convexApproxSmoothing ρ u x0 r ε x := id (Eq.symm (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator hU hρ hx hball hr hε hεOne))

end

theorem measurableEmbedding_convexApproxSample
    {d : ℕ} (x0 z : Vec d) (r ε : ℝ)
    (hε : ε < 1) :
    MeasurableEmbedding
      (convexApproxSample x0 z r ε) := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)
  have haPos : 0 < a := by
    dsimp only [a]
    linarith
  have haNe : a ≠ 0 :=
    haPos.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    (Homeomorph.smulOfNeZero a haNe).trans
      (Homeomorph.addRight b)
  have heq :
      (fun x : Vec d => e x) =
        convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  rw [← heq]
  exact e.toMeasurableEquiv.measurableEmbedding

section
variable {d : ℕ} {U : Set (Vec d)}

theorem map_restrict_convexApproxSample
    (_hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
        volume.restrict
          (convexApproxSample x0 z r ε '' U) := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)
  have haPos : 0 < a := by
    dsimp only [a]
    linarith
  have haNe : a ≠ 0 :=
    haPos.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    (Homeomorph.smulOfNeZero a haNe).trans
      (Homeomorph.addRight b)
  have heq :
      (fun x : Vec d => e x) =
        convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  have hrestrict :
      Measure.map (convexApproxSample x0 z r ε)
          (volume.restrict U) =
        (Measure.map (convexApproxSample x0 z r ε)
          volume).restrict
            (convexApproxSample x0 z r ε '' U) := by
    have htmp :
        (volume.restrict U).map e =
          (volume.map e).restrict (e '' U) := by
      have h :=
        ((e.toMeasurableEquiv.restrict_map
          (μ := volume) (s := e '' U)).symm)
      simpa [Set.preimage_image_eq _ e.injective] using h
    simpa [heq] using htmp
  have hmapVolume :
      Measure.map (convexApproxSample x0 z r ε) volume =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume := by
    have hmapSmul :
        Measure.map (fun x : Vec d => a • x) volume =
          ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
      let f : Vec d →ₗ[ℝ] Vec d :=
        a • (1 : Vec d →ₗ[ℝ] Vec d)
      have hf : LinearMap.det f ≠ 0 := by
        simp [f, haNe]
      have hdet : LinearMap.det f = a ^ d := by
        simp [f]
      have hmapf :=
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (ι := Fin d) (f := f) hf
      have hpowInvNonneg : 0 ≤ (a ^ d)⁻¹ := by
        positivity
      rw [hdet] at hmapf
      have hfun : (fun x : Vec d => a • x) = ⇑f := by
        funext x
        simp [f]
      rw [hfun]
      simpa only [abs_of_nonneg hpowInvNonneg] using
        hmapf
    calc
      Measure.map (convexApproxSample x0 z r ε) volume =
          (Measure.map (fun x : Vec d => a • x)
            volume).map
              (fun y : Vec d => y + b) := by
        rw [Measure.map_map
            (μ := volume)
            (g := fun y : Vec d => y + b)
            (f := fun x : Vec d => a • x)
            (measurable_id.add measurable_const)
            (measurable_const_smul a)]
        rfl
      _ =
          Measure.map (fun y : Vec d => y + b)
            (ENNReal.ofReal ((a ^ d)⁻¹) • volume) := by
        rw [hmapSmul]
      _ =
          ENNReal.ofReal ((a ^ d)⁻¹) •
            Measure.map (fun y : Vec d => y + b)
              volume := by
        rw [Measure.map_smul (f := fun y : Vec d => y + b) _
          (measurable_add_const b).aemeasurable]
      _ =
          ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
        rw [map_add_right_eq_self]
      _ =
          ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume := by
        simp only [a]
  calc
    Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      (Measure.map (convexApproxSample x0 z r ε)
        volume).restrict
          (convexApproxSample x0 z r ε '' U) :=
      hrestrict
    _ =
        (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume).restrict
            (convexApproxSample x0 z r ε '' U) := by
      rw [hmapVolume]
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume.restrict
            (convexApproxSample x0 z r ε '' U) := by
      rw [Measure.restrict_smul]

theorem eLpNorm_comp_convexApproxSample_le
    {u : Vec d → ℝ} {p : ENNReal}
    (hp : p ≠ ⊤) (hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1)
    (hmap :
      convexApproxSample x0 z r ε '' U ⊆ U) :
    eLpNorm
        (fun x => u (convexApproxSample x0 z r ε x))
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) := by
  by_cases huMeas : AEStronglyMeasurable u (volume.restrict U)
  swap
  · have hc : ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal ≠ 0 :=
      (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (sub_pos.2 hε) d)))
        ENNReal.ofReal_ne_top).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable huMeas, ENNReal.mul_top hc]
    exact le_top
  calc
    eLpNorm
        (fun x => u (convexApproxSample x0 z r ε x))
        p (volume.restrict U) =
      eLpNorm u p
        (Measure.map
          (convexApproxSample x0 z r ε)
          (volume.restrict U)) := by
      symm
      exact
        (measurableEmbedding_convexApproxSample
          x0 z r ε hε).eLpNorm_map_measure
    _ =
        eLpNorm u p
          (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [map_restrict_convexApproxSample
        hU x0 z r ε hε]
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal •
          eLpNorm u p
            (volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [eLpNorm_smul_measure_of_ne_top hp _ _
        (huMeas.mono_measure (Measure.restrict_mono_set volume hmap))]
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal •
          eLpNorm u p (volume.restrict U) := by
      exact
        smul_le_smul_of_nonneg_left
          (eLpNorm_mono_measure u
            (Measure.restrict_mono_set volume hmap))
          (by positivity)
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p (volume.restrict U) := by
      rw [smul_eq_mul]

theorem eLpNorm_convexApproxSmoothing_le
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) := by
  let g : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  have hUMeas := hU.isOpen.measurableSet
  have hmapZeroMapsTo :
      Set.MapsTo
        (convexApproxSample x0 0 r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr.le (by simp) hε.le (le_of_lt hεOne)
  have hmapZero :
      convexApproxSample x0 0 r ε '' U ⊆ U := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmapZeroMapsTo hx
  have hrepresentative :
      (fun x =>
        convexApproxSmoothing ρ u x0 r ε x) =ᵐ[
          volume.restrict U]
        fun x =>
          g (convexApproxSample x0 0 r ε x) := by
    filter_upwards [ae_restrict_mem hUMeas] with x hx
    simpa [g, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u)
        hU hρ hx hball hr hε hεOne)
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hconv :
      eLpNorm g p volume ≤
        eLpNorm (Set.indicator U u) p volume := by
    dsimp only [g]
    exact
      eLpNorm_convolution_le_of_integral_one hpOne hpTop
        (scaledConvexApproxKernel_nonneg hρ hεr)
        (integrable_scaledConvexApproxKernel hρ hεr)
        (integral_scaledConvexApproxKernel hρ hεr)
        (measurable_scaledConvexApproxKernel
          hρ.continuous (ε * r))
        huIndicator.aestronglyMeasurable.aemeasurable
  calc
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) =
      eLpNorm
        (fun x =>
          g (convexApproxSample x0 0 r ε x))
        p (volume.restrict U) :=
      eLpNorm_congr_ae hrepresentative
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm g p (volume.restrict U) :=
      eLpNorm_comp_convexApproxSample_le
        hpTop hUMeas x0 0 r ε hεOne hmapZero
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm g p volume :=
      mul_le_mul' le_rfl
        (eLpNorm_mono_measure g
          Measure.restrict_le_self)
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm (Set.indicator U u) p volume :=
      mul_le_mul' le_rfl hconv
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p (volume.restrict U) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUMeas]

end

section
variable {d : ℕ} {U : Set (Vec d)} {ρ u v : Vec d → ℝ} {p : ENNReal}
  (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
include hU hρ

theorem convexApproxSmoothing_sub_ae_eq
    (hp : 1 ≤ p)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    (fun x =>
      convexApproxSmoothing ρ
        (fun y => u y - v y) x0 r ε x) =ᵐ[
          volume.restrict U]
      fun x =>
        convexApproxSmoothing ρ u x0 r ε x -
          convexApproxSmoothing ρ v x0 r ε x := by
  let k : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r)
  let gu : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  let gv : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U v
  let gw : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U (fun y => u y - v y)
  have hUMeas : MeasurableSet U :=
    hU.isOpen.measurableSet
  have hεr : 0 < ε * r := by
    positivity
  have hkContinuous : Continuous k := by
    dsimp only [k]
    exact
      continuous_scaledConvexApproxKernel
        hρ.continuous (ε * r)
  have hkCompact : HasCompactSupport k := by
    dsimp only [k]
    exact
      hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport hεr
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hvIndicator :
      MemLp (Set.indicator U v) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hv
  have huLocallyIntegrable :
      LocallyIntegrable (Set.indicator U u) volume :=
    huIndicator.locallyIntegrable hp
  have hvLocallyIntegrable :
      LocallyIntegrable (Set.indicator U v) volume :=
    hvIndicator.locallyIntegrable hp
  have hnegvLocallyIntegrable :
      LocallyIntegrable
        ((-1 : ℝ) • Set.indicator U v) volume := by
    simpa using hvLocallyIntegrable.smul (-1 : ℝ)
  have hconvU :
      ConvolutionExists k (Set.indicator U u)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous huLocallyIntegrable
  have hconvNegV :
      ConvolutionExists k
        ((-1 : ℝ) • Set.indicator U v)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous hnegvLocallyIntegrable
  have hindicatorSub :
      Set.indicator U (fun y => u y - v y) =
        Set.indicator U u +
          (-1 : ℝ) • Set.indicator U v := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx, sub_eq_add_neg]
    · simp [hx]
  have hconvSub :
      gw = fun x => gu x - gv x := by
    ext x
    dsimp only [gw, gu, gv]
    rw [hindicatorSub,
      hconvU.distrib_add hconvNegV, convolution_smul]
    simp [sub_eq_add_neg]
  filter_upwards [ae_restrict_mem hUMeas] with x hx
  have huRepresentative :
      convexApproxSmoothing ρ u x0 r ε x =
        gu (convexApproxSample x0 0 r ε x) := by
    simpa [gu, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u) hU hρ hx hball hr hε hεOne)
  have hvRepresentative :
      convexApproxSmoothing ρ v x0 r ε x =
        gv (convexApproxSample x0 0 r ε x) := by
    simpa [gv, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := v) hU hρ hx hball hr hε hεOne)
  have hwRepresentative :
      convexApproxSmoothing ρ
          (fun y => u y - v y) x0 r ε x =
        gw (convexApproxSample x0 0 r ε x) := by
    simpa [gw, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := fun y => u y - v y)
        hU hρ hx hball hr hε hεOne)
  rw [huRepresentative, hvRepresentative, hwRepresentative]
  rw [hconvSub]

theorem eLpNorm_sub_convexApproxSmoothing_le
    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r ε x -
            convexApproxSmoothing ρ v x0 r ε x)
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm (fun x => u x - v x)
          p (volume.restrict U) := by
  have huv := hu.sub hv
  calc
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r ε x -
            convexApproxSmoothing ρ v x0 r ε x)
        p (volume.restrict U) =
      eLpNorm
        (convexApproxSmoothing ρ
          (fun y => u y - v y) x0 r ε)
        p (volume.restrict U) := by
      exact
        eLpNorm_congr_ae
          (convexApproxSmoothing_sub_ae_eq
            hU hρ hpOne hu hv
            hball hr hε hεOne).symm
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm (fun x => u x - v x)
            p (volume.restrict U) :=
      eLpNorm_convexApproxSmoothing_le
        hU hρ hpOne hpTop huv hball hr hε hεOne

end

end

end PDE
