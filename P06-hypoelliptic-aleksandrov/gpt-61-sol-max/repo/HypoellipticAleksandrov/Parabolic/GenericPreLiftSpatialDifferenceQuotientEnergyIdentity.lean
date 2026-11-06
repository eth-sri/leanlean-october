module

public import HypoellipticAleksandrov.Parabolic.ParabolicMemLpSpatialDifferenceQuotient
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
section
open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
private alias _sharedProof_83_2 := HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport
end


/-!
# Quotient-test energy identity

This module begins the direct spacetime-mollification proof of the localized
spatial difference-quotient energy identity.  The private infrastructure below
constructs a precompact shift-safe collar and globalizes the localized value
and its selected weak spatial derivatives.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convolution ENNReal Pointwise
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
open SpacetimeMollifierWeightedTimeEnergy

variable {d : ℕ}

variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d}









private theorem timeDerivative_tsupport_subset
      :
    tsupport (timeDerivative f) ⊆ tsupport f := (_sharedProof_83_2 f)


section
variable (k : Fin d) (h : ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiff ℝ PDE.smoothOrder f)

include hf
/-- Time differentiation commutes exactly with a spatial difference quotient. -/
private theorem timeDerivative_spatialDifferenceQuotient
      :
    timeDerivative (spatialDifferenceQuotient k h f) =
      spatialDifferenceQuotient k h (timeDerivative f) := by
  funext z
  have htrans : DifferentiableAt ℝ (spatialTranslate k h f) z :=
    (ContDiff.spatialTranslate hf).differentiable (by simp) z
  have hfd : DifferentiableAt ℝ f z := hf.differentiable (by simp) z
  have ht := timeDerivative_spatialTranslate k h f z
  unfold timeDerivative at ht
  unfold timeDerivative spatialDifferenceQuotient
  rw [show (fun z ↦ (spatialTranslate k h f z - f z) / h) =
      fun z ↦ h⁻¹ * (spatialTranslate k h f z - f z) by
        funext y
        ring]
  rw [fderiv_const_mul (a := fun y ↦ spatialTranslate k h f y - f y)
    (htrans.sub hfd)]
  rw [show fderiv ℝ (fun y ↦ spatialTranslate k h f y - f y) z =
      fderiv ℝ (spatialTranslate k h f) z - fderiv ℝ f z from
    (htrans.hasFDerivAt.sub hfd.hasFDerivAt).fderiv]
  simp [ht, div_eq_mul_inv, mul_comm]

/-- A selected velocity derivative commutes exactly with a spatial difference
quotient of a smooth function. -/
private theorem velocityGradient_spatialDifferenceQuotient
      (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (spatialDifferenceQuotient k h f) z i =
      spatialDifferenceQuotient k h (fun y ↦ velocityGradient f y i) z := by
  have htrans : DifferentiableAt ℝ (spatialTranslate k h f) z :=
    (ContDiff.spatialTranslate hf).differentiable (by simp) z
  have hfd : DifferentiableAt ℝ f z := hf.differentiable (by simp) z
  have hv := congrFun (velocityGradient_spatialTranslate k h f z) i
  unfold velocityGradient at hv
  unfold velocityGradient spatialDifferenceQuotient
  rw [show (fun y ↦ (spatialTranslate k h f y - f y) / h) =
      fun y ↦ h⁻¹ * (spatialTranslate k h f y - f y) by
        funext y
        ring]
  rw [fderiv_const_mul (a := fun y ↦ spatialTranslate k h f y - f y)
    (htrans.sub hfd)]
  rw [show fderiv ℝ (fun y ↦ spatialTranslate k h f y - f y) z =
      fderiv ℝ (spatialTranslate k h f) z - fderiv ℝ f z from
    (htrans.hasFDerivAt.sub hfd.hasFDerivAt).fderiv]
  simp [hv, div_eq_mul_inv, mul_comm]
end


/-- A selected velocity derivative of a backward quotient transposes from a
smooth compact test to the forward quotient of an `L²` factor. -/
private theorem setIntegral_mul_velocityGradient_spatialDifferenceQuotient_neg
     {S C V : HypoellipticAleksandrov.Parabolic.Region d}
    (hSmeas : MeasurableSet S) (hCcompact : IsCompact C)
    (hCS : C ⊆ S) (hVC : V ⊆ C)
    (H : HypoellipticAleksandrov.Parabolic.ScalarField d) (hH : ParabolicMemLpOn C 2 H)
    (k : Fin d) (h : ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hfSmooth : ContDiff ℝ PDE.smoothOrder f)
    (hfCompact : HasCompactSupport f) (hfSupport : tsupport f ⊆ V)
    (hfShift : Set.MapsTo (spatialShift k h) V C) (i : Fin d) :
    (∫ z in S, H z * velocityGradient
        (spatialDifferenceQuotient k (-h) f) z i) =
      -∫ z in V, spatialDifferenceQuotient k h H z * velocityGradient f z i := by
  let g  := fun z ↦ velocityGradient f z i


  have hgSupport : tsupport g ⊆ V :=
    _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset.trans hfSupport
  have hquotSupport  :=
    tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k (-h) g hgSupport hVC (by simpa using hfShift)
  have hrestrictLeft :
      (∫ z in S, H z * spatialDifferenceQuotient k (-h) g z) =
        ∫ z in C, H z * spatialDifferenceQuotient k (-h) g z := by
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hSmeas hCS
      (fun z hz ↦ by

        rw [(image_eq_zero_of_notMem_tsupport (fun hzt ↦ hz.2 (hquotSupport hzt)))]
        simp)
  have htranspose :=
    setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      C k h H g hH (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty hfSmooth).continuous (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hfCompact)
      (hgSupport.trans hVC) (fun z hz ↦ hfShift (hgSupport hz))
  have hrestrictRight :
      (∫ z in C, spatialDifferenceQuotient k h H z * g z) =
        ∫ z in V, spatialDifferenceQuotient k h H z * g z := by
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hCcompact.measurableSet hVC
      (fun z hz ↦ by

        rw [(image_eq_zero_of_notMem_tsupport (fun hzt ↦ hz.2 (hgSupport hzt)))]
        simp)
  simp_rw [velocityGradient_spatialDifferenceQuotient k (-h) f hfSmooth i]
  linarith

/-- Transposition of the time derivative of a backward quotient from a smooth
compact test to the forward quotient of the rough factor, with the latter
pairing restricted to its shift-safe carrier. -/
private theorem setIntegral_mul_timeDerivative_spatialDifferenceQuotient_neg
     {S V : HypoellipticAleksandrov.Parabolic.Region d}
    (hSmeas : MeasurableSet S) (hVS : V ⊆ S)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : ParabolicMemLpOn S 2 q)
    (k : Fin d) (h : ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hfSmooth : ContDiff ℝ PDE.smoothOrder f)
    (hfCompact : HasCompactSupport f) (hfSupport : tsupport f ⊆ V)
    (hfShift : Set.MapsTo (spatialShift k h) V S) :
    (∫ z in S, q z * timeDerivative
        (spatialDifferenceQuotient k (-h) f) z) =
      -∫ z in V, spatialDifferenceQuotient k h q z * timeDerivative f z := by
  let sharedTerm_0d3f736ec6 := (∫ z in V, spatialDifferenceQuotient k h q z * timeDerivative f z)
  let sharedTerm_cb9337ac27 := (∫ z in S, spatialDifferenceQuotient k h q z * timeDerivative f z)


  have hdtSupport : tsupport (timeDerivative f) ⊆ V :=
    timeDerivative_tsupport_subset.trans hfSupport
  have htranspose :=
    setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      S k h q _ hq (show ContDiff ℝ PDE.smoothOrder (timeDerivative f) by
          unfold timeDerivative
          exact (contDiff_infty_iff_fderiv.mp hfSmooth).2.clm_apply contDiff_const).continuous (by
          unfold timeDerivative
          simpa using hfCompact.fderiv_apply (𝕜 := ℝ) ((1, 0) ))
      (hdtSupport.trans hVS) (fun z hz ↦ hfShift (hdtSupport hz))
  have hrestrict :
      (sharedTerm_cb9337ac27) =
        sharedTerm_0d3f736ec6 := by
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hSmeas hVS
      (fun z hz ↦ by

        simp [(image_eq_zero_of_notMem_tsupport (fun hzt ↦ hz.2 (hdtSupport hzt)))])
  rw [timeDerivative_spatialDifferenceQuotient k (-h) f hfSmooth]
  calc
    (∫ z in S, q z * spatialDifferenceQuotient k (-h) (timeDerivative f) z) =
        -(sharedTerm_cb9337ac27) := by
      linarith
    _ = -sharedTerm_0d3f736ec6 := by
      rw [hrestrict]

private theorem tsupport_spacetimeMollification_subset_cthickening
     {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (spacetimeMollification ε f) ⊆ Metric.cthickening ε (tsupport f) := (closure_mono (by
      intro z hz
      have hzsum := support_convolution_subset
        _ hz
      rcases hzsum with ⟨x, hx, y, hy, rfl⟩
      apply Metric.mem_thickening_iff.mpr
      refine ⟨y, subset_tsupport f hy, ?_⟩
      rw [dist_eq_norm]
      simpa [spacetimeMollifier_support hε] using hx)).trans
    (Metric.closure_thickening_subset_cthickening ε (tsupport f))

/-- A local `L²` representative can be globalized without changing the
weighted time-energy pairing near the support of the smooth weight. -/
private theorem tendsto_localized_timeEnergy_spacetimeMollification
     {V : HypoellipticAleksandrov.Parabolic.Region d}
    (hVopen : IsOpen V)
    (qh w : HypoellipticAleksandrov.Parabolic.ScalarField d) (hqh : ParabolicMemLpOn V 2 qh)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    Filter.Tendsto (fun ε  ↦ ∫ z in V, qh z *
        timeDerivative (spacetimeMollification ε (fun y ↦ w y * qh y)) z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * ∫ z in V,
        timeDerivative w z * qh z ^ 2)) := by
  let sharedTerm_71ecdf62d0 := ((fun y ↦ w y * qh y))
  obtain ⟨δ, hδ, χ, hχSmooth, hχCompact, hχSupport, hχOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset
      hVopen hwCompact.isCompact hwSupport
  let Q  := fun z ↦ χ z * qh z



  have hQ  :=
    (show ParabolicMemLpOn V 2 Q by
        simpa only [Q, mul_comm] using hqh.fun_mul (show ParabolicMemLpOn V ∞ χ from (hχSmooth.continuous.memLp_of_hasCompactSupport hχCompact).restrict V)).memLp_of_support_subset hVopen.measurableSet (by
        intro z hz
        have hzχ : χ z ≠ 0 := by
          intro hzero
          apply hz
          simp [Q, hzero]
        exact hχSupport (subset_tsupport χ hzχ))
  have hχOneK : Set.EqOn χ 1 (tsupport w) := fun z hz ↦
    hχOne (Metric.self_subset_cthickening (tsupport w) hz)
  have hwQ : (fun z ↦ w z * Q z) = fun z ↦ w z * qh z := by
    funext z
    by_cases hz : z ∈ tsupport w
    · simp [Q, hχOneK hz]
    ·
      simp [(image_eq_zero_of_notMem_tsupport hz)]
  have hwtQsq : (fun z ↦ timeDerivative w z * Q z ^ 2) =
      fun z ↦ timeDerivative w z * qh z ^ 2 := by
    funext z
    by_cases hz : z ∈ tsupport w
    · simp [Q, hχOneK hz]
    · have hwtz  :=
        image_eq_zero_of_notMem_tsupport
          (fun hzt ↦ hz (timeDerivative_tsupport_subset hzt))
      simp [hwtz]
  have hglobal :=
    tendsto_integral_mul_timeDerivative_spacetimeMollification_mul
      Q w hQ hwSmooth hwCompact

  have hlimitEq :
      ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
          timeDerivative w z * Q z ^ 2) =
        (1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2 := by
    rw [hwtQsq]
    congr 1
    have ht := setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (μ := (volume )) MeasurableSet.univ
      (subset_univ V) (f := fun z ↦ timeDerivative w z * qh z ^ 2) (fun z hz ↦ by
        have hwtz  :=
          image_eq_zero_of_notMem_tsupport
            (fun hzt ↦ hz.2 (hwSupport (timeDerivative_tsupport_subset hzt)))
        rw [hwtz]
        simp)
    simpa only [Measure.restrict_univ] using ht
  rw [← hlimitEq]
  exact hglobal.congr' (by
      filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < δ from hδ)).filter_mono
          inf_le_left,
        self_mem_nhdsWithin] with ε hεδ hεpos
      rw [hwQ]
      let D  := fun z ↦ timeDerivative
        (spacetimeMollification ε sharedTerm_71ecdf62d0) z
      have hχ_at_D (z : TimeVelocity d) (hzD : D z ≠ 0) : χ z = 1 := by
        have hzmoll := timeDerivative_tsupport_subset (subset_tsupport D hzD)


        exact hχOne (Metric.cthickening_mono hεδ.le (tsupport w)
          ((show Metric.cthickening ε
            (tsupport sharedTerm_71ecdf62d0) ⊆
            Metric.cthickening ε (tsupport w) by
              exact Metric.cthickening_subset_of_subset ε tsupport_mul_subset_left) (tsupport_spacetimeMollification_subset_cthickening hεpos hzmoll)))
      calc
        (∫ z : TimeVelocity d, Q z * D z) = ∫ z in V, Q z * D z := by
          have ht := setIntegral_eq_of_subset_of_forall_diff_eq_zero
            (μ := (volume )) MeasurableSet.univ
            (subset_univ V) (f := fun z ↦ Q z * D z) (fun z hz ↦ by
              by_cases hzD : D z = 0
              · simp [hzD]
              ·

                exact (hz.2 (show z ∈ V from hχSupport (subset_tsupport χ (by simp [(hχ_at_D z hzD)])))).elim)
          simpa only [Measure.restrict_univ] using ht
        _ = ∫ z in V, qh z * D z := by
          apply integral_congr_ae
          filter_upwards [] with z
          by_cases hzD : D z = 0
          · simp [hzD]
          · simp [Q, hχ_at_D z hzD])

/-- The localized quotient test and all its selected spatial derivatives have
global `L²` representatives and ambient weak-derivative relations. -/
private theorem exists_global_localizedQuotient_weakGradient
     {S : HypoellipticAleksandrov.Parabolic.Region d} (hS : IsOpen S)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : ParabolicMemLpOn S 2 q)
    (hG : ∀ j, ParabolicMemLpOn S 2 (G j))
    (hWeak : ∀ j, HasWeakVelocityPartialDerivOn S j q (G j))
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ S)
    (k : Fin d) (h : ℝ)
    (hwShift : Set.MapsTo (spatialShift k h) (tsupport w) S) :
    ∃ V C : HypoellipticAleksandrov.Parabolic.Region d, IsOpen V ∧ IsCompact (closure V) ∧
      tsupport w ⊆ V ∧ V ⊆ S ∧
      IsCompact C ∧ V ⊆ C ∧ C ⊆ S ∧
      Set.MapsTo (spatialShift k h) V C ∧
      ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h q) ∧
      (∀ i, ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h (G i))) ∧
      (∀ i, HasWeakVelocityPartialDerivOn V i
        (spatialDifferenceQuotient k h q)
        (spatialDifferenceQuotient k h (G i))) ∧
      MemLp (fun z ↦ w z * spatialDifferenceQuotient k h q z) 2  ∧
      (∀ i, MemLp (fun z ↦
        velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z) 2 ) ∧
      (∀ i, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z ↦ w z * spatialDifferenceQuotient k h q z)
        (fun z ↦ velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z)) ∧
      ∀ i, tsupport (fun z ↦
        velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z) ⊆ V := by
  let K  := tsupport w
  let U  :=
    S ∩ spatialShift k h ⁻¹' S
  have hshiftContinuous : Continuous (spatialShift k h) := by
    convert (Homeomorph.addRight
      ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous using 1
    funext z
    apply Prod.ext
    · rfl
    · rfl


  obtain ⟨δ, hδ, hcollar⟩ := hwCompact.isCompact.exists_cthickening_subset_open (hS.inter (hS.preimage hshiftContinuous)) (by
      intro z hz
      exact ⟨hwSupport hz, hwShift hz⟩)
  let V  := Metric.thickening δ K
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hVclosure : IsCompact (closure V) := by
    apply IsCompact.of_isClosed_subset hwCompact.isCompact.cthickening isClosed_closure
    exact Metric.closure_thickening_subset_cthickening δ K
  have hKV : K ⊆ V := Metric.self_subset_thickening hδ K
  have hVU : V ⊆ U :=
    (Metric.thickening_subset_cthickening δ K).trans hcollar
  have hclosureVU : closure V ⊆ U :=
    (Metric.closure_thickening_subset_cthickening δ K).trans hcollar
  have hVS : V ⊆ S := fun z hz ↦ (hVU hz).1
  have hVshift : Set.MapsTo (spatialShift k h) V S := fun z hz ↦ (hVU hz).2





  let qh  := spatialDifferenceQuotient k h q
  let Gh  := fun i ↦
    spatialDifferenceQuotient k h (G i)
  let ψ  := fun z ↦ w z * qh z
  let Dψ  := fun i z ↦
    velocityGradient w z i * qh z + w z * Gh i z
  have hqh : ParabolicMemLpOn V 2 qh :=
    hq.spatialDifferenceQuotient_of_subset_mapsTo k h hVS hVshift
  have hGh (i : Fin d) : ParabolicMemLpOn V 2 (Gh i) :=
    (hG i).spatialDifferenceQuotient_of_subset_mapsTo k h hVS hVshift
  have hqhWeak (i : Fin d) : HasWeakVelocityPartialDerivOn V i qh (Gh i) := (hWeak i).spatialDifferenceQuotient_of_subset_mapsTo
      (hq.locallyIntegrableOn (by norm_num))
      ((hG i).locallyIntegrableOn (by norm_num)) k h hVS hVshift
  have hwTop : ParabolicMemLpOn V ∞ w :=
    (hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact).restrict V
  have hdwTop (i : Fin d) : ParabolicMemLpOn V ∞
      (fun z ↦ velocityGradient w z i) :=
    ((_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty (i := i) hwSmooth).continuous.memLp_of_hasCompactSupport
      (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport  hwCompact)).restrict V

  have hDψV (i : Fin d) : ParabolicMemLpOn V 2 (Dψ i) := by


    exact (show ParabolicMemLpOn V 2 (fun z ↦ velocityGradient w z i * qh z) by simpa only [mul_comm] using hqh.fun_mul (hdwTop i)).add (by
        simpa only [mul_comm] using (hGh i).mul' hwTop)
  have hψWeakV (i : Fin d) : HasWeakVelocityPartialDerivOn V i ψ (Dψ i) := by
    have hp := (hqhWeak i).mul_contDiff hwSmooth
      (hqh.locallyIntegrableOn (by norm_num))
      ((hGh i).locallyIntegrableOn (by norm_num))
    convert hp using 1
    · funext z
      simp only [Dψ]
      ring
  have hψSupport : tsupport ψ ⊆ V :=
    (tsupport_mul_subset_left (f := w) (g := qh)).trans hKV
  have hDψSupport (i : Fin d) : tsupport (Dψ i) ⊆ V := by
    refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_mul_subset_left (f := fun z ↦ velocityGradient w z i)
        (g := qh)).trans (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset.trans hKV)
    · exact (tsupport_mul_subset_left (f := w) (g := Gh i)).trans hKV
  have hψGlobal  :=
    (show ParabolicMemLpOn V 2 ψ by
        simpa only [ψ, mul_comm] using hqh.fun_mul hwTop).memLp_of_support_subset hVopen.measurableSet
      ((subset_tsupport ψ).trans hψSupport)
  have hDψGlobal (i : Fin d)  :=
    (hDψV i).memLp_of_support_subset hVopen.measurableSet
      ((subset_tsupport (Dψ i)).trans (hDψSupport i))
  have hψWeakGlobal (i : Fin d)  :=
    (hψWeakV i).univ_of_tsupport_subset hVopen hψSupport (hDψSupport i)
  exact ⟨V, (closure V ∪ spatialShift k h '' closure V), hVopen, hVclosure, hKV, hVS, (hVclosure.union (hVclosure.image hshiftContinuous)), (by
      intro z hz
      exact Or.inl (subset_closure hz)), (by
      rintro z (hz | ⟨y, hy, rfl⟩)
      · exact (hclosureVU hz).1
      · exact (hclosureVU hy).2), (by
      intro z hz
      exact Or.inr ⟨z, subset_closure hz, rfl⟩),
    hqh, hGh, hqhWeak,
    hψGlobal, hDψGlobal, hψWeakGlobal, hDψSupport⟩

/-- Positive-radius mollification of the localized quotient gives smooth
compact tests, their exact selected gradients, and a backward-quotient test
whose support remains in the original open carrier. -/
private theorem exists_mollifiedLocalizedQuotient_testPackage
     {S V : HypoellipticAleksandrov.Parabolic.Region d}
    (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hVS : V ⊆ S) (k : Fin d) (h : ℝ)
    (hVshift : Set.MapsTo (spatialShift k h) V S)
    (ψ : HypoellipticAleksandrov.Parabolic.ScalarField d) (Dψ : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hψ : MemLp ψ 2 ) (hDψ : ∀ i, MemLp (Dψ i) 2 )
    (hψWeak : ∀ i, HasWeakVelocityPartialDerivOn Set.univ i ψ (Dψ i))
    (hψSupport : tsupport ψ ⊆ V) :
    ∃ r : ℝ, 0 < r ∧
      (∀ ε : ℝ, 0 < ε → ε < r →
        ContDiff ℝ PDE.smoothOrder (spacetimeMollification ε ψ) ∧
        HasCompactSupport (spacetimeMollification ε ψ) ∧
        tsupport (spacetimeMollification ε ψ) ⊆ V ∧
        (∀ i z, velocityGradient (spacetimeMollification ε ψ) z i =
          spacetimeMollification ε (Dψ i) z) ∧
        ContDiff ℝ PDE.smoothOrder
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) ∧
        HasCompactSupport
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) ∧
        tsupport (spatialDifferenceQuotient k (-h)
          (spacetimeMollification ε ψ)) ⊆ S) ∧
      Filter.Tendsto (fun ε  ↦ eLpNorm (spacetimeMollification ε ψ - ψ) 2 )
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ i, Filter.Tendsto (fun ε  ↦
        eLpNorm (spacetimeMollification ε (Dψ i) - Dψ i) 2 )
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hψCompact : HasCompactSupport ψ :=
    hVcompact.of_isClosed_subset (isClosed_tsupport ψ) (hψSupport.trans subset_closure)
  obtain ⟨r, hr, hcollar⟩ := hψCompact.isCompact.exists_cthickening_subset_open
    hVopen hψSupport
  refine ⟨r, hr, ?_,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub ψ hψ,
    fun i ↦ SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub
      (Dψ i) (hDψ i)⟩
  intro ε hε hεr
  have hsmooth := contDiff_spacetimeMollification hε ψ
    (hψ.locallyIntegrable (by norm_num))
  have hcompact : HasCompactSupport (spacetimeMollification ε ψ) := by
    exact (spacetimeMollifier_hasCompactSupport hε).convolution
      _ hψCompact
  have hsupp : tsupport (spacetimeMollification ε ψ) ⊆ V :=
    (tsupport_spacetimeMollification_subset_cthickening hε).trans
      ((Metric.cthickening_mono hεr.le (tsupport ψ)).trans hcollar)
  have hgrad (i : Fin d) := velocityGradient_spacetimeMollification hε i ψ (Dψ i)
    (hψ.locallyIntegrable (by norm_num))
    ((hDψ i).locallyIntegrable (by norm_num)) (hψWeak i)



  exact ⟨hsmooth, hcompact, hsupp, fun i z ↦ congrFun (hgrad i) z,
    (ContDiff.spatialDifferenceQuotient hsmooth), (HasCompactSupport.spatialDifferenceQuotient hcompact), (tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
          k (-h) (spacetimeMollification ε ψ) hsupp hVS (by simpa using hVshift))⟩

/-- A fixed nonzero spatial quotient is a bounded operator on ambient `L²`,
so it preserves strong `L²` convergence. -/
private theorem tendsto_eLpNorm_spatialDifferenceQuotient_sub
     {l : Filter ℝ} (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (f : ℝ → HypoellipticAleksandrov.Parabolic.ScalarField d) (f₀ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ᶠ ε in l, MemLp (f ε) 2 ) (hf₀ : MemLp f₀ 2 )
    (hlim : Filter.Tendsto (fun ε ↦ eLpNorm (f ε - f₀) 2 )
      l (nhds 0)) :
    Filter.Tendsto (fun ε ↦ eLpNorm
      (spatialDifferenceQuotient k h (f ε) -
        spatialDifferenceQuotient k h f₀) 2 ) l (nhds 0) := by
  let sharedTerm_9ba1378ea6 := (‖(1 / h : ℝ)‖ₑ)
  let g  := fun ε ↦ f ε - f₀
  have hg : ∀ᶠ ε in l, MemLp (g ε) 2  := by
    filter_upwards [hf] with ε hε
    exact hε.sub hf₀


  have hright : Filter.Tendsto (fun ε ↦
      sharedTerm_9ba1378ea6 * (eLpNorm (g ε) 2  + eLpNorm (g ε) 2 ))
      l (nhds 0) := by
    simpa only [zero_add, mul_zero] using
      ENNReal.Tendsto.const_mul (hlim.add hlim)
        (Or.inr (enorm_ne_top : sharedTerm_9ba1378ea6 ≠ ∞))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hright
    (Filter.Eventually.of_forall fun _ ↦ bot_le) (by
        filter_upwards [hg, (show ∀ᶠ ε in l,
      eLpNorm (g ε ∘ spatialShift k h) 2  = eLpNorm (g ε) 2 by
            filter_upwards [hg] with ε hε
            exact eLpNorm_comp_measurePreserving hε.aestronglyMeasurable
              (spatialShift_measurePreserving k h))] with ε hε hshift


        rw [show spatialDifferenceQuotient k h (f ε) -
            spatialDifferenceQuotient k h f₀ =
              (1 / h : ℝ) • ((g ε ∘ spatialShift k h) - g ε) by
          funext z
          simp only [g, spatialDifferenceQuotient_apply, spatialTranslate_apply,
            Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
          field_simp [hh]
          ring]
        rw [eLpNorm_const_smul]
        gcongr
        exact (eLpNorm_sub_le (by norm_num)).trans_eq
          (by rw [hshift]))

/-- The source stays undifferenced when the mollified localized quotient is
passed to the fixed backward quotient. -/
private theorem tendsto_sourcePairing_mollifiedBackwardQuotient
     (S : HypoellipticAleksandrov.Parabolic.Region d) (R ψ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hR : ParabolicMemLpOn S 2 R) (hψ : MemLp ψ 2 )
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) :
    Filter.Tendsto (fun ε  ↦ ∫ z in S, R z *
      spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ) z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z)) := by
  have hmoll : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      MemLp (spacetimeMollification ε ψ) 2  := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hε ψ hψ
  have hquotLim := tendsto_eLpNorm_spatialDifferenceQuotient_sub k (-h)
    (neg_ne_zero.mpr hh) _ ψ hmoll hψ
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub ψ hψ)
  have hquotMem (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : MemLp u 2 ) :
      MemLp (spatialDifferenceQuotient k (-h) u) 2  := by
    rw [show spatialDifferenceQuotient k (-h) u =
        (1 / (-h) : ℝ) • ((u ∘ spatialShift k (-h)) - u) by
      funext z
      simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      ring]
    exact ((hu.comp_measurePreserving
      (spatialShift_measurePreserving k (-h))).sub hu).const_smul _

  apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    (fun _ ↦ R) (fun ε ↦ spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) R (spatialDifferenceQuotient k (-h) ψ)
  · exact Filter.Eventually.of_forall fun _ ↦ hR
  · filter_upwards [hmoll] with ε hε
    exact (hquotMem _ hε).mono_measure Measure.restrict_le_self
  · exact hR
  · exact (hquotMem _ hψ).mono_measure Measure.restrict_le_self
  · simp_all
  · exact (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hquotLim
        (Filter.Eventually.of_forall fun _ ↦ bot_le)
        (Filter.Eventually.of_forall fun ε ↦
          eLpNorm_mono_measure _ Measure.restrict_le_self))

/-- Rearranging the supplied divergence identity for the mollified
backward-quotient test gives the signs produced by testing with its negative. -/
private theorem testedEquation_neg_mollifiedBackwardQuotient
     {S : HypoellipticAleksandrov.Parabolic.Region d}
    (A : TimeVelocity d → PDE.Mat d) (q R : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hEq : ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ → tsupport φ ⊆ S →
      -(∫ z in S, q z * timeDerivative φ z) -
          ∑ i, ∑ j, ∫ z in S,
            A z i j * G j z * velocityGradient φ z i =
        ∫ z in S, R z * φ z)
    (k : Fin d) (h ε : ℝ) (ψ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hεSmooth : ContDiff ℝ PDE.smoothOrder
      (spacetimeMollification ε ψ))
    (hεCompact : HasCompactSupport (spacetimeMollification ε ψ))
    (hTestSupport : tsupport (spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) ⊆ S) :
    (∫ z in S, q z * timeDerivative
        (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) z) +
      ∑ i, ∑ j, ∫ z in S, A z i j * G j z *
        velocityGradient
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) z i =
      -(∫ z in S, R z * spatialDifferenceQuotient k (-h)
        (spacetimeMollification ε ψ) z) := by



  have heq := hEq
    (((spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ))))
    (ContDiff.spatialDifferenceQuotient hεSmooth) (HasCompactSupport.spatialDifferenceQuotient hεCompact) hTestSupport
  linarith

/-- A spatial difference quotient commutes exactly with a finite sum, without
any regularity or nonzero-step assumption. -/
private theorem spatialDifferenceQuotient_finset_sum
     {ι : Type*} (s : Finset ι) (k : Fin d) (h : ℝ)
    (H : ι → HypoellipticAleksandrov.Parabolic.ScalarField d) :
    spatialDifferenceQuotient k h (fun x ↦ ∑ j ∈ s, H j x) =
      fun z ↦ ∑ j ∈ s, spatialDifferenceQuotient k h (H j) z := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- The weighted time-energy density is integrable on the original carrier.
Only local `L²` control of the quotient near the compact weight support is
used. -/
private theorem integrableOn_timeDerivative_mul_spatialDifferenceQuotient_sq
     {S V : HypoellipticAleksandrov.Parabolic.Region d} (hVS : V ⊆ S)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : ParabolicMemLpOn V 2 q)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    IntegrableOn (fun z ↦ timeDerivative w z * q z ^ 2) S := by
  have hdtTop : ParabolicMemLpOn V ∞ (timeDerivative w) :=
    ((contDiff_infty_iff_fderiv.mp hwSmooth).2.clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport
        ((id (HasCompactSupport.fderiv_apply ℝ hwCompact (1, 0))))
      |>.restrict V

  have hsupp : Function.support (fun z ↦ timeDerivative w z * q z ^ 2) ⊆ V := by
    intro z hz

    exact hwSupport (timeDerivative_tsupport_subset (subset_tsupport _ (by
        intro hzero
        exact hz (by simp [hzero]))))
  have hglobal := (integrableOn_iff_integrable_of_support_subset hsupp).mp (by

      apply ((hq.mul' (r := 2) hdtTop).integrable_mul hq).congr
      filter_upwards with z
      simp only [Pi.mul_apply]
      ring)
  exact (integrableOn_iff_integrable_of_support_subset (hsupp.trans hVS)).mpr hglobal

/-- Pairing an `L²` source on a carrier with a fixed backward quotient of a
global `L²` function is integrable on that carrier. -/
private theorem integrableOn_source_mul_spatialDifferenceQuotient
     (S : HypoellipticAleksandrov.Parabolic.Region d)
    (R ψ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hR : ParabolicMemLpOn S 2 R)
    (hψ : MemLp ψ 2 ) (k : Fin d) (h : ℝ) :
    IntegrableOn (fun z ↦ R z * spatialDifferenceQuotient k (-h) ψ z) S := by

  exact hR.integrable_mul ((show MemLp (spatialDifferenceQuotient k (-h) ψ) 2 by
      rw [show spatialDifferenceQuotient k (-h) ψ =
          (1 / (-h) : ℝ) • ((ψ ∘ spatialShift k (-h)) - ψ) by
        funext z
        simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
        ring]
      exact ((hψ.comp_measurePreserving
        (spatialShift_measurePreserving k (-h))).sub hψ).const_smul _).mono_measure Measure.restrict_le_self)

/-- The aggregate forward flux quotient paired with a compactly supported
global `L²` test gradient is integrable on the original carrier. -/
private theorem integrableOn_sum_principalFluxQuotient_mul
     {S C V : HypoellipticAleksandrov.Parabolic.Region d}
    (hCcompact : IsCompact C) (hCS : C ⊆ S) (hVC : V ⊆ C)
    (A : TimeVelocity d → PDE.Mat d) (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hFlux : ∀ i j, ∀ K : HypoellipticAleksandrov.Parabolic.Region d, IsCompact K → K ⊆ S →
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z))
    (i k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V C)
    (Dψ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hDψ : MemLp Dψ 2 )
    (hDψSupport : tsupport Dψ ⊆ V) :
    IntegrableOn (fun z ↦ spatialDifferenceQuotient k h
        (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) S := by
  have hentries (j : Fin d)  :=
    (hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
      k h hVC hshift



  exact ((integrableOn_iff_integrable_of_support_subset (by
      intro z hz

      exact hDψSupport (subset_tsupport Dψ (by
          intro hzero
          exact hz (by simp [hzero]))))).mp (by
      rw [spatialDifferenceQuotient_finset_sum Finset.univ k h
        (fun j x ↦ A x i j * G j x)]
      exact (memLp_finset_sum _ fun j _ ↦ hentries j).integrable_mul (hDψ.mono_measure Measure.restrict_le_self))).restrict

/-- The quotient-test energy identity obtained from a tested divergence-form
equation by smooth compact approximation. -/
theorem integral_spatialDifferenceQuotient_energyIdentity_of_testedEquation
    (d : ℕ) (S : HypoellipticAleksandrov.Parabolic.Region d) (hS : IsOpen S)
    (A : TimeVelocity d → PDE.Mat d) (q R : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : ParabolicMemLpOn S 2 q) (hR : ParabolicMemLpOn S 2 R)
    (hG : ∀ j, ParabolicMemLpOn S 2 (G j))
    (hFlux : ∀ i j, ∀ K : HypoellipticAleksandrov.Parabolic.Region d, IsCompact K → K ⊆ S →
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z))
    (hWeak : ∀ j, HasWeakVelocityPartialDerivOn S j q (G j))
    (hEq : ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ → tsupport φ ⊆ S →
      -(∫ z in S, q z * timeDerivative φ z) -
          ∑ i, ∑ j, ∫ z in S,
            A z i j * G j z * velocityGradient φ z i =
        ∫ z in S, R z * φ z)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ S)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hwShift : Set.MapsTo (spatialShift k h) (tsupport w) S) :
    IntegrableOn
        (fun z ↦ timeDerivative w z *
          (spatialDifferenceQuotient k h q z) ^ 2) S ∧
      (∀ i, IntegrableOn
        (fun z ↦ spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z *
          (velocityGradient w z i * spatialDifferenceQuotient k h q z +
            w z * spatialDifferenceQuotient k h (G i) z)) S) ∧
      IntegrableOn
        (fun z ↦ R z * spatialDifferenceQuotient k (-h)
          (fun x ↦ w x * spatialDifferenceQuotient k h q x) z) S ∧
      (-1 / 2 : ℝ) *
          (∫ z in S, timeDerivative w z *
            (spatialDifferenceQuotient k h q z) ^ 2) -
        ∑ i, ∫ z in S, spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z *
          (velocityGradient w z i * spatialDifferenceQuotient k h q z +
            w z * spatialDifferenceQuotient k h (G i) z) =
        -(∫ z in S, R z * spatialDifferenceQuotient k (-h)
          (fun x ↦ w x * spatialDifferenceQuotient k h q x) z) := by
  obtain ⟨V, C, hVopen, hVcompact, hwV, hVS, hCcompact, hVC, hCS,
      hVshift, hqh, hGh, hqhWeak, hψ, hDψ, hψWeak, hDψSupport⟩ :=
    exists_global_localizedQuotient_weakGradient hS q G hq hG hWeak w
      hwSmooth hwCompact hwSupport k h hwShift
  let qh  := spatialDifferenceQuotient k h q
  let ψ  := fun z ↦ w z * qh z
  let Dψ  := fun i z ↦
    velocityGradient w z i * qh z +
      w z * spatialDifferenceQuotient k h (G i) z
  obtain ⟨r, hr, htest, hψlim, hDψlim⟩ :=
    exists_mollifiedLocalizedQuotient_testPackage hVopen hVcompact hVS k h
      (fun z hz ↦ hCS (hVshift hz)) ψ Dψ hψ hDψ hψWeak
      (tsupport_mul_subset_left.trans hwV)
  have htimeInt  :=
    integrableOn_timeDerivative_mul_spatialDifferenceQuotient_sq hVS qh hqh w
      hwSmooth hwCompact hwV
  have hsourceInt  :=
    integrableOn_source_mul_spatialDifferenceQuotient S R ψ hR hψ k h
  have hfluxInt (i : Fin d) : IntegrableOn (fun z ↦
      spatialDifferenceQuotient k h (fun x ↦ ∑ j, A x i j * G j x) z *
        Dψ i z) S :=
    integrableOn_sum_principalFluxQuotient_mul hCcompact hCS hVC A G hFlux
      i k h hVshift (Dψ i) (hDψ i) (hDψSupport i)
  refine ⟨htimeInt, hfluxInt, hsourceInt, ?_⟩
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let f  := fun ε ↦ spacetimeMollification ε ψ
  have hevent : ∀ᶠ ε in l, 0 < ε ∧ ε < r := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with ε hε hεr
    exact ⟨hε, hεr⟩

  have htimeLim : Filter.Tendsto (fun ε ↦ ∫ z in V, qh z *
      timeDerivative (f ε) z) l
      (nhds ((1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2)) := tendsto_localized_timeEnergy_spacetimeMollification hVopen qh w hqh
      hwSmooth hwCompact hwV
  have hsourceLim : Filter.Tendsto (fun ε ↦ ∫ z in S, R z *
      spatialDifferenceQuotient k (-h) (f ε) z) l
      (nhds (∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z)) := tendsto_sourcePairing_mollifiedBackwardQuotient S R ψ hR hψ k h hh
  have hfluxLim (i j : Fin d) : Filter.Tendsto (fun ε ↦
      ∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * spacetimeMollification ε (Dψ i) z) l
      (nhds (∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * Dψ i z)) := by
    have hentry  :=
      (hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
        k h hVC hVshift
    apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun _ ↦ spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z))
      (fun ε ↦ spacetimeMollification ε (Dψ i))
      (spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z)) (Dψ i)
    · exact Filter.Eventually.of_forall fun _ ↦ hentry
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε (Dψ i)
        (hDψ i)).mono_measure Measure.restrict_le_self
    · exact hentry
    · exact (hDψ i).mono_measure Measure.restrict_le_self
    · convert (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ (0 : ℝ≥0∞)) l (nhds 0)) using 1
      simp
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hDψlim i) (Filter.Eventually.of_forall fun _ ↦ bot_le)
        (Filter.Eventually.of_forall fun ε ↦
          eLpNorm_mono_measure _ Measure.restrict_le_self)




  have hlimEq := tendsto_nhds_unique (show Filter.Tendsto (fun ε ↦
      -(∫ z in V, qh z * timeDerivative (f ε) z) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z *
            spacetimeMollification ε (Dψ i) z) l
      (nhds (-((1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z)) by
      exact htimeLim.neg.sub (tendsto_finset_sum _ fun i _ ↦
        tendsto_finset_sum _ fun j _ ↦
          hfluxLim i j))
    (hsourceLim.neg.congr' (by
        filter_upwards [(show ∀ᶠ ε in l,
          -(∫ z in V, qh z * timeDerivative (f ε) z) -
              ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
                (fun x ↦ A x i j * G j x) z *
                  spacetimeMollification ε (Dψ i) z =
            -(∫ z in S, R z * spatialDifferenceQuotient k (-h) (f ε) z) by
            filter_upwards [hevent] with ε hε
            have hp := htest ε hε.1 hε.2
            have he := testedEquation_neg_mollifiedBackwardQuotient A q R G hEq k h ε ψ
              hp.1 hp.2.1 hp.2.2.2.2.2.2
            have ht := setIntegral_mul_timeDerivative_spatialDifferenceQuotient_neg
              hS.measurableSet hVS q hq k h (f ε) hp.1 hp.2.1 hp.2.2.1
              (fun z hz ↦ hCS (hVshift hz))
            have hf (i j : Fin d) :=
              setIntegral_mul_velocityGradient_spatialDifferenceQuotient_neg
                hS.measurableSet hCcompact hCS hVC (fun z ↦ A z i j * G j z)
                (hFlux i j C hCcompact hCS) k h (f ε) hp.1 hp.2.1 hp.2.2.1
                hVshift i
            dsimp only [f] at he ht hf ⊢
            rw [ht] at he
            have hfsum : (∑ i, ∑ j, ∫ z in S, A z i j * G j z *
                velocityGradient (spatialDifferenceQuotient k (-h)
                  (spacetimeMollification ε ψ)) z i) =
                ∑ i, ∑ j, -(∫ z in V, spatialDifferenceQuotient k h
                  (fun x ↦ A x i j * G j x) z *
                    velocityGradient (spacetimeMollification ε ψ) z i) := by
              exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl
                (fun j _ ↦ hf i j))
            rw [hfsum] at he
            have hgradsum : (∑ i, ∑ j, -(∫ z in V,
                spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
                  velocityGradient (spacetimeMollification ε ψ) z i)) =
                ∑ i, ∑ j, -(∫ z in V,
                  spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
                    spacetimeMollification ε (Dψ i) z) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              congr 2
              funext z
              rw [hp.2.2.2.1 i z]
            rw [hgradsum] at he
            simp only [Finset.sum_neg_distrib] at he
            dsimp only [qh] at ⊢
            linarith)] with ε he
        exact he.symm))
  rw [show (∫ z in V, timeDerivative w z * qh z ^ 2) =
      ∫ z in S, timeDerivative w z * qh z ^ 2 from (setIntegral_eq_of_subset_of_forall_diff_eq_zero hS.measurableSet hVS
          (fun z hz ↦ by
            have hzero  :=
              image_eq_zero_of_notMem_tsupport
                (fun hzt ↦ hz.2 (hwV (timeDerivative_tsupport_subset hzt)))
            simp [hzero])).symm
    ] at hlimEq
  have hfluxEq (i : Fin d) :
      (∫ z in S, spatialDifferenceQuotient k h
          (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
        ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z := by
    have hentryInt (j : Fin d) : IntegrableOn (fun z ↦
        spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
          Dψ i z) V := ((hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
        k h hVC hVshift).integrable_mul
          ((hDψ i).mono_measure Measure.restrict_le_self)
    calc
      (∫ z in S, spatialDifferenceQuotient k h
          (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
          ∫ z in V, spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z := setIntegral_eq_of_subset_of_forall_diff_eq_zero hS.measurableSet hVS
          (fun z hz ↦ by
            have hzero : Dψ i z = 0 := image_eq_zero_of_notMem_tsupport
              (fun hzt ↦ hz.2 (hDψSupport i hzt))
            simp [hzero])
      _ = ∫ z in V, (∑ j, spatialDifferenceQuotient k h
            (fun x ↦ A x i j * G j x) z) * Dψ i z := by
        rw [spatialDifferenceQuotient_finset_sum Finset.univ k h
          (fun j x ↦ A x i j * G j x)]
      _ = ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z := by
        rw [show (fun z ↦ (∑ j, spatialDifferenceQuotient k h
            (fun x ↦ A x i j * G j x) z) * Dψ i z) =
          fun z ↦ ∑ j, spatialDifferenceQuotient k h
              (fun x ↦ A x i j * G j x) z * Dψ i z by
          funext z
          rw [Finset.sum_mul]]
        exact integral_finset_sum _ (fun j _ ↦ hentryInt j)
  rw [show (∑ i, ∫ z in S, spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
      ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * Dψ i z from Finset.sum_congr rfl (fun i _ ↦ hfluxEq i)]
  simp_rw [qh, Dψ] at hlimEq ⊢
  linarith

end HypoellipticAleksandrov.Parabolic
