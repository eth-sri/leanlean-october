module

import Mathlib.Topology.Order.ProjIcc

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertSteklov
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Continuous Hilbert representatives in reverse time

This module constructs the closed-time spatial-`L²` representative supplied
by a reverse-time Gelfand weak derivative.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- A continuous closed-time spatial-`L²` curve agrees almost everywhere with
the spatial value image of the reverse-time Bochner curve. -/
def ReverseTimeHilbertRepresentativeAgrees
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T)
    (Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞))) : Prop :=
  ∀ᵐ tau ∂reverseTimeVolume T,
    ∀ htau : tau ∈ Set.Ioo 0 T,
      Ubar ⟨tau, ⟨le_of_lt htau.1, le_of_lt htau.2⟩⟩ =
        valueCLM hΩ (u tau)

/-- Extend the time representative by clamping. On the closed time interval the
extension still agrees almost everywhere with the Bochner representative. -/
theorem ReverseTimeHilbertRepresentativeAgrees.ae_IccExtend {hΩ : IsOpen Ω} {T : ℝ} {u : ReverseTimeL2V hΩ T}
    {Ubar : C(↥(Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞))}
    (h : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar) (hT : 0 ≤ T) :
    IccExtend hT Ubar =ᵐ[volume.restrict (Icc 0 T)] fun t => valueCLM hΩ (u t) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t hu ht
  rw [IccExtend_of_mem hT _ (Ioo_subset_Icc_self ht)]
  exact hu ht

end

private theorem collar_bounds {T : ℝ} (hT : 0 < T) :
    0 < T / 3 ∧ T / 3 < 2 * T / 3 ∧ 2 * T / 3 < T := by
  constructor
  · positivity
  constructor <;> linarith

private theorem tendstoInMeasure_of_tendsto_sqNorm_integral
    {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ}
    {F : ℕ → ℝ → E} {f : ℝ → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : AEStronglyMeasurable f μ)
    (hMem : ∀ n, MemLp (F n - f) (2 : ℝ≥0∞) μ)
    (h2 : Tendsto (fun n => ∫ t, ‖F n t - f t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ F atTop f := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  have hroot : Tendsto (fun n => (∫ t, ‖F n t - f t‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹))
      atTop (𝓝 0) := by
    convert
      (Real.continuousAt_rpow_const 0 ((2 : ℝ)⁻¹) (Or.inr (by norm_num))).tendsto.comp h2
      using 1 <;>
      norm_num [Function.comp_def, Real.zero_rpow]
  have hELp : Tendsto
      (fun n => ENNReal.ofReal ((∫ t, ‖F n t - f t‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hroot
  apply hELp.congr'
  filter_upwards with n
  rw [(hMem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  norm_num

private theorem tendsto_value_sqNorm_integral_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (T : ℝ) (_hT : 0 < T) (u : ReverseTimeL2V hΩ T)
    (F : ℕ → ℝ → H10HilbertGraph hΩ)
    (hF : ∀ n, Continuous (F n))
    (hfull : Tendsto (fun n => ∫ t in Icc 0 T, ‖F n t - u t‖ ^ 2)
      atTop (𝓝 0))
    {c e : ℝ} (hc : 0 ≤ c) (_hce : c ≤ e) (he : e ≤ T) :
    Tendsto (fun n => ∫ t in Icc c e,
      ‖valueCLM hΩ (F n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
  have hsub : Icc c e ⊆ Icc 0 T := by
    intro t ht
    exact ⟨hc.trans ht.1, ht.2.trans he⟩
  have hu := memLp_two_on_full_Icc T u
  apply squeeze_zero'
  · filter_upwards with n
    exact integral_nonneg fun _ => sq_nonneg _
  · filter_upwards with n
    let D : ℝ → H10HilbertGraph hΩ := fun t => F n t - u t
    have hFD : MemLp D (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)) :=
      (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous (F n) (hF n) 0 T).sub hu
    have hDint : IntegrableOn (fun t => ‖D t‖ ^ 2) (Icc 0 T) volume := by
      change Integrable (fun t => ‖D t‖ ^ 2) (volume.restrict (Icc 0 T))
      exact (memLp_two_iff_integrable_sq_norm hFD.aestronglyMeasurable).mp hFD
    have hVD : MemLp (fun t => valueCLM hΩ (D t)) (2 : ℝ≥0∞)
        (volume.restrict (Icc 0 T)) := by
      simpa only [Function.comp_def] using (valueCLM hΩ).comp_memLp' hFD
    have hVDint : IntegrableOn (fun t => ‖valueCLM hΩ (D t)‖ ^ 2) (Icc 0 T) volume := by
      change Integrable (fun t => ‖valueCLM hΩ (D t)‖ ^ 2)
        (volume.restrict (Icc 0 T))
      exact (memLp_two_iff_integrable_sq_norm hVD.aestronglyMeasurable).mp hVD
    have hRDint : IntegrableOn (fun t => ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2)
        (Icc 0 T) volume := hDint.const_mul _
    calc
      (∫ t in Icc c e, ‖valueCLM hΩ (F n t) - valueCLM hΩ (u t)‖ ^ 2) =
          ∫ t in Icc c e, ‖valueCLM hΩ (D t)‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with t
            dsimp only [D]
            rw [← (valueCLM hΩ).map_sub]
      _ ≤ ∫ t in Icc c e, ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2 := by
            apply setIntegral_mono_on (hVDint.mono_set hsub) (hRDint.mono_set hsub)
              measurableSet_Icc
            intro t _
            have hbound := (valueCLM hΩ).le_opNorm (D t)
            calc
              ‖valueCLM hΩ (D t)‖ ^ 2 ≤ (‖valueCLM hΩ‖ * ‖D t‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) hbound 2
              _ = ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2 := by rw [mul_pow]
      _ ≤ ‖valueCLM hΩ‖ ^ 2 * (∫ t in Icc 0 T, ‖D t‖ ^ 2) := by
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left
              (setIntegral_mono_set hDint (Eventually.of_forall fun _ => sq_nonneg _)
                (Eventually.of_forall hsub))
              (sq_nonneg _)
      _ = ‖valueCLM hΩ‖ ^ 2 * (∫ t in Icc 0 T, ‖F n t - u t‖ ^ 2) := rfl
  · simpa only [mul_zero] using tendsto_const_nhds.mul hfull

private theorem tendsto_continuousMap_apply
    {X E ι : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {l : Filter ι} (F : ι → C(X, E)) (U : C(X, E)) (x : X)
    (hF : Tendsto F l (𝓝 U)) :
    Tendsto (fun n => F n x) l (𝓝 (U x)) := ((continuous_eval_const x).tendsto U).comp hF

private theorem exists_continuousMap_glue_of_local_ae
    {E : Type*} [NormedAddCommGroup E]
    {a b T : ℝ} (ha0 : 0 < a) (hab : a < b) (hbT : b < T)
    (f : ℝ → E)
    (UL : C(↥(Icc 0 b), E)) (UR : C(↥(Icc a T), E))
    (hLeftAE : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      ∀ ht : t ∈ Icc 0 b, UL ⟨t, ht⟩ = f t)
    (hRightAE : ∀ᵐ t ∂volume.restrict (Icc a T),
      ∀ ht : t ∈ Icc a T, UR ⟨t, ht⟩ = f t) :
    ∃ Ubar : C(↥(Icc 0 T), E),
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ∀ ht : t ∈ Icc 0 T, Ubar ⟨t, ht⟩ = f t := by
  let L : ℝ → E := IccExtend (ha0.le.trans hab.le) UL
  let R : ℝ → E := IccExtend (hab.le.trans hbT.le) UR
  have hL : Continuous L := UL.continuous.Icc_extend'
  have hR : Continuous R := UR.continuous.Icc_extend'
  have hLf : L =ᵐ[volume.restrict (Icc 0 b)] f := by
    filter_upwards [hLeftAE, ae_restrict_mem measurableSet_Icc] with t h ht
    simpa only [L, IccExtend_of_mem _ _ ht] using h ht
  have hRf : R =ᵐ[volume.restrict (Icc a T)] f := by
    filter_upwards [hRightAE, ae_restrict_mem measurableSet_Icc] with t h ht
    simpa only [R, IccExtend_of_mem _ _ ht] using h ht
  have hLR : EqOn L R (Icc a b) :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne
      ((show L =ᵐ[volume.restrict (Icc a b)] f from ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_left ha0.le) hLf).trans
        (show R =ᵐ[volume.restrict (Icc a b)] f from ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right hbT.le) hRf).symm)
      hL.continuousOn hR.continuousOn
  let g := (Iic b).piecewise L R
  have hgL : EqOn g L (Icc 0 b) := fun x hx => piecewise_eq_of_mem (Iic b) L R hx.2
  have hgR : EqOn g R (Icc a T) := by
    intro x hx
    by_cases hxb : x ≤ b
    · exact (piecewise_eq_of_mem (Iic b) L R hxb).trans (hLR ⟨hx.1, hxb⟩)
    · exact piecewise_eq_of_notMem (Iic b) L R hxb
  have hcover : Icc 0 b ∪ Icc a T = Icc 0 T := by
    rw [Icc_union_Icc' hab.le (ha0.le.trans (hab.le.trans hbT.le)), min_eq_left ha0.le, max_eq_right hbT.le]
  have hg : ContinuousOn g (Icc 0 T) := hcover ▸
    (hL.continuousOn.congr hgL).union_of_isClosed (hR.continuousOn.congr hgR) isClosed_Icc isClosed_Icc
  refine ⟨⟨fun t => g t, hg.restrict⟩, ?_⟩
  have hgf : g =ᵐ[volume.restrict (Icc 0 T)] f := by
    rw [← hcover, Filter.EventuallyEq, ae_restrict_union_iff]
    exact ⟨(hgL.aeEq_restrict measurableSet_Icc).trans hLf, (hgR.aeEq_restrict measurableSet_Icc).trans hRf⟩
  exact hgf.mono fun _ h _ => h

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
  (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
  (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
include hT g hderiv

private theorem exists_reverseTimeHilbertRepresentative_agrees :
    ∃ Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)),
      ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar := by
  let a : ℝ := T / 3
  let b : ℝ := 2 * T / 3
  obtain ⟨ha0, hab, hbT⟩ := collar_bounds hT
  have h0b : 0 ≤ b := by
    dsimp only [b]
    positivity
  have haT : a ≤ T := by
    dsimp only [a]
    linarith
  obtain ⟨UL, hUL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u g hderiv
      (by simpa only [b] using (show 0 < 2 * T / 3 by linarith))
      (by simpa only [b] using hbT))
  obtain ⟨UR, hUR⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u g hderiv
      (by simpa only [a] using ha0)
      (by simpa only [a] using (show T / 3 < T by linarith)))
  have hUL' : Tendsto (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b)
      atTop (𝓝 UL) := by
    simpa only [b] using hUL
  have hUR' : Tendsto (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a)
      atTop (𝓝 UR) := by
    simpa only [a] using hUR
  let SL : ℕ → C(↥(Icc 0 b), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
    reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b
  let SR : ℕ → C(↥(Icc a T), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
    reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a
  have hSL : Tendsto SL atTop (𝓝 UL) := hUL'
  have hSR : Tendsto SR atTop (𝓝 UR) := hUR'
  let FL : ℕ → ℝ → H10HilbertGraph hΩ := fun n t =>
    reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u t
  let FR : ℕ → ℝ → H10HilbertGraph hΩ := fun n t =>
    reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u t
  have hFLcont : ∀ n, Continuous (FL n) := by
    intro n
    simpa only [FL] using continuous_reverseTimeForwardSteklov T
      (reverseTimeSteklovStep T n) (by
        unfold reverseTimeSteklovStep
        positivity) u
  have hFRcont : ∀ n, Continuous (FR n) := by
    intro n
    simpa only [FR] using continuous_reverseTimeBackwardSteklov T
      (reverseTimeSteklovStep T n) (by
        unfold reverseTimeSteklovStep
        positivity) u
  have hFLraw : Tendsto (fun n => ∫ t in Icc 0 T, ‖FL n t - u t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [FL, Function.comp_def] using
      (tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
        (tendsto_reverseTimeSteklovStep T hT)
  have hFRraw : Tendsto (fun n => ∫ t in Icc 0 T, ‖FR n t - u t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [FR, Function.comp_def] using
      (tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
        (tendsto_reverseTimeSteklovStep T hT)
  have hVL : Tendsto (fun n => ∫ t in Icc 0 b,
      ‖valueCLM hΩ (FL n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
    exact tendsto_value_sqNorm_integral_on_Icc hΩ T hT u FL hFLcont hFLraw
      le_rfl h0b hbT.le
  have hVR : Tendsto (fun n => ∫ t in Icc a T,
      ‖valueCLM hΩ (FR n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
    exact tendsto_value_sqNorm_integral_on_Icc hΩ T hT u FR hFRcont hFRraw
      ha0.le haT le_rfl
  have huFull := memLp_two_on_full_Icc T u
  have hLsub : Icc 0 b ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hbT.le⟩
  have hRsub : Icc a T ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ha0.le.trans ht.1, ht.2⟩
  have huL : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞)
      (volume.restrict (Icc 0 b)) := by
    simpa only [Measure.restrict_restrict_of_subset hLsub] using
      huFull.restrict (Icc 0 b)
  have huR : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞)
      (volume.restrict (Icc a T)) := by
    simpa only [Measure.restrict_restrict_of_subset hRsub] using
      huFull.restrict (Icc a T)
  have hVDL : ∀ n, MemLp
      ((fun t => valueCLM hΩ (FL n t)) - fun t => valueCLM hΩ (u t))
      (2 : ℝ≥0∞) (volume.restrict (Icc 0 b)) := by
    intro n
    have hdiff := (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous (FL n) (hFLcont n) 0 b).sub huL
    simpa only [Pi.sub_def, ContinuousLinearMap.map_sub] using
      hdiff.continuousLinearMap_comp (valueCLM hΩ)
  have hVDR : ∀ n, MemLp
      ((fun t => valueCLM hΩ (FR n t)) - fun t => valueCLM hΩ (u t))
      (2 : ℝ≥0∞) (volume.restrict (Icc a T)) := by
    intro n
    have hdiff := (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous (FR n) (hFRcont n) a T).sub huR
    simpa only [Pi.sub_def, ContinuousLinearMap.map_sub] using
      hdiff.continuousLinearMap_comp (valueCLM hΩ)
  have hIML : TendstoInMeasure (volume.restrict (Icc 0 b))
      (fun n t => valueCLM hΩ (FL n t)) atTop (fun t => valueCLM hΩ (u t)) := by
    apply tendstoInMeasure_of_tendsto_sqNorm_integral
      (fun n => ((valueCLM hΩ).continuous.comp (hFLcont n)).aestronglyMeasurable)
      (huL.continuousLinearMap_comp (valueCLM hΩ)).aestronglyMeasurable hVDL
    exact hVL
  have hIMR : TendstoInMeasure (volume.restrict (Icc a T))
      (fun n t => valueCLM hΩ (FR n t)) atTop (fun t => valueCLM hΩ (u t)) := by
    apply tendstoInMeasure_of_tendsto_sqNorm_integral
      (fun n => ((valueCLM hΩ).continuous.comp (hFRcont n)).aestronglyMeasurable)
      (huR.continuousLinearMap_comp (valueCLM hΩ)).aestronglyMeasurable hVDR
    exact hVR
  obtain ⟨nsL, hnsL, hsubL⟩ := hIML.exists_seq_tendsto_ae
  obtain ⟨nsR, hnsR, hsubR⟩ := hIMR.exists_seq_tendsto_ae
  have hULAE : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      ∀ ht : t ∈ Icc 0 b, UL ⟨t, ht⟩ = valueCLM hΩ (u t) := by
    filter_upwards [hsubL, ae_restrict_mem measurableSet_Icc] with t ht htb
    intro htb'
    have hPoint : Tendsto (fun n =>
        SL (nsL n) ⟨t, htb'⟩) atTop (𝓝 (UL ⟨t, htb'⟩)) := by
      exact (tendsto_continuousMap_apply SL UL ⟨t, htb'⟩ hSL).comp hnsL.tendsto_atTop
    apply tendsto_nhds_unique
      (by
        convert hPoint using 1
        funext n
        rfl)
      ht
  have hURAE : ∀ᵐ t ∂volume.restrict (Icc a T),
      ∀ ht : t ∈ Icc a T, UR ⟨t, ht⟩ = valueCLM hΩ (u t) := by
    filter_upwards [hsubR, ae_restrict_mem measurableSet_Icc] with t ht hta
    intro hta'
    have hPoint : Tendsto (fun n =>
        SR (nsR n) ⟨t, hta'⟩) atTop (𝓝 (UR ⟨t, hta'⟩)) := by
      exact (tendsto_continuousMap_apply SR UR ⟨t, hta'⟩ hSR).comp hnsR.tendsto_atTop
    apply tendsto_nhds_unique
      (by
        convert hPoint using 1
        funext n
        rfl)
      ht
  obtain ⟨Ubar, hClosedAE⟩ := exists_continuousMap_glue_of_local_ae ha0 hab hbT
    (fun t => valueCLM hΩ (u t)) UL UR hULAE hURAE
  refine ⟨Ubar, ?_⟩
  change ∀ᵐ tau ∂volume.restrict (Ioo 0 T),
    ∀ htau : tau ∈ Ioo 0 T,
      Ubar ⟨tau, ⟨le_of_lt htau.1, le_of_lt htau.2⟩⟩ = valueCLM hΩ (u tau)
  rw [restrict_Ioo_eq_restrict_Icc]
  filter_upwards [hClosedAE] with tau hTau
  intro htau
  simpa only [Subsingleton.elim] using
    hTau ⟨le_of_lt htau.1, le_of_lt htau.2⟩

private theorem reverseTimeHilbertRepresentative_energy_increment
    (Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar) :
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
      s ≤ t →
        ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, _, heAE, heInc⟩ :=
    exists_continuous_reverseTimeScalarEnergyRepresentative hΩ T hT u g hderiv
  have heAE' : e =ᵐ[volume.restrict (Icc 0 T)] fun t => ‖valueCLM hΩ (u t)‖ ^ 2 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using heAE
  have hNorm : EqOn (fun t => ‖IccExtend hT.le Ubar t‖ ^ 2) e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne
      (((hUbar.ae_IccExtend hT.le).fun_comp (fun x => ‖x‖ ^ 2)).trans heAE'.symm)
      ((Ubar.continuous.Icc_extend').norm.pow 2).continuousOn heCont
  intro s t hs ht hst
  have hst' := congrArg₂ (· - ·) (hNorm ht) (hNorm hs)
  rw [heInc s t hs ht hst] at hst'
  simpa only [IccExtend_of_mem hT.le _ ht, IccExtend_of_mem hT.le _ hs] using hst'

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- Two continuous spatial-`L²` curves which agree with the same reverse-time
Bochner curve almost everywhere have the same closed-time representative. -/
theorem ReverseTimeHilbertRepresentativeAgrees.unique {hΩ : IsOpen Ω} {T : ℝ}
    {u : ReverseTimeL2V hΩ T}
    {Ubar Vbar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞))}
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar)
    (hT : 0 < T)
    (hVbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Vbar) :
    Ubar = Vbar := by
  have hEqOn := Measure.eqOn_Icc_of_ae_eq volume hT.ne
    ((hUbar.ae_IccExtend hT.le).trans (hVbar.ae_IccExtend hT.le).symm)
    (Ubar.continuous.Icc_extend').continuousOn (Vbar.continuous.Icc_extend').continuousOn
  apply ContinuousMap.ext
  intro x
  simpa only [IccExtend_val] using hEqOn x.2

/-- The continuous spatial-`L²` representative of a reverse-time Gelfand
weak derivative, with its one-curve energy increment. -/
theorem existsUnique_reverseTimeHilbertRepresentative
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃! Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)),
      ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar ∧
      ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
        s ≤ t →
          ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
            2 * (∫ r in Set.Ioc s t,
              (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨Ubar, hUbar⟩ :=
    exists_reverseTimeHilbertRepresentative_agrees hΩ T hT u g hderiv
  refine ⟨Ubar, ⟨hUbar, ?_⟩, ?_⟩
  · exact reverseTimeHilbertRepresentative_energy_increment hΩ T hT u g hderiv Ubar hUbar
  · intro Vbar hVbar
    exact hVbar.1.unique hT hUbar

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
