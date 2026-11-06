module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertSteklov
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertSteklov
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing

open private HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_two_on_full_Icc from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing


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

/-- A continuous closed-time spatial-`L²` curve agrees almost everywhere with
the spatial value image of the reverse-time Bochner curve. -/
def ReverseTimeHilbertRepresentativeAgrees
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T)
    (Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 ))) : Prop :=
  ∀ᵐ tau ∂reverseTimeVolume T,
    ∀ htau : tau ∈ Set.Ioo 0 T,
      Ubar ⟨tau, ⟨le_of_lt htau.1, le_of_lt htau.2⟩⟩ =
        valueCLM hΩ (u tau)

private theorem collar_bounds {T : ℝ} (hT : 0 < T) :
    0 < T / 3 ∧ T / 3 < 2 * T / 3 ∧ 2 * T / 3 < T := by
  constructor
  · positivity
  constructor <;> linarith

variable {E : Type*}

private theorem tendstoInMeasure_of_tendsto_sqNorm_integral
     [NormedAddCommGroup E] {μ : Measure ℝ}
    {F : ℕ → ℝ → E} {f : ℝ → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : AEStronglyMeasurable f μ)
    (hMem : ∀ n, MemLp (F n - f) (2 ) μ)
    (h2 : Tendsto (fun n => ∫ t, ‖F n t - f t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ F atTop f := by
  let sharedTerm_d593edcc44 := (((2 : ℝ)⁻¹))
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)

  have hELp : Tendsto
      (fun n => ENNReal.ofReal ((∫ t, ‖F n t - f t‖ ^ 2 ∂μ) ^ sharedTerm_d593edcc44))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp (by
          convert
            (Real.continuousAt_rpow_const 0 sharedTerm_d593edcc44 (Or.inr (by norm_num))).tendsto.comp h2
            using 1 <;>
            norm_num [Function.comp_def, Real.zero_rpow])
  apply hELp.congr'
  filter_upwards with n
  rw [(hMem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  norm_num







private theorem tendsto_value_sqNorm_integral_on_Icc
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (T : ℝ) (_hT : 0 < T) (u : ReverseTimeL2V hΩ T)
    (F : ℕ → ℝ → H10HilbertGraph hΩ)
    (hF : ∀ n, Continuous (F n))
    (hfull : Tendsto (fun n => ∫ t in Icc 0 T, ‖F n t - u t‖ ^ 2)
      atTop (𝓝 0))
    {c e : ℝ} (hc : 0 ≤ c) (_hce : c ≤ e) (he : e ≤ T) :
    Tendsto (fun n => ∫ t in Icc c e,
      ‖valueCLM hΩ (F n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
  let sharedTerm_063a6038bb := ((volume.restrict (Icc 0 T)))
  have hsub : Icc c e ⊆ Icc 0 T := by
    intro t ht
    exact ⟨hc.trans ht.1, ht.2.trans he⟩

  apply squeeze_zero'
  · filter_upwards with n
    exact integral_nonneg fun _ => sq_nonneg _
  · filter_upwards with n
    let D : ℝ → H10HilbertGraph hΩ := fun t => F n t - u t
    have hFD : MemLp D (2 ) sharedTerm_063a6038bb :=
      (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous (F n) (hF n) 0 T).sub (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_two_on_full_Icc T u)
    have hDint : IntegrableOn (fun t => ‖D t‖ ^ 2) (Icc 0 T) volume := by
      change Integrable (fun t => ‖D t‖ ^ 2) sharedTerm_063a6038bb
      exact (memLp_two_iff_integrable_sq_norm hFD.aestronglyMeasurable).mp hFD
    have hVD : MemLp (fun t => valueCLM hΩ (D t)) (2 )
        sharedTerm_063a6038bb := by
      simpa only [Function.comp_def] using (valueCLM hΩ).comp_memLp' hFD

    have hRDint : IntegrableOn (fun t => ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2)
        (Icc 0 T) volume := hDint.const_mul _
    calc
      (∫ t in Icc c e, ‖valueCLM hΩ (F n t) - valueCLM hΩ (u t)‖ ^ 2) =
          ∫ t in Icc c e, ‖valueCLM hΩ (D t)‖ ^ 2 := rfl
      _ ≤ ∫ t in Icc c e, ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2 := by
            apply setIntegral_mono_on ((show IntegrableOn (fun t => ‖valueCLM hΩ (D t)‖ ^ 2) (Icc 0 T) volume by
                change Integrable (fun t => ‖valueCLM hΩ (D t)‖ ^ 2)
                  sharedTerm_063a6038bb
                exact (memLp_two_iff_integrable_sq_norm hVD.aestronglyMeasurable).mp hVD).mono_set hsub) (hRDint.mono_set hsub)
              measurableSet_Icc
            intro t _

            calc
              ‖valueCLM hΩ (D t)‖ ^ 2 ≤ (‖valueCLM hΩ‖ * ‖D t‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) ((valueCLM hΩ).le_opNorm (D t)) 2
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
  have h0b  := ha0.le.trans hab.le
  have haT  := hab.le.trans hbT.le
  have hLsub : Icc 0 b ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hbT.le⟩
  have hRsub : Icc a T ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ha0.le.trans ht.1, ht.2⟩
  let leftExt  := fun t =>
    UL ⟨min b (max 0 t), ⟨le_min h0b (le_max_left _ _), min_le_left _ _⟩⟩
  let rightExt  := fun t =>
    UR ⟨max a (min T t), ⟨le_max_left _ _, max_le haT (min_le_left _ _)⟩⟩
  have hLeftExtCont : Continuous leftExt := by
    dsimp only [leftExt]
    exact UL.continuous.comp
      (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id))
        fun t => ⟨le_min h0b (le_max_left _ _), min_le_left _ _⟩)
  have hRightExtCont : Continuous rightExt := by
    dsimp only [rightExt]
    exact UR.continuous.comp
      (Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id))
        fun t => ⟨le_max_left _ _, max_le haT (min_le_left _ _)⟩)
  have hLeftExtAE : ∀ᵐ t ∂volume.restrict (Icc 0 b), leftExt t = f t := by
    filter_upwards [hLeftAE, ae_restrict_mem measurableSet_Icc] with t hUL ht
    simpa only [leftExt, max_eq_right ht.1, min_eq_right ht.2] using hUL ht
  have hRightExtAE : ∀ᵐ t ∂volume.restrict (Icc a T), rightExt t = f t := by
    filter_upwards [hRightAE, ae_restrict_mem measurableSet_Icc] with t hUR ht
    simpa only [rightExt, min_eq_right ht.2, max_eq_right ht.1] using hUR ht
  have hLeftOverlap := ae_restrict_of_ae_restrict_of_subset
    (show Icc a b ⊆ Icc 0 b by
      intro t ht
      exact ⟨ha0.le.trans ht.1, ht.2⟩) hLeftExtAE
  have hRightOverlap := ae_restrict_of_ae_restrict_of_subset
    (show Icc a b ⊆ Icc a T by
      intro t ht
      exact ⟨ht.1, ht.2.trans hbT.le⟩) hRightExtAE

  have hOverlapEqOn  :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne (by
        filter_upwards [hLeftOverlap, hRightOverlap] with t hL hR
        rw [hL, hR])
      hLeftExtCont.continuousOn hRightExtCont.continuousOn
  let glue : ↥(Icc 0 T) → E := fun t =>
    if htb : (t : ℝ) ≤ b then
      UL ⟨t, ⟨t.2.1, htb⟩⟩
    else
      UR ⟨t, ⟨le_of_lt (hab.trans (lt_of_not_ge htb)), t.2.2⟩⟩
  let S : Set (↥(Icc 0 T)) := {t | (t : ℝ) ≤ b}
  let R : Set (↥(Icc 0 T)) := {t | a ≤ (t : ℝ)}


  have hSR : S ∪ R = univ := by
    ext t
    simp only [mem_union, mem_univ, iff_true]
    by_cases htb : (t : ℝ) ≤ b
    · exact Or.inl htb
    · exact Or.inr (le_of_lt (hab.trans (lt_of_not_ge htb)))

  have hGlueEqRight : EqOn glue (fun t  => rightExt t) R := by
    intro t ht
    change a ≤ (t : ℝ) at ht
    change (if h : (t : ℝ) ≤ b then UL ⟨t, ⟨t.2.1, h⟩⟩ else
      UR ⟨t, ⟨le_of_lt (hab.trans (lt_of_not_ge h)), t.2.2⟩⟩) = rightExt t
    by_cases htb : (t : ℝ) ≤ b
    ·
      have heq := hOverlapEqOn (⟨ht, htb⟩)
      change leftExt t = rightExt t at heq
      rw [dif_pos htb]
      change UL ⟨t, ⟨t.2.1, htb⟩⟩ = UR ⟨max a (min T t), _⟩
      change UL ⟨min b (max 0 t), _⟩ = UR ⟨max a (min T t), _⟩ at heq
      simpa only [max_eq_right t.2.1, min_eq_right htb] using heq
    ·
      rw [dif_neg htb]
      change UR ⟨t, ⟨ht, t.2.2⟩⟩ = UR ⟨max a (min T t), _⟩
      apply congrArg UR
      apply Subtype.ext
      dsimp
      rw [min_eq_right t.2.2, max_eq_right ht]
  have hGlueS  :=
    ContinuousOn.congr
      (hLeftExtCont.comp continuous_subtype_val).continuousOn (show EqOn glue (fun t  => leftExt t) S by
          intro t ht
          change (if htb : (t : ℝ) ≤ b then UL ⟨t, ⟨t.2.1, htb⟩⟩ else
            UR ⟨t, ⟨le_of_lt (hab.trans (lt_of_not_ge htb)), t.2.2⟩⟩) = leftExt t
          change (t : ℝ) ≤ b at ht
          rw [dif_pos ht]
          change UL ⟨t, ⟨t.2.1, ht⟩⟩ = UL ⟨min b (max 0 t), _⟩
          apply congrArg UL
          apply Subtype.ext
          dsimp
          rw [max_eq_right t.2.1, min_eq_right ht])
  have hGlueR  :=
    ContinuousOn.congr
      (hRightExtCont.comp continuous_subtype_val).continuousOn hGlueEqRight
  have hGlueOn  :=
    ContinuousOn.union_of_isClosed hGlueS hGlueR ((id (isClosed_le continuous_subtype_val continuous_const))) ((id (isClosed_le continuous_const continuous_subtype_val)))

  let Ubar : C(↥(Icc 0 T), E) := ⟨glue, (by
      rw [hSR] at hGlueOn
      simpa using hGlueOn)⟩


  have hcover : Icc 0 b ∪ Icc a T = Icc 0 T := by
    apply Set.Subset.antisymm
    · intro t ht
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans hbT.le⟩
      · exact ⟨ha0.le.trans ht.1, ht.2⟩
    · intro t ht
      by_cases htb : t ≤ b
      · exact Or.inl ⟨ht.1, htb⟩
      · exact Or.inr ⟨le_of_lt (hab.trans (lt_of_not_ge htb)), ht.2⟩
  have hUnionAE : ∀ᵐ t ∂volume.restrict (Icc 0 b ∪ Icc a T),
      ∀ ht : t ∈ Icc 0 T, Ubar ⟨t, ht⟩ = f t :=
    (ae_restrict_union_iff (μ := volume) (Icc 0 b) (Icc a T)
    fun t => ∀ ht : t ∈ Icc 0 T, Ubar ⟨t, ht⟩ = f t).mpr
    ⟨by
      filter_upwards [(show ∀ᵐ t ∂volume.restrict (Icc 0 b),
      ∀ ht : t ∈ Icc 0 b, Ubar ⟨t, hLsub ht⟩ = f t by
          filter_upwards [hLeftExtAE, ae_restrict_mem measurableSet_Icc] with t hLeft ht
          intro ht'
          change glue ⟨t, hLsub ht'⟩ = _
          simpa only [glue, leftExt, dif_pos ht'.2, max_eq_right ht'.1, min_eq_right ht'.2] using hLeft), ae_restrict_mem measurableSet_Icc] with t h htb
      intro ht
      exact h htb,
    by
      filter_upwards [(show ∀ᵐ t ∂volume.restrict (Icc a T),
      ∀ ht : t ∈ Icc a T, Ubar ⟨t, hRsub ht⟩ = f t by
          filter_upwards [hRightExtAE, ae_restrict_mem measurableSet_Icc] with t hRight ht
          intro ht'
          let x : ↥(Icc 0 T) := ⟨t, hRsub ht'⟩

          have hEq := hGlueEqRight (show x ∈ R by
              change a ≤ t
              exact ht'.1)
          change Ubar x = _
          calc
            Ubar x = rightExt t := hEq
            _ = f t := hRight), ae_restrict_mem measurableSet_Icc] with t h hta
      intro ht
      exact h hta⟩
  refine ⟨Ubar, ?_⟩
  simpa only [hcover] using hUnionAE

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T)

section
variable (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hderiv
private theorem exists_reverseTimeHilbertRepresentative_agrees
      :
    ∃ Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 )),
      ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar := by
  let sharedTerm_620679e2f9 := ((fun t => valueCLM hΩ (u t)))
  let a : ℝ := T / 3
  let b : ℝ := 2 * T / 3
  obtain ⟨ha0, hab, hbT⟩ := collar_bounds hT


  obtain ⟨UL, hUL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u g hderiv
      (by simpa only [b] using (show 0 < 2 * T / 3 by linarith))
      (hbT))
  obtain ⟨UR, hUR⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u g hderiv
      (ha0)
      (by simpa only [a] using (show T / 3 < T by linarith)))
  have hUL' : Tendsto (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b)
      atTop (𝓝 UL) := by
    exact hUL
  have hUR' : Tendsto (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a)
      atTop (𝓝 UR) := by
    exact hUR




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


  have hVL  := tendsto_value_sqNorm_integral_on_Icc hΩ T hT u FL hFLcont (show Tendsto (fun n => ∫ t in Icc 0 T, ‖FL n t - u t‖ ^ 2)
      atTop (𝓝 0) by
      simpa only [FL, Function.comp_def] using
        (tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
          (tendsto_reverseTimeSteklovStep T hT))
      le_rfl (show 0 ≤ b by
          dsimp only [b]
          positivity) hbT.le
  have hVR  := tendsto_value_sqNorm_integral_on_Icc hΩ T hT u FR hFRcont (show Tendsto (fun n => ∫ t in Icc 0 T, ‖FR n t - u t‖ ^ 2)
      atTop (𝓝 0) by
      simpa only [FR, Function.comp_def] using
        (tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
          (tendsto_reverseTimeSteklovStep T hT))
      ha0.le (show a ≤ T by
          dsimp only [a]
          linarith) le_rfl
  have huFull := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_two_on_full_Icc T u


  have huL : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 )
      (volume.restrict (Icc 0 b)) := by
    simpa only [Measure.restrict_restrict_of_subset (show Icc 0 b ⊆ Icc 0 T by
        intro t ht
        exact ⟨ht.1, ht.2.trans hbT.le⟩)] using
      huFull.restrict (Icc 0 b)
  have huR : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 )
      (volume.restrict (Icc a T)) := by
    simpa only [Measure.restrict_restrict_of_subset (show Icc a T ⊆ Icc 0 T by
        intro t ht
        exact ⟨ha0.le.trans ht.1, ht.2⟩)] using
      huFull.restrict (Icc a T)


  have hIML : TendstoInMeasure (volume.restrict (Icc 0 b))
      (fun n t => valueCLM hΩ (FL n t)) atTop sharedTerm_620679e2f9 := by
    apply tendstoInMeasure_of_tendsto_sqNorm_integral
      (fun n => ((valueCLM hΩ).continuous.comp (hFLcont n)).aestronglyMeasurable)
      (huL.continuousLinearMap_comp (valueCLM hΩ)).aestronglyMeasurable (show ∀ n, MemLp
      ((fun t => valueCLM hΩ (FL n t)) - sharedTerm_620679e2f9)
      (2 ) (volume.restrict (Icc 0 b)) by
          intro n

          simpa only [Pi.sub_def, ContinuousLinearMap.map_sub] using
            ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous (FL n) (hFLcont n) 0 b).sub huL).continuousLinearMap_comp (valueCLM hΩ))
    exact hVL
  have hIMR : TendstoInMeasure (volume.restrict (Icc a T))
      (fun n t => valueCLM hΩ (FR n t)) atTop sharedTerm_620679e2f9 := by
    apply tendstoInMeasure_of_tendsto_sqNorm_integral
      (fun n => ((valueCLM hΩ).continuous.comp (hFRcont n)).aestronglyMeasurable)
      (huR.continuousLinearMap_comp (valueCLM hΩ)).aestronglyMeasurable (show ∀ n, MemLp
      ((fun t => valueCLM hΩ (FR n t)) - sharedTerm_620679e2f9)
      (2 ) (volume.restrict (Icc a T)) by
          intro n

          simpa only [Pi.sub_def, ContinuousLinearMap.map_sub] using
            ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous (FR n) (hFRcont n) a T).sub huR).continuousLinearMap_comp (valueCLM hΩ))
    exact hVR
  obtain ⟨nsL, hnsL, hsubL⟩ := hIML.exists_seq_tendsto_ae
  obtain ⟨nsR, hnsR, hsubR⟩ := hIMR.exists_seq_tendsto_ae


  obtain ⟨Ubar, hClosedAE⟩ := exists_continuousMap_glue_of_local_ae ha0 hab hbT
    sharedTerm_620679e2f9 UL UR (by
        filter_upwards [hsubL, ae_restrict_mem measurableSet_Icc] with t ht htb
        intro htb'
        have hPoint  := (tendsto_continuousMap_apply (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b) UL ⟨t, htb'⟩ hUL').comp hnsL.tendsto_atTop
        apply tendsto_nhds_unique
          (by
            convert hPoint using 1
            funext n
            rfl)
          ht) (by
        filter_upwards [hsubR, ae_restrict_mem measurableSet_Icc] with t ht hta
        intro hta'
        have hPoint  := (tendsto_continuousMap_apply (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a) UR ⟨t, hta'⟩ hUR').comp hnsR.tendsto_atTop
        apply tendsto_nhds_unique
          (by
            convert hPoint using 1
            funext n
            rfl)
          ht)
  refine ⟨Ubar, ?_⟩
  change ∀ᵐ tau ∂volume.restrict (Ioo 0 T),
    ∀ htau : tau ∈ Ioo 0 T,
      Ubar ⟨tau, ⟨le_of_lt htau.1, le_of_lt htau.2⟩⟩ = valueCLM hΩ (u tau)
  rw [restrict_Ioo_eq_restrict_Icc]
  filter_upwards [hClosedAE] with tau hTau
  intro htau
  exact hTau ⟨le_of_lt htau.1, le_of_lt htau.2⟩

private theorem reverseTimeHilbertRepresentative_energy_increment

    (Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 )))
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar) :
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
      s ≤ t →
        ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, _heNonneg, heAE, heInc⟩ :=
    exists_continuous_reverseTimeScalarEnergyRepresentative hΩ T hT u g hderiv
  let Uext  := fun t =>
    if ht : t ∈ Icc 0 T then Ubar ⟨t, ht⟩ else 0






  have hNormSqEqOn  :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne (by
        filter_upwards [(by
            rw [← restrict_Ioo_eq_restrict_Icc]
            exact ae_restrict_mem measurableSet_Ioo), (show ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Ubar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) by
                simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
                  reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hUbar), (show e =ᵐ[volume.restrict (Icc 0 T)]
      fun t => ‖valueCLM hΩ (u t)‖ ^ 2 by
                simpa only [reverseTimeVolume, reverseTimeOpenInterval,
                  restrict_Ioo_eq_restrict_Icc] using heAE)] with t ht hUbar he
        have htIcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        calc
          ‖Uext t‖ ^ 2 = ‖Ubar ⟨t, htIcc⟩‖ ^ 2 := by
            simp only [Uext, dif_pos htIcc]
          _ = ‖valueCLM hΩ (u t)‖ ^ 2 := by rw [hUbar ht]
          _ = e t := he.symm) (((show ContinuousOn Uext (Icc 0 T) by
        rw [continuousOn_iff_continuous_domRestrict]
        have hEq : (Icc 0 T).domRestrict Uext = Ubar := by
          funext t
          simp only [Set.domRestrict_apply, Uext, dif_pos t.2]
        rw [hEq]
        exact Ubar.continuous).norm.pow 2)) heCont
  intro s t hs ht hst
  calc
    ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
        ‖Uext t‖ ^ 2 - ‖Uext s‖ ^ 2 := by
          simp only [Uext, dif_pos hs, dif_pos ht]
    _ = e t - e s := congrArg₂ (fun x y : ℝ => x - y)
      (hNormSqEqOn ht) (hNormSqEqOn hs)
    _ = 2 * (∫ r in Ioc s t, (g r) (u r) ∂reverseTimeVolume T) :=
      heInc s t hs ht hst
end


include hT in
private theorem reverseTimeHilbertRepresentative_eq

    (Ubar Vbar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 )))
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar)
    (hVbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Vbar) :
    Ubar = Vbar := by
  let Uext  := fun t =>
    if ht : t ∈ Icc 0 T then Ubar ⟨t, ht⟩ else 0
  let Vext  := fun t =>
    if ht : t ∈ Icc 0 T then Vbar ⟨t, ht⟩ else 0






  have hEqOn  :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne (by
        filter_upwards [(by
            rw [← restrict_Ioo_eq_restrict_Icc]
            exact ae_restrict_mem measurableSet_Ioo), (show ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Ubar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) by
                simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
                  reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hUbar), (show ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Vbar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) by
                simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
                  reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hVbar)] with t ht hUbar hVbar
        have htIcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        calc
          Uext t = Ubar ⟨t, htIcc⟩ := by simp only [Uext, dif_pos htIcc]
          _ = valueCLM hΩ (u t) := hUbar ht
          _ = Vbar ⟨t, htIcc⟩ := (hVbar ht).symm
          _ = Vext t := by simp only [Vext, dif_pos htIcc]) (by
        rw [continuousOn_iff_continuous_domRestrict]
        have hEq : (Icc 0 T).domRestrict Uext = Ubar := by
          funext t
          simp only [Set.domRestrict_apply, Uext, dif_pos t.2]
        rw [hEq]
        exact Ubar.continuous) (by
        rw [continuousOn_iff_continuous_domRestrict]
        have hEq : (Icc 0 T).domRestrict Vext = Vbar := by
          funext t
          simp only [Set.domRestrict_apply, Vext, dif_pos t.2]
        rw [hEq]
        exact Vbar.continuous)
  apply ContinuousMap.ext
  intro t
  simpa only [Uext, Vext, dif_pos t.2] using hEqOn t.2

/-- The continuous spatial-`L²` representative of a reverse-time Gelfand
weak derivative, with its one-curve energy increment. -/
theorem existsUnique_reverseTimeHilbertRepresentative
     (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃! Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 )),
      ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar ∧
      ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
        s ≤ t →
          ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
            2 * (∫ r in Set.Ioc s t,
              (g r) (u r) ∂reverseTimeVolume T) := (Exists.casesOn (exists_reverseTimeHilbertRepresentative_agrees hΩ T hT u g hderiv) fun Ubar hUbar =>
  Exists.intro Ubar
    ⟨⟨hUbar, reverseTimeHilbertRepresentative_energy_increment hΩ T hT u g hderiv Ubar hUbar⟩, fun Vbar hVbar =>
      reverseTimeHilbertRepresentative_eq hΩ T hT u Vbar Ubar hVbar.left hUbar⟩)

end HypoellipticAleksandrov.Parabolic.Dirichlet
