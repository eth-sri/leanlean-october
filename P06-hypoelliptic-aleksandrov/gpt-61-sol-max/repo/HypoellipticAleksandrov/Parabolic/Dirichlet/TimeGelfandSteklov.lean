module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandAffine
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity



/-!
# Reverse-time Gelfand--Steklov calculus

This module transfers the almost-everywhere reverse-time Gelfand affine
identity through literal Steklov windows.  Its derivative formulas concern
only the resulting regularized dual curves, not pointwise representatives of
the underlying `Lp` curves.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {E F : Type*}

private theorem forwardSteklov_map_eq_setIntegral
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (T : ℝ)
    (u : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (W : ℝ → F) (hAE : (fun s => L (u s)) =ᵐ[reverseTimeVolume T] W)
    (h t : ℝ) :
    L (reverseTimeForwardSteklov T h u t) =
      h⁻¹ • (∫ s in Ioc t (t + h), W s ∂reverseTimeVolume T ) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance

  rw [reverseTimeForwardSteklov, map_smul]
  congr 1
  calc
    L (∫ s in Ioc t (t + h), u s ∂reverseTimeVolume T) =
        ∫ s in Ioc t (t + h), L (u s) ∂reverseTimeVolume T :=
      (ContinuousLinearMap.integral_comp_comm L ((MeasureTheory.Lp.memLp u).integrable (by norm_num)).restrict).symm
    _ = ∫ s in Ioc t (t + h), W s ∂reverseTimeVolume T :=
      setIntegral_congr_ae measurableSet_Ioc (hAE.mono fun _ hs _ => hs)

private theorem backwardSteklov_map_eq_setIntegral
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (T : ℝ)
    (u : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (W : ℝ → F) (hAE : (fun s => L (u s)) =ᵐ[reverseTimeVolume T] W)
    (h t : ℝ) :
    L (reverseTimeBackwardSteklov T h u t) =
      h⁻¹ • (∫ s in Ioc (t - h) t, W s ∂reverseTimeVolume T ) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance

  rw [reverseTimeBackwardSteklov, map_smul]
  congr 1
  calc
    L (∫ s in Ioc (t - h) t, u s ∂reverseTimeVolume T) =
        ∫ s in Ioc (t - h) t, L (u s) ∂reverseTimeVolume T :=
      (ContinuousLinearMap.integral_comp_comm L ((MeasureTheory.Lp.memLp u).integrable (by norm_num)).restrict).symm
    _ = ∫ s in Ioc (t - h) t, W s ∂reverseTimeVolume T :=
      setIntegral_congr_ae measurableSet_Ioc (hAE.mono fun _ hs _ => hs)

variable {E : Type*}

private theorem hasDerivAt_forward_affineAverage
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h) (W : ℝ → E)
    (hW : ContinuousOn W (Icc 0 T))
    {t : ℝ} (ht0 : 0 < t) (htT : t + h < T) :
    HasDerivAt
      (fun s => h⁻¹ • ∫ r in Ioc s (s + h), W r ∂reverseTimeVolume T)
      (h⁻¹ • (W (t + h) - W t)) t := by
  have hAtIoo : ∀ x ∈ Ioo (0 : ℝ) T, ContinuousAt W x := by
    intro x hx
    exact hW.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hAtT  := hAtIoo t ⟨ht0, by linarith⟩
  have hAtTh  := hAtIoo (t + h) ⟨by linarith, htT⟩

  have hmeasTh : StronglyMeasurableAtFilter W (𝓝 (t + h))  :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hAtIoo (t + h)
      ⟨by linarith, htT⟩
  let A  := fun x => ∫ r in (0 )..x, W r
  have hIntT : IntervalIntegrable W volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hW.mono (by
      grind))
  have hIntTh : IntervalIntegrable W volume 0 (t + h) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hW.mono (by
      gcongr <;> first | positivity | assumption | norm_num))



  have hDerivDiff : HasDerivAt (fun s => A (s + h) - A s)
      (W (t + h) - W t) t := by
    exact (show HasDerivAt (fun s => A (s + h)) (W (t + h)) t by
        convert ((show HasDerivAt A (W (t + h)) (t + h) from intervalIntegral.integral_hasDerivAt_right hIntTh hmeasTh hAtTh).hasFDerivAt.comp t
          ((hasDerivAt_id t).add_const h).hasFDerivAt).hasDerivAt using 1 <;>
          simp [Function.comp_def, ContinuousLinearMap.comp_apply]).sub (intervalIntegral.integral_hasDerivAt_right hIntT (show StronglyMeasurableAtFilter W (𝓝 t) volume from ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hAtIoo t ⟨ht0, by linarith⟩) hAtT)
  have hDerivNormal : HasDerivAt (fun s => h⁻¹ • (A (s + h) - A s))
      (h⁻¹ • (W (t + h) - W t)) t := hDerivDiff.const_smul h⁻¹
  apply hDerivNormal.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht0 (by linarith : t < T - h)] with s hs
  have hWin : Ioc s (s + h) ⊆ Ioo (0 ) T := by
    intro r hr
    constructor
    · exact lt_of_lt_of_le hs.1 hr.1.le
    · linarith [hr.2, hs.2]
  have hCont0s : ContinuousOn W (Icc 0 s) := hW.mono (by
    intro r hr
    constructor
    · exact hr.1
    · exact le_of_lt (by linarith [hr.2, hs.2, hh]))
  have hContSh : ContinuousOn W (Icc s (s + h)) := hW.mono (by
    intro r hr
    constructor
    · exact le_of_lt (lt_of_lt_of_le hs.1 hr.1)
    · exact le_of_lt (lt_of_le_of_lt hr.2 (by linarith [hs.2])))
  have hAdj := intervalIntegral.integral_add_adjacent_intervals
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hs.1.le hCont0s)
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (by linarith [hh]) hContSh)
  have hSub : (∫ r in s..s + h, W r) = A (s + h) - A s :=
    (eq_sub_iff_add_eq).mpr (by simpa only [A, add_comm] using hAdj)
  change h⁻¹ • (∫ r, W r ∂(volume.restrict (Ioo (0 : ℝ) T)).restrict
    (Ioc s (s + h))) = _
  rw [Measure.restrict_restrict_of_subset hWin,
    ← intervalIntegral.integral_of_le (by linarith), hSub]

private theorem hasDerivAt_backward_affineAverage
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h) (W : ℝ → E)
    (hW : ContinuousOn W (Icc 0 T))
    {t : ℝ} (ht0 : 0 < t - h) (htT : t < T) :
    HasDerivAt
      (fun s => h⁻¹ • ∫ r in Ioc (s - h) s, W r ∂reverseTimeVolume T)
      (h⁻¹ • (W t - W (t - h))) t := by
  have hAtIoo : ∀ x ∈ Ioo (0 : ℝ) T, ContinuousAt W x := by
    intro x hx
    exact hW.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hAtT  := hAtIoo t ⟨by linarith, htT⟩
  have hAtTmh  := hAtIoo (t - h) ⟨ht0, by linarith⟩

  have hmeasTmh : StronglyMeasurableAtFilter W (𝓝 (t - h))  :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hAtIoo (t - h)
      ⟨ht0, by linarith⟩
  let A  := fun x => ∫ r in (0 )..x, W r
  have hIntT : IntervalIntegrable W volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hW.mono (by
      gcongr <;> first | positivity | assumption | norm_num))
  have hIntTmh : IntervalIntegrable W volume 0 (t - h) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hW.mono (by
      grind))



  have hDerivDiff : HasDerivAt (fun s => A s - A (s - h))
      (W t - W (t - h)) t := by
    exact (intervalIntegral.integral_hasDerivAt_right hIntT (show StronglyMeasurableAtFilter W (𝓝 t) volume from ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hAtIoo t ⟨by linarith, htT⟩) hAtT).sub (by
        convert ((show HasDerivAt A (W (t - h)) (t - h) from intervalIntegral.integral_hasDerivAt_right hIntTmh hmeasTmh hAtTmh).hasFDerivAt.comp t
          ((hasDerivAt_id t).sub_const h).hasFDerivAt).hasDerivAt using 1 <;>
          simp [Function.comp_def, ContinuousLinearMap.comp_apply])
  have hDerivNormal : HasDerivAt (fun s => h⁻¹ • (A s - A (s - h)))
      (h⁻¹ • (W t - W (t - h))) t := hDerivDiff.const_smul h⁻¹
  apply hDerivNormal.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by linarith : h < t) htT] with s hs
  have hWin : Ioc (s - h) s ⊆ Ioo (0 ) T := by
    intro r hr
    constructor
    · linarith [hs.1, hr.1]
    · exact lt_of_le_of_lt hr.2 hs.2
  have hCont0Smh : ContinuousOn W (Icc 0 (s - h)) := hW.mono (by
    intro r hr
    constructor
    · exact hr.1
    · linarith [hr.2, hs.2])
  have hContSmhS : ContinuousOn W (Icc (s - h) s) := hW.mono (by
    intro r hr
    constructor
    · linarith [hs.1, hr.1]
    · exact le_of_lt (lt_of_le_of_lt hr.2 hs.2))
  have hAdj := intervalIntegral.integral_add_adjacent_intervals
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (a := 0) (b := s - h)
      (sub_nonneg.mpr hs.1.le) hCont0Smh)
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (a := s - h) (b := s)
      (by linarith [hh]) hContSmhS)
  have hSub : (∫ r in s - h..s, W r) = A s - A (s - h) :=
    (eq_sub_iff_add_eq).mpr (by simpa only [A, add_comm] using hAdj)
  change h⁻¹ • (∫ r, W r ∂(volume.restrict (Ioo (0 : ℝ) T)).restrict
    (Ioc (s - h) s)) = _
  rw [Measure.restrict_restrict_of_subset hWin,
    ← intervalIntegral.integral_of_le (by linarith), hSub]

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)

/-- The continuous affine `V*` curve attached to a reverse-time Gelfand
weak derivative. -/
def reverseTimeGelfandAffineCurve
     :
    ℝ → H10HilbertGraphDual hΩ :=
  fun t => reverseTimeVStarPrimitive hΩ T g t +
    reverseTimeGelfandAffineConstant hΩ T hT u g

private theorem continuousOn_reverseTimeGelfandAffineCurve
     :
    ContinuousOn (reverseTimeGelfandAffineCurve hΩ T hT u g) (Icc 0 T) := (continuousOn_reverseTimeVStarPrimitive hΩ T g).add continuousOn_const

/-- Endpoint-safe increments of the affine Gelfand curve. -/
theorem reverseTimeGelfandAffineCurve_sub

    {s t : ℝ} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    reverseTimeGelfandAffineCurve hΩ T hT u g t -
        reverseTimeGelfandAffineCurve hΩ T hT u g s =
      ∫ r in Set.Ioc s t, g r ∂reverseTimeVolume T := by
  change (reverseTimeVStarPrimitive hΩ T g t +
      reverseTimeGelfandAffineConstant hΩ T hT u g) -
    (reverseTimeVStarPrimitive hΩ T g s +
      reverseTimeGelfandAffineConstant hΩ T hT u g) = _
  rw [add_sub_add_right_eq_sub]
  exact reverseTimeVStarPrimitive_sub hΩ T g hs ht hst

variable (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hderiv in
private theorem reverseTimeGelfandAffineCurve_ae

     :
    (fun s => ((scalarLpToH10HilbertGraphDual hΩ).comp (valueCLM hΩ)) (u s))
      =ᵐ[reverseTimeVolume T] reverseTimeGelfandAffineCurve hΩ T hT u g := by
  filter_upwards [(coeFn_reverseTimeGelfandCLM hΩ T u).symm.trans
    (reverseTimeGelfandCLM_ae_eq_reverseTimeVStarPrimitive_add_affineConstant
      hΩ T hT u g hderiv)] with t ht
  exact ht

section
variable (h t : ℝ) (_hh : 0 < h)

include hderiv _hh
private theorem forward_gelfand_window_eq_affineAverage_raw


     (_ht0 : 0 ≤ t) (_htT : t + h ≤ T) :
    scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ (reverseTimeForwardSteklov T h u t)) =
      h⁻¹ • (∫ s in Ioc t (t + h),
        reverseTimeGelfandAffineCurve hΩ T hT u g s
        ∂reverseTimeVolume T ) := (forwardSteklov_map_eq_setIntegral (scalarLpToH10HilbertGraphDual hΩ ∘SL valueCLM hΩ) T u
  (reverseTimeGelfandAffineCurve hΩ T hT u g) (reverseTimeGelfandAffineCurve_ae hΩ T hT u g hderiv) h t)

private theorem backward_gelfand_window_eq_affineAverage_raw


     (_ht0 : 0 ≤ t - h) (_htT : t ≤ T) :
    scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ (reverseTimeBackwardSteklov T h u t)) =
      h⁻¹ • (∫ s in Ioc (t - h) t,
        reverseTimeGelfandAffineCurve hΩ T hT u g s
        ∂reverseTimeVolume T ) := (backwardSteklov_map_eq_setIntegral (scalarLpToH10HilbertGraphDual hΩ ∘SL valueCLM hΩ) T u
  (reverseTimeGelfandAffineCurve hΩ T hT u g) (reverseTimeGelfandAffineCurve_ae hΩ T hT u g hderiv) h t)
end


section
variable {h t : ℝ} (hh : 0 < h)

include hderiv hh
private theorem forward_gelfand_window_eventuallyEq_affineAverage


     (ht0 : 0 < t) (htT : t + h < T) :
    (fun s => scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeForwardSteklov T h u s))) =ᶠ[𝓝 t]
    fun s => h⁻¹ • (∫ r in Ioc s (s + h),
      reverseTimeGelfandAffineCurve hΩ T hT u g r
      ∂reverseTimeVolume T ) := by
  filter_upwards [Ioo_mem_nhds ht0 (by linarith : t < T - h)] with s hs
  exact forward_gelfand_window_eq_affineAverage_raw hΩ T hT u g hderiv h s hh
    (le_of_lt hs.1) (by linarith [hs.2])

private theorem backward_gelfand_window_eventuallyEq_affineAverage


     (ht0 : 0 < t - h) (htT : t < T) :
    (fun s => scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeBackwardSteklov T h u s))) =ᶠ[𝓝 t]
    fun s => h⁻¹ • (∫ r in Ioc (s - h) s,
      reverseTimeGelfandAffineCurve hΩ T hT u g r
      ∂reverseTimeVolume T ) := by
  filter_upwards [Ioo_mem_nhds (by linarith : h < t) htT] with s hs
  exact backward_gelfand_window_eq_affineAverage_raw hΩ T hT u g hderiv h s hh
    (by linarith [hs.1]) (le_of_lt hs.2)
end


section
variable {h t : ℝ} (hh : 0 < h)

include hh
private theorem forward_affineIncrement_normalized_eq_steklov

     (ht0 : 0 < t) (htT : t + h < T) :
    h⁻¹ • (reverseTimeGelfandAffineCurve hΩ T hT u g (t + h) -
      reverseTimeGelfandAffineCurve hΩ T hT u g t) =
      reverseTimeForwardSteklov T h g t := by
  change h⁻¹ • (reverseTimeGelfandAffineCurve hΩ T hT u g (t + h) -
      reverseTimeGelfandAffineCurve hΩ T hT u g t) =
    h⁻¹ • (∫ r in Ioc t (t + h), g r ∂reverseTimeVolume T )
  exact congrArg (fun z : H10HilbertGraphDual hΩ => h⁻¹ • z)
    (reverseTimeGelfandAffineCurve_sub hΩ T hT u g
      (show t ∈ Icc 0 T by
        constructor
        · linarith
        · linarith)
      (show t + h ∈ Icc 0 T by
        constructor
        · linarith
        · linarith)
      (by linarith))

private theorem backward_affineIncrement_normalized_eq_steklov

     (ht0 : 0 < t - h) (htT : t < T) :
    h⁻¹ • (reverseTimeGelfandAffineCurve hΩ T hT u g t -
      reverseTimeGelfandAffineCurve hΩ T hT u g (t - h)) =
      reverseTimeBackwardSteklov T h g t := by
  change h⁻¹ • (reverseTimeGelfandAffineCurve hΩ T hT u g t -
      reverseTimeGelfandAffineCurve hΩ T hT u g (t - h)) =
    h⁻¹ • (∫ r in Ioc (t - h) t, g r ∂reverseTimeVolume T )
  exact congrArg (fun z : H10HilbertGraphDual hΩ => h⁻¹ • z)
    (reverseTimeGelfandAffineCurve_sub hΩ T hT u g
      (show t - h ∈ Icc 0 T by
        constructor
        · linarith
        · linarith)
      (show t ∈ Icc 0 T by
        constructor
        · linarith
        · linarith)
      (by linarith))
end


variable (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) {h t : ℝ} (hh : 0 < h)

include hderiv hh
/-- Strict-interior derivative of the pivoted forward Steklov curve. -/
theorem hasDerivAt_reverseTimeForwardSteklov_gelfand

     (ht0 : 0 < t) (htT : t + h < T) :
    HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ (reverseTimeForwardSteklov T h u s)))
      (reverseTimeForwardSteklov T h g t) t := by

  have hAverage := hasDerivAt_forward_affineAverage T h hh
    (reverseTimeGelfandAffineCurve hΩ T hT u g) (continuousOn_reverseTimeGelfandAffineCurve hΩ T hT u g) ht0 htT
  have hTransport : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ (reverseTimeForwardSteklov T h u s)))
      (h⁻¹ • (reverseTimeGelfandAffineCurve hΩ T hT u g (t + h) -
        reverseTimeGelfandAffineCurve hΩ T hT u g t)) t :=
    hAverage.congr_of_eventuallyEq
      (forward_gelfand_window_eventuallyEq_affineAverage
        hΩ T hT u g hderiv hh ht0 htT)
  simpa only [forward_affineIncrement_normalized_eq_steklov
    (hΩ := hΩ) (T := T) (hT := hT) (u := u) (g := g)
    (hh := hh) (ht0 := ht0) (htT := htT)] using hTransport

/-- Strict-interior derivative of the pivoted backward Steklov curve. -/
theorem hasDerivAt_reverseTimeBackwardSteklov_gelfand

     (ht0 : 0 < t - h) (htT : t < T) :
    HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ (reverseTimeBackwardSteklov T h u s)))
      (reverseTimeBackwardSteklov T h g t) t := by

  have hAverage := hasDerivAt_backward_affineAverage T h hh
    (reverseTimeGelfandAffineCurve hΩ T hT u g) (continuousOn_reverseTimeGelfandAffineCurve hΩ T hT u g) ht0 htT
  have hTransport : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ (reverseTimeBackwardSteklov T h u s)))
      (h⁻¹ • (reverseTimeGelfandAffineCurve hΩ T hT u g t -
        reverseTimeGelfandAffineCurve hΩ T hT u g (t - h))) t :=
    hAverage.congr_of_eventuallyEq
      (backward_gelfand_window_eventuallyEq_affineAverage
        hΩ T hT u g hderiv hh ht0 htT)
  simpa only [backward_affineIncrement_normalized_eq_steklov
    (hΩ := hΩ) (T := T) (hT := hT) (u := u) (g := g)
    (hh := hh) (ht0 := ht0) (htT := htT)] using hTransport

end HypoellipticAleksandrov.Parabolic.Dirichlet
