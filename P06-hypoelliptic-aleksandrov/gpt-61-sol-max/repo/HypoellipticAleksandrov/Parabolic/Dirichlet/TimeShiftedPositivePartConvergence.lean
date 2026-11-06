module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartEnergySupport
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy

open private HypoellipticAleksandrov.Parabolic.Dirichlet.abs_sqNorm_valueCLM_sub_le from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.abs_sq_sub_le_of_bounds from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
section
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_dualPairing from HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
private alias _sharedProof_466_0 := HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_dualPairing
end


/-!
# Continuity of affine-threshold shifted positive parts in reverse time

This module decomposes the finite-measure Vitali argument proving strong
continuity of the affine-threshold shifted positive-part operation on the
reverse-time Bochner `L²` space.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable (hΩ : IsOpen Ω)

/-- Raw representatives of a sequence of affine-threshold shifted positive
parts. -/
def shiftedPositivePartSequence
     (M N : ℝ≥0)
    (un : ℕ → ℝ → H10HilbertGraph hΩ) :
    ℕ → ℝ → H10HilbertGraph hΩ :=
  fun n τ => h10ShiftedPositivePart hΩ (un n τ)
    (reverseTimeAffineThreshold M N τ)

/-- The sharp spatial norm bound transfers uniform integrability to the
affine-threshold shifted positive parts. -/
theorem unifIntegrable_shiftedPositivePartSequence
     (T : ℝ) (M N : ℝ≥0)
    (un : ℕ → ReverseTimeL2V hΩ T)
    (hunUI : UnifIntegrable (fun n τ => un n τ) (2 )
      (reverseTimeVolume T)) :
    UnifIntegrable
      (shiftedPositivePartSequence hΩ M N (fun n τ => un n τ))
      (2 ) (reverseTimeVolume T) := by
  rw [unifIntegrable_iff']
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff'.mp hunUI ε hε
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  refine (eLpNorm_mono
    ((continuous_h10ShiftedPositivePart hΩ).comp_aestronglyMeasurable
      ((Lp.memLp (un n)).aestronglyMeasurable.prodMk
        (continuous_const.add (continuous_real_toNNReal.mul continuous_const)
          |>.aestronglyMeasurable))).restrict ?_).trans (hbound n s hs hμs)
  intro τ
  exact norm_h10ShiftedPositivePart_le hΩ (un n τ)
    (reverseTimeAffineThreshold M N τ)

/-- At a fixed reverse time, convergence of the spatial inputs implies
convergence of their shifted positive parts with the affine threshold held
fixed. -/
theorem tendsto_shiftedPositivePart_at_fixed_time
     (M N : ℝ≥0)
    (un : ℕ → H10HilbertGraph hΩ)
    (u : H10HilbertGraph hΩ) (τ : ℝ)
    (hτ : Tendsto un atTop (𝓝 u)) :
    Tendsto
      (fun n => h10ShiftedPositivePart hΩ (un n)
        (reverseTimeAffineThreshold M N τ))
      atTop
      (𝓝 (h10ShiftedPositivePart hΩ u
        (reverseTimeAffineThreshold M N τ))) := (Tendsto.comp
  (ContinuousAt.tendsto
    (Continuous.continuousAt
      (Continuous.comp (continuous_h10ShiftedPositivePart hΩ) (Continuous.prodMk continuous_id continuous_const))))
  hτ)

variable (T : ℝ) (M N : ℝ≥0)

private theorem exists_subseq_tendsto_reverseTimeShiftedPositivePart

    (un : ℕ → ReverseTimeL2V hΩ T) (u : ReverseTimeL2V hΩ T)
    (hun : Tendsto un atTop (𝓝 u))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto
        (fun n => reverseTimeShiftedPositivePart hΩ T M N (un (ns (ms n))))
        atTop (𝓝 (reverseTimeShiftedPositivePart hΩ T M N u)) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  let f  := fun n τ => un n τ
  let g  :=
    shiftedPositivePartSequence hΩ M N f
  let g₀  := fun τ =>
    h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M N τ)
  have hfMem : ∀ n, MemLp (f n) (2 ) (reverseTimeVolume T) :=
    fun n => Lp.memLp (un n)
  have huMem : MemLp (fun τ => u τ) (2 ) (reverseTimeVolume T) :=
    Lp.memLp u
  have hfLp : Tendsto (fun n => eLpNorm (f n - fun τ => u τ) 2
      (reverseTimeVolume T)) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' un u).1 hun
  have hfUI : UnifIntegrable f (2 ) (reverseTimeVolume T) :=
    unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num) hfMem huMem hfLp

  have hgMem : ∀ n, MemLp (g n) (2 ) (reverseTimeVolume T) := by
    intro n
    exact (memLp_congr_ae
      (coeFn_reverseTimeShiftedPositivePart hΩ T M N (un n))).mp
      (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N (un n)))
  have hg₀Mem : MemLp g₀ (2 ) (reverseTimeVolume T) :=
    (memLp_congr_ae (coeFn_reverseTimeShiftedPositivePart hΩ T M N u)).mp
      (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u))
  obtain ⟨ms, hms, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      (hun.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩


  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine (show Tendsto (fun n => eLpNorm
      (g (ns (ms n)) - g₀) (2 ) (reverseTimeVolume T))
      atTop (𝓝 0) by
      apply tendsto_Lp_finite_of_tendsto_ae (p := (2 ))
        (by norm_num) (by norm_num)
      · exact fun n => (hgMem (ns (ms n))).aestronglyMeasurable
      · exact hg₀Mem
      · rw [unifIntegrable_iff]
        intro ε hε
        obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.mp (unifIntegrable_shiftedPositivePartSequence hΩ T M N un hfUI) ε hε
        exact ⟨δ, hδ, fun n => hbound (ns (ms n))⟩
      · exact (by
          filter_upwards [hae] with τ hτ
          exact tendsto_shiftedPositivePart_at_fixed_time hΩ M N
            (fun n => un (ns (ms n)) τ) (u τ) τ hτ)).congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards
      [coeFn_reverseTimeShiftedPositivePart hΩ T M N (un (ns (ms n))),
        coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with τ hleft hright
  simp only [Pi.sub_apply, g, g₀, shiftedPositivePartSequence]
  change _ = (reverseTimeShiftedPositivePart hΩ T M N (un (ns (ms n)))) τ -
    (reverseTimeShiftedPositivePart hΩ T M N u) τ
  rw [hleft, hright]

/-- The affine-threshold shifted positive-part operation is strongly
continuous on reverse-time Bochner `L²(V)`. -/
theorem continuous_reverseTimeShiftedPositivePart
      :
    Continuous (reverseTimeShiftedPositivePart hΩ T M N ) := by
  rw [continuous_iff_seqContinuous]
  intro un u hun
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hconv⟩ :=
    exists_subseq_tendsto_reverseTimeShiftedPositivePart
      hΩ T M N un u hun ns hns
  exact ⟨ms, hconv⟩

variable {E : Type*}

/-- The forward Steklov average as a totalized reverse-time Bochner `L²`
class.  Nonpositive averaging widths are assigned the original class. -/
def reverseTimeForwardSteklovL2
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))  :=
  if hh : 0 < h then
    reverseTimeL2OfContinuousOn T _
      (continuous_reverseTimeForwardSteklov T h hh f).continuousOn
  else
    f

/-- At a positive averaging width, the lifted forward Steklov class is
represented almost everywhere by the pointwise average. -/
theorem coeFn_reverseTimeForwardSteklovL2_of_pos
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) {h : ℝ} (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    reverseTimeForwardSteklovL2 T h f =ᵐ[reverseTimeVolume T]
      reverseTimeForwardSteklov T h f := by
  rw [reverseTimeForwardSteklovL2, dif_pos hh]
  exact coeFn_reverseTimeL2OfContinuousOn T _ _

/-- The totalized forward Steklov lift converges strongly to the original
reverse-time Bochner `L²` class as the averaging width tends to zero from the
right. -/
theorem tendsto_reverseTimeForwardSteklovL2
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Tendsto (fun h  => reverseTimeForwardSteklovL2 T h f)
      (nhdsWithin 0 (Ioi 0)) (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]


  refine (show Tendsto
      (fun h : ℝ => √(∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) by
      simpa only [Real.sqrt_zero, Function.comp_def] using
        (Continuous.tendsto Real.continuous_sqrt 0).comp (tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hraw  :=
    memLp_two_reverseTime_of_continuousOn T _
      (continuous_reverseTimeForwardSteklov T h hh f).continuousOn
  let hsub := hraw.sub (Lp.memLp f)
  have htoLp : hsub.toLp
      (reverseTimeForwardSteklov T h f - fun t => f t) =
      reverseTimeForwardSteklovL2 T h f - f := by
    apply Lp.ext
    filter_upwards [hsub.coeFn_toLp,
        coeFn_reverseTimeForwardSteklovL2_of_pos T hh f,
        Lp.coeFn_sub (reverseTimeForwardSteklovL2 T h f) f]
      with t hsubt hlift hliftSub
    rw [hsubt]
    calc
      (reverseTimeForwardSteklov T h f - fun t => f t) t =
          reverseTimeForwardSteklovL2 T h f t - f t := by
        rw [Pi.sub_apply, hlift]
      _ = (reverseTimeForwardSteklovL2 T h f - f) t := hliftSub.symm
  have hint : (∫ t in Icc 0 T,
      ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
      ‖hsub.toLp
        (reverseTimeForwardSteklov T h f - fun t => f t)‖ ^ 2 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, Pi.sub_apply] using
      integral_norm_sq_eq_norm_sq_toLp
        (reverseTimeForwardSteklov T h f - fun t => f t) hsub
  rw [← Real.sqrt_sq (norm_nonneg
    (reverseTimeForwardSteklovL2 T h f - f)), ← htoLp, ← hint]

private theorem tendsto_sqNorm_integral_restrict_of_Lp
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {l : Filter ι}
    {T : ℝ} {f : MeasureTheory.Lp E 2 (reverseTimeVolume T)}
    {fh : ι → MeasureTheory.Lp E 2 (reverseTimeVolume T)}
    (hfh : Tendsto fh l (𝓝 f)) (s : Set ℝ)
    (hs : volume.restrict s ≤ reverseTimeVolume T) :
    Tendsto (fun h : ι => ∫ t in s, ‖fh h t - f t‖ ^ 2) l (𝓝 0) := by

  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  · filter_upwards with h
    have hm : MemLp (fun t => fh h t - f t) 2 (reverseTimeVolume T) :=
      (Lp.memLp (fh h)).sub (Lp.memLp f)
    calc
      (∫ t in s, ‖fh h t - f t‖ ^ 2) ≤
          ∫ t, ‖fh h t - f t‖ ^ 2 ∂reverseTimeVolume T := by
        apply integral_mono_measure
        · exact hs
        · exact Eventually.of_forall fun _ => sq_nonneg _
        · exact hm.integrable_norm_pow (by norm_num : (2 ) ≠ 0)
      _ = ‖fh h - f‖ ^ 2 := by

        have htoLp : hm.toLp (fun t => fh h t - f t) = fh h - f := by
          apply Lp.ext
          filter_upwards [hm.coeFn_toLp, (show (fun t => fh h t - f t) =ᵐ[reverseTimeVolume T]
            fun t => (fh h - f) t by
              filter_upwards [Lp.coeFn_sub (fh h) f] with t ht
              exact ht.symm)] with t h1 h2
          rw [h1, h2]
        simpa only [htoLp] using integral_norm_sq_eq_norm_sq_toLp (fun t => fh h t - f t) hm
  · exact (show Tendsto (fun h : ι => ‖fh h - f‖ ^ 2) l (𝓝 0) by
      simpa only [zero_pow (by norm_num : (2 ) ≠ 0)] using
        (tendsto_iff_norm_sub_tendsto_zero.mp hfh).pow 2)







private theorem tendsto_integral_mul_of_tendsto_integral_abs
    {ι : Type*} {l : Filter ι} {μ : Measure ℝ} {F : ι → ℝ → ℝ}
    {f phi : ℝ → ℝ}
    (hF : ∀ᶠ h : ι in l, Integrable (F h) μ)
    (hf : Integrable f μ) (hphi : AEStronglyMeasurable phi μ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ‖phi t‖ ≤ C)
    (hlim : Tendsto (fun h  => ∫ t, |F h t - f t| ∂μ) l (𝓝 0)) :
    Tendsto (fun h  => ∫ t, F h t * phi t ∂μ) l
      (𝓝 (∫ t, f t * phi t ∂μ)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnorm : ∀ t : ℝ, ‖‖phi t‖‖ ≤ C := by
    intro t
    simpa only [norm_norm] using hC t


  have := (show Tendsto (fun h  => ∫ t, (F h t - f t) * phi t ∂μ)
      l (𝓝 0) by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero'
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · filter_upwards [hF] with h hFh
        have hd : Integrable (fun t => F h t - f t) μ := hFh.sub hf

        calc
          ‖∫ t, (F h t - f t) * phi t ∂μ‖ ≤
              ∫ t, ‖(F h t - f t) * phi t‖ ∂μ :=
            norm_integral_le_integral_norm _
          _ ≤ ∫ t, C * |F h t - f t| ∂μ := by
            apply integral_mono
            · simpa only [norm_mul, Real.norm_eq_abs] using (hd.norm.mul_bdd hphi.norm (Eventually.of_forall hCnorm))
            · exact hd.norm.const_mul C
            · intro t
              simp only [norm_mul, Real.norm_eq_abs]
              calc
                |F h t - f t| * ‖phi t‖ ≤ |F h t - f t| * C :=
                  mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)
                _ = C * |F h t - f t| := mul_comm _ _
          _ = C * (∫ t, |F h t - f t| ∂μ) := integral_const_mul _ _
      · simpa only [mul_zero] using tendsto_const_nhds.mul hlim).add (tendsto_const_nhds : Tendsto (fun _ : ι =>
      ∫ t, f t * phi t ∂μ) l _)
  simpa only [zero_add] using this.congr' (by
    filter_upwards [hF] with h hFh
    have hd : Integrable (fun t => F h t - f t) μ := hFh.sub hf

    have hr := hf.mul_bdd hphi (Eventually.of_forall hC)
    rw [← integral_add (hd.mul_bdd hphi (Eventually.of_forall hC)) hr]
    apply integral_congr_ae
    filter_upwards with t
    ring)

/-- Strong reverse-time `L²` convergence gives local convergence of the
square of the spatial `L²` value norm. -/
theorem tendsto_integral_abs_valueCLM_sq_of_tendsto
    (hΩ : IsOpen Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (un : ℕ → ReverseTimeL2V hΩ T)
    (hun : Tendsto un atTop (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |‖valueCLM hΩ (un n t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|)
      atTop (𝓝 0) := by
  let sharedTerm_8164f0b22d := ((by norm_num : (2 ) ≠ 0))
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let L : H10HilbertGraph hΩ →L[ℝ]
      MeasureTheory.Lp ℝ 2 (PDE.volumeOn Ω) := valueCLM hΩ
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) 2 μ :=
    (Lp.memLp u).mono_measure hμ
  have hunMem : ∀ n, MemLp (un n : ℝ → H10HilbertGraph hΩ) 2 μ :=
    fun n => (Lp.memLp (un n)).mono_measure hμ
  have hsq : Tendsto (fun n => ∫ t, ‖un n t - u t‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
    exact tendsto_sqNorm_integral_restrict_of_Lp hun (Icc a b) hμ
  let C : ℝ := ‖L‖ ^ 2


  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
  · exact Eventually.of_forall (show ∀ n,
      (∫ t, |‖L (un n t)‖ ^ 2 - ‖L (u t)‖ ^ 2| ∂μ) ≤
        C * (∫ t, ‖un n t - u t‖ ^ 2 ∂μ) +
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
          √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ) by
      intro n
      have hdu := (hunMem n).sub hu
      have hLun := (hunMem n).continuousLinearMap_comp L
      have hLu := hu.continuousLinearMap_comp L

      have hterm1 : Integrable (fun t => C * ‖un n t - u t‖ ^ 2) μ :=
        (hdu.integrable_norm_pow sharedTerm_8164f0b22d).const_mul _
      have hterm2 : Integrable (fun t =>
          2 * C * ‖u t‖ * ‖un n t - u t‖) μ := by
        apply ((hu.norm).integrable_mul hdu.norm).const_mul (2 * C) |>.congr
        filter_upwards with t
        change 2 * C * (((fun x => ‖u x‖) * fun x => ‖un n x - u x‖) t) = _
        simp only [Pi.mul_apply]
        ring

      calc
        _ ≤ ∫ t, C * ‖un n t - u t‖ ^ 2 +
            2 * C * ‖u t‖ * ‖un n t - u t‖ ∂μ :=
          integral_mono (by
              simpa only [Real.norm_eq_abs, Pi.sub_def] using
                ((hLun.integrable_norm_pow sharedTerm_8164f0b22d).sub
                  (hLu.integrable_norm_pow sharedTerm_8164f0b22d)).norm) (hterm1.add hterm2) (by
              intro t
              simpa only [L, C] using
                _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.abs_sqNorm_valueCLM_sub_le hΩ (un n t) (u t))
        _ = C * (∫ t, ‖un n t - u t‖ ^ 2 ∂μ) +
            2 * C * (∫ t, ‖u t‖ * ‖un n t - u t‖ ∂μ) := by
          rw [integral_add hterm1 hterm2, integral_const_mul]
          rw [show (fun t => 2 * C * ‖u t‖ * ‖un n t - u t‖) =
            fun t => (2 * C) * (‖u t‖ * ‖un n t - u t‖) by funext t; ring,
            integral_const_mul]
        _ ≤ _ := by
          apply add_le_add_right
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (integral_mul_norm_le_sqrt_mul_sqrt u (fun t => un n t - u t) hu hdu)
            (by positivity : 0 ≤ 2 * C))
  · have hfirst : Tendsto (fun n =>
        C * (∫ t, ‖un n t - u t‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hsq
    have hsecond := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ)) atTop _).mul (show Tendsto (fun n => √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ))
      atTop (𝓝 0) by
            simpa only [Real.sqrt_zero] using hsq.sqrt)
    simpa only [mul_zero, add_zero] using hfirst.add hsecond

/-- A bounded scalar functional sends strong reverse-time `L²` convergence to
local `L¹` convergence. -/
theorem tendsto_integral_abs_continuousLinearMap_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T a b : ℝ} (Q : E →L[ℝ] ℝ)
    (u : MeasureTheory.Lp E 2 (reverseTimeVolume T))
    (un : ℕ → MeasureTheory.Lp E 2 (reverseTimeVolume T))
    (hun : Tendsto un atTop (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b, |Q (un n t) - Q (u t)|)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Icc a b)


  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
  · filter_upwards with n
    have hd : MemLp (fun t => un n t - u t) 2 μ :=
      ((Lp.memLp (un n)).mono_measure hμ).sub ((Lp.memLp u).mono_measure hμ)
    calc
      (∫ t, |Q (un n t) - Q (u t)| ∂μ) =
          ∫ t, ‖Q (un n t - u t)‖ ∂μ := by
        norm_num
      _ ≤ ‖Q‖ * ∫ t, ‖un n t - u t‖ ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono
        · exact (hd.continuousLinearMap_comp Q).integrable (by norm_num) |>.norm
        · exact hd.integrable (by norm_num) |>.norm.const_mul _
        · intro t
          exact Q.le_opNorm _
      _ ≤ ‖Q‖ * √(∫ _t : ℝ, ‖(1 : ℝ)‖ ^ 2 ∂μ) *
          √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ) := by
        have hh := integral_mul_norm_le_sqrt_mul_sqrt
          (fun _  => (1 : ℝ)) (fun t => un n t - u t)
          (memLp_const (μ := μ) (p := (2 )) (1 : ℝ)) hd

        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (show (∫ t, ‖un n t - u t‖ ∂μ) ≤
            √(∫ _t : ℝ, ‖(1 : ℝ)‖ ^ 2 ∂μ) *
              √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ) by
              simpa only [norm_one, one_mul] using hh) (norm_nonneg Q)
  · simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ‖Q‖ * √(∫ _t : ℝ, ‖(1 : ℝ)‖ ^ 2 ∂μ)) atTop _).mul (show Tendsto (fun n => √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ))
      atTop (𝓝 0) by simpa only [Real.sqrt_zero] using (tendsto_sqNorm_integral_restrict_of_Lp hun (Icc a b) hμ).sqrt)

variable (hΩ : IsOpen Ω)

/-- The spatial-mass specialization of the bounded-functional adapter. -/
theorem tendsto_integral_abs_spatialMass_value_of_tendsto
     (hΩbounded : Bornology.IsBounded Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (un : ℕ → ReverseTimeL2V hΩ T)
    (hun : Tendsto un atTop (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) (un n t) -
        ((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) (u t)|)
      atTop (𝓝 0) :=
  tendsto_integral_abs_continuousLinearMap_of_tendsto
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) u un hun hμ

private theorem shifted_dualPairing_pointwise_le
     (u uh : H10HilbertGraph hΩ)
    (g gh : H10HilbertGraphDual hΩ) :
    |gh uh - g u| ≤ ‖gh - g‖ * ‖uh‖ + ‖g‖ * ‖uh - u‖ := by
  change ‖gh uh - g u‖ ≤ _
  calc
    _ = ‖(gh - g) uh + g (uh - u)‖ := by
      congr 1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.map_sub]
      ring
    _ ≤ ‖(gh - g) uh‖ + ‖g (uh - u)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (ContinuousLinearMap.le_opNorm _ _)
      (ContinuousLinearMap.le_opNorm _ _)

variable {μ : Measure ℝ}

private theorem shifted_integrable_dualPairing

    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => (g t) (u t)) μ := (_sharedProof_466_0 hΩ μ u g hu hg)


private theorem shifted_dualPairing_integral_le

    (u uh : ℝ → H10HilbertGraph hΩ)
    (g gh : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (huh : MemLp uh 2 μ)
    (hg : MemLp g 2 μ) (hgh : MemLp gh 2 μ) :
    (∫ t, |(gh t) (uh t) - (g t) (u t)| ∂μ) ≤
      √(∫ t, ‖gh t - g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh t‖ ^ 2 ∂μ) +
      √(∫ t, ‖g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh t - u t‖ ^ 2 ∂μ) := (Trans.trans
  (Trans.trans
    (integral_mono
      (Integrable.norm
        (Integrable.sub (shifted_integrable_dualPairing hΩ uh gh huh hgh)
          (shifted_integrable_dualPairing hΩ u g hu hg)))
      (Integrable.add (MemLp.integrable_mul (MemLp.norm (MemLp.sub hgh hg)) (MemLp.norm huh))
        (MemLp.integrable_mul (MemLp.norm hg) (MemLp.norm (MemLp.sub huh hu))))
      fun t => shifted_dualPairing_pointwise_le hΩ (u t) (uh t) (g t) (gh t))
    (integral_add (MemLp.integrable_mul (MemLp.norm (MemLp.sub hgh hg)) (MemLp.norm huh))
      (MemLp.integrable_mul (MemLp.norm hg) (MemLp.norm (MemLp.sub huh hu)))))
  (add_le_add (integral_mul_norm_le_sqrt_mul_sqrt (fun t => gh t - g t) uh (MemLp.sub hgh hg) huh)
    (integral_mul_norm_le_sqrt_mul_sqrt g (fun t => uh t - u t) hg (MemLp.sub huh hu))))

private theorem integral_abs_sub_mul_sub_le
    {μ : Measure ℝ} (A B X Y : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : Integrable A μ) (hB : Integrable B μ)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ t, |A t - c * X t - (B t - c * Y t)| ∂μ) ≤
      (∫ t, |A t - B t| ∂μ) + c * (∫ t, |X t - Y t| ∂μ) := by


  have hAB' : Integrable (fun t => |A t - B t|) μ := by
    exact ((hA.sub hB).norm)
  have hXY' : Integrable (fun t => |X t - Y t|) μ := by
    exact ((hX.sub hY).norm)
  calc
    _ ≤ ∫ t, |A t - B t| + c * |X t - Y t| ∂μ := by
      apply integral_mono
      · fun_prop
      · exact hAB'.add (hXY'.const_mul c)
      · intro t
        calc
          |A t - c * X t - (B t - c * Y t)| =
              |(A t - B t) - c * (X t - Y t)| := by
            congr 1
            ring
          _ ≤ |A t - B t| + |c * (X t - Y t)| := abs_sub _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hc]
    _ = _ := by
      rw [integral_add hAB' (hXY'.const_mul c), integral_const_mul]

/-- Strong convergence in the primal and dual reverse-time `L²` spaces gives
local `L¹` convergence of their pointwise dual pairing. -/
theorem tendsto_integral_abs_dualPairing_of_tendsto
    (hΩ : IsOpen Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (un : ℕ → ReverseTimeL2V hΩ T)
    (gn : ℕ → ReverseTimeL2VStar hΩ T)
    (hun : Tendsto un atTop (𝓝 u)) (hgn : Tendsto gn atTop (𝓝 g))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |(gn n t) (un n t) - (g t) (u t)|) atTop (𝓝 0) := by
  let μ := volume.restrict (Icc a b)





  have hG := tendsto_sqNorm_integral_restrict_of_Lp hgn (Icc a b) hμ



  have hlocalb : IsBoundedUnder LE.le atTop
      (fun n => √(∫ t, ‖un n t‖ ^ 2 ∂μ)) := by
    obtain ⟨C, hC⟩ := hun.norm.isBoundedUnder_le.eventually_le
    apply isBoundedUnder_of_eventually_le
    filter_upwards [hC] with n hn
    have hglobal := Lp.memLp (un n)
    have hi : (∫ t, ‖un n t‖ ^ 2 ∂μ) ≤
        ∫ t, ‖un n t‖ ^ 2 ∂reverseTimeVolume T :=
      integral_mono_measure hμ (Eventually.of_forall fun _ => sq_nonneg _)
        (hglobal.integrable_norm_pow (by norm_num))
    rw [integral_norm_sq_eq_norm_sq_toLp (un n) hglobal] at hi
    have hto : hglobal.toLp (un n) = un n := by
      apply Lp.ext
      exact hglobal.coeFn_toLp
    rw [hto] at hi
    exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_sq (norm_nonneg _)) |>.trans hn

  have hfirst := (show Tendsto (fun n => √(∫ t, ‖gn n t - g t‖ ^ 2 ∂μ))
      atTop (𝓝 0) by simpa only [Real.sqrt_zero] using hG.sqrt).zero_mul_isBoundedUnder_le (show IsBoundedUnder LE.le atTop
      (fun n => ‖√(∫ t, ‖un n t‖ ^ 2 ∂μ)‖) by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hlocalb)

  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
  · filter_upwards with n
    exact shifted_dualPairing_integral_le hΩ u (un n) g (gn n)
      ((Lp.memLp u).mono_measure hμ) ((fun n => (Lp.memLp (un n)).mono_measure hμ) n) ((Lp.memLp g).mono_measure hμ) ((fun n => (Lp.memLp (gn n)).mono_measure hμ) n)
  · simpa only [zero_add] using hfirst.add (by
      simpa only [mul_zero] using tendsto_const_nhds.mul (show Tendsto (fun n => √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ))
      atTop (𝓝 0) by simpa only [Real.sqrt_zero] using (tendsto_sqNorm_integral_restrict_of_Lp hun (Icc a b) hμ).sqrt))

/-- Forward Steklov regularization preserves the tested affine-threshold
shifted-positive-part energy in the zero-width limit. -/
theorem tendsto_forwardSteklov_shiftedPositivePartEnergy_test
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (M N : ℝ≥0) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    Tendsto (fun h  => ∫ t in Icc a b,
      shiftedPositivePartEnergy hΩ M N
        ((reverseTimeForwardSteklov T h u)) t * eta.deriv t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        shiftedPositivePartEnergy hΩ M N (fun t => u t) t * eta.deriv t)) := by


  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T := by
    change volume.restrict (Icc a b) ≤ volume.restrict (Ioo (0 : ℝ) T)
    exact Measure.restrict_mono' (ae_of_all _ fun t ht => (show Icc a b ⊆ Ioo (0 ) T by
        intro t ht
        exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩) ht) le_rfl
  rw [tendsto_iff_seq_tendsto]
  intro hs hhs
  let uh : ℕ → ReverseTimeL2V hΩ T := fun n =>
    reverseTimeForwardSteklovL2 T (hs n) u
  let up  := reverseTimeShiftedPositivePart hΩ T M N u
  let uhp  := fun n =>
    reverseTimeShiftedPositivePart hΩ T M N (uh n)


  have hclass := tendsto_integral_abs_valueCLM_sq_of_tendsto
    hΩ up uhp ((continuous_reverseTimeShiftedPositivePart hΩ T M N).continuousAt.tendsto.comp ((tendsto_reverseTimeForwardSteklovL2 T (lt_trans ha (lt_trans hab hb)) u).comp hhs)) hμ
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < hs n :=
    hhs (self_mem_nhdsWithin )



  exact tendsto_integral_mul_of_tendsto_integral_abs (by
      filter_upwards [hpos] with n hn
      exact (((valueCLM hΩ).continuous.comp
        ((continuous_h10ShiftedPositivePart hΩ).comp
          ((continuous_reverseTimeForwardSteklov T (hs n) hn u).prodMk
            (continuous_const.add
              (continuous_real_toNNReal.mul continuous_const))))).norm.pow 2).integrableOn_Icc) (by


      apply ((((Lp.memLp up).mono_measure hμ).continuousLinearMap_comp (valueCLM hΩ)).integrable_norm_pow (by norm_num : (2 ) ≠ 0)).congr
      filter_upwards [(coeFn_reverseTimeShiftedPositivePart hΩ T M N u).filter_mono
          (ae_mono hμ)] with t ht
      simp only [shiftedPositivePartEnergy]
      rw [ht])
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le (by
        apply hclass.congr'
        filter_upwards [hpos] with n hn
        apply integral_congr_ae
        filter_upwards
            [(coeFn_reverseTimeForwardSteklovL2_of_pos T hn u).filter_mono
                (ae_mono hμ),
              (coeFn_reverseTimeShiftedPositivePart hΩ T M N (uh n)).filter_mono
                (ae_mono hμ),
              (coeFn_reverseTimeShiftedPositivePart hΩ T M N u).filter_mono
                (ae_mono hμ)]
          with t hraw hshift hlimit
        simp only [uhp, up, shiftedPositivePartEnergy]
        rw [hshift, hlimit, hraw])

variable (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0) (T : ℝ)

private theorem ae_shiftedPositivePartEnergyRate_forwardSteklovL2
     {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    ((shiftedPositivePartEnergyRate hΩ hΩbounded M N (fun r => reverseTimeForwardSteklov T h u r)
  (fun r => reverseTimeForwardSteklov T h g r))) =ᵐ[reverseTimeVolume T]
    fun t => (reverseTimeForwardSteklovL2 T h g t)
      (reverseTimeShiftedPositivePart hΩ T M N
        (reverseTimeForwardSteklovL2 T h u) t) -
      (N : ℝ) * ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (reverseTimeShiftedPositivePart hΩ T M N
          (reverseTimeForwardSteklovL2 T h u) t) := by
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := inferInstance
  letI : ContinuousENorm (H10HilbertGraphDual hΩ) := inferInstance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := inferInstance
  letI : CompleteSpace (H10HilbertGraphDual hΩ) := inferInstance
  filter_upwards [coeFn_reverseTimeForwardSteklovL2_of_pos T hh u,
      coeFn_reverseTimeForwardSteklovL2_of_pos T hh g,
      coeFn_reverseTimeShiftedPositivePart hΩ T M N
        (reverseTimeForwardSteklovL2 T h u)] with t hu hg hup
  simp only [shiftedPositivePartEnergyRate, ContinuousLinearMap.comp_apply]
  simp only [← hup, ← hu, ← hg]

variable (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)

private theorem ae_shiftedPositivePartEnergyRate_L2
      :
    ((shiftedPositivePartEnergyRate hΩ hΩbounded M N (fun r => u r) (fun r => g r))) =ᵐ[reverseTimeVolume T]
    fun t => (g t) (reverseTimeShiftedPositivePart hΩ T M N u t) -
      (N : ℝ) * ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (reverseTimeShiftedPositivePart hΩ T M N u t) := by
  filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with t hup
  simp only [shiftedPositivePartEnergyRate, ContinuousLinearMap.comp_apply]
  rw [hup]

private theorem integrable_shiftedPositivePartEnergyRate_L2_on_Icc

    {a b : ℝ} (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Integrable (shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun t => u t) (fun t => g t)) (volume.restrict (Icc a b)) := by
  have huLocal := (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).mono_measure hμ

  have hp := shifted_integrable_dualPairing hΩ
    (reverseTimeShiftedPositivePart hΩ T M N u) g huLocal ((Lp.memLp g).mono_measure hμ)
  have hm := huLocal.continuousLinearMap_comp
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
  apply (hp.sub ((hm.integrable (by norm_num)).const_mul (N : ℝ))).congr
  exact (ae_shiftedPositivePartEnergyRate_L2 hΩ hΩbounded M N T u g).symm.filter_mono
    (ae_mono hμ)

private theorem integrable_shiftedPositivePartEnergyRate_forwardSteklov_on_Icc
     {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (a b : ℝ) :
    Integrable (shiftedPositivePartEnergyRate hΩ hΩbounded M N
      ((reverseTimeForwardSteklov T h u))
      ((reverseTimeForwardSteklov T h g)))
      (volume.restrict (Icc a b)) := by
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  exact (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
    (continuous_const.mul
      (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp))
    |>.integrableOn_Icc)

/-- Forward Steklov regularization preserves the tested affine-threshold
shifted-positive-part energy rate in the zero-width limit. -/
theorem tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    Tendsto (fun h  => ∫ t in Icc a b,
      shiftedPositivePartEnergyRate hΩ hΩbounded M N
        ((reverseTimeForwardSteklov T h u))
        ((reverseTimeForwardSteklov T h g)) t * eta t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => u t) (fun t => g t) t * eta t)) := by

  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := inferInstance
  letI : ContinuousENorm (H10HilbertGraphDual hΩ) := inferInstance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := inferInstance
  letI : CompleteSpace (H10HilbertGraphDual hΩ) := inferInstance
  have hT : 0 < T := lt_trans ha (lt_trans hab hb)

  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T := by
    change volume.restrict (Icc a b) ≤ volume.restrict (Ioo (0 : ℝ) T)
    exact Measure.restrict_mono' (ae_of_all _ fun t ht => (show Icc a b ⊆ Ioo (0 ) T by
        intro t ht
        exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩) ht) le_rfl
  rw [tendsto_iff_seq_tendsto]
  intro hs hhs
  let uh : ℕ → ReverseTimeL2V hΩ T := fun n =>
    reverseTimeForwardSteklovL2 T (hs n) u
  let gh : ℕ → ReverseTimeL2VStar hΩ T := fun n =>
    reverseTimeForwardSteklovL2 T (hs n) g
  let up  := reverseTimeShiftedPositivePart hΩ T M N u
  let uhp  := fun n =>
    reverseTimeShiftedPositivePart hΩ T M N (uh n)


  have huhp : Tendsto uhp atTop (𝓝 up) :=
    (continuous_reverseTimeShiftedPositivePart hΩ T M N).continuousAt.tendsto.comp ((tendsto_reverseTimeForwardSteklovL2 T hT u).comp hhs)
  let Q := (spatialMassCLM hΩbounded).comp (valueCLM hΩ)
  have hpair := tendsto_integral_abs_dualPairing_of_tendsto
    hΩ up g uhp gh huhp ((tendsto_reverseTimeForwardSteklovL2 T hT g).comp hhs) hμ
  have hmass := tendsto_integral_abs_spatialMass_value_of_tendsto
    hΩ hΩbounded up uhp huhp hμ
  have herrClass : Tendsto (fun n => ∫ t in Icc a b,
      |(gh n t) (uhp n t) - (N : ℝ) *
          Q (uhp n t) -
        ((g t) (up t) - (N : ℝ) *
          Q (up t))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n =>
      (∫ t in Icc a b, |(gh n t) (uhp n t) - (g t) (up t)|) +
      (N : ℝ) * (∫ t in Icc a b,
        |Q (uhp n t) - Q (up t)|))
    · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
    · filter_upwards with n
      have huLocal := (Lp.memLp up).mono_measure hμ
      have huhLocal := (Lp.memLp (uhp n)).mono_measure hμ



      have hp1 := shifted_integrable_dualPairing hΩ (uhp n) (gh n)
        huhLocal ((Lp.memLp (gh n)).mono_measure hμ)
      have hm0 := huLocal.continuousLinearMap_comp
        Q
      have hm1 := huhLocal.continuousLinearMap_comp
        Q
      exact integral_abs_sub_mul_sub_le
        (fun t => (gh n t) (uhp n t)) (fun t => (g t) (up t))
        (fun t => Q (uhp n t)) (fun t => Q (up t)) (N : ℝ) N.coe_nonneg
        hp1 (shifted_integrable_dualPairing hΩ up g huLocal ((Lp.memLp g).mono_measure hμ)) (hm1.integrable (by norm_num)) (hm0.integrable (by norm_num))
    ·
      simpa only [zero_add] using hpair.add (by
          simpa only [mul_zero] using tendsto_const_nhds.mul hmass)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < hs n :=
    hhs (self_mem_nhdsWithin )

  have hraw := integrable_shiftedPositivePartEnergyRate_L2_on_Icc
    hΩ hΩbounded M N T u g hμ

  exact tendsto_integral_mul_of_tendsto_integral_abs (by
      filter_upwards [hpos] with n hn
      exact integrable_shiftedPositivePartEnergyRate_forwardSteklov_on_Icc
        hΩ hΩbounded M N T hn u g a b) hraw
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le (by
        apply herrClass.congr'
        filter_upwards [hpos] with n hn
        apply integral_congr_ae
        filter_upwards
            [(ae_shiftedPositivePartEnergyRate_forwardSteklovL2 hΩ hΩbounded
                M N T hn u g).filter_mono (ae_mono hμ),
              (ae_shiftedPositivePartEnergyRate_L2 hΩ hΩbounded M N T u g).filter_mono
                (ae_mono hμ)] with t hforwardRate hlimitRate
        exact congrArg₂ (fun x y : ℝ => |x - y|) hforwardRate.symm hlimitRate.symm)

end HypoellipticAleksandrov.Parabolic.Dirichlet
