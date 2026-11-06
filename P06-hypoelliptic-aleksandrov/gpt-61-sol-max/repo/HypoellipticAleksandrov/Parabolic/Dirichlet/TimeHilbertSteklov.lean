module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.ContinuousMap.Compact
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Bound
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing

open private HypoellipticAleksandrov.Parabolic.Dirichlet.hasDerivAt_of_pivoted_curve from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integral_mul_norm_le_sqrt_mul_sqrt from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
open private HypoellipticAleksandrov.Parabolic.Dirichlet.pivot_normSq_sub_eq_dualSub_apply_add from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_clm_apply from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.normSq_sub_eq_inner_add_sub_inner from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing


/-!
# Hilbert-valued reverse-time Steklov curves

This module packages the literal one-sided Steklov averages as continuous
Hilbert-valued curves on closed time collars.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The deterministic positive Steklov step used for the Hilbert representative. -/
def reverseTimeSteklovStep (T : ℝ) (n : ℕ) : ℝ :=
  T / ((n + 2 : ℕ) : ℝ)

section
variable (T : ℝ) (hT : 0 < T)

include hT
/-- The deterministic Steklov step is positive for positive terminal time. -/
theorem reverseTimeSteklovStep_pos  (n : ℕ) :
    0 < reverseTimeSteklovStep T n := by
  unfold reverseTimeSteklovStep
  positivity

/-- The deterministic Steklov steps tend to zero from the right. -/
theorem tendsto_reverseTimeSteklovStep
     :
    Filter.Tendsto (reverseTimeSteklovStep T) Filter.atTop
      (𝓝[>] (0 )) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [reverseTimeSteklovStep, Function.comp_def] using!
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 2)
  · simp_all [reverseTimeSteklovStep_pos]
end


variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T)

/-- Forward Hilbert-valued Steklov curves on a left closed time collar. -/
def reverseTimeForwardSteklovHilbertOnIcc
     (b : ℝ) :
    ℕ → C(↥(Set.Icc 0 b), PDE.ScalarLp Ω (2 )) :=
  fun n =>
    ⟨fun t => valueCLM hΩ
        (reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u t),
      ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) u)).continuousOn.restrict⟩

/-- Backward Hilbert-valued Steklov curves on a right closed time collar. -/
def reverseTimeBackwardSteklovHilbertOnIcc
     (a : ℝ) :
    ℕ → C(↥(Set.Icc a T), PDE.ScalarLp Ω (2 )) :=
  fun n =>
    ⟨fun t => valueCLM hΩ
        (reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u t),
      ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) u)).continuousOn.restrict⟩













variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private theorem mixed_energy_identity_of_pivot

    (x : ℝ → H10HilbertGraph hΩ) (y : ℝ → H10HilbertGraphDual hΩ)
    (U : ℝ → H10HilbertGraph hΩ →L[ℝ] ℝ)
    {a b : ℝ} (hab : a ≤ b) (hx : Continuous x) (hy : Continuous y)
    (hpivot : ∀ r s : ℝ,
      ‖valueCLM hΩ (x r)‖ ^ 2 - ‖valueCLM hΩ (x s)‖ ^ 2 =
        (U r - U s) (x r + x s))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt U (y t) t) :
    ‖valueCLM hΩ (x b)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 =
      2 * ∫ t in Icc a b, y t (x t) := by
  let E  := fun t => ‖valueCLM hΩ (x t)‖ ^ 2



  have hFTC : (∫ t in a..b, 2 * y t (x t)) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (((valueCLM hΩ).continuous.comp hx).norm.pow 2).continuousOn (by
        intro t ht
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.hasDerivAt_of_pivoted_curve hx hpivot (hderiv t ht))
      ((continuous_const.mul (hy.clm_apply hx)).intervalIntegrable a b)
  calc
    ‖valueCLM hΩ (x b)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 = E b - E a := rfl
    _ = ∫ t in a..b, 2 * y t (x t) := hFTC.symm
    _ = 2 * ∫ t in Ioc a b, y t (x t) := by
      rw [intervalIntegral.integral_of_le hab, integral_const_mul]
    _ = 2 * ∫ t in Icc a b, y t (x t) := by
      rw [integral_Icc_eq_integral_Ioc]

section
variable (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) {h k t : ℝ} (hh : 0 < h) (hk : 0 < k)

include hderiv hh hk
private theorem hasDerivAt_forward_mixed_gelfand

    (hth : t + h < T) (htk : t + k < T) (ht0 : 0 < t) :
    HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T k u s)))
      (reverseTimeForwardSteklov T h g t - reverseTimeForwardSteklov T k g t) t := (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv
      hh ht0 hth).sub
    (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv
        hk ht0 htk)

private theorem hasDerivAt_backward_mixed_gelfand

    (hth : 0 < t - h) (htk : 0 < t - k) (htT : t < T) :
    HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T k u s)))
      (reverseTimeBackwardSteklov T h g t - reverseTimeBackwardSteklov T k g t) t := (hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv
      hh hth htT).sub
    (hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv
        hk htk htT)
end


variable (T h k : ℝ) (u : ReverseTimeL2V hΩ T) (r s : ℝ)

private theorem forward_mixed_pivot

     :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u r -
        reverseTimeForwardSteklov T k u r)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeForwardSteklov T h u s -
        reverseTimeForwardSteklov T k u s)‖ ^ 2 =
      ((scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T h u r)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T k u r))) -
        (scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T k u s))))
        ((reverseTimeForwardSteklov T h u r - reverseTimeForwardSteklov T k u r) +
          (reverseTimeForwardSteklov T h u s - reverseTimeForwardSteklov T k u s)) := by
  simpa only [ContinuousLinearMap.map_sub] using
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.pivot_normSq_sub_eq_dualSub_apply_add hΩ
      (reverseTimeForwardSteklov T h u r - reverseTimeForwardSteklov T k u r)
      (reverseTimeForwardSteklov T h u s - reverseTimeForwardSteklov T k u s)

private theorem backward_mixed_pivot

     :
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u r -
        reverseTimeBackwardSteklov T k u r)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u s -
        reverseTimeBackwardSteklov T k u s)‖ ^ 2 =
      ((scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T h u r)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T k u r))) -
        (scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T k u s))))
        ((reverseTimeBackwardSteklov T h u r - reverseTimeBackwardSteklov T k u r) +
          (reverseTimeBackwardSteklov T h u s - reverseTimeBackwardSteklov T k u s)) := by
  simpa only [ContinuousLinearMap.map_sub] using
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.pivot_normSq_sub_eq_dualSub_apply_add hΩ
      (reverseTimeBackwardSteklov T h u r - reverseTimeBackwardSteklov T k u r)
      (reverseTimeBackwardSteklov T h u s - reverseTimeBackwardSteklov T k u s)







variable {E : Type*}

private theorem exists_sqNorm_le_average_on_Icc
     [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Icc a b, ‖f r‖ ^ 2 ≤
      ⨍ t, ‖f t‖ ^ 2 ∂(volume.restrict (Icc a b)) := by
  let μ  := volume.restrict (Icc a b)
  letI : IsFiniteMeasure μ := (id inferInstance)
  have hvol : 0 < μ.real univ := by
    dsimp only [μ]
    rw [MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Icc_of_le hab.le]
    linarith



  obtain ⟨r, hr, hrq⟩ := MeasureTheory.exists_notMem_null_le_average (show μ ≠ 0 by
      intro hzero
      have hzero' : μ.real univ = 0 := by simp [hzero]
      linarith) (show Integrable (fun t => ‖f t‖ ^ 2) μ by
      exact (hf.norm.pow 2).integrableOn_Icc) (show μ (Icc a b)ᶜ = 0 by
      dsimp only [μ]
      rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Icc)]
      simp)
  refine ⟨r, ?_, hrq⟩
  simpa only [mem_compl_iff, not_not] using hr

private theorem memLp_two_on_full_Icc
     [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    MemLp (f : ℝ → E) (2 ) (volume.restrict (Icc 0 T)) := by
  simpa only [reverseTimeVolume, reverseTimeOpenInterval,
    restrict_Ioo_eq_restrict_Icc] using Lp.memLp f

section
variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) {h k a b : ℝ} (hh : 0 < h) (hk : 0 < k)

include hderiv hh hk
private theorem forward_mixed_energy_identity
     (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbh : b + h ≤ T) (hbk : b + k ≤ T) :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b -
        reverseTimeForwardSteklov T k u b)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a -
        reverseTimeForwardSteklov T k u a)‖ ^ 2 =
      2 * ∫ t in Icc a b,
        (reverseTimeForwardSteklov T h g t - reverseTimeForwardSteklov T k g t)
          (reverseTimeForwardSteklov T h u t - reverseTimeForwardSteklov T k u t) := by
  let x  := fun t =>
    reverseTimeForwardSteklov T h u t - reverseTimeForwardSteklov T k u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t =>
    reverseTimeForwardSteklov T h g t - reverseTimeForwardSteklov T k g t
  let U : ℝ → H10HilbertGraph hΩ →L[ℝ] ℝ := fun t =>
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeForwardSteklov T h u t)) -
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeForwardSteklov T k u t))
  have hx : Continuous x :=
    (continuous_reverseTimeForwardSteklov T h hh u).sub
      (continuous_reverseTimeForwardSteklov T k hk u)
  have hy : Continuous y :=
    ((continuous_reverseTimeForwardSteklov T h hh g).sub
      (continuous_reverseTimeForwardSteklov T k hk g))
  apply mixed_energy_identity_of_pivot hΩ x y U hab hx hy
    (forward_mixed_pivot hΩ T h k u)
  intro t ht

  exact (hasDerivAt_forward_mixed_gelfand hΩ T hT u g hderiv hh hk
        (by linarith [hbh, ht.2]) (by linarith [hbk, ht.2])
        (by linarith [ha0, ht.1]))

private theorem backward_mixed_energy_identity
     (hah : 0 ≤ a - h)
    (hak : 0 ≤ a - k) (hab : a ≤ b) (hbT : b ≤ T) :
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u b -
        reverseTimeBackwardSteklov T k u b)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u a -
        reverseTimeBackwardSteklov T k u a)‖ ^ 2 =
      2 * ∫ t in Icc a b,
        (reverseTimeBackwardSteklov T h g t - reverseTimeBackwardSteklov T k g t)
          (reverseTimeBackwardSteklov T h u t - reverseTimeBackwardSteklov T k u t) := by
  let x  := fun t =>
    reverseTimeBackwardSteklov T h u t - reverseTimeBackwardSteklov T k u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t =>
    reverseTimeBackwardSteklov T h g t - reverseTimeBackwardSteklov T k g t
  let U : ℝ → H10HilbertGraph hΩ →L[ℝ] ℝ := fun t =>
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeBackwardSteklov T h u t)) -
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeBackwardSteklov T k u t))
  have hx : Continuous x :=
    (continuous_reverseTimeBackwardSteklov T h hh u).sub
      (continuous_reverseTimeBackwardSteklov T k hk u)
  have hy : Continuous y :=
    ((continuous_reverseTimeBackwardSteklov T h hh g).sub
      (continuous_reverseTimeBackwardSteklov T k hk g))
  apply mixed_energy_identity_of_pivot hΩ x y U hab hx hy
    (backward_mixed_pivot hΩ T h k u)
  intro t ht

  exact (hasDerivAt_backward_mixed_gelfand hΩ T hT u g hderiv hh hk
        (by linarith [hah, ht.1]) (by linarith [hak, ht.1])
        (by linarith [hbT, ht.2]))
end


private theorem sqNorm_sub_le_two_mul_sqNorm_sub_add
    {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
  let sharedTerm_a98c898a9d := (‖x - z‖ + ‖y - z‖)

  calc
    ‖x - y‖ ^ 2 ≤ (sharedTerm_a98c898a9d) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by
          calc
            ‖x - y‖ = ‖(x - z) + (z - y)‖ := by
              congr 1
              abel
            _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
            _ = sharedTerm_a98c898a9d := by rw [norm_sub_rev z y]) 2
    _ ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x - z‖ - ‖y - z‖)]

private theorem add_three_le_add_three
    {a b c d e f : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) :
    a + c + e ≤ b + d + f := by
  linarith

private theorem eventually_pairwise_sqNorm_integral_lt
    {E : Type*} [NormedAddCommGroup E]
    (T : ℝ) (F : ℕ → ℝ → E) (f : ℝ → E)
    (hF : ∀ n, MemLp (F n) (2 ) (volume.restrict (Icc 0 T)))
    (hf : MemLp f (2 ) (volume.restrict (Icc 0 T)))
    (hlim : Filter.Tendsto
      (fun n => ∫ t in Icc 0 T, ‖F n t - f t‖ ^ 2) Filter.atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ t in Icc 0 T, ‖F m t - F n t‖ ^ 2 < δ := by
  have htail : ∀ᶠ n : ℕ in Filter.atTop,
      ∫ t in Icc 0 T, ‖F n t - f t‖ ^ 2 < δ / 4 :=
    hlim.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 htail)
  refine ⟨N, fun m hm n hn => ?_⟩
  let μ  := volume.restrict (Icc 0 T)
  have hmf  := (hF m).sub hf
  have hnf  := (hF n).sub hf
  have hmn  := (hF m).sub (hF n)
  have hmfInt : Integrable (fun t => ‖F m t - f t‖ ^ 2) μ := by
    simpa only [Pi.sub_apply] using hmf.integrable_norm_pow (by norm_num)
  have hnfInt : Integrable (fun t => ‖F n t - f t‖ ^ 2) μ := by
    exact hnf.integrable_norm_pow (by norm_num)


  have hm := hN m hm
  have hn := hN n hn
  have hmf2  :=
    hmfInt.const_mul 2
  have hnf2  :=
    hnfInt.const_mul 2
  change (∫ t, ‖F m t - F n t‖ ^ 2 ∂μ) < δ
  calc
    (∫ t, ‖F m t - F n t‖ ^ 2 ∂μ) ≤
        ∫ t, (2 : ℝ) * ‖F m t - f t‖ ^ 2 + 2 * ‖F n t - f t‖ ^ 2 ∂μ := (by
            apply integral_mono (by
                exact hmn.integrable_norm_pow (by norm_num))
              ((hmfInt.const_mul 2).add (hnfInt.const_mul 2))
            intro t
            exact sqNorm_sub_le_two_mul_sqNorm_sub_add (F m t) (F n t) (f t))
    _ = 2 * (∫ t, ‖F m t - f t‖ ^ 2 ∂μ) +
        2 * (∫ t, ‖F n t - f t‖ ^ 2 ∂μ) := by
      rw [integral_add hmf2 hnf2, integral_const_mul, integral_const_mul]
    _ < δ := by linarith

private theorem sqNorm_valueCLM_sub_le_opNorm_sq_mul
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ (x - y)‖ ^ 2 ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 := by

  calc
    ‖valueCLM hΩ (x - y)‖ ^ 2 ≤
        (‖valueCLM hΩ‖ * ‖x - y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((valueCLM hΩ).le_opNorm (x - y)) 2
    _ = ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 := by rw [mul_pow]

variable {E : Type*}

private theorem tendsto_forward_step_sqNorm_error
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun n => ∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) f t - f t‖ ^ 2)
      Filter.atTop (𝓝 0) := (tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f).comp
    (tendsto_reverseTimeSteklovStep T hT)

private theorem tendsto_backward_step_sqNorm_error
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun n => ∫ t in Icc 0 T,
        ‖reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) f t - f t‖ ^ 2)
      Filter.atTop (𝓝 0) := (tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f).comp
    (tendsto_reverseTimeSteklovStep T hT)

private theorem eventually_forward_pairwise_sqNorm_integral_lt
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T (reverseTimeSteklovStep T m) f t -
          reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) f t‖ ^ 2 < δ := by
  apply eventually_pairwise_sqNorm_integral_lt T
    (fun n => reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) f) f
  · intro n
    exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous _
      (continuous_reverseTimeForwardSteklov T _
        (reverseTimeSteklovStep_pos T hT n) f) 0 T
  · exact memLp_two_on_full_Icc T f
  · exact tendsto_forward_step_sqNorm_error T hT f
  · exact hδ

private theorem eventually_backward_pairwise_sqNorm_integral_lt
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ t in Icc 0 T,
        ‖reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m) f t -
          reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) f t‖ ^ 2 < δ := by
  apply eventually_pairwise_sqNorm_integral_lt T
    (fun n => reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) f) f
  · intro n
    exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous _
      (continuous_reverseTimeBackwardSteklov T _
        (reverseTimeSteklovStep_pos T hT n) f) 0 T
  · exact memLp_two_on_full_Icc T f
  · exact tendsto_backward_step_sqNorm_error T hT f
  · exact hδ

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ)

variable (x : ℝ → H10HilbertGraph hΩ)

section
variable (y : ℝ → H10HilbertGraphDual hΩ) (hx : Continuous x) (hy : Continuous y)

include hx hy
private theorem abs_setIntegral_pairing_le_sqrt_full


    {a b : ℝ} (hsub : Icc a b ⊆ Icc 0 T) :
    |∫ t in Icc a b, y t (x t)| ≤
      √(∫ t in Icc 0 T, ‖y t‖ ^ 2) * √(∫ t in Icc 0 T, ‖x t‖ ^ 2) := by
  let μ  := volume.restrict (Icc a b)
  let ν  := volume.restrict (Icc 0 T)
  have hxμ : MemLp x (2 ) μ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous x hx a b
  have hyμ : MemLp y (2 ) μ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous y hy a b
  have hxν  := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous x hx 0 T






  calc
    |∫ t in Icc a b, y t (x t)| = |∫ t, y t (x t) ∂μ| := rfl
    _ ≤ ∫ t, ‖y t‖ * ‖x t‖ ∂μ := (by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (show Integrable (fun t => ‖y t‖ * ‖x t‖) μ from hyμ.norm.integrable_mul hxμ.norm)
        filter_upwards with t
        simpa only [Real.norm_eq_abs] using (y t).le_opNorm (x t))
    _ ≤ √(∫ t, ‖y t‖ ^ 2 ∂μ) * √(∫ t, ‖x t‖ ^ 2 ∂μ) := (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_mul_norm_le_sqrt_mul_sqrt y x hyμ hxμ)
    _ ≤ √(∫ t, ‖y t‖ ^ 2 ∂ν) * √(∫ t, ‖x t‖ ^ 2 ∂ν) := mul_le_mul (Real.sqrt_le_sqrt (by
        apply setIntegral_mono_set ((show MemLp y (2 ) ν from _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous y hy 0 T).integrable_norm_pow (by norm_num))
          (Eventually.of_forall fun _ => sq_nonneg _)
        exact hsub.eventuallyLE)) (Real.sqrt_le_sqrt (by
        apply setIntegral_mono_set (hxν.integrable_norm_pow (by norm_num))
          (Eventually.of_forall fun _ => sq_nonneg _)
        exact hsub.eventuallyLE))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := rfl

private theorem sqNorm_at_le_anchor_add_pairwise_integrals


    (K : Set ℝ) (hK : K ⊆ Icc 0 T)
    (henergy : ∀ {a b : ℝ}, a ≤ b → a ∈ K → b ∈ K →
      ‖valueCLM hΩ (x b)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 =
        2 * ∫ s in Icc a b, y s (x s))
    {r t : ℝ} (hr : r ∈ K) (ht : t ∈ K) :
    ‖valueCLM hΩ (x t)‖ ^ 2 ≤ ‖valueCLM hΩ (x r)‖ ^ 2 +
      (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := by
  let sharedTerm_e9deddadb9 := (∫ s in Icc t r, y s (x s))
  let sharedTerm_05f629a620 := (∫ s in Icc r t, y s (x s))
  let Y : ℝ := ∫ s in Icc 0 T, ‖y s‖ ^ 2
  let X : ℝ := ∫ s in Icc 0 T, ‖x s‖ ^ 2
  have hY0 : 0 ≤ Y := integral_nonneg fun _ => sq_nonneg _
  have hX0 : 0 ≤ X := integral_nonneg fun _ => sq_nonneg _
  have hcross : 2 * (√Y * √X) ≤ Y + X := by
    have h := two_mul_le_add_sq (√Y) (√X)
    simpa only [mul_assoc, Real.sq_sqrt hY0, Real.sq_sqrt hX0] using h
  rcases le_total r t with hrt | htr
  · have hsubset : Icc r t ⊆ Icc 0 T := by
      intro s hs
      exact ⟨(hK hr).1.trans hs.1, hs.2.trans (hK ht).2⟩


    have hdiff : ‖valueCLM hΩ (x t)‖ ^ 2 - ‖valueCLM hΩ (x r)‖ ^ 2 ≤ Y + X := by
      rw [(henergy hrt hr ht)]
      calc
        2 * sharedTerm_05f629a620 ≤ 2 * |sharedTerm_05f629a620| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two
        _ ≤ 2 * (√Y * √X) := mul_le_mul_of_nonneg_left (abs_setIntegral_pairing_le_sqrt_full hΩ T x y hx hy hsubset) zero_le_two
        _ ≤ Y + X := hcross
    linarith
  · have hsubset : Icc t r ⊆ Icc 0 T := by
      intro s hs
      exact ⟨(hK ht).1.trans hs.1, hs.2.trans (hK hr).2⟩



    have hneg  :=
      neg_le_of_abs_le (show |‖valueCLM hΩ (x r)‖ ^ 2 - ‖valueCLM hΩ (x t)‖ ^ 2| ≤ Y + X by
          rw [(henergy htr ht hr)]
          calc
            |2 * sharedTerm_e9deddadb9| = 2 * |sharedTerm_e9deddadb9| := by
              rw [abs_mul, abs_of_nonneg zero_le_two]
            _ ≤ 2 * (√Y * √X) := mul_le_mul_of_nonneg_left (abs_setIntegral_pairing_le_sqrt_full hΩ T x y hx hy hsubset) zero_le_two
            _ ≤ Y + X := hcross)
    linarith
end


private theorem exists_anchor_sqNorm_valueCLM_le

     (hx : Continuous x)
    {a b v : ℝ} (hab : a < b) (hvol : volume.real (Icc a b) = v)
    (hsub : Icc a b ⊆ Icc 0 T) :
    ∃ r ∈ Icc a b,
      ‖valueCLM hΩ (x r)‖ ^ 2 ≤
        v⁻¹ * ‖valueCLM hΩ‖ ^ 2 * ∫ t in Icc 0 T, ‖x t‖ ^ 2 := by
  let sharedTerm_e3f503b061 := (∫ t in Icc a b, ‖valueCLM hΩ (x t)‖ ^ 2)
  let sharedTerm_14cf017ff0 := ((volume.restrict (Icc a b)))
  obtain ⟨r, hr, hravg⟩ := exists_sqNorm_le_average_on_Icc
    (fun t => valueCLM hΩ (x t)) ((valueCLM hΩ).continuous.comp hx) hab


  have hxK  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous x hx 0 T




  refine ⟨r, hr, ?_⟩
  calc
    ‖valueCLM hΩ (x r)‖ ^ 2 ≤
        v⁻¹ * sharedTerm_e3f503b061 := (by
            rw [MeasureTheory.average_eq,
              MeasureTheory.measureReal_restrict_apply_univ, hvol, smul_eq_mul] at hravg
            exact hravg)
    _ ≤ v⁻¹ * (∫ t in Icc a b, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2) := mul_le_mul_of_nonneg_left (by
        apply integral_mono (show Integrable (fun t => ‖valueCLM hΩ (x t)‖ ^ 2)
      sharedTerm_14cf017ff0 from (((valueCLM hΩ).continuous.comp hx).norm.pow 2).integrableOn_Icc) (show _ by
            exact ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous x hx a b).integrable_norm_pow (by norm_num)).const_mul _)
        intro t
        simpa only [sub_zero] using sqNorm_valueCLM_sub_le_opNorm_sq_mul hΩ (x t) 0) (inv_nonneg.mpr (by
        bound))
    _ ≤ v⁻¹ * (∫ t in Icc 0 T, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2) := mul_le_mul_of_nonneg_left (by
        apply setIntegral_mono_set
          ((hxK.integrable_norm_pow (by norm_num)).const_mul _)
          (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        exact hsub.eventuallyLE) (inv_nonneg.mpr (by
        bound))
    _ = v⁻¹ * ‖valueCLM hΩ‖ ^ 2 * ∫ t in Icc 0 T, ‖x t‖ ^ 2 := by
      rw [integral_const_mul]
      ring

variable (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hderiv
/-- The deterministic forward Steklov curves are Cauchy uniformly in spatial `L²` on every
left closed collar `Icc 0 b` with `0 < b < T`. -/
theorem cauchySeq_reverseTimeForwardSteklovHilbertOnIcc

    {b : ℝ} (hb0 : 0 < b) (hbT : b < T) :
    CauchySeq (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b) := by

  rw [Metric.cauchySeq_iff]
  intro ε hε
  let c : ℝ := (b / 3)⁻¹ * ‖valueCLM hΩ‖ ^ 2
  let η : ℝ := ε ^ 2 / (c + 3)
  have hc0 : 0 ≤ c := by
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _)
  have hc3 : 0 < c + 3 := by linarith
  have hη : 0 < η := by
    exact div_pos (sq_pos_of_pos hε) hc3
  obtain ⟨Nu, hNu⟩ := eventually_forward_pairwise_sqNorm_integral_lt T hT u hη
  obtain ⟨Ng, hNg⟩ := eventually_forward_pairwise_sqNorm_integral_lt T hT g hη


  obtain ⟨Nh, hNh⟩ := eventually_atTop.1 ((tendsto_reverseTimeSteklovStep T hT).eventually ((eventually_lt_nhds (sub_pos.mpr hbT)).filter_mono nhdsWithin_le_nhds))
  refine ⟨max (max Nu Ng) Nh, ?_⟩
  intro m hm n hn
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  let x  := fun s =>
    reverseTimeForwardSteklov T (reverseTimeSteklovStep T m) u s -
      reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u s
  let y : ℝ → H10HilbertGraphDual hΩ := fun s =>
    reverseTimeForwardSteklov T (reverseTimeSteklovStep T m) g s -
      reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) g s






  have hU : ∫ s in Icc 0 T, ‖x s‖ ^ 2 < η := by
    simpa only [x] using hNu m (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)) n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
  have hG : ∫ s in Icc 0 T, ‖y s‖ ^ 2 < η := by
    simpa only [y] using hNg m (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)) n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))


  have hx : Continuous x := by
    exact (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T m)
      (reverseTimeSteklovStep_pos T hT m) u).sub
      (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) u)

  have hApos : b / 3 < 2 * b / 3 := by linarith
  have hAvol : volume.real (((Icc (b / 3) (2 * b / 3)))) = b / 3 := by
    rw [Real.volume_real_Icc_of_le hApos.le]
    ring

  obtain ⟨r, hr, hrbound⟩ := exists_anchor_sqNorm_valueCLM_le hΩ T x hx hApos hAvol (by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, hbT])




  have hprop := sqNorm_at_le_anchor_add_pairwise_integrals hΩ T x y hx ((continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T m)
        (reverseTimeSteklovStep_pos T hT m) g).sub
        (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) g))
    (Icc 0 b) (by
        intro s hs
        exact ⟨hs.1, hs.2.trans hbT.le⟩) (by
        intro a q haq ha hq
        simpa only using
          forward_mixed_energy_identity hΩ T hT u g hderiv (reverseTimeSteklovStep_pos T hT m)
            (reverseTimeSteklovStep_pos T hT n) ha.1 haq (by linarith [x, y, hq.2, (hNh m (le_trans (le_max_right _ _) hm))])
            (by linarith [hq.2, (hNh n (le_trans (le_max_right _ _) hn))])) (show r ∈ Icc 0 b by
                constructor <;> linarith [hr.1, hr.2]) t.2



  simpa only [reverseTimeForwardSteklovHilbertOnIcc, ContinuousMap.coe_mk,
    ContinuousMap.coe_mk, dist_eq_norm, ContinuousLinearMap.map_sub, x] using! ((sq_lt_sq₀ (norm_nonneg _) hε.le).mp (by

        have hfinal : c * η + η + η < ε ^ 2 := by

          have hlt : c * η + η + η < (c + 3) * η := by
            calc
              c * η + η + η = (c + 2) * η := by ring
              _ < (c + 3) * η := mul_lt_mul_of_pos_right (by linarith) hη
          exact hlt.trans_eq (by
              dsimp only [η]
              field_simp [ne_of_gt hc3])
        calc
          ‖valueCLM hΩ (x (t : ℝ))‖ ^ 2 ≤
              ‖valueCLM hΩ (x r)‖ ^ 2 +
                (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := hprop
          _ ≤ c * (∫ s in Icc 0 T, ‖x s‖ ^ 2) +
                η + η := add_three_le_add_three (by
                    exact hrbound) hG.le hU.le
          _ ≤ c * η + η + η := add_three_le_add_three (mul_le_mul_of_nonneg_left hU.le hc0) le_rfl le_rfl
          _ < ε ^ 2 := hfinal))

/-- The deterministic backward Steklov curves are Cauchy uniformly in spatial `L²` on every
right closed collar `Icc a T` with `0 < a < T`. -/
theorem cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc

    {a : ℝ} (ha0 : 0 < a) (haT : a < T) :
    CauchySeq (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a) := by

  rw [Metric.cauchySeq_iff]
  intro ε hε
  let c : ℝ := ((T - a) / 3)⁻¹ * ‖valueCLM hΩ‖ ^ 2
  let η : ℝ := ε ^ 2 / (c + 3)

  have hc0 : 0 ≤ c := by
    exact mul_nonneg (inv_nonneg.mpr (show 0 < (T - a) / 3 by linarith).le) (sq_nonneg _)
  have hc3 : 0 < c + 3 := by linarith
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) hc3
  obtain ⟨Nu, hNu⟩ := eventually_backward_pairwise_sqNorm_integral_lt T hT u hη
  obtain ⟨Ng, hNg⟩ := eventually_backward_pairwise_sqNorm_integral_lt T hT g hη


  obtain ⟨Nh, hNh⟩ := eventually_atTop.1 ((tendsto_reverseTimeSteklovStep T hT).eventually ((eventually_lt_nhds ha0).filter_mono nhdsWithin_le_nhds))
  refine ⟨max (max Nu Ng) Nh, ?_⟩
  intro m hm n hn
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  let x  := fun s =>
    reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m) u s -
      reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u s
  let y : ℝ → H10HilbertGraphDual hΩ := fun s =>
    reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m) g s -
      reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) g s






  have hU : ∫ s in Icc 0 T, ‖x s‖ ^ 2 < η := by
    simpa only [x] using hNu m (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)) n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))



  have hx : Continuous x := by
    exact (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m)
      (reverseTimeSteklovStep_pos T hT m) u).sub
      (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) u)

  have hApos : (2 * a + T) / 3 < (a + 2 * T) / 3 := by linarith


  obtain ⟨r, hr, hrbound⟩ := exists_anchor_sqNorm_valueCLM_le hΩ T x hx hApos (show volume.real (((Icc ((2 * a + T) / 3) ((a + 2 * T) / 3)))) = (T - a) / 3 by
      rw [Real.volume_real_Icc_of_le hApos.le]
      ring) (by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, ha0, haT])




  have hprop := sqNorm_at_le_anchor_add_pairwise_integrals hΩ T x y hx ((continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m)
        (reverseTimeSteklovStep_pos T hT m) g).sub
        (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) g))
    (Icc a T) (by
        intro s hs
        exact ⟨ha0.le.trans hs.1, hs.2⟩) (by
        intro p q hpq hp hq
        simpa only using
          backward_mixed_energy_identity hΩ T hT u g hderiv (reverseTimeSteklovStep_pos T hT m)
            (reverseTimeSteklovStep_pos T hT n) (by linarith [x, y, hp.1, (hNh m (le_trans (le_max_right _ _) hm))])
            (by linarith [hp.1, (hNh n (le_trans (le_max_right _ _) hn))]) hpq hq.2) (show r ∈ Icc a T by constructor <;> linarith [hr.1, hr.2, haT]) t.2



  simpa only [reverseTimeBackwardSteklovHilbertOnIcc, ContinuousMap.coe_mk,
    ContinuousMap.coe_mk, dist_eq_norm, ContinuousLinearMap.map_sub, x] using! ((sq_lt_sq₀ (norm_nonneg _) hε.le).mp (by

        have hfinal : c * η + η + η < ε ^ 2 := by


          exact (show c * η + η + η < (c + 3) * η by
              calc
                c * η + η + η = (c + 2) * η := by ring
                _ < (c + 3) * η := mul_lt_mul_of_pos_right (by linarith) hη).trans_eq (by
              dsimp only [η]
              field_simp [ne_of_gt hc3])
        calc
          ‖valueCLM hΩ (x (t : ℝ))‖ ^ 2 ≤
              ‖valueCLM hΩ (x r)‖ ^ 2 +
                (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := hprop
          _ ≤ c * (∫ s in Icc 0 T, ‖x s‖ ^ 2) +
                η + η := add_three_le_add_three (hrbound) (show ∫ s in Icc 0 T, ‖y s‖ ^ 2 < η by
                        simpa only [y] using hNg m (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)) n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))).le hU.le
          _ ≤ c * η + η + η := add_three_le_add_three (mul_le_mul_of_nonneg_left hU.le hc0) le_rfl le_rfl
          _ < ε ^ 2 := hfinal))

end HypoellipticAleksandrov.Parabolic.Dirichlet
