module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.ContinuousMap.Compact
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy

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
noncomputable def reverseTimeSteklovStep (T : ℝ) (n : ℕ) : ℝ :=
  T / ((n + 2 : ℕ) : ℝ)

section
variable (T : ℝ) (hT : 0 < T)
include hT

/-- The deterministic Steklov step is positive for positive terminal time. -/
theorem reverseTimeSteklovStep_pos (n : ℕ) :
    0 < reverseTimeSteklovStep T n := by
  unfold reverseTimeSteklovStep
  positivity

/-- The deterministic Steklov steps tend to zero from the right. -/
theorem tendsto_reverseTimeSteklovStep :
    Filter.Tendsto (reverseTimeSteklovStep T) Filter.atTop
      (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [reverseTimeSteklovStep, Function.comp_def] using!
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 2)
  · filter_upwards with n
    exact reverseTimeSteklovStep_pos T hT n

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
  (u : ReverseTimeL2V hΩ T)
include hΩ T hT u

/-- Forward Hilbert-valued Steklov curves on a left closed time collar. -/
noncomputable def reverseTimeForwardSteklovHilbertOnIcc (b : ℝ) :
    ℕ → C(↥(Set.Icc 0 b), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  fun n =>
    ⟨fun t => valueCLM hΩ
        (reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u t),
      ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) u)).continuousOn.restrict⟩

/-- Backward Hilbert-valued Steklov curves on a right closed time collar. -/
noncomputable def reverseTimeBackwardSteklovHilbertOnIcc (a : ℝ) :
    ℕ → C(↥(Set.Icc a T), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  fun n =>
    ⟨fun t => valueCLM hΩ
        (reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u t),
      ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) u)).continuousOn.restrict⟩

end

section
variable {E : Type*}

private theorem exists_sqNorm_le_average_on_Icc [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Icc a b, ‖f r‖ ^ 2 ≤
      ⨍ t, ‖f t‖ ^ 2 ∂(volume.restrict (Icc a b)) := by
  have hμ : volume.restrict (Icc a b) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  simpa only [mem_compl_iff, not_not, Pi.pow_apply] using
    exists_notMem_null_le_average hμ (hf.norm.pow 2).integrableOn_Icc
      (N := (Icc a b)ᶜ) (by rw [Measure.restrict_apply measurableSet_Icc.compl]; simp)

theorem memLp_two_on_full_Icc [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    MemLp (f : ℝ → E) (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)) := by
  simpa only [reverseTimeVolume, reverseTimeOpenInterval,
    restrict_Ioo_eq_restrict_Icc] using Lp.memLp f

private theorem sqNorm_sub_le_two_mul_sqNorm_sub_add [NormedAddCommGroup E] (x y z : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
  have h : ‖x - y‖ ≤ ‖x - z‖ + ‖y - z‖ := by
    simpa only [norm_sub_rev z y] using norm_sub_le_norm_sub_add_norm_sub x z y
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2, sq_nonneg (‖x - z‖ - ‖y - z‖)]

private theorem eventually_pairwise_sqNorm_integral_lt [NormedAddCommGroup E]
    (T : ℝ) (F : ℕ → ℝ → E) (f : ℝ → E)
    (hF : ∀ n, Continuous (F n))
    (hf : MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)))
    (hlim : Tendsto (fun n => ∫ t in Icc 0 T, ‖F n t - f t‖ ^ 2) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ t in Icc 0 T, ‖F m t - F n t‖ ^ 2 < δ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (show 0 < δ / 4 by positivity)))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hInt k : IntegrableOn (fun t => ‖F k t - f t‖ ^ 2) (Icc 0 T) :=
    ((memLp_on_Icc_of_continuous _ (hF k) 0 T).sub hf).integrable_norm_pow (by norm_num)
  have h := integral_mono (((hF m).sub (hF n)).norm.pow 2).integrableOn_Icc
    (((hInt m).const_mul 2).add ((hInt n).const_mul 2))
    (fun t => sqNorm_sub_le_two_mul_sqNorm_sub_add (F m t) (F n t) (f t))
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply] at h
  rw [integral_add ((hInt m).const_mul 2) ((hInt n).const_mul 2), integral_const_mul,
    integral_const_mul] at h
  linarith [hN m hm, hN n hn]

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)

private theorem abs_energy_increment_le {T : ℝ}
    {x : ℝ → H10HilbertGraph hΩ} {y : ℝ → H10HilbertGraphDual hΩ}
    (hx : Continuous x) (hy : Continuous y)
    {a b : ℝ} (hsub : Icc a b ⊆ Icc 0 T) :
    |2 * ∫ t in Icc a b, y t (x t)| ≤
      (∫ t in Icc 0 T, ‖y t‖ ^ 2) + ∫ t in Icc 0 T, ‖x t‖ ^ 2 := by
  have hsum : Continuous (fun t => ‖y t‖ ^ 2 + ‖x t‖ ^ 2) := (hy.norm.pow 2).add (hx.norm.pow 2)
  have hsumIntegral : (∫ t in Icc 0 T, ‖y t‖ ^ 2 + ‖x t‖ ^ 2) =
      (∫ t in Icc 0 T, ‖y t‖ ^ 2) + ∫ t in Icc 0 T, ‖x t‖ ^ 2 :=
    integral_add (hy.norm.pow 2).integrableOn_Icc (hx.norm.pow 2).integrableOn_Icc
  rw [← integral_const_mul, ← Real.norm_eq_abs, ← hsumIntegral]
  refine (norm_integral_le_of_norm_le hsum.integrableOn_Icc ?_).trans
    (setIntegral_mono_set hsum.integrableOn_Icc (.of_forall fun _ => by positivity) hsub.eventuallyLE)
  exact .of_forall fun t => by
    rw [norm_mul, Real.norm_of_nonneg zero_le_two]
    refine (mul_le_mul_of_nonneg_left ((y t).le_opNorm (x t)) zero_le_two).trans ?_
    simpa only [mul_assoc] using two_mul_le_add_sq (‖y t‖) (‖x t‖)

private theorem uniform_sqNorm_le_of_energy_identity {T a b : ℝ}
    {x : ℝ → H10HilbertGraph hΩ} {y : ℝ → H10HilbertGraphDual hΩ}
    (hx : Continuous x) (hy : Continuous y)
    (hab : a < b) (hsub : Icc a b ⊆ Icc 0 T)
    (henergy : ∀ {p q : ℝ}, p ≤ q → p ∈ Icc a b → q ∈ Icc a b →
      ‖valueCLM hΩ (x q)‖ ^ 2 - ‖valueCLM hΩ (x p)‖ ^ 2 = 2 * ∫ s in Icc p q, y s (x s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖valueCLM hΩ (x t)‖ ^ 2 ≤
      ((b - a)⁻¹ * ‖valueCLM hΩ‖ ^ 2 + 1) * (∫ s in Icc 0 T, ‖x s‖ ^ 2) +
        ∫ s in Icc 0 T, ‖y s‖ ^ 2 := by
  let L := valueCLM hΩ
  obtain ⟨r, hr, hravg⟩ := exists_sqNorm_le_average_on_Icc (L ∘ x) (L.continuous.comp hx) hab
  rw [average_eq, measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le hab.le,
    smul_eq_mul] at hravg
  have hbound : (∫ s in Icc a b, ‖L (x s)‖ ^ 2) ≤
      ‖L‖ ^ 2 * (∫ s in Icc 0 T, ‖x s‖ ^ 2) := by
    rw [← integral_const_mul]
    have hi : Continuous (fun s => ‖L‖ ^ 2 * ‖x s‖ ^ 2) := continuous_const.mul (hx.norm.pow 2)
    refine (integral_mono ((L.continuous.comp hx).norm.pow 2).integrableOn_Icc
      hi.integrableOn_Icc (fun s => ?_)).trans
      (setIntegral_mono_set hi.integrableOn_Icc (.of_forall fun _ => by positivity) hsub.eventuallyLE)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm _) 2
  have hrbound := hravg.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
  have hi {p q : ℝ} (hpq : p ≤ q) (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) :
      |‖L (x q)‖ ^ 2 - ‖L (x p)‖ ^ 2| ≤
        (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := by
    rw [henergy hpq hp hq]
    exact abs_energy_increment_le hΩ hx hy (Icc_subset_Icc (hsub hp).1 (hsub hq).2)
  have htbound : ‖L (x t)‖ ^ 2 - ‖L (x r)‖ ^ 2 ≤
      (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := by
    rcases le_total r t with h | h
    · exact (le_abs_self _).trans (hi h hr ht)
    · refine (le_abs_self _).trans ?_
      rw [abs_sub_comm]
      exact hi h ht hr
  change ‖L (x t)‖ ^ 2 ≤ _
  simp only [Function.comp_apply, ← mul_assoc] at hrbound
  rw [add_mul, one_mul]
  linarith only [htbound, hrbound]

/-- L² convergence of both members of a pivoted pair, together with the derivative
identity on a collar, yields uniform Cauchy convergence in the pivot norm. -/
private theorem cauchySeq_of_pivoted_derivatives (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ T) (hab : a < b)
    (U : ℕ → ℝ → H10HilbertGraph hΩ) (G : ℕ → ℝ → H10HilbertGraphDual hΩ)
    (hU : ∀ n, Continuous (U n)) (hG : ∀ n, Continuous (G n))
    (hUlim : Tendsto (fun n => ∫ t in Icc 0 T, ‖U n t - u t‖ ^ 2) atTop (𝓝 0))
    (hGlim : Tendsto (fun n => ∫ t in Icc 0 T, ‖G n t - g t‖ ^ 2) atTop (𝓝 0))
    (hderiv : ∃ N, ∀ n ≥ N, ∀ t ∈ Ioo a b, HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (U n s))) (G n t) t) :
    CauchySeq (fun n => (⟨fun t : Icc a b => valueCLM hΩ (U n t),
      ((valueCLM hΩ).continuous.comp (hU n)).continuousOn.restrict⟩ : C(Icc a b, PDE.ScalarLp Ω 2))) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let c := (b - a)⁻¹ * ‖valueCLM hΩ‖ ^ 2 + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let η := ε ^ 2 / (c + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Nu, hu⟩ := eventually_pairwise_sqNorm_integral_lt T U u hU (memLp_two_on_full_Icc T u) hUlim hη
  obtain ⟨Ng, hg⟩ := eventually_pairwise_sqNorm_integral_lt T G g hG (memLp_two_on_full_Icc T g) hGlim hη
  obtain ⟨Nd, hd⟩ := hderiv
  refine ⟨max (max Nu Ng) Nd, fun m hm n hn => (ContinuousMap.dist_lt_iff hε).mpr fun t => ?_⟩
  simp only [max_le_iff] at hm hn
  have hbound := uniform_sqNorm_le_of_energy_identity hΩ ((hU m).sub (hU n))
    ((hG m).sub (hG n)) hab (Icc_subset_Icc ha hb) (fun hpq hp hq =>
      pivoted_curve_energy_identity hΩ hpq ((hU m).sub (hU n)) ((hG m).sub (hG n))
        (fun s hs => by
          have hs' := Ioo_subset_Ioo hp.1 hq.2 hs
          simpa only [Pi.sub_apply, ContinuousLinearMap.map_sub] using! (hd m hm.2 s hs').sub (hd n hn.2 s hs'))) t.2
  have hsq : ‖valueCLM hΩ (U m t - U n t)‖ ^ 2 < ε ^ 2 := by
    have heq : c * η + η = ε ^ 2 := by
      rw [← add_one_mul, mul_div_cancel₀ _ (by positivity : c + 1 ≠ 0)]
    exact hbound.trans_lt ((add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hu m hm.1.1 n hn.1.1).le hc) (hg m hm.1.2 n hn.1.2)).trans_eq heq)
  rw [dist_eq_norm]
  change ‖valueCLM hΩ (U m t) - valueCLM hΩ (U n t)‖ < ε
  rw [← map_sub]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq

end

private theorem eventually_step_lt (T : ℝ) (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N, ∀ n ≥ N, reverseTimeSteklovStep T n < ρ :=
  eventually_atTop.mp ((tendsto_reverseTimeSteklovStep T hT).eventually
    ((eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds))

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
  (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
  (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
include g hderiv

/-- The deterministic forward Steklov curves are Cauchy uniformly in spatial `L²` on every
left closed collar `Icc 0 b` with `0 < b < T`. -/
theorem cauchySeq_reverseTimeForwardSteklovHilbertOnIcc
    {b : ℝ} (hb0 : 0 < b) (hbT : b < T) :
    CauchySeq (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b) := by
  refine cauchySeq_of_pivoted_derivatives hΩ T u g le_rfl hbT.le hb0
    (fun n => reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u)
    (fun n => reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) g)
    (fun n => continuous_reverseTimeForwardSteklov T _ (reverseTimeSteklovStep_pos T hT n) u)
    (fun n => continuous_reverseTimeForwardSteklov T _ (reverseTimeSteklovStep_pos T hT n) g)
    ((tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
      (tendsto_reverseTimeSteklovStep T hT))
    ((tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT g).comp
      (tendsto_reverseTimeSteklovStep T hT)) ?_
  obtain ⟨N, hN⟩ := eventually_step_lt T hT (sub_pos.mpr hbT)
  refine ⟨N, fun n hn t ht => ?_⟩
  have hs := hN n hn
  exact hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv
    (reverseTimeSteklovStep_pos T hT n) ht.1 (by linarith [ht.2])

/-- The deterministic backward Steklov curves are Cauchy uniformly in spatial `L²` on every
right closed collar `Icc a T` with `0 < a < T`. -/
theorem cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc
    {a : ℝ} (ha0 : 0 < a) (haT : a < T) :
    CauchySeq (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a) := by
  refine cauchySeq_of_pivoted_derivatives hΩ T u g ha0.le le_rfl haT
    (fun n => reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u)
    (fun n => reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) g)
    (fun n => continuous_reverseTimeBackwardSteklov T _ (reverseTimeSteklovStep_pos T hT n) u)
    (fun n => continuous_reverseTimeBackwardSteklov T _ (reverseTimeSteklovStep_pos T hT n) g)
    ((tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
      (tendsto_reverseTimeSteklovStep T hT))
    ((tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT g).comp
      (tendsto_reverseTimeSteklovStep T hT)) ?_
  obtain ⟨N, hN⟩ := eventually_step_lt T hT ha0
  refine ⟨N, fun n hn t ht => ?_⟩
  have hs := hN n hn
  exact hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv
    (reverseTimeSteklovStep_pos T hT n) (by linarith [ht.1]) ht.2

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
