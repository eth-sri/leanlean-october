module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith

/-! # Dominated convergence for the weak-jet cutoff passage -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter

/-- A smooth cutoff vanishing near the zero vector and converging to one elsewhere. -/
noncomputable def originCutoff {d : ℕ} (n : ℕ) (x : PDE.Vec d) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * PDE.vecNormSq x - 1)

/-- The vector cutoff is infinitely differentiable. -/
theorem contDiff_originCutoff (d n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (originCutoff (d := d) n) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul PDE.contDiff_vecNormSq).sub contDiff_const)

/-- The vector cutoff has absolute value at most one. -/
theorem abs_originCutoff_le_one {d : ℕ} (n : ℕ) (x : PDE.Vec d) :
    |originCutoff n x| ≤ 1 := by
  unfold originCutoff
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

/-- Each cutoff vanishes on a neighborhood of the zero vector. -/
theorem originCutoff_eventually_zero (d n : ℕ) :
    originCutoff (d := d) n =ᶠ[nhds 0] (fun _ => 0) := by
  have hc : Continuous (fun x : PDE.Vec d => ((n : ℝ) + 1) * PDE.vecNormSq x) :=
    continuous_const.mul PDE.continuous_vecNormSq
  have he : ∀ᶠ x : PDE.Vec d in nhds 0, ((n : ℝ) + 1) * PDE.vecNormSq x < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by simp [PDE.vecNormSq, PDE.vecDot]))
  filter_upwards [he] with x hx
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Away from zero, the vector cutoff tends to one. -/
theorem originCutoff_tendsto {d : ℕ} (x : PDE.Vec d) (hx : x ≠ 0) :
    Tendsto (fun n => originCutoff n x) atTop (nhds 1) := by
  have hp : 0 < PDE.vecNormSq x := lt_of_le_of_ne (PDE.vecNormSq_nonneg x)
    (Ne.symm (mt PDE.vecNormSq_eq_zero hx))
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have he := (hn.atTop_mul_const hp).eventually (eventually_ge_atTop (2 : ℝ))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  exact (Real.smoothTransition.one_of_one_le (by linarith)).symm

section
variable {d : ℕ} (n : ℕ) (q : XV d) (i : Fin d)

/-- A cutoff in velocity has zero position derivative. -/
theorem dx_velocity_cutoff :
    dx (fun z : XV d => originCutoff n z.2) q i = 0 := by
  have hc : DifferentiableAt ℝ (originCutoff (d := d) n) q.2 :=
    ((contDiff_originCutoff d n).differentiable (by simp)).differentiableAt
  unfold dx
  rw [fderiv_fun_comp q hc differentiableAt_snd, fderiv_snd]
  simp

/-- A cutoff in position has zero velocity derivative. -/
theorem dv_position_cutoff :
    dv (fun z : XV d => originCutoff n z.1) q i = 0 := by
  have hc : DifferentiableAt ℝ (originCutoff (d := d) n) q.1 :=
    ((contDiff_originCutoff d n).differentiable (by simp)).differentiableAt
  unfold dv
  rw [fderiv_fun_comp q hc differentiableAt_fst, fderiv_fst]
  simp

end

section
variable {d : ℕ} (test : XV d → ℝ) (n : ℕ) (q : XV d) (ht : DifferentiableAt ℝ test q) (i : Fin d)
include ht

/-- Complementary-coordinate cutoff multiplication preserves the position derivative. -/
theorem dx_mul_velocity_cutoff :
    dx (fun z => test z * originCutoff n z.2) q i =
      dx test q i * originCutoff n q.2 := by
  have hc : DifferentiableAt ℝ (fun z : XV d => originCutoff n z.2) q :=
    (((contDiff_originCutoff d n).comp contDiff_snd).differentiable (by simp)).differentiableAt
  have hz := dx_velocity_cutoff n q i
  unfold dx at hz ⊢
  rw [fderiv_fun_mul ht hc]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hz, mul_zero, zero_add, mul_comm]

/-- Complementary-coordinate cutoff multiplication preserves the velocity derivative. -/
theorem dv_mul_position_cutoff :
    dv (fun z => test z * originCutoff n z.1) q i =
      dv test q i * originCutoff n q.1 := by
  have hc : DifferentiableAt ℝ (fun z : XV d => originCutoff n z.1) q :=
    (((contDiff_originCutoff d n).comp contDiff_fst).differentiable (by simp)).differentiableAt
  have hz := dv_position_cutoff n q i
  unfold dv at hz ⊢
  rw [fderiv_fun_mul ht hc]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hz, mul_zero, zero_add, mul_comm]

end

section
variable {d : ℕ} (test : XV d → ℝ)

/-- A C2 test has continuously differentiable velocity derivative components. -/
theorem contDiff_dv_test
    (ht : ContDiff ℝ 2 test) (k : Fin d) :
    ContDiff ℝ 1 (fun q => dv test q k) := by
  exact (ht.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

/-- Complementary-coordinate cutoffs also preserve the second velocity test derivative. -/
theorem dvv_mul_position_cutoff (n : ℕ)
    (ht : ContDiff ℝ 2 test) (q : XV d) (i k : Fin d) :
    dvv (fun z => test z * originCutoff n z.1) q i k =
      dvv test q i k * originCutoff n q.1 := by
  have he : (fun z => dv (fun y => test y * originCutoff n y.1) z k) =
      (fun z => dv test z k * originCutoff n z.1) := by
    funext z
    exact dv_mul_position_cutoff test n z (ht.differentiable (by norm_num) z) k
  unfold dvv
  rw [he]
  exact dv_mul_position_cutoff (fun z => dv test z k) n q
    ((contDiff_dv_test test ht k).differentiable (by norm_num) q) i

end

/-- Bounded scalar cutoffs tending to one preserve the integral of an integrable function. -/
private theorem integral_mul_cutoff_tendsto {d : ℕ} (f : XV d → ℝ)
    (hf : Integrable f volume) (cutoff : ℕ → XV d → ℝ)
    (hc : ∀ n, Measurable (cutoff n))
    (hb : ∀ n q, |cutoff n q| ≤ 1)
    (hlim : ∀ᵐ q ∂volume, Tendsto (fun n => cutoff n q) atTop (nhds 1)) :
    Tendsto (fun n => ∫ q, f q * cutoff n q) atTop (nhds (∫ q, f q)) := by
  apply tendsto_integral_of_dominated_convergence (fun q => ‖f q‖)
  · intro n
    exact hf.aestronglyMeasurable.mul (hc n).aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Filter.Eventually.of_forall (fun q => by
      rw [norm_mul, Real.norm_eq_abs (cutoff n q)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb n q) (norm_nonneg _))
  · filter_upwards [hlim] with q hq
    simpa only [mul_one] using tendsto_const_nhds.mul hq

/-- A linear integral identity for every cutoff passes to the uncut integrals. -/
theorem integral_eq_of_originCutoff {d : ℕ} {f g : XV d → ℝ} (hf : Integrable f volume)
    (hg : Integrable g volume) (s : ℝ) {proj : XV d → PDE.Vec d} (hp : Continuous proj)
    (hae : ∀ᵐ q ∂volume, proj q ≠ 0)
    (he : ∀ n, (∫ q, f q * originCutoff n (proj q)) = s * ∫ q, g q * originCutoff n (proj q)) :
    (∫ q, f q) = s * ∫ q, g q := by
  let cut n q := originCutoff n (proj q)
  have hc (n : ℕ) : Measurable (cut n) :=
    ((contDiff_originCutoff d n).continuous.comp hp).measurable
  have hbound (n : ℕ) (q : XV d) : |cut n q| ≤ 1 := abs_originCutoff_le_one n _
  have hlim : ∀ᵐ q ∂volume, Tendsto (fun n => cut n q) atTop (nhds 1) :=
    hae.mono (fun q hq => originCutoff_tendsto (proj q) hq)
  exact tendsto_nhds_unique_of_eventuallyEq
    (integral_mul_cutoff_tendsto f hf cut hc hbound hlim)
    (tendsto_const_nhds.mul (integral_mul_cutoff_tendsto g hg cut hc hbound hlim))
    (Eventually.of_forall he)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
