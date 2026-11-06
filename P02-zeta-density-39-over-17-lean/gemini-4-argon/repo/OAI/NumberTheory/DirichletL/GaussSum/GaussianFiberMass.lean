module
public import OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

theorem breveE_real_trace_div (r : ℝ) (u v : ℤ) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (r : ℂ)) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ))))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / (r : ℂ)) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ) by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_real_trace_of_O (r : ℝ) (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((ActualEisensteinCoordinates.coords z).2 : ℂ) / (r : ℂ)) := by
  rw [← ActualEisensteinCoordinates.eval_coords z]
  rw [eisEmbedding_eval]
  simp only [ShortDraftLatticeCount.coords_eval]
  exact breveE_real_trace_div r _ _

end ActualEisensteinCubic
namespace SqrtBranch

private theorem arg_ne_pi_of_re_pos {a : ℂ} (ha : 0 < a.re) : a.arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).1
  linarith

theorem cpow_half_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    a ^ (1 / 2 : ℂ) * (((r : ℂ) / a) ^ (1 / 2 : ℂ)) =
      (r : ℂ) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have harg := arg_ne_pi_of_re_pos ha
  have hlog : Complex.log ((r : ℂ) / a) = (Real.log r : ℂ) - Complex.log a := by
    rw [div_eq_mul_inv, Complex.log_ofReal_mul hr (inv_ne_zero ha0),
      Complex.log_inv a harg]
    ring
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv : (r : ℂ) / a ≠ 0 := div_ne_zero hr0 ha0
  rw [Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hdiv,
    Complex.cpow_def_of_ne_zero hr0, hlog, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_log hr.le]
  ring

theorem prefactor_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (((r : ℂ) / a) ^ (1 / 2 : ℂ))) =
      1 / ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    congrArg (fun z : ℂ => z⁻¹) (cpow_half_product ha hr)

end SqrtBranch


namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

theorem actual_fiber_gaussian_eq_shifted
    (a b x y m n : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) (η : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding
        (ActualEisensteinCoordinates.eval x y +
          ActualEisensteinCoordinates.eval a b *
            ActualEisensteinCoordinates.eval m n)‖ ^ 2 : ℂ)) =
      RankTwoEisShift.shifted
        (η * ((a*a-a*b+b*b : ℤ) : ℝ))
        (EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    ne_of_gt (coordinate_norm_pos_of_nonzero a b hc)
  have hqR : EisensteinFiberShift.q (a : ℝ) (b : ℝ) ≠ 0 := by
    dsimp [EisensteinFiberShift.q, EisensteinFiberShift.Q]
    exact_mod_cast hqZ
  have hshift := EisensteinFiberShift.exact_shift
    (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ) (m : ℝ) (n : ℝ) hqR
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      (((a*a-a*b+b*b)*(m*m-m*n+n*n) +
        ((2*a-b)*x+(2*b-a)*y)*m +
        (-(a+b)*x+(2*a-b)*y)*n +
        (x*x-x*y+y*y) : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_fiber_norm_sq a b x y m n
  rw [hnormC]
  dsimp [RankTwoEisShift.shifted, RankTwoEisShift.Q]
  congr 1
  dsimp [EisensteinFiberShift.Q, EisensteinFiberShift.q] at hshift
  have hshiftC := congrArg (fun v : ℝ => (v : ℂ)) hshift
  push_cast at hshiftC ⊢
  linear_combination -(Real.pi : ℂ) * (η : ℂ) * hshiftC

end ActualEisensteinCubic

namespace EisensteinAbelFiber


theorem shifted_gaussian_mass (x y : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z))
      (𝓝[>] (0 : ℝ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z) =
        ((2 / Real.sqrt 3 : ℝ) : ℂ) *
          (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by
    rw [RankTwoEisShift.shifted_eisenstein_gaussian_poisson ht x y]
    have hpre := EisensteinGaussianPrefactor.complex_eta_times_prefactor
      t 1 ht (by norm_num)
    simp only [mul_one] at hpre
    change (t : ℂ) *
        ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) = _
    calc
      (t : ℂ) * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) =
        (((t : ℂ) * (1 / (t : ℂ) ^ (1 / 2 : ℂ))) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ)))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by ring
      _ = _ := by rw [hpre]
  have hlim := (RankTwoLimit.dual_sum_tendsto_one_small_t x y).const_mul
    (((2 / Real.sqrt 3 : ℝ) : ℂ))
  have heq : (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((2 / Real.sqrt 3 : ℝ) : ℂ) *
        (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  simpa using hlim.congr' heq.symm

theorem scaled_shifted_gaussian_mass (q : ℝ) (hq : 0 < q)
    (x y : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted (η*q) x y z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 * q) : ℝ) : ℂ))) := by
  have hscale : Tendsto (fun η : ℝ => η*q)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun η : ℝ => η)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using hid.mul_const q
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hη hq
  have hlim := (shifted_gaussian_mass x y).comp hscale
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hlim' := hlim.const_mul (1 / (q : ℂ))
  convert hlim' using 1
  · funext η
    dsimp
    push_cast
    field_simp [hqC]
  · push_cast
    field_simp [hqC]

end EisensteinAbelFiber

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT

theorem actual_fiber_gaussian_mass (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ,
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding
            (ActualEisensteinCoordinates.eval x y +
              ActualEisensteinCoordinates.eval a b *
                ActualEisensteinCoordinates.eval z.1 z.2)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  have hq : 0 < (((a*a-a*b+b*b : ℤ) : ℝ)) := by
    exact_mod_cast coordinate_norm_pos_of_nonzero a b hc
  let u := EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  let v := EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  have h := EisensteinAbelFiber.scaled_shifted_gaussian_mass
    (((a*a-a*b+b*b : ℤ) : ℝ)) hq u v
  convert h using 1
  funext η
  congr 1
  apply tsum_congr
  intro z
  exact actual_fiber_gaussian_eq_shifted a b x y z.1 z.2 hc η

end

section

open EisensteinEmbedding ConcreteTraceCRT

def latticeCoordEquiv : O ≃ ℤ × ℤ where
  toFun := ActualEisensteinCoordinates.coords
  invFun z := ActualEisensteinCoordinates.eval z.1 z.2
  left_inv := ActualEisensteinCoordinates.eval_coords
  right_inv z := ShortDraftLatticeCount.coords_eval z.1 z.2

theorem eis_gaussian_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  have hbase := RankTwoPoisson.eis_gauss_summable hη
  have hcomp : Summable (fun z : O =>
      RankTwoPoisson.eisGauss η (latticeCoordEquiv z)) :=
    (latticeCoordEquiv.summable_iff).2 hbase
  convert hcomp using 1
  funext z
  let p := ActualEisensteinCoordinates.coords z
  have hz : z = ActualEisensteinCoordinates.eval p.1 p.2 :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval p.1 p.2)‖ : ℂ)^2) =
      ((p.1*p.1-p.1*p.2+p.2*p.2 : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq p.1 p.2
  rw [hnormC]
  change _ = RankTwoPoisson.eisGauss η
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval p.1 p.2))
  rw [ShortDraftLatticeCount.coords_eval]
  dsimp [RankTwoPoisson.eisGauss, RankTwoPoisson.eisQ]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_kernel_summable (c : O) (hc : c ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  have hbase := (eis_gaussian_summable hη).norm
  apply hbase.of_norm_bounded
  intro z
  simp only [norm_mul]
  rw [AddChar.norm_apply]
  simp

end

end ActualEisensteinCubic
namespace GaussianPhasePointwise

theorem exp_imag_diff_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

theorem exp_imag_denominator_error (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]

end GaussianPhasePointwise

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

theorem actual_O_fiber_gaussian_mass (c r : O) (hc : c ≠ 0) :
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' w : O, Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  dsimp only
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let x := (ActualEisensteinCoordinates.coords r).1
  let y := (ActualEisensteinCoordinates.coords r).2
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hreq : r = ActualEisensteinCoordinates.eval x y :=
    (ActualEisensteinCoordinates.eval_coords r).symm
  have hcE : ActualEisensteinCoordinates.eval a b ≠ 0 := by
    rw [← hceq]
    exact hc
  have hmass := actual_fiber_gaussian_mass a b x y hcE
  convert hmass using 1
  funext η
  congr 1
  let W : O → ℂ := fun w => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))
  have hsum := (latticeCoordEquiv.symm.tsum_eq W).symm
  have happly (z : ℤ × ℤ) : latticeCoordEquiv.symm z =
      ActualEisensteinCoordinates.eval z.1 z.2 := rfl
  simpa only [W, hceq, hreq, happly] using hsum

theorem original_abel_gauss_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    let K : ℂ := ((2 / (Real.sqrt 3 *
      (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc) (r ^ 2))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let K : ℂ := ((2 / (Real.sqrt 3 *
    (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let W (η : ℝ) (z : O) := Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding z‖ ^ 2 : ℂ))
  have hfiber (r : O ⧸ Ideal.span {c}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    simpa only [K, a, b, W] using
      actual_O_fiber_gaussian_mass c
        (GaussianShiftedPartition.representative c r) hc
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul (ψ (r ^ 2))
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' z : O, ψ
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))) := by
    have hpart := GaussianShiftedPartition.actual_quadratic_shifted_partition
      c hc (W η) (actual_oscillatory_kernel_summable c hc hη)
    change (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w) at hpart
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  simpa only [K, ψ, W, Finset.mul_sum, mul_comm] using hlim
