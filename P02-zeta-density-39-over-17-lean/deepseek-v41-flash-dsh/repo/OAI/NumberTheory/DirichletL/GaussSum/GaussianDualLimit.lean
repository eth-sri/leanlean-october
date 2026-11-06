module
public import OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex

namespace ActualEisensteinCubic

theorem principal_absNorm_pow (p : O) (k : ℕ) :
    Ideal.absNorm (Ideal.span {p ^ k}) =
      (Ideal.absNorm (Ideal.span {p})) ^ k := by
  rw [← Ideal.span_singleton_pow]
  exact map_pow Ideal.absNorm (Ideal.span {p}) k

end ActualEisensteinCubic
namespace OscillatoryDeterminant

open Complex

def q (a b : ℂ) : ℂ := a*a-a*b+b*b

end OscillatoryDeterminant

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

end ActualEisensteinCubic
namespace EisensteinFiberShift

def Q (x y : ℝ) : ℝ := x*x-x*y+y*y
def q (a b : ℝ) : ℝ := Q a b
noncomputable def shiftX (a b x y : ℝ) : ℝ := ((a-b)*x+b*y)/q a b
noncomputable def shiftY (a b x y : ℝ) : ℝ := (-b*x+a*y)/q a b

theorem exact_shift (a b x y m n : ℝ) (hq : q a b ≠ 0) :
    Q (x+a*m-b*n) (y+b*m+(a-b)*n) =
      q a b * Q (m+shiftX a b x y) (n+shiftY a b x y) := by
  dsimp [shiftX, shiftY, Q]
  field_simp [hq]
  dsimp [q, Q]
  ring

end EisensteinFiberShift

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

noncomputable def rowNormBall (H : ℕ) : Finset O := by
  classical
  let I : Finset ℤ := Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
  exact (I.product I).image (fun v => eval v.1 v.2)

theorem mem_rowNormBall_of_qNat_le (H : ℕ) (u : O)
    (h : qNat u ≤ H) : u ∈ rowNormBall H := by
  classical
  have hq : q (coords u) ≤ (H : ℤ) := by
    change (q (coords u)).toNat ≤ H at h
    have hnonneg := qO_nonneg u
    omega
  let a := (coords u).1
  let b := (coords u).2
  have hab : a ^ 2 - a * b + b ^ 2 ≤ (H : ℤ) := hq
  obtain ⟨ha2, hb2⟩ := coordinate_squares a b (H : ℤ)
    (by positivity) hab
  have hH : (0 : ℤ) ≤ H := by positivity
  have haL : -((H : ℤ) + 1) ≤ a := by nlinarith [sq_nonneg (H : ℤ)]
  have haU : a ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  have hbL : -((H : ℤ) + 1) ≤ b := by nlinarith [sq_nonneg (H : ℤ)]
  have hbU : b ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  unfold rowNormBall
  apply Finset.mem_image.mpr
  refine ⟨coords u, ?_, eval_coords u⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨haL, haU⟩,
     Finset.mem_Icc.mpr ⟨hbL, hbU⟩⟩

theorem mem_rowNormBall_of_absNorm_le (H : ℕ) (u : O)
    (h : Ideal.absNorm (Ideal.span {u}) ≤ H) :
    u ∈ rowNormBall H := by
  apply mem_rowNormBall_of_qNat_le
  simpa only [ActualEisensteinCubic.qNat_eq_absNorm_span] using h

end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor

theorem sqrt_product (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (3*t/4) =
      Real.sqrt 3 * t / 2 := by
  have h3 : Real.sqrt (3/4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have harg : 3*t/4 = (3/4:ℝ)*t := by ring
  rw [harg, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4), h3]
  calc
    Real.sqrt t * (Real.sqrt 3 / 2 * Real.sqrt t) =
        Real.sqrt 3 / 2 * (Real.sqrt t)^2 := by ring
    _ = Real.sqrt 3 * t / 2 := by rw [Real.sq_sqrt ht]; ring

theorem eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    η * (1 / Real.sqrt (η*q)) *
      (1 / Real.sqrt (3*(η*q)/4)) =
      2 / (Real.sqrt 3 * q) := by
  have ht : 0 < η*q := mul_pos hη hq
  have hsqrt : Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4) =
      Real.sqrt 3 * (η*q) / 2 := sqrt_product (η*q) ht.le
  have hne1 : Real.sqrt (η*q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hne2 : Real.sqrt (3*(η*q)/4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hne3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    η * (1 / Real.sqrt (η*q)) *
        (1 / Real.sqrt (3*(η*q)/4)) =
        η / (Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4)) := by ring
    _ = η / (Real.sqrt 3 * (η*q) / 2) := by rw [hsqrt]
    _ = 2 / (Real.sqrt 3 * q) := by
      field_simp

end EisensteinGaussianPrefactor

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_gaussian_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * ((m*m-m*n+n*n : ℤ) : ℂ) -
          2 * Complex.I *
            (((-b*m*m+2*a*m*n+(b-a)*n*n : ℤ) : ℂ) /
              ((a*a-a*b+b*b : ℤ) : ℂ)))) := by
  dsimp only
  rw [quadraticTraceModChar_coordinate a b m n hc]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      ((m*m-m*n+n*n : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq m n
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end ActualEisensteinCubic

namespace EisensteinGaussianPrefactor

theorem complex_eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    (η : ℂ) *
      (1 / ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ)) *
      (1 / (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ))) =
      ((2 / (Real.sqrt 3 * q) : ℝ) : ℂ) := by
  have ht : 0 ≤ η*q := (mul_pos hη hq).le
  have hs : 0 ≤ 3*(η*q)/4 := by positivity
  have hpow1 : ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
      (Real.sqrt (η*q) : ℂ) := by
    calc
      ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
          ((η*q : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ)) := by norm_num
      _ = (((η*q) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow ht (1/2 : ℝ)).symm
      _ = (Real.sqrt (η*q) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  have hpow2 : (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
      (Real.sqrt (3*(η*q)/4) : ℂ) := by
    calc
      (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
          (((3*(η*q)/4 : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ))) := by norm_num
      _ = (((3*(η*q)/4) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow hs (1/2 : ℝ)).symm
      _ = (Real.sqrt (3*(η*q)/4) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  rw [hpow1, hpow2]
  exact_mod_cast eta_times_prefactor η q hη hq

end EisensteinGaussianPrefactor

namespace ActualEisensteinCubic

end ActualEisensteinCubic
namespace OscillatoryDeterminant

open Complex

noncomputable def r (t a b : ℂ) : ℂ := 1 + 3 * q a b * t^2 / 16

end OscillatoryDeterminant
open Filter Real Asymptotics

namespace RankTwoLimit

section

open scoped Topology

open RankTwoPoisson RankTwoEisShift Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem eisQ_pos {z : ℤ × ℤ} (hz : z ≠ (0,0)) :
    0 < RankTwoPoisson.eisQ z := by
  by_cases hm : z.1 = 0
  · have hn : z.2 ≠ 0 := by
      intro h0
      exact hz (Prod.ext hm h0)
    have hnR : (z.2 : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hnR]
  · have hmR : (z.1 : ℝ) ≠ 0 := by exact_mod_cast hm
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hmR, sq_nonneg (z.2 : ℝ)]

private theorem eisGauss_norm (T : ℝ) (z : ℤ × ℤ) :
    ‖RankTwoPoisson.eisGauss T z‖ =
      Real.exp (-Real.pi * T * RankTwoPoisson.eisQ z) := by
  simp [RankTwoPoisson.eisGauss, Complex.norm_exp]

noncomputable def dualTerm (T : ℝ) (x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  RankTwoPoisson.eisGauss T (z.1,-z.2) * RankTwoEisShift.dualPhase z.1 z.2 x y

noncomputable def limitTerm (z : ℤ × ℤ) : ℂ :=
  if z = (0,0) then 1 else 0

private theorem dualTerm_tendsto (x y : ℝ) (z : ℤ × ℤ) :
    Tendsto (fun T : ℝ => dualTerm T x y z) atTop (𝓝 (limitTerm z)) := by
  by_cases hz : z = (0,0)
  · subst z
    simp [dualTerm, limitTerm, RankTwoPoisson.eisGauss,
      RankTwoPoisson.eisQ, RankTwoEisShift.dualPhase]
  · have hz' : (z.1,-z.2) ≠ ((0,0) : ℤ × ℤ) := by
      intro h
      apply hz
      have h1 : z.1 = 0 := by simpa using congrArg Prod.fst h
      have h2 : z.2 = 0 := by simpa using congrArg Prod.snd h
      exact Prod.ext h1 h2
    have hq := eisQ_pos hz'
    have hneg : -Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) < 0 := by
      nlinarith [mul_pos Real.pi_pos hq]
    have harg : Tendsto
        (fun T : ℝ => -Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2))
        atTop atBot := by
      convert tendsto_id.const_mul_atTop_of_neg hneg using 1
      ext T
      simp [mul_assoc, mul_comm]
    have hexp : Tendsto
        (fun T : ℝ => Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
    have hc : Tendsto (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2))
        atTop (𝓝 (0 : ℂ)) := by
      have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hexp
      have heq : (fun T : ℝ =>
          ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ)) =
          (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2)) := by
        funext T
        simp [RankTwoPoisson.eisGauss, Complex.ofReal_exp]
      change Tendsto (fun T : ℝ =>
        ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) at hh
      rw [heq] at hh
      exact hh
    simpa [dualTerm, limitTerm, hz] using
      hc.mul_const (RankTwoEisShift.dualPhase z.1 z.2 x y)

theorem dual_sum_tendsto_one (x y : ℝ) :
    Tendsto (fun T : ℝ => ∑' z : ℤ × ℤ, dualTerm T x y z)
      atTop (𝓝 (1 : ℂ)) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss 1 (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable (by norm_num))
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ z : ℤ × ℤ,
      ‖dualTerm T x y z‖ ≤ ‖RankTwoPoisson.eisGauss 1 (z.1,-z.2)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT z
    rw [dualTerm, norm_mul, RankTwoEisShift.dualPhase_norm, mul_one,
      eisGauss_norm, eisGauss_norm]
    have hq := eisQ_nonneg (z.1,-z.2)
    have hpq : 0 ≤ Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) :=
      mul_nonneg Real.pi_pos.le hq
    have hm := mul_le_mul_of_nonneg_right hT hpq
    apply Real.exp_le_exp.mpr
    nlinarith [hm]
  have h := tendsto_tsum_of_dominated_convergence hE.norm
    (dualTerm_tendsto x y) hbound
  simpa [limitTerm] using h

end

open scoped Topology
open Filter

theorem dual_sum_tendsto_one_small_t (x y : ℝ) :
    Tendsto (fun t : ℝ => ∑' z : ℤ × ℤ, dualTerm (4 / (3 * t)) x y z)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hT : Tendsto (fun t : ℝ => (4 / 3 : ℝ) * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).2
      tendsto_inv_nhdsGT_zero
  have h := (dual_sum_tendsto_one x y).comp hT
  simpa [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end RankTwoLimit

end

end OAI
