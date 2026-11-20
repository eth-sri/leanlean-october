module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

open Complex Finset Set
open scoped BigOperators InnerProductSpace

namespace GuthMaynard.NativeMoment

/-!
# The logarithmic exponential sums used in the classical density argument

This file develops the two concrete van der Corput estimates needed by the
project.  Angles in `unitaryPhase` are measured in radians; this avoids a
pervasive factor `2 * pi` when the phase is `-t * log x`.
-/

/-- The standard additive character with its argument measured in radians. -/
noncomputable def unitaryPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * x)

/-- The resolvent appearing in summation by parts for a unitary phase. -/
noncomputable def phaseResolvent (x : ℝ) : ℂ := (1 - unitaryPhase x)⁻¹

@[simp] theorem norm_unitaryPhase (x : ℝ) : ‖unitaryPhase x‖ = 1 := by
  simp [unitaryPhase]

theorem unitaryPhase_add (x y : ℝ) :
    unitaryPhase (x + y) = unitaryPhase x * unitaryPhase y := by
  simp only [unitaryPhase, ofReal_add, mul_add, Complex.exp_add]

theorem unitaryPhase_sub (x y : ℝ) :
    unitaryPhase (x - y) = unitaryPhase x * starRingEnd ℂ (unitaryPhase y) := by
  rw [sub_eq_add_neg, unitaryPhase_add]
  simp only [unitaryPhase, ofReal_neg, mul_neg]
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- A finite exponential sum on the half-open integer interval `[A, B)`. -/
noncomputable def phaseSum (f : ℝ → ℝ) (A B : ℕ) : ℂ :=
  ∑ n ∈ Ico A B, unitaryPhase (f n)

/-- The logarithmic phase occurring in `n ^ (-it)`. -/
noncomputable def logarithmicPhase (t x : ℝ) : ℝ := -t * Real.log x

/-- The unweighted logarithmic exponential sum on `[A, B)`. -/
noncomputable def logarithmicSum (t : ℝ) (A B : ℕ) : ℂ :=
  phaseSum (logarithmicPhase t) A B

theorem unitaryPhase_logarithmicPhase_eq_cpow (t : ℝ) (n : ℕ) (hn : 0 < n) :
    unitaryPhase (logarithmicPhase t n) = (n : ℂ) ^ (-(t : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.ne_of_gt hn)]
  simp only [unitaryPhase, logarithmicPhase, Complex.natCast_log, ofReal_neg,
    ofReal_mul]
  congr 1
  ring

theorem logarithmicSum_eq_cpow (t : ℝ) (A B : ℕ) (hA : 0 < A) :
    logarithmicSum t A B = ∑ n ∈ Ico A B, (n : ℂ) ^ (-(t : ℂ) * I) := by
  unfold logarithmicSum phaseSum
  apply Finset.sum_congr rfl
  intro n hn
  exact unitaryPhase_logarithmicPhase_eq_cpow t n (hA.trans_le (mem_Ico.mp hn).1)



/-- First derivative of the logarithmic phase. -/
theorem hasDerivAt_logarithmicPhase (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logarithmicPhase t) (-t / x) x := by
  change HasDerivAt (fun y => -t * Real.log y) (-t / x) x
  simpa only [neg_mul, div_eq_mul_inv] using (Real.hasDerivAt_log hx).const_mul (-t)

/-! ## Kusmin--Landau cancellation -/

/-- Exact cotangent expression for the phase resolvent. -/
theorem phaseResolvent_eq (x : ℝ) (hs : Real.sin (x / 2) ≠ 0) :
    phaseResolvent x = (1 : ℂ) / 2 + Complex.I * (Real.cot (x / 2) / 2 : ℝ) := by
  have hden : (1 - unitaryPhase x : ℂ) ≠ 0 := by
    intro h
    have hn : ‖(1 - unitaryPhase x : ℂ)‖ = ‖(2 * Real.sin (x / 2) : ℝ)‖ := by
      rw [← norm_neg, neg_sub]
      exact Complex.norm_exp_I_mul_ofReal_sub_one x
    rw [h, norm_zero] at hn
    have : (2 * Real.sin (x / 2) : ℝ) = 0 := norm_eq_zero.mp hn.symm
    exact hs (by linarith)
  rw [phaseResolvent]
  apply (mul_eq_one_iff_inv_eq₀ hden).mp
  have hcot := Complex.cot_eq_exp_ratio ((x / 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_cot] at hcot
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hcot
  rw [show (2 : ℂ) * Complex.I * ((x : ℂ) / 2) = Complex.I * x by ring_nf] at hcot
  have hdenexp : (1 - Complex.exp (Complex.I * x) : ℂ) ≠ 0 := by
    simpa only [unitaryPhase] using hden
  rw [eq_div_iff (mul_ne_zero Complex.I_ne_zero hdenexp)] at hcot
  rw [unitaryPhase]
  push_cast at hcot ⊢
  ring_nf at hcot ⊢
  linear_combination (1 / 2 : ℂ) * hcot

/-- Derivative of real cotangent on its fundamental open interval. -/
theorem hasDerivAt_real_cot {x : ℝ} (hx : x ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt Real.cot (-(1 / Real.sin x ^ 2)) x := by
  have hsin : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  have hquot := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsin
  convert hquot using 1
  · funext y
    simp [Real.cot_eq_cos_div_sin]
  · field_simp [hsin]
    nlinarith [Real.sin_sq_add_cos_sq x]

/-- Cotangent is strictly decreasing between its consecutive poles at `0` and `π`. -/
theorem strictAntiOn_real_cot : StrictAntiOn Real.cot (Set.Ioo 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) Real.pi)
  · intro x hx
    exact (hasDerivAt_real_cot hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_real_cot hx).deriv]
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have : 0 < 1 / Real.sin x ^ 2 := by positivity
    linarith

/-- Jordan's inequality, reflected about `π / 2`, in the form needed to stay
away from both endpoints of a full phase period. -/
theorem sin_half_lower {δ θ : ℝ} (hδ : 0 ≤ δ) (hθlow : δ ≤ θ)
    (hθhigh : θ ≤ 2 * Real.pi - δ) :
    δ / Real.pi ≤ Real.sin (θ / 2) := by
  by_cases hθ : θ ≤ Real.pi
  · have harg0 : 0 ≤ θ / 2 := by linarith
    have harg1 : θ / 2 ≤ Real.pi / 2 := by linarith
    have hJ := Real.mul_le_sin harg0 harg1
    calc
      δ / Real.pi ≤ θ / Real.pi :=
        (div_le_div_iff_of_pos_right Real.pi_pos).mpr hθlow
      _ = 2 / Real.pi * (θ / 2) := by ring_nf
      _ ≤ Real.sin (θ / 2) := hJ
  · have hθpi : Real.pi ≤ θ := le_of_not_ge hθ
    have harg0 : 0 ≤ Real.pi - θ / 2 := by linarith
    have harg1 : Real.pi - θ / 2 ≤ Real.pi / 2 := by linarith
    have hJ := Real.mul_le_sin harg0 harg1
    rw [Real.sin_pi_sub] at hJ
    calc
      δ / Real.pi ≤ (2 * Real.pi - θ) / Real.pi :=
        (div_le_div_iff_of_pos_right Real.pi_pos).mpr (by linarith)
      _ = 2 / Real.pi * (Real.pi - θ / 2) := by ring_nf
      _ ≤ Real.sin (θ / 2) := hJ

/-- Quantitative norm bound for the phase resolvent away from the endpoints
of a full period. -/
theorem norm_phaseResolvent_le {δ θ : ℝ} (hδ : 0 < δ) (hθlow : δ ≤ θ)
    (hθhigh : θ ≤ 2 * Real.pi - δ) :
    ‖phaseResolvent θ‖ ≤ Real.pi / (2 * δ) := by
  have hsin := sin_half_lower hδ.le hθlow hθhigh
  have hsinPos : 0 < Real.sin (θ / 2) := lt_of_lt_of_le (div_pos hδ Real.pi_pos) hsin
  have hden : 2 * δ / Real.pi ≤ ‖(1 - unitaryPhase θ : ℂ)‖ := by
    rw [← norm_neg, neg_sub, unitaryPhase,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      abs_of_pos (mul_pos zero_lt_two hsinPos)]
    convert mul_le_mul_of_nonneg_left hsin zero_le_two using 1
    ring_nf
  rw [phaseResolvent, norm_inv, ← one_div]
  calc
    1 / ‖(1 - unitaryPhase θ : ℂ)‖ ≤ 1 / (2 * δ / Real.pi) :=
      one_div_le_one_div_of_le (div_pos (mul_pos zero_lt_two hδ) Real.pi_pos) hden
    _ = Real.pi / (2 * δ) := by field_simp

/-- Exact variation of the phase resolvent between two ordered angles in one period. -/
theorem norm_phaseResolvent_sub_eq {x y : ℝ}
    (hx0 : 0 < x) (hy2pi : y < 2 * Real.pi) (hxy : x ≤ y) :
    ‖phaseResolvent y - phaseResolvent x‖ =
      (Real.cot (x / 2) - Real.cot (y / 2)) / 2 := by
  have hxmem : x / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by constructor <;> linarith
  have hymem : y / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by constructor <;> linarith
  have hsinx : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hxmem.1 hxmem.2).ne'
  have hsiny : Real.sin (y / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hymem.1 hymem.2).ne'
  have hcot : Real.cot (y / 2) ≤ Real.cot (x / 2) :=
    strictAntiOn_real_cot.antitoneOn hxmem hymem (by linarith)
  rw [phaseResolvent_eq y hsiny, phaseResolvent_eq x hsinx]
  have heq :
      (1 / 2 + Complex.I * (Real.cot (y / 2) / 2 : ℝ) : ℂ) -
          (1 / 2 + Complex.I * (Real.cot (x / 2) / 2 : ℝ) : ℂ) =
        Complex.I * ((Real.cot (y / 2) - Real.cot (x / 2)) / 2 : ℝ) := by
    push_cast
    ring_nf
  rw [heq, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  ring_nf

/-- Total variation of resolvents for an increasing sequence of angles in one period. -/
theorem phaseResolvent_variation (θ : ℕ → ℝ) (N : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (hlow : ∀ n ≤ N, δ ≤ θ n)
    (hhigh : ∀ n ≤ N, θ n ≤ 2 * Real.pi - δ)
    (hmono : ∀ n < N, θ n ≤ θ (n + 1)) :
    ∑ n ∈ Finset.range N, ‖phaseResolvent (θ (n + 1)) - phaseResolvent (θ n)‖ =
      (Real.cot (θ 0 / 2) - Real.cot (θ N / 2)) / 2 := by
  calc
    ∑ n ∈ Finset.range N, ‖phaseResolvent (θ (n + 1)) - phaseResolvent (θ n)‖ =
        ∑ n ∈ Finset.range N,
          (Real.cot (θ n / 2) - Real.cot (θ (n + 1) / 2)) / 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnlt := Finset.mem_range.mp hn
      apply norm_phaseResolvent_sub_eq
      · exact hδ.trans_le (hlow n (by omega))
      · linarith [hhigh (n + 1) (by omega)]
      · exact hmono n hnlt
    _ = (Real.cot (θ 0 / 2) - Real.cot (θ N / 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_range_sub']

/-- The cotangent component of the resolvent is controlled by its complex norm. -/
theorem abs_cot_half_le_norm_phaseResolvent {θ : ℝ}
    (hθ0 : 0 < θ) (hθ2pi : θ < 2 * Real.pi) :
    |Real.cot (θ / 2) / 2| ≤ ‖phaseResolvent θ‖ := by
  have hmem : θ / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by constructor <;> linarith
  have hsin : Real.sin (θ / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2).ne'
  rw [phaseResolvent_eq θ hsin]
  let z : ℂ := (1 : ℂ) / 2 + Complex.I * (Real.cot (θ / 2) / 2 : ℝ)
  have him : z.im = Real.cot (θ / 2) / 2 := by
    dsimp only [z]
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add, Complex.ofReal_re]
  calc
    |Real.cot (θ / 2) / 2| = |z.im| := congrArg abs him.symm
    _ ≤ ‖z‖ := Complex.abs_im_le_norm z

/-- A single phase term written as a resolvent times a forward difference. -/
theorem unitaryPhase_resolvent_step (f : ℕ → ℝ) (n : ℕ)
    (hsin : Real.sin ((f (n + 1) - f n) / 2) ≠ 0) :
    unitaryPhase (f n) = phaseResolvent (f (n + 1) - f n) *
      (unitaryPhase (f n) - unitaryPhase (f (n + 1))) := by
  have hden : (1 - unitaryPhase (f (n + 1) - f n) : ℂ) ≠ 0 := by
    intro h
    have hn : ‖(1 - unitaryPhase (f (n + 1) - f n) : ℂ)‖ =
        ‖(2 * Real.sin ((f (n + 1) - f n) / 2) : ℝ)‖ := by
      rw [← norm_neg, neg_sub]
      exact Complex.norm_exp_I_mul_ofReal_sub_one (f (n + 1) - f n)
    rw [h, norm_zero] at hn
    have hz : (2 * Real.sin ((f (n + 1) - f n) / 2) : ℝ) = 0 :=
      norm_eq_zero.mp hn.symm
    exact hsin (by linarith)
  rw [show f (n + 1) = f n + (f (n + 1) - f n) by ring_nf,
    unitaryPhase_add, phaseResolvent]
  field_simp [hden]
  ring_nf

/-- Exact finite summation by parts for resolvents. -/
theorem finite_resolvent_telescoping (z q : ℕ → ℂ) (N : ℕ)
    (hrec : ∀ n ≤ N, z n = q n * (z n - z (n + 1))) :
    ∑ n ∈ Finset.range (N + 1), z n =
      q 0 * z 0 - q N * z (N + 1) +
        ∑ n ∈ Finset.range N, (q (n + 1) - q n) * z (n + 1) := by
  induction N with
  | zero =>
      simpa [mul_sub] using hrec 0 le_rfl
  | succ N ih =>
      calc
        ∑ n ∈ Finset.range (N + 1 + 1), z n =
            (∑ n ∈ Finset.range (N + 1), z n) + z (N + 1) := by
              rw [Finset.sum_range_succ]
        _ = (q 0 * z 0 - q N * z (N + 1) +
              ∑ n ∈ Finset.range N, (q (n + 1) - q n) * z (n + 1)) +
              z (N + 1) := by
                rw [ih (fun n hn => hrec n (hn.trans (Nat.le_succ N)))]
        _ = q 0 * z 0 - q (N + 1) * z (N + 1 + 1) +
              ∑ n ∈ Finset.range (N + 1), (q (n + 1) - q n) * z (n + 1) := by
                rw [Finset.sum_range_succ]
                linear_combination hrec (N + 1) le_rfl

/-- Norm form of finite resolvent summation by parts. -/
theorem norm_sum_le_resolvent_variation (z q : ℕ → ℂ) (N : ℕ)
    (hz : ∀ n ≤ N + 1, ‖z n‖ = 1)
    (hrec : ∀ n ≤ N, z n = q n * (z n - z (n + 1))) :
    ‖∑ n ∈ Finset.range (N + 1), z n‖ ≤
      ‖q 0‖ + ‖q N‖ + ∑ n ∈ Finset.range N, ‖q (n + 1) - q n‖ := by
  rw [finite_resolvent_telescoping z q N hrec]
  calc
    ‖q 0 * z 0 - q N * z (N + 1) +
        ∑ n ∈ Finset.range N, (q (n + 1) - q n) * z (n + 1)‖ ≤
        ‖q 0 * z 0 - q N * z (N + 1)‖ +
          ‖∑ n ∈ Finset.range N, (q (n + 1) - q n) * z (n + 1)‖ := norm_add_le _ _
    _ ≤ (‖q 0 * z 0‖ + ‖q N * z (N + 1)‖) +
          ∑ n ∈ Finset.range N, ‖(q (n + 1) - q n) * z (n + 1)‖ := by
      gcongr
      · exact norm_sub_le _ _
      · exact norm_sum_le _ _
    _ = ‖q 0‖ + ‖q N‖ + ∑ n ∈ Finset.range N, ‖q (n + 1) - q n‖ := by
      simp only [norm_mul]
      rw [hz 0 (by omega), hz (N + 1) (by omega), mul_one, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hz (n + 1) (by have := Finset.mem_range.mp hn; omega), mul_one]

/-- Kusmin--Landau cancellation while all phase increments remain in one
period and a fixed positive distance from its endpoints. -/
theorem kusminLandau_one_period (f : ℕ → ℝ) (N : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (hlow : ∀ n ≤ N, δ ≤ f (n + 1) - f n)
    (hhigh : ∀ n ≤ N, f (n + 1) - f n ≤ 2 * Real.pi - δ)
    (hmono : ∀ n < N, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.range (N + 1), unitaryPhase (f n)‖ ≤
      2 * Real.pi / δ := by
  let θ : ℕ → ℝ := fun n => f (n + 1) - f n
  have hθlow : ∀ n ≤ N, δ ≤ θ n := hlow
  have hθhigh : ∀ n ≤ N, θ n ≤ 2 * Real.pi - δ := hhigh
  have hθmono : ∀ n < N, θ n ≤ θ (n + 1) := hmono
  have hθpos : ∀ n ≤ N, 0 < θ n := fun n hn => hδ.trans_le (hθlow n hn)
  have hθlt : ∀ n ≤ N, θ n < 2 * Real.pi := fun n hn => by
    linarith [hθhigh n hn]
  have hsin : ∀ n ≤ N, Real.sin (θ n / 2) ≠ 0 := fun n hn => by
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθpos n hn])
      (by linarith [hθlt n hn])).ne'
  have hbase := norm_sum_le_resolvent_variation
    (fun n => unitaryPhase (f n)) (fun n => phaseResolvent (θ n)) N
    (fun n _hn => norm_unitaryPhase (f n))
    (fun n hn => unitaryPhase_resolvent_step f n (hsin n hn))
  rw [phaseResolvent_variation θ N δ hδ hθlow hθhigh hθmono] at hbase
  have hvar : (Real.cot (θ 0 / 2) - Real.cot (θ N / 2)) / 2 ≤
      ‖phaseResolvent (θ 0)‖ + ‖phaseResolvent (θ N)‖ := by
    have h0 := abs_cot_half_le_norm_phaseResolvent (hθpos 0 (by omega))
      (hθlt 0 (by omega))
    have hN := abs_cot_half_le_norm_phaseResolvent (hθpos N le_rfl) (hθlt N le_rfl)
    have hleft : Real.cot (θ 0 / 2) / 2 ≤ ‖phaseResolvent (θ 0)‖ :=
      (le_abs_self _).trans h0
    have hright : -(Real.cot (θ N / 2) / 2) ≤ ‖phaseResolvent (θ N)‖ :=
      (neg_le_abs _).trans hN
    linarith
  have hq0 := norm_phaseResolvent_le hδ (hθlow 0 (by omega)) (hθhigh 0 (by omega))
  have hqN := norm_phaseResolvent_le hδ (hθlow N le_rfl) (hθhigh N le_rfl)
  calc
    ‖∑ n ∈ Finset.range (N + 1), unitaryPhase (f n)‖ ≤
        ‖phaseResolvent (θ 0)‖ + ‖phaseResolvent (θ N)‖ +
          (Real.cot (θ 0 / 2) - Real.cot (θ N / 2)) / 2 := hbase
    _ ≤ 2 * (‖phaseResolvent (θ 0)‖ + ‖phaseResolvent (θ N)‖) := by linarith
    _ ≤ 2 * Real.pi / δ := by
      calc
        2 * (‖phaseResolvent (θ 0)‖ + ‖phaseResolvent (θ N)‖) ≤
            2 * (Real.pi / (2 * δ) + Real.pi / (2 * δ)) := by gcongr
        _ = 2 * Real.pi / δ := by
          field_simp
          norm_num

/-- A phase is unchanged by adding an integral multiple of its full period. -/
theorem unitaryPhase_int_mul_two_pi (k : ℤ) :
    unitaryPhase ((k : ℝ) * (2 * Real.pi)) = 1 := by
  rw [unitaryPhase]
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  push_cast
  ring_nf

/-- Subtracting an integral multiple of `2π` does not change a unitary phase. -/
theorem unitaryPhase_sub_int_mul_two_pi (x : ℝ) (k : ℤ) :
    unitaryPhase (x - (k : ℝ) * (2 * Real.pi)) = unitaryPhase x := by
  rw [unitaryPhase_sub, unitaryPhase_int_mul_two_pi]
  simp

/-- Shifted-index and shifted-period form of Kusmin--Landau cancellation. -/
theorem kusminLandau_interval (f : ℕ → ℝ) (A N : ℕ) (k : ℤ) (δ : ℝ)
    (hδ : 0 < δ)
    (hlow : ∀ n ≤ N, δ ≤
      f (A + n + 1) - f (A + n) - (k : ℝ) * (2 * Real.pi))
    (hhigh : ∀ n ≤ N,
      f (A + n + 1) - f (A + n) - (k : ℝ) * (2 * Real.pi) ≤
        2 * Real.pi - δ)
    (hmono : ∀ n < N,
      f (A + n + 1) - f (A + n) ≤ f (A + n + 2) - f (A + n + 1)) :
    ‖∑ n ∈ Finset.range (N + 1), unitaryPhase (f (A + n))‖ ≤
      2 * Real.pi / δ := by
  let g : ℕ → ℝ := fun n =>
    f (A + n) - (((k * (n : ℤ) : ℤ) : ℝ) * (2 * Real.pi))
  have hdiff (n : ℕ) :
      g (n + 1) - g n =
        f (A + n + 1) - f (A + n) - (k : ℝ) * (2 * Real.pi) := by
    dsimp only [g]
    push_cast
    rw [show A + (n + 1) = A + n + 1 by omega]
    ring_nf
  have hphase (n : ℕ) : unitaryPhase (g n) = unitaryPhase (f (A + n)) := by
    dsimp only [g]
    simpa only [Int.cast_mul, Int.cast_natCast] using
      unitaryPhase_sub_int_mul_two_pi (f (A + n)) (k * (n : ℤ))
  have hKL := kusminLandau_one_period g N δ hδ
    (fun n hn => by rw [hdiff]; exact hlow n hn)
    (fun n hn => by rw [hdiff]; exact hhigh n hn)
    (fun n hn => by
      rw [hdiff, hdiff]
      simpa only [Nat.add_assoc] using
        sub_le_sub_right (hmono n hn) ((k : ℝ) * (2 * Real.pi)))
  simpa only [hphase] using hKL

/-! ## Finite Weyl differencing -/

/-- Cauchy--Schwarz for the norm of a finite complex sum, in the precise
form used by Weyl differencing. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ s, a i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, a i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
      exact sq_sum_le_card_mul_sum_sq






end GuthMaynard.NativeMoment
