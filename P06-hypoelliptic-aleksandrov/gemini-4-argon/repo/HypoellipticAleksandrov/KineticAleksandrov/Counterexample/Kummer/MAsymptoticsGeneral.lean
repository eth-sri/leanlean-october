module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsContinuation
import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsPositive
import Mathlib.Tactic.FieldSimp

/-!
# General negative-axis expansion

The proved contiguous relation extends Euler asymptotics to every first parameter above minus one.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

/- Monotonicity of algebraic asymptotic orders on the positive half-line. -/
theorem rpow_isBigO_of_le (r s : ℝ) (hrs : r ≤ s) :
    IsBigO atTop (fun X : ℝ => X ^ r) (fun X => X ^ s) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hX]) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hX]) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hX hrs

/- Continuation gives the expansion at every positive truncation order. -/
theorem M_negative_expansion_succ (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 (N + 1) X)
      (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have hab1 : a + 1 < (next b).1 := by change a + 1 < b.1 + 1; linarith only [hab]
  have hab2 : a + 1 < (next (next b)).1 := by
    change a + 1 < b.1 + 1 + 1
    linarith only [hab]
  have h1 := M_negative_expansion_positive (a + 1) (next b) ha1 hab1 N
  have h2 := M_negative_expansion_positive (a + 1) (next (next b)) ha1 hab2 (N + 1)
  have hb2 : (next (next b)).1 = b.1 + 2 := by dsimp [next]; ring
  rw [hb2] at h2
  have hX : IsBigO atTop (fun X : ℝ => X) (fun X => X ^ (1 : ℝ)) := by
    simpa only [Real.rpow_one] using (isBigO_refl (fun X : ℝ => X) atTop)
  have h2X := hX.mul_atTop_rpow_of_isBigO_rpow 1
    (-(a + 1) - ((N + 1 : ℕ) : ℝ)) (-a - ((N + 1 : ℕ) : ℝ)) h2 (by linarith)
  have h1' : IsBigO atTop
      (fun X => M (a + 1) (next b) (-X) - mExpansion (a + 1) (b.1 + 1) N X)
      (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
    convert h1 using 1
    · rfl
    · ext X
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  have h := h1'.add (h2X.const_mul_left (-((a - b.1) / (b.1 * (b.1 + 1)))))
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hXp
    have _h_xinl_0 : mExpansion a b.1 (N + 1) X = mExpansion (a + 1) (b.1 + 1) N X +
      (-((a - b.1) / (b.1 * (b.1 + 1))) * X) *
        mExpansion (a + 1) (b.1 + 2) (N + 1) X := by
      rw [mExpansion_eq_sum a b.1 (N + 1) X hXp,
        mExpansion_eq_sum (a + 1) (b.1 + 1) N X hXp,
        mExpansion_eq_sum (a + 1) (b.1 + 2) (N + 1) X hXp]
      let k : ℝ := -((a - b.1) / (b.1 * (b.1 + 1)))
      have hx (n : ℕ) : X * Real.rpow X (-(a + 1 + n)) = Real.rpow X (-(a + n)) := by
        change X * X ^ (-(a + 1 + (n : ℝ))) = X ^ (-(a + n))
        calc
          _ = X ^ (1 : ℝ) * X ^ (-(a + 1 + (n : ℝ))) := by rw [Real.rpow_one]
          _ = X ^ ((1 : ℝ) + -(a + 1 + n)) := (Real.rpow_add hXp _ _).symm
          _ = _ := by congr 1; ring
      have hm : (k * X) *
          (∑ n ∈ Finset.range (N + 1), expansionCoeff (a + 1) (b.1 + 2) n *
            Real.rpow X (-(a + 1 + n))) =
          ∑ n ∈ Finset.range (N + 1), k * expansionCoeff (a + 1) (b.1 + 2) n *
            Real.rpow X (-(a + n)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        calc
          _ = (k * expansionCoeff (a + 1) (b.1 + 2) n) *
              (X * Real.rpow X (-(a + 1 + n))) := by ring
          _ = _ := by rw [hx]
      change _ = _ + (k * X) * _
      rw [hm]
      have ht (n : ℕ) : expansionCoeff a b.1 (n + 1) *
          Real.rpow X (-(a + (n + 1 : ℕ))) =
          expansionCoeff (a + 1) (b.1 + 1) n * Real.rpow X (-(a + 1 + n)) +
          k * expansionCoeff (a + 1) (b.1 + 2) (n + 1) *
            Real.rpow X (-(a + (n + 1 : ℕ))) := by
        have _h_inl_9 : expansionCoeff a b.1 (n + 1) = expansionCoeff (a + 1) (b.1 + 1) n +
          -((a - b.1) / (b.1 * (b.1 + 1))) *
            expansionCoeff (a + 1) (b.1 + 2) (n + 1) := by
            rw [expansionCoeff_contiguous_second a b hab, expansionCoeff, expansionCoeff,
              Real.Gamma_add_one (ne_of_gt b.2),
              show b.1 + 1 - (a + 1) = b.1 - a by ring,
              show a + 1 - (b.1 + 1) + 1 = a - b.1 + 1 by ring,
              poch_succ_left a n, poch_succ (a - b.1 + 1) n,
              poch_succ (a + 1) n, poch_succ_left (a - b.1) n,
              Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
            have hn : (n + 1 : ℝ) ≠ 0 := by positivity
            field_simp
            ring

          /- The exact matching of finite contiguous expansions at adjacent truncation orders. -/
        rw [_h_inl_9]
        simp only [Nat.cast_add, Nat.cast_one]
        rw [show a + ((n : ℝ) + 1) = a + 1 + n by ring]
        dsimp [k]
        ring
      have hs := Finset.sum_congr (s₁ := Finset.range N) rfl (fun n _ => ht n)
      rw [Finset.sum_add_distrib] at hs
      simp only [Finset.sum_range_succ', Nat.cast_zero, add_zero]
      have _h_inl_8 : expansionCoeff a b.1 0 = -((a - b.1) / (b.1 * (b.1 + 1))) *
          expansionCoeff (a + 1) (b.1 + 2) 0 := by
          rw [expansionCoeff_contiguous_second a b hab]
          simp only [expansionCoeff, poch_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]

        /- The higher coefficients of the contiguous expansion. -/
      rw [_h_inl_8]
      change _ + k * _ * _ = _ + (_ + k * _ * _)
      linarith only [hs]
    rw [M_contiguous a b (-X), _h_xinl_0]
    simp only [Pi.mul_apply]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/- The complete algebraic expansion with its exact remainder order. -/
theorem M_negative_expansion (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => Real.rpow X (-a - (N : ℝ))) := by
  cases N with
  | succ N => exact M_negative_expansion_succ a b ha hab N
  | zero =>
    have h1 := (M_negative_expansion_succ a b ha hab 0).trans
      (rpow_isBigO_of_le (-a - ((0 + 1 : ℕ) : ℝ)) (-a) (by norm_num))
    have h0 : IsBigO atTop (mExpansion a b.1 1) (fun X : ℝ => X ^ (-a)) := by
      have h := (isBigO_refl (fun X : ℝ => X ^ (-a)) atTop)
        |>.const_mul_left (Real.Gamma b.1 / Real.Gamma (b.1 - a))
      convert h using 1
      ext X
      simp [mExpansion]
    have h := h1.add h0
    convert h using 1
    · ext X
      simp only [mExpansion, Finset.range_zero, Finset.sum_empty, mul_zero]
      ring
    · ext X
      simp only [Nat.cast_zero, sub_zero]
      rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
