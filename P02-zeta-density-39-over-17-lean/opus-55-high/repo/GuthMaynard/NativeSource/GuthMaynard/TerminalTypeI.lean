module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalDichotomy
public import GuthMaynard.NativeSource.GuthMaynard.WeylZeta
import WeylPort.Analytic.RealLaplace

public section

open Complex Finset

namespace GuthMaynard.NativeMoment

/-!
# Terminal Type-I blocks

At the terminal end of the ordinary-zeta Type-I range the logarithmic
phase has first derivative bounded away from a full period.  The finite
Kusmin--Landau estimate therefore controls every prefix, and Abel summation
transfers that cancellation to the decreasing weight `n^(-sigma)`.
-/

/-- Uniform first-derivative cancellation for every prefix beginning just
to the right of `A`.  The deliberately generous constant is uniform in the
prefix length. -/
theorem norm_logarithmicPhase_prefix_le_div
    (A L : ℕ) (t : ℝ) (hA : 0 < A) (hL : L ≤ A)
    (htOne : 1 ≤ t) (htA : t ≤ (A : ℝ)) :
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      6 * Real.pi * (A : ℝ) / t := by
  by_cases hL0 : L = 0
  · subst L
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  pm_456 hAReal A hA
  let δ : ℝ := t / (3 * (A : ℝ))
  pm_4790 hδ δ
  have hinc (n : ℕ) (hn : n ≤ L - 1) :
      let m := A + 1 + n
      δ ≤ logarithmicPhase t (m + 1) - logarithmicPhase t m + 2 * Real.pi ∧
        logarithmicPhase t (m + 1) - logarithmicPhase t m + 2 * Real.pi ≤
          2 * Real.pi - δ := by
    dsimp only
    let m := A + 1 + n
    pm_4647 hm m
    have hmLower : A ≤ m := by dsimp only [m]; omega
    have hmUpper : m + 1 ≤ 3 * A := by
      dsimp only [m]
      omega
    have hlogs :
        1 / ((m : ℝ) + 1) ≤
            Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ∧
          Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤
            1 / (m : ℝ) := by
      pm_4642
      · calc
          1 / ((m : ℝ) + 1) =
              1 - ((((m + 1 : ℕ) : ℝ) / (m : ℝ))⁻¹) := by
                push_cast
                field_simp [hmReal.ne']
                ring
          _ ≤ Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            Real.one_sub_inv_le_log_of_pos hratio
          _ = Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := hlog
      · rw [← hlog]
        calc
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
              ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos hratio
          _ = 1 / (m : ℝ) := by
            push_cast
            field_simp [hmReal.ne']
            ring
    pm_4646 t
    pm_456 hmReal m hm
    have hmLowerReal : (A : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmLower
    have hmUpperReal : ((m : ℝ) + 1) ≤ 3 * (A : ℝ) := by
      exact_mod_cast hmUpper
    pm_8184 htOverM t htA.trans
    pm_995 A
    have hdeltaLog : δ ≤ t *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      have hrecip : 1 / (3 * (A : ℝ)) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hmUpperReal
      dsimp only [δ]
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_le_mul_of_nonneg_left hrecip (zero_le_one.trans htOne)).trans
          (mul_le_mul_of_nonneg_left hlogs.1 (zero_le_one.trans htOne))
    constructor
    · have hlogUpper : t *
          (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left hlogs.2 (zero_le_one.trans htOne)).trans (by
          simpa only [div_eq_mul_inv, one_mul] using htOverM)
      nlinarith [Real.pi_gt_three]
    · linarith
  have hmono : ∀ n < L - 1,
      logarithmicPhase t (A + 1 + n + 1) - logarithmicPhase t (A + 1 + n) ≤
        logarithmicPhase t (A + 1 + n + 2) -
          logarithmicPhase t (A + 1 + n + 1) := by
    pm_8947 A
    pm_4643
    pm_4645 t
  have hKL := kusminLandau_interval (fun n : ℕ => logarithmicPhase t n)
    (A + 1) (L - 1) (-1) δ hδ
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using (hinc n hn).1)
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using (hinc n hn).2)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hmono n hn)
  pm_4648 L hKL
  calc
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
        2 * Real.pi / δ := by
          pm_99 Nat.cast_add Nat.cast_one Nat.cast_ofNat add_assoc hKL
    _ = 6 * Real.pi * (A : ℝ) / t := by
      dsimp only [δ]
      field_simp [show t ≠ 0 by linarith, hAReal.ne']
      ring

/-- The sharp-cutoff Type-I coefficients on a dyadic block are exactly a
decreasing real weight, followed (if necessary) by zeros. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_terminal
    (C N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      ∑ i ∈ Finset.range N,
        (if N + 1 + i ≤ C then
          ((N + 1 + i : ℝ) ^ (-σ) : ℝ) •
            unitaryPhase (logarithmicPhase t (N + 1 + i))
        else 0) := by
  unfold dirichletPoly
  rw [dyadicInterval_eq_Ico_succ, Finset.sum_Ico_eq_sum_range]
  pm_4641 hLength N
  apply Finset.sum_congr rfl
  intro i hi
  pm_8165 hm N i
  by_cases hmC : N + 1 + i ≤ C
  · rw [ite_eq_left hmC, classicalZetaLongLineCoeff_term C (N + 1 + i) σ t hm hmC]
    have hcastReal : ((N + 1 + i : ℕ) : ℝ) = (N : ℝ) + 1 + (i : ℝ) := by
      push_cast
      ring
    rw [← hcastReal]
    rw [Complex.real_smul,
      unitaryPhase_logarithmicPhase_eq_cpow t (N + 1 + i) hm]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (N + 1 + i))]
    simp only [Complex.ofReal_natCast]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hm.ne')]
    congr 2
    push_cast
    ring
  · rw [ite_eq_right hmC, classicalZetaLongLineCoeff, ite_eq_right hmC, zero_mul]

/-- Concrete terminal estimate for the actual sharp Type-I dyadic block.
It remains valid when the sharp upper cutoff stops inside the block. -/
theorem norm_terminal_classicalZetaLongLineCoeff_le
    (C N : ℕ) (σ t : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N)
    (hNC : N < C) (htOne : 1 ≤ t) (htN : t ≤ (N : ℝ)) :
    ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖ ≤
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) := by
  pm_4626
  have hBound := norm_weighted_sum_le_of_antitone f g N
    (6 * Real.pi * (N : ℝ) / t) hN
    (by
      pm_8125
      · exact le_rfl)
    hanti
    (by
      intro j hj
      dsimp only [g]
      exact norm_logarithmicPhase_prefix_le_div N j t hN hj htOne htN)
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_terminal C N σ t hN]
  pm_4934 hStart N C
  simpa only [f, g, ite_eq_left hStart, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_zero, add_zero, ite_smul, zero_smul] using hBound

/-- A block whose asserted detector threshold exceeds the terminal
Kusmin--Landau majorant must lie strictly below the height.  This is the
case-splitting form consumed by the finite density reduction. -/
theorem typeI_scale_lt_height_of_large
    (C N : ℕ) (σ t V : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N)
    (hNC : N < C) (htOne : 1 ≤ t)
    (hLarge : V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖)
    (hMajorant :
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) < V) :
    (N : ℝ) < t := by
  pm_8235 hNot
  have hUpper := norm_terminal_classicalZetaLongLineCoeff_le
    C N σ t hσ hN hNC htOne htN
  linarith

end GuthMaynard.NativeMoment
