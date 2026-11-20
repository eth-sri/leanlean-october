module

public import PottsDiscontinuity.Bethe.RatioOddCoefficient
public import PottsDiscontinuity.Bethe.RatioOddLogCorrection

/-! # Exact five-factor expression for the odd eigenvalue quotient -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

theorem ratio_exp_ell {c : ℝ} (hc : 2 < c) (x : ℝ) :
    Real.exp (ratioEll c x) = ‖M c (z x)‖ := Real.exp_log (norm_pos_iff.mpr (ratio_M_ne_zero hc x))

theorem ratio_exp_sum_ell {ι : Type*} [Fintype ι] {c : ℝ} (hc : 2 < c) (u : ι → ℝ) :
    Real.exp (∑ j, ratioEll c (u j)) = ∏ j, ‖M c (z (u j))‖ := by
  simp [Real.exp_sum, ratio_exp_ell hc]

/-- The coefficient divided by N, the central inverse pole times N,
the boundary factor, the Wallis correction and the bulk factor. -/
theorem ratio_odd_quotient_factors {c : ℝ} (hc : 2 < c) (s N : ℕ) (h4 : 4 ∣ N)
    (hr : 2 * s + 1 ≤ N / 2) (hn : 0 < N / 2 - (2 * s + 1))
    (p : Fin (N / 2) → ℝ) (hp : p ∈ S_n (N / 2))
    (q : Fin (N / 2 - (2 * s + 1)) → ℝ) (hq : q ∈ S_n (N / 2 - (2 * s + 1)))
    (l : Fin (N / 2 - (2 * s + 1))) (hl : q l = 0) :
    eigenvalueZero N c q l / eigenvalueRegular c p =
      (((ratioZeroCoefficient (anisotropy c) c N q l / (2 * N)) *
        ((N : ℝ) * ‖M c (z (ratioPositiveRoot N h4 p ⟨0, by obtain ⟨z, hz⟩ := h4; omega⟩))‖⁻¹) *
        (‖M c (z (p ⟨s, by omega⟩))‖ * (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2)⁻¹ *
        Real.exp (∑ j : Fin (N / 4 - s - 1), ratioMidpointLog c N h4 p s j) *
        Real.exp (∑ j, (ratioEll c (q j) - ratioEll c (alignedRoot N (2 * s + 1) hr p j))) : ℝ) : ℂ) := by
  have hfirstBound : 0 < N / 4 := by
    obtain ⟨m, hm⟩ := h4
    omega
  let first : Fin (N / 4) := ⟨0, hfirstBound⟩
  have hsBound : s < N / 2 := by omega
  have hN : (N : ℝ) ≠ 0 := by norm_cast at *; omega
  have hfullQ : (∏ j ∈ univ.erase l, ‖M c (z (q j))‖) = ∏ j, ‖M c (z (q j))‖ := by
    have he := prod_erase_mul univ (fun j => ‖M c (z (q j))‖) (mem_univ l)
    simpa [hl, M] using he
  have hbulk : (∏ j, ‖M c (z (q j))‖) / (∏ j, ‖M c (z (p j))‖) =
      Real.exp (∑ j, (ratioEll c (q j) - ratioEll c (alignedRoot N (2 * s + 1) hr p j))) *
        Real.exp ((∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) - ∑ j, ratioEll c (p j)) := by
    rw [← Real.exp_add, sum_sub_distrib]
    rw [sub_add_sub_cancel, Real.exp_sub, ratio_exp_sum_ell hc q, ratio_exp_sum_ell hc p]
  have hcorrection : Real.exp ((∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) - ∑ j, ratioEll c (p j)) =
      ‖M c (z (ratioPositiveRoot N h4 p first))‖⁻¹ *
        (‖M c (z (p ⟨s, hsBound⟩))‖ * (∏ j : Fin s, ‖M c (z (p ⟨j.val, by omega⟩))‖) ^ 2)⁻¹ *
          Real.exp (∑ j : Fin (N / 4 - s - 1), ratioMidpointLog c N h4 p s j) := by
    rw [ratio_odd_log_correction c s N h4 hr hn p hp,
      Real.exp_sub, Real.exp_sub, Real.exp_sub, ratio_exp_ell hc, ratio_exp_ell hc]
    simp only [two_mul, Real.exp_add, ratio_exp_sum_ell hc]
    ring
  rw [ratio_odd_eigenvalue_quotient hc hp hq l hl, hfullQ]
  congr 1
  rw [hbulk, hcorrection]
  have hm (x : ℝ) : ‖M c (z x)‖ ≠ 0 := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)
  have hprod (v : Fin s → ℝ) : (∏ j, ‖M c (z (v j))‖) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => hm (v j)
  field_simp [hN, hm, hprod]
  rfl

end PottsDiscontinuity.Bethe
