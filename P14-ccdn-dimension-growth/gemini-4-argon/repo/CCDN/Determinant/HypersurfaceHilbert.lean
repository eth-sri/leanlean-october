/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SingularTangent

/-! Binomial profiles for hypersurface local layers in all dimensions.
The cumulative bound retains the leading coefficient μ/n! needed for the
sharp determinant exponent. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The degree-k Hilbert function of a homogeneous hypersurface of degree μ
in n+1 variables, including the degrees below μ. -/
def hypersurfaceLayerBound (n μ k : ℕ) : ℕ :=
  (n + k).choose n - if μ ≤ k then (n + (k - μ)).choose n else 0

/-- The cumulative local Hilbert function has this bound. -/
theorem originLayer_cumulative_le {K : Type*} [Field K] {n μ : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K)
    (hf : f ∈ idealOfVars (Fin (n + 2)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) (k : ℕ) :
    (∑ j : Fin (k + 1), Module.finrank K (originLayer f j.val)) ≤
      μ * (n + k + 1).choose (n + 1) := by
  /- For positive degree `μ`, the Hilbert function `hypersurfaceLayerBound n μ` takes the value `1`
  in degree zero. -/
  /- Recursion for the Hilbert function of a hypersurface: `hypersurfaceLayerBound (n + 1) (μ + 1)`
  in degree `k + 1` equals `(n + (k + 1)).choose n` plus `hypersurfaceLayerBound (n + 1) μ` in degree
  `k`. -/
  /- A uniform shifted bound with the exact leading coefficient. The dimension
  is n+1; unlike the sharper error in CCDN 2.1, the lower terms here may contain μ. -/
  have hlayer (μ k : ℕ) : hypersurfaceLayerBound (n + 1) μ k ≤ μ * (n + k).choose n := by
    induction μ generalizing k with
    | zero => simp [hypersurfaceLayerBound]
    | succ μ ih =>
      cases k with
      | zero => simp [hypersurfaceLayerBound]
      | succ k =>
        have hrec : hypersurfaceLayerBound (n + 1) (μ + 1) (k + 1) =
            (n + (k + 1)).choose n + hypersurfaceLayerBound (n + 1) μ k := by
          have hchoose : (n + 1 + (k + 1)).choose (n + 1) =
              (n + (k + 1)).choose n + (n + 1 + k).choose (n + 1) := by
            rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 by omega, Nat.choose_succ_succ',
              show n + 1 + k = n + (k + 1) by omega]
          unfold hypersurfaceLayerBound; rw [hchoose]
          by_cases hk : μ ≤ k
          · rw [ite_eq_left hk, ite_eq_left (by omega : μ + 1 ≤ k + 1), Nat.add_sub_add_right]
            have := Nat.choose_le_choose (n + 1) (show n + 1 + (k - μ) ≤ n + 1 + k by omega); omega
          · rw [ite_eq_right hk, ite_eq_right (by omega : ¬ μ + 1 ≤ k + 1)]; omega
        have h := (ih k).trans (Nat.mul_le_mul_left μ
          (Nat.choose_le_choose n (show n + k ≤ n + (k + 1) by omega)))
        rw [hrec]; nlinarith
  have hle {m : ℕ} (g : MvPolynomial (Fin (m + 1)) K)
      (hg : g ∈ idealOfVars (Fin (m + 1)) K ^ μ)
      (hμg : homogeneousComponent μ g ≠ 0) (j : ℕ) :
      Module.finrank K (originLayer g j) ≤ hypersurfaceLayerBound m μ j := by
    unfold hypersurfaceLayerBound
    split_ifs with hk
    · have h := originLayer_hilbert_bound g hg hμg hk
      rw [Nat.choose_symm_add (a := m), Nat.choose_symm_add (a := m)]
      omega
    · rw [Nat.sub_zero, Nat.choose_symm_add]
      exact originLayer_finrank_le g j
  calc
    _ ≤ ∑ j : Fin (k + 1), hypersurfaceLayerBound (n + 1) μ j.val :=
      Finset.sum_le_sum fun j _ => hle f hf hμ j.val
    _ ≤ ∑ j : Fin (k + 1), μ * (n + j.val).choose n :=
      Finset.sum_le_sum fun j _ => hlayer μ j.val
    _ = μ * (n + k + 1).choose (n + 1) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (n + j).choose n)]
      simp_rw [Nat.add_comm n]
      rw [Nat.sum_range_add_choose, Nat.add_comm 1 n]

end
end CCDN
