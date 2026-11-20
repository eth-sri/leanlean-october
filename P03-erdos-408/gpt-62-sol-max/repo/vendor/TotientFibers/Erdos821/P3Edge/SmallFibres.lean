module

public import Erdos821.P3.SmallPrefix
public import Erdos821.P3Edge.SmallDamp
public import Erdos821.P3Edge.SmallFresh
public import Erdos821.P3Edge.TransferBounds

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {g : P.Group}

/-- Per-small-group damped weight. -/
def smallGroupWeight (F : FixedData) (J : ℕ) (g : P.SmallGroup)
    (y : (p : P.Prime g.val) → ZMod p.val) : ℝ :=
  (P.V g.val) ^ (-(F.ell : ℤ)) *
    F.q ^ ((((Finset.univ.filter (fun p : P.Prime g.val => y p = 0)).card : ℝ) -
      ((J : ℝ) + (F.ell : ℝ))) / 2)

lemma smallGroupWeight_nonneg (F : FixedData) (J : ℕ) (g : P.SmallGroup)
    (hV : 0 < P.V g.val) (y : (p : P.Prime g.val) → ZMod p.val) :
    0 ≤ smallGroupWeight F J g y := by
  unfold smallGroupWeight
  exact mul_nonneg (zpow_nonneg hV.le _) (Real.rpow_nonneg F.q_pos.le _)

/-- The product of `smallGroupWeight` over all small groups equals
`smallTargetFactor F * smallDamping F J y`. -/
lemma prod_smallGroupWeight_eq (F : FixedData) (J : ℕ) (y : P.SmallResidues) :
    (∏ g : P.SmallGroup, smallGroupWeight F J g (y g)) =
      smallTargetFactor (P := P) F * smallDamping F J y := by
  unfold smallGroupWeight smallTargetFactor smallDamping smallOmega
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos F.q_pos]
  congr 2
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Nat.cast_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- Unconditional bound on the small-group fiber sum for one small group `g`. -/
lemma smallPrefixFibre_sum_le (F : FixedData) (J m : ℕ) (Csmall0 : ℝ)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0)
    (g : P.SmallGroup) (hVlo : F.vMin ≤ P.V g.val)
    (y : (p : P.Prime g.val) → ZMod p.val) (d : Fin J → P.Prime g.val) :
    (∑ b : Fin (J + F.ell) → P.Prime g.val,
      if b ∈ smallPrefixFibre J F.ell y d then smallGroupWeight F J g y else 0) ≤
      max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0) := by
  classical
  have hsum : (∑ b : Fin (J + F.ell) → P.Prime g.val,
      if b ∈ smallPrefixFibre J F.ell y d then smallGroupWeight F J g y else 0) =
      ((smallPrefixFibre J F.ell y d).card : ℝ) * smallGroupWeight F J g y := by
    rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  rcases Finset.eq_empty_or_nonempty (smallPrefixFibre J F.ell y d) with hemp | hne
  · rw [hemp, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact le_trans zero_le_one (le_max_left _ _)
  · obtain ⟨hd, hy, hZ⟩ := smallPrefixFibre_nonempty J F.ell y d hne
    set Z := (Finset.univ.filter (fun p : P.Prime g.val => y p = 0)).card
    have hcard_R : ((smallPrefixFibre J F.ell y d).card : ℝ) ≤ ((Z - J : ℕ) : ℝ) ^ F.ell :=
      le_trans (Nat.cast_le.mpr (smallPrefixFibre_card J F.ell y d hd hy))
        (descFactorial_le_pow (Z - J) F.ell)
    have hY : F.ell ≤ Z - J := by omega
    have hexp_eq : ((Z : ℝ) - ((J : ℝ) + (F.ell : ℝ))) / 2 =
        ((((Z - J) - F.ell : ℕ) : ℝ) / 2) := by
      have h1 : (Z - J) - F.ell = Z - (J + F.ell) := Nat.sub_sub Z J F.ell
      rw [h1, Nat.cast_sub hZ, Nat.cast_add]
    have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hVlo
    have hVinv : (P.V g.val) ^ (-(F.ell : ℤ)) ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) :=
      Vinv_pow_le F.vMin_pos (P.V g.val) hVlo F.ell (Nat.le_add_right _ _)
    have hdamp : ((Z - J : ℕ) : ℝ) ^ F.ell *
        F.q ^ ((((Z : ℝ) - ((J : ℝ) + (F.ell : ℝ))) / 2)) ≤ Csmall0 := by
      rw [hexp_eq]
      exact hCsmall0 (Z - J) hY
    have hwg_nn : 0 ≤ smallGroupWeight F J g y := smallGroupWeight_nonneg F J g hVpos y
    calc ((smallPrefixFibre J F.ell y d).card : ℝ) * smallGroupWeight F J g y
        ≤ ((Z - J : ℕ) : ℝ) ^ F.ell * smallGroupWeight F J g y :=
          mul_le_mul_of_nonneg_right hcard_R hwg_nn
      _ = (P.V g.val) ^ (-(F.ell : ℤ)) *
          (((Z - J : ℕ) : ℝ) ^ F.ell *
            F.q ^ (((Z : ℝ) - ((J : ℝ) + (F.ell : ℝ))) / 2)) := by
          unfold smallGroupWeight
          ring
      _ ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0 := by
          apply mul_le_mul hVinv hdamp
          · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg F.q_pos.le _)
          · exact le_trans zero_le_one (le_max_left _ _)
      _ ≤ max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0) := le_max_right _ _

end Erdos821.P3Edge
