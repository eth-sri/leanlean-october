module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosure
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedGeometry
public import Mathlib.Algebra.Order.Field.GeomSum
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Measure.ParabolicDyadicAddress

open private HypoellipticAleksandrov.Parabolic.parabolicDyadicTruncate_le_succ_eq_truncate_parent from HypoellipticAleksandrov.Measure.ParabolicDyadicAddress


/-!
# Finite closed dyadic parabolic Morrey tails

This module telescopes the closed one-step dyadic projection estimate along a
finite addressed prefix.  It proves no infinite-chain or representative result.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

variable {d m n : Nat} (hmn : m <= n)




private theorem parabolicDyadicSourceBox_radius_rpow_truncate_mul
     (index : ParabolicDyadicIndex d n)
    (alpha : Real) :
    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius ^ alpha *
        ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (parabolicDyadicSourceBox index).radius ^ alpha := by
  let sharedTerm_d4fd6503fa := ((by norm_num : (0 : Real) ≤ 2))
  change ((2 : Real) ^ m)⁻¹ ^ alpha * ((2 : Real) ^ (-alpha)) ^ (n - m) =
    ((2 : Real) ^ n)⁻¹ ^ alpha
  have hbase (k : Nat) : ((2 : Real) ^ k)⁻¹ ^ alpha =
      (2 : Real) ^ (-(k : Real) * alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg sharedTerm_d4fd6503fa,
      ← Real.rpow_mul sharedTerm_d4fd6503fa]
  have hfactor : ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (2 : Real) ^ (-alpha * ((n - m : Nat) : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul sharedTerm_d4fd6503fa]
  rw [hbase m, hbase n, hfactor, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
  congr 1
  rw [Nat.cast_sub hmn]
  ring

variable (d : Nat)

private theorem parabolicMorreyDerivativeLpNorm_nonneg
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) : 0 <= parabolicMorreyDerivativeLpNorm d u := by
  unfold parabolicMorreyDerivativeLpNorm parabolicLpNorm parabolicELpNorm
  refine add_nonneg ENNReal.toReal_nonneg ?_
  refine Finset.sum_nonneg fun i _ => ?_
  refine Finset.sum_nonneg fun j _ => ?_
  exact ENNReal.toReal_nonneg

private theorem parabolicMorreyDyadicTruncateProjectionClosedFiniteTail
     (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (m n : Nat) (hmn : m <= n) (index : ParabolicDyadicIndex d n)
        (u : HypoellipticAleksandrov.Parabolic.ScalarField d),
        ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∀ z : TimeVelocity d,
          z ∈ parabolicClosedBox 1
              (parabolicDyadicSourceBox index).radius
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center ->
          |parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center
              (parabolicDyadicSourceBox index).radius u z -
            parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).baseTime
              (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).center
              (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius u z| <=
            C * (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius ^
                  parabolicMorreyExponent d *
              (∑ k ∈ Finset.range (n - m),
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) *
              parabolicMorreyDerivativeLpNorm d u := by
  let sharedTerm_1d8128c316 := ((2 : Real) ^ (-parabolicMorreyExponent d))
  obtain ⟨C, hCpos, hstep⟩ :=
    exists_parabolicMorreyDyadicChildProjectionClosedConst d hd
  refine ⟨C, hCpos, ?_⟩
  intro m n hmn index u hu huc z hz

  induction n, hmn using Nat.le_induction with
  | base =>
      simp [parabolicDyadicTruncate_self]
  | succ n hmn ih =>
      let parent := parabolicDyadicParent index
      let child  := index (Fin.last n)
      have hindex : index = parabolicDyadicChildIndex parent child := by
        exact (parabolicDyadicChildIndex_parent_last index).symm


      have htrunc : parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index =
          parabolicDyadicTruncate hmn parent := by
        exact _root_.HypoellipticAleksandrov.Parabolic.parabolicDyadicTruncate_le_succ_eq_truncate_parent hmn index


      have hstepNorm : |parabolicMorreyBoxAffineProjection
          (parabolicDyadicSourceBox index).baseTime
          (parabolicDyadicSourceBox index).center
          (parabolicDyadicSourceBox index).radius u z -
          parabolicMorreyBoxAffineProjection
          (parabolicDyadicSourceBox parent).baseTime
          (parabolicDyadicSourceBox parent).center
          (parabolicDyadicSourceBox parent).radius u z| <=
          C * (parabolicDyadicSourceBox parent).radius ^ parabolicMorreyExponent d *
            parabolicMorreyDerivativeLpNorm d u := by
        simpa only [hindex] using
          ((hstep n parent child u hu z (by simpa only [hindex] using hz)).trans
            (mul_le_mul_of_nonneg_left (parabolicMorreyDerivativeLpNormOn_le u _ (parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc))
              (mul_nonneg hCpos.le
                (Real.rpow_nonneg (parabolicDyadicSourceBox_radius_pos parent).le _))))
      have hparentRadius := parabolicDyadicSourceBox_radius_rpow_truncate_mul
        hmn parent (parabolicMorreyExponent d)

      rw [htrunc]
      rw [hindex]
      rw [Nat.succ_sub hmn, Finset.sum_range_succ]
      calc
        |parabolicMorreyBoxAffineProjection
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius u z -
          parabolicMorreyBoxAffineProjection
            (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).center
            (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius u z| <=
            |parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
                (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center
                (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius u z -
              parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox parent).baseTime
                (parabolicDyadicSourceBox parent).center
                (parabolicDyadicSourceBox parent).radius u z| +
              |parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox parent).baseTime
                (parabolicDyadicSourceBox parent).center
                (parabolicDyadicSourceBox parent).radius u z -
              parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).baseTime
                (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).center
                (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius u z| := by
              let sharedTerm_682310c607 := ((parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)))
              let sharedTerm_dc610ce455 := ((parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)))
              let sharedTerm_960fde2543 := (parabolicMorreyBoxAffineProjection (parabolicDyadicSourceBox parent).baseTime (parabolicDyadicSourceBox parent).center
                (parabolicDyadicSourceBox parent).radius u z)
              rw [show parabolicMorreyBoxAffineProjection
                    sharedTerm_dc610ce455.baseTime
                    sharedTerm_dc610ce455.center
                    sharedTerm_dc610ce455.radius u z -
                  parabolicMorreyBoxAffineProjection
                    sharedTerm_682310c607.baseTime
                    sharedTerm_682310c607.center
                    sharedTerm_682310c607.radius u z =
                  (parabolicMorreyBoxAffineProjection
                    sharedTerm_dc610ce455.baseTime
                    sharedTerm_dc610ce455.center
                    sharedTerm_dc610ce455.radius u z -
                    sharedTerm_960fde2543) +
                    (sharedTerm_960fde2543 -
                      parabolicMorreyBoxAffineProjection
                        sharedTerm_682310c607.baseTime
                        sharedTerm_682310c607.center
                        sharedTerm_682310c607.radius u z) by ring]
              exact abs_add_le _ _
        _ <= C * (parabolicDyadicSourceBox parent).radius ^ parabolicMorreyExponent d *
              parabolicMorreyDerivativeLpNorm d u +
            C * (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius ^
              parabolicMorreyExponent d *
              (∑ k ∈ Finset.range (n - m),
                (sharedTerm_1d8128c316) ^ k) *
              parabolicMorreyDerivativeLpNorm d u := add_le_add (by simpa only [hindex] using hstepNorm) (ih parent (parabolicDyadicClosedForwardBox_child_subset parent child (by
                      simpa only [hindex] using hz)))
        _ = C * (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius ^
              parabolicMorreyExponent d *
              ((∑ k ∈ Finset.range (n - m),
                (sharedTerm_1d8128c316) ^ k) +
                (sharedTerm_1d8128c316) ^ (n - m)) *
              parabolicMorreyDerivativeLpNorm d u := by
              rw [← hparentRadius]
              ring

/-- A finite closed dyadic address tail is bounded by the geometric Morrey tail. -/
theorem exists_parabolicMorreyDyadicAddressPrefixProjectionClosedTailConst
     (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (a b : ParabolicDyadicAddress d) (u : HypoellipticAleksandrov.Parabolic.ScalarField d),
        parabolicDyadicAddressPrefix a b ->
        ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∀ z : TimeVelocity d,
          z ∈ parabolicClosedBox 1
              (parabolicDyadicSourceBox b.2).radius
              (parabolicDyadicSourceBox b.2).baseTime
              (parabolicDyadicSourceBox b.2).center ->
          |parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox b.2).baseTime
              (parabolicDyadicSourceBox b.2).center
              (parabolicDyadicSourceBox b.2).radius u z -
            parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox a.2).baseTime
              (parabolicDyadicSourceBox a.2).center
              (parabolicDyadicSourceBox a.2).radius u z| <=
            C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
              (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ *
              parabolicMorreyDerivativeLpNorm d u := by
  let sharedTerm_3a8b81e6f8 := ((2 : Real) ^ (-parabolicMorreyExponent d))
  obtain ⟨C, hCpos, hfinite⟩ :=
    parabolicMorreyDyadicTruncateProjectionClosedFiniteTail d hd
  refine ⟨C, hCpos, ?_⟩
  intro a b u hab hu huc z hz
  rcases hab with ⟨hmn, htruncate⟩
  have hfinite' := hfinite a.1 b.1 hmn b.2 u hu huc z hz
  rw [htruncate] at hfinite'


  have hqlt : sharedTerm_3a8b81e6f8 < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr (by
        unfold parabolicMorreyExponent

        positivity))


  have hclear (N : Nat) :
      (∑ k ∈ Finset.range N, (sharedTerm_3a8b81e6f8) ^ k) *
        (1 - sharedTerm_3a8b81e6f8) =
      1 - (sharedTerm_3a8b81e6f8) ^ N := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        calc
          ((∑ k ∈ Finset.range N,
              (sharedTerm_3a8b81e6f8) ^ k) +
              (sharedTerm_3a8b81e6f8) ^ N) *
              (1 - sharedTerm_3a8b81e6f8) =
              (∑ k ∈ Finset.range N,
                (sharedTerm_3a8b81e6f8) ^ k) *
                (1 - sharedTerm_3a8b81e6f8) +
                (sharedTerm_3a8b81e6f8) ^ N *
                  (1 - sharedTerm_3a8b81e6f8) := by ring
          _ = (1 - (sharedTerm_3a8b81e6f8) ^ N) +
                (sharedTerm_3a8b81e6f8) ^ N *
                  (1 - sharedTerm_3a8b81e6f8) := by rw [ih]
          _ = 1 - (sharedTerm_3a8b81e6f8) ^ (N + 1) := by
                rw [pow_succ]
                ring

  have hraw := parabolicMorreyDerivativeLpNorm_nonneg d u

  calc
    _ <= C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
        (∑ k ∈ Finset.range (b.1 - a.1),
          (sharedTerm_3a8b81e6f8) ^ k) *
        parabolicMorreyDerivativeLpNorm d u := hfinite'
    _ = (C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
        parabolicMorreyDerivativeLpNorm d u) *
        (∑ k ∈ Finset.range (b.1 - a.1),
          (sharedTerm_3a8b81e6f8) ^ k) := by ring
    _ <= (C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
        parabolicMorreyDerivativeLpNorm d u) *
        (1 - sharedTerm_3a8b81e6f8)⁻¹ :=
        mul_le_mul_of_nonneg_left (by
            rw [inv_eq_one_div]
            apply (le_div_iff₀ (show 0 < 1 - sharedTerm_3a8b81e6f8 from sub_pos.mpr hqlt)).mpr
            rw [hclear]
            linarith [pow_nonneg (show 0 <= sharedTerm_3a8b81e6f8 from (Real.rpow_pos_of_pos (by norm_num) _).le) (b.1 - a.1)]) (mul_nonneg
              (mul_nonneg hCpos.le (Real.rpow_nonneg
                (parabolicDyadicSourceBox_radius_pos a.2).le _)) hraw)
    _ = _ := by ring

end HypoellipticAleksandrov.Parabolic
