module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointSelector
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep
public import Mathlib.Algebra.Order.Field.GeomSum
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedTail
import all HypoellipticAleksandrov.Parabolic.ScalingMeasure

open private HypoellipticAleksandrov.Parabolic.parabolicDyadicSourceBox_radius_rpow_truncate_mul from HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedTail
open private HypoellipticAleksandrov.Parabolic.parabolicExponent_toReal from HypoellipticAleksandrov.Parabolic.ScalingMeasure
open private HypoellipticAleksandrov.Parabolic.parabolicMorreyDerivativeLpNorm_nonneg from HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedTail


/-!
# Finite weighted dyadic slope tails and a root bound

This module records two finite coefficient estimates for the parabolic Morrey
program.  The first telescopes the velocity slopes along the selected dyadic
chain with its terminal radius.  The second bounds the root coefficients by
the full smooth-jet norm.  Neither result asserts slope convergence or defines
a limiting representative.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

private theorem parabolicDyadicParent_indexContaining_succ
    (d : Nat) (z : TimeVelocity d)
    (hz : z ∈ parabolicDyadicReferenceCell d) (n : Nat) :
    parabolicDyadicParent (parabolicDyadicIndexContaining d z hz (n + 1)) =
      parabolicDyadicIndexContaining d z hz n := by
  rcases parabolicDyadicAddressContaining_prefix d z hz (Nat.le_succ n) with
    ⟨h, hprefix⟩
  assumption







private theorem finite_radius_weighted_slope_tail
    {d : Nat} (C alpha D q : Real) (r : Nat -> Real) (b : Nat -> Fin d -> Real)
    (_hC : 0 < C) (_hD : 0 <= D) (hr : ∀ n, 0 < r n)
    (hhalf : ∀ n, r (n + 1) = r n / 2)
    (hscale : ∀ n, r n ^ alpha * (2 : Real) ^ (-alpha) = r (n + 1) ^ alpha)
    (hq : q = (2 : Real) ^ (-(1 - alpha)))
    (hstep : ∀ n, r (n + 1) * ∑ i : Fin d, |b (n + 1) i - b n i| <=
      C * r n ^ alpha * D) :
    ∀ n : Nat,
      r n * ∑ i : Fin d, |b n i - b 0 i| <=
        ((2 : Real) ^ alpha * C) * r n ^ alpha *
          (∑ k ∈ Finset.range n, q ^ k) * D := by
  let sharedTerm_1615437231 := ((2 : Real) ^ alpha * C)
  let sharedTerm_205ee4bf0a := ((2 : Real) ^ (-alpha))
  let sharedTerm_b6f8dd2d59 := (Real.rpow_add (by norm_num : (0 : Real) < 2))
  have htwo : (2 : Real) ^ alpha * sharedTerm_205ee4bf0a = 1 := by
    rw [← sharedTerm_b6f8dd2d59]
    rw [show alpha + -alpha = 0 by ring]
    simp
  have hweight : (1 / 2 : Real) * (2 : Real) ^ alpha = q := by
    rw [hq, show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num,
      ← Real.rpow_neg_one]
    rw [← sharedTerm_b6f8dd2d59]
    congr 1
    ring
  have hgeom : ∀ n : Nat,
      1 + q * (∑ k ∈ Finset.range n, q ^ k) =
        ∑ k ∈ Finset.range (n + 1), q ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
        rw [← ih]
        ring
  intro n
  induction n with
  | zero => simp
  | succ n ih =>



      have hCscale : C * r n ^ alpha =
          (sharedTerm_1615437231) * r (n + 1) ^ alpha := by
        calc
          C * r n ^ alpha = C * r n ^ alpha * 1 := by ring
          _ = C * r n ^ alpha *
              ((2 : Real) ^ alpha * sharedTerm_205ee4bf0a) := by rw [htwo, mul_one]
          _ = (sharedTerm_1615437231) *
              (r n ^ alpha * sharedTerm_205ee4bf0a) := by ring
          _ = (sharedTerm_1615437231) * r (n + 1) ^ alpha := by rw [hscale n]
      calc
        r (n + 1) * ∑ i : Fin d, |b (n + 1) i - b 0 i| <=
            r (n + 1) * ∑ i : Fin d, |b (n + 1) i - b n i| +
              r (n + 1) * ∑ i : Fin d, |b n i - b 0 i| := (by
                  calc
                    r (n + 1) * ∑ i : Fin d, |b (n + 1) i - b 0 i| <=
                        r (n + 1) *
                          (∑ i : Fin d, |b (n + 1) i - b n i| +
                            ∑ i : Fin d, |b n i - b 0 i|) :=
                      mul_le_mul_of_nonneg_left (by
                          rw [← Finset.sum_add_distrib]
                          refine Finset.sum_le_sum fun i _ => ?_
                          rw [show b (n + 1) i - b 0 i =
                              (b (n + 1) i - b n i) + (b n i - b 0 i) by ring]
                          exact abs_add_le _ _) (hr (n + 1)).le
                    _ = _ := by ring)
        _ <= C * r n ^ alpha * D +
            (1 / 2 : Real) *
              ((sharedTerm_1615437231) * r n ^ alpha *
                (∑ k ∈ Finset.range n, q ^ k) * D) :=
          add_le_add (hstep n) (by
              rw [hhalf n]
              calc
                (r n / 2) * ∑ i : Fin d, |b n i - b 0 i| =
                    (1 / 2 : Real) *
                      (r n * ∑ i : Fin d, |b n i - b 0 i|) := by ring
                _ <= (1 / 2 : Real) *
                    ((sharedTerm_1615437231) * r n ^ alpha *
                      (∑ k ∈ Finset.range n, q ^ k) * D) :=
                  mul_le_mul_of_nonneg_left ih (by norm_num))
        _ = C * r n ^ alpha *
            (1 + ((1 / 2 : Real) * (2 : Real) ^ alpha) *
              (∑ k ∈ Finset.range n, q ^ k)) * D := by ring
        _ = C * r n ^ alpha *
            (1 + q * (∑ k ∈ Finset.range n, q ^ k)) * D := by rw [hweight]
        _ = C * r n ^ alpha *
            (∑ k ∈ Finset.range (n + 1), q ^ k) * D := by rw [hgeom n]
        _ = (sharedTerm_1615437231) * r (n + 1) ^ alpha *
            (∑ k ∈ Finset.range (n + 1), q ^ k) * D := by rw [hCscale]

private theorem parabolicELpNorm_le_parabolicSmoothJetELpNorm
    (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    parabolicELpNorm d u <= parabolicSmoothJetELpNorm d u := (id
  (Trans.trans (Trans.trans (le_add_of_nonneg_right bot_le) (le_add_of_nonneg_right bot_le))
    (le_add_of_nonneg_right bot_le)))

private theorem parabolicLpNorm_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicLpNorm d u <= parabolicSmoothJetLpNorm d u := by
  unfold parabolicLpNorm parabolicSmoothJetLpNorm
  exact ENNReal.toReal_mono (parabolicSmoothJetELpNorm_ne_top hu)
    (parabolicELpNorm_le_parabolicSmoothJetELpNorm d u)




private theorem parabolicLpMeanNormOn_root_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicLpMeanNormOn d u (parabolicBox 1 1 0 (0 ))
        (memLp_parabolicNormalizedVolumeOn_of_memLp
          (volume_parabolicMorreyBox_pos 0 0 (by norm_num))
          (hu.1.mono_measure Measure.restrict_le_self)) <=
      parabolicSmoothJetLpNorm d u := by
  let Q  := parabolicBox 1 1 0 (0 : PDE.Vec d)
  let hraw : MemLp u (parabolicExponent d) (volume.restrict Q) :=
    hu.1.mono_measure Measure.restrict_le_self
  let hmean  :=
    memLp_parabolicNormalizedVolumeOn_of_memLp
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num)) hraw



  change parabolicLpMeanNormOn d u Q hmean <= parabolicSmoothJetLpNorm d u
  exact (show parabolicLpMeanNormOn d u Q hmean <= parabolicLpNorm d u by
      rw [parabolicLpMeanNormOn_eq_volume_toReal_inv_rpow_mul_parabolicLpNormOn
        (volume_parabolicMorreyBox_pos 0 0 (by norm_num))
        (volume_parabolicMorreyBox_lt_top 0 0 (by norm_num)) u hraw hmean]
      calc
        ((volume Q).toReal)⁻¹ ^ (1 / parabolicExponent d).toReal *
            parabolicLpNormOn d u Q <= 1 * parabolicLpNormOn d u Q :=
          mul_le_mul_of_nonneg_right (by
              rw [show (volume Q).toReal = (2 : Real) ^ d by
                simpa only [Q, mul_one, one_pow] using
                  volume_parabolicMorreyBox_toReal (d := d) 0 (0 )
                    (r := 1) (by norm_num)]
              apply Real.rpow_le_one
              · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
              · bound
              · positivity) ENNReal.toReal_nonneg
        _ <= 1 * parabolicLpNorm d u :=
          mul_le_mul_of_nonneg_left (parabolicLpNormOn_le_parabolicLpNorm u Q hu.1) (by norm_num)
        _ = parabolicLpNorm d u := by ring).trans (parabolicLpNorm_le_parabolicSmoothJetLpNorm hu)

variable (d : Nat)

/-- A finite selected dyadic chain has a radius-weighted velocity-slope tail.
This is finite only; it asserts neither convergence nor a limiting slope. -/
theorem exists_parabolicMorreyDyadicContainingRadiusWeightedSlopeTailConst
     (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (hz : z ∈ parabolicDyadicReferenceCell d)
        (u : HypoellipticAleksandrov.Parabolic.ScalarField d),
        ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∀ n : Nat,
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).radius *
            ∑ i : Fin d,
              |parabolicMorreyBoxVelocitySlope
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz n).2).baseTime
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz n).2).center
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz n).2).radius u i -
                parabolicMorreyBoxVelocitySlope
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz 0).2).center
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz 0).2).radius u i| <=
            C *
              (parabolicDyadicSourceBox
                (parabolicDyadicAddressContaining d z hz n).2).radius ^
                parabolicMorreyExponent d *
              (∑ k ∈ Finset.range n,
                ((2 : Real) ^ (-(1 - parabolicMorreyExponent d))) ^ k) *
              parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C, hCpos, hchild⟩ := exists_parabolicMorreyDyadicChildAffineJetConst d hd
  refine ⟨(2 : Real) ^ parabolicMorreyExponent d * C, by positivity, ?_⟩
  intro z hz u hu huc n
  let r  := fun k =>
    (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).radius
  let b  := fun k i =>
    parabolicMorreyBoxVelocitySlope
      (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).baseTime
      (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).center
      (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).radius u i
  let D : Real := parabolicMorreyDerivativeLpNorm d u

  have hr  := fun k =>
    parabolicDyadicSourceBox_radius_pos (parabolicDyadicAddressContaining d z hz k).2



  simpa only [r, b, D] using
    finite_radius_weighted_slope_tail C (parabolicMorreyExponent d) D
      ((2 : Real) ^ (-(1 - parabolicMorreyExponent d))) r b hCpos
      (_root_.HypoellipticAleksandrov.Parabolic.parabolicMorreyDerivativeLpNorm_nonneg d u) hr (by
          intro k
          let parent := parabolicDyadicIndexContaining d z hz k
          let child  :=
            parabolicDyadicIndexContaining d z hz (k + 1) (Fin.last k)
          have hparent := parabolicDyadicParent_indexContaining_succ d z hz k

          calc
            r (k + 1) = (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex parent child)).radius := rfl
            _ = (parabolicDyadicSourceBox parent).radius / 2 :=
              parabolicDyadicSourceBox_radius_childIndex parent child
            _ = r k / 2 := rfl) (by
          intro k
          let index := parabolicDyadicIndexContaining d z hz (k + 1)
          have htrunc : parabolicDyadicTruncate (Nat.le_succ k) index =
              parabolicDyadicIndexContaining d z hz k := by

            calc
              parabolicDyadicTruncate (Nat.le_succ k) index =
                  parabolicDyadicParent index := rfl
              _ = parabolicDyadicIndexContaining d z hz k := (parabolicDyadicParent_indexContaining_succ d z hz k)
          simpa only [r, parabolicDyadicAddressContaining, index, htrunc,
            Nat.succ_sub (Nat.le_refl k), Nat.sub_self, pow_one] using
            (_root_.HypoellipticAleksandrov.Parabolic.parabolicDyadicSourceBox_radius_rpow_truncate_mul (Nat.le_succ k) index
              (parabolicMorreyExponent d))) rfl (by
                  intro k
                  let parent := parabolicDyadicIndexContaining d z hz k
                  let child  :=
                    parabolicDyadicIndexContaining d z hz (k + 1) (Fin.last k)
                  have hparent := parabolicDyadicParent_indexContaining_succ d z hz k
                  have hindex : parabolicDyadicIndexContaining d z hz (k + 1) =
                      parabolicDyadicChildIndex parent child := by
                    calc
                      parabolicDyadicIndexContaining d z hz (k + 1) =
                          parabolicDyadicChildIndex
                            (parabolicDyadicParent
                              (parabolicDyadicIndexContaining d z hz (k + 1))) child := (parabolicDyadicChildIndex_parent_last
                                (parabolicDyadicIndexContaining d z hz (k + 1))).symm
                      _ = parabolicDyadicChildIndex parent child := by rw [hparent]
                  have hraw := hchild k parent child u hu

                  have hnorm := parabolicMorreyDerivativeLpNormOn_le u
                    (parabolicBox 1 (parabolicDyadicSourceBox parent).radius
                      (parabolicDyadicSourceBox parent).baseTime
                      (parabolicDyadicSourceBox parent).center) (parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc)
                  have hglobal  := (show (parabolicDyadicSourceBox
                        (parabolicDyadicChildIndex parent child)).radius *
                        ∑ i : Fin d,
                          |parabolicMorreyBoxVelocitySlope
                              (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).baseTime
                              (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).center
                              (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).radius u i -
                            parabolicMorreyBoxVelocitySlope
                              (parabolicDyadicSourceBox parent).baseTime
                              (parabolicDyadicSourceBox parent).center
                              (parabolicDyadicSourceBox parent).radius u i| <=
                        C * (parabolicDyadicSourceBox parent).radius ^ parabolicMorreyExponent d *
                          parabolicMorreyDerivativeLpNormOn d u
                            (parabolicBox 1 (parabolicDyadicSourceBox parent).radius
                              (parabolicDyadicSourceBox parent).baseTime
                              (parabolicDyadicSourceBox parent).center) by
                      calc
                        _ <= |parabolicMorreyBoxAverage
                              (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).baseTime
                              (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).center
                              (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).radius u -
                            parabolicMorreyBoxAffineProjection
                              (parabolicDyadicSourceBox parent).baseTime
                              (parabolicDyadicSourceBox parent).center
                              (parabolicDyadicSourceBox parent).radius u
                              ((parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).baseTime,
                               (parabolicDyadicSourceBox
                                (parabolicDyadicChildIndex parent child)).center)| +
                            (parabolicDyadicSourceBox
                              (parabolicDyadicChildIndex parent child)).radius *
                              ∑ i : Fin d,
                                |parabolicMorreyBoxVelocitySlope
                                    (parabolicDyadicSourceBox
                                      (parabolicDyadicChildIndex parent child)).baseTime
                                    (parabolicDyadicSourceBox
                                      (parabolicDyadicChildIndex parent child)).center
                                    (parabolicDyadicSourceBox
                                      (parabolicDyadicChildIndex parent child)).radius u i -
                                  parabolicMorreyBoxVelocitySlope
                                    (parabolicDyadicSourceBox parent).baseTime
                                    (parabolicDyadicSourceBox parent).center
                                    (parabolicDyadicSourceBox parent).radius u i| :=
                          le_add_of_nonneg_left (abs_nonneg _)
                        _ <= _ := hraw).trans (mul_le_mul_of_nonneg_left hnorm
                      (mul_nonneg hCpos.le (Real.rpow_nonneg
                        (parabolicDyadicSourceBox_radius_pos parent).le _)))
                  simpa only [r, b, D, parabolicDyadicAddressContaining, hindex, hparent] using hglobal) n

/-- The root moment-projection coefficients are bounded by the full selected
smooth-jet norm. -/
theorem parabolicMorreyRootAffineCoefficient_le_parabolicSmoothJetLpNorm
     (u : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hu : ContDiff Real 2 u) (huc : HasCompactSupport u) :
    |parabolicMorreyBoxAverage 0 (0 : PDE.Vec d) 1 u| +
        ∑ i : Fin d,
          |parabolicMorreyBoxVelocitySlope 0 (0 : PDE.Vec d) 1 u i| <=
      (1 + 3 * (d : Real)) * parabolicSmoothJetLpNorm d u := by
  let sharedTerm_5d7d8743be := (∑ i : Fin d, |parabolicMorreyBoxVelocitySlope 0 (0 : PDE.Vec d) 1 u i|)
  let sharedTerm_b1163838b6 := (|parabolicMorreyBoxAverage 0 (0 : PDE.Vec d) 1 u|)
  have huJet  :=
    parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
  have hmean : MemLp u (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 1 0 (0 ))) :=
    memLp_parabolicNormalizedVolumeOn_of_memLp
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num))
      (huJet.1.mono_measure Measure.restrict_le_self)
  have hcoefficient := parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
    0 (0 : PDE.Vec d) (by norm_num : (0 : Real) < 1) u hmean
  calc
    sharedTerm_b1163838b6 +
        sharedTerm_5d7d8743be =
        sharedTerm_b1163838b6 +
          1 * sharedTerm_5d7d8743be := by ring
    _ <= (1 + 3 * (d : Real)) *
        parabolicLpMeanNormOn d u _ hmean :=
      hcoefficient
    _ <= (1 + 3 * (d : Real)) * parabolicSmoothJetLpNorm d u :=
      mul_le_mul_of_nonneg_left
        (parabolicLpMeanNormOn_root_le_parabolicSmoothJetLpNorm huJet) (by positivity)

end HypoellipticAleksandrov.Parabolic
