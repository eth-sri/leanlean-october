module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointSelector
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep
public import Mathlib.Algebra.Order.Field.GeomSum
public import HypoellipticAleksandrov.Measure.DensityNearOneMeasure

/-!
# Finite weighted dyadic slope tails and a root bound

This module records two finite coefficient estimates for the parabolic Morrey
program.  The first telescopes the velocity slopes along the selected dyadic
chain with its terminal radius.  The second bounds the root coefficients by
the full smooth-jet norm.  Neither result asserts slope convergence or defines
a limiting representative.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

variable (d : Nat) (u : TimeVelocity d -> Real)

private theorem parabolicDyadicParent_indexContaining_succ
     (z : TimeVelocity d)
    (hz : z ∈ parabolicDyadicReferenceCell d) (n : Nat) :
    parabolicDyadicParent (parabolicDyadicIndexContaining d z hz (n + 1)) =
      parabolicDyadicIndexContaining d z hz n := by
  rcases parabolicDyadicAddressContaining_prefix d z hz (Nat.le_succ n) with
    ⟨h, hprefix⟩
  have hparent :
      parabolicDyadicParent (parabolicDyadicIndexContaining d z hz _) =
        parabolicDyadicTruncate (Nat.le_succ n)
          (parabolicDyadicIndexContaining d z hz (n + 1)) := by
    funext j
    apply congrArg _
    exact Fin.ext (by rfl)
  exact hparent.trans hprefix

theorem parabolicDyadicSourceBox_radius_rpow_truncate_mul
    {d m n : Nat} (hmn : m <= n) (index : ParabolicDyadicIndex d n)
    (alpha : Real) :
    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius ^ alpha *
        ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (parabolicDyadicSourceBox index).radius ^ alpha := by
  change ((2 : Real) ^ m)⁻¹ ^ alpha * ((2) ^ (-alpha)) ^ (n - m) =
    ((2 : Real) ^ n)⁻¹ ^ alpha
  have hbase (k : Nat) : ((2) ^ k)⁻¹ ^ alpha =
      (2 : Real) ^ (-k * alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num),
      ← Real.rpow_mul (by norm_num)]
  have hfactor : ((2) ^ (-alpha)) ^ (n - m) =
      (2 : Real) ^ (-alpha * ((n - m : Nat))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [hbase, hbase, hfactor, ← Real.rpow_add (by norm_num), Nat.cast_sub hmn]
  ring

private theorem parabolicMorreyDerivativeLpNorm_nonneg  : 0 <= parabolicMorreyDerivativeLpNorm d u := by
  refine add_nonneg ENNReal.toReal_nonneg ?_
  refine Finset.sum_nonneg fun i _ => ?_
  refine Finset.sum_nonneg fun j _ => ?_
  exact ENNReal.toReal_nonneg

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
  have htwo : (2) ^ alpha * (2 : Real) ^ (-alpha) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have hweight : (1 / 2) * (2) ^ alpha = q := by
    rw [hq, show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num,
      ← Real.rpow_neg_one]
    rw [← Real.rpow_add (by norm_num)]
    ring
  have hgeom : ∀ n : Nat,
      1 + q * (∑ k ∈ Finset.range n, q ^ k) =
        ∑ k ∈ Finset.range (n + 1), q ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
        ring
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have htriangle :
          ∑ i : Fin d, |b (n + 1) i - b 0 i| <=
            ∑ i : Fin d, |b (n + 1) i - b n i| +
              ∑ i : Fin d, |b n i - b 0 i| := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [show b (n + 1) i - b 0 i =
            (b (n + 1) i - b n i) + (b n i - b 0 i) by ring]
        exact abs_add_le _ _
      have hsplit :
          r (n + 1) * ∑ i : Fin d, |b (n + 1) i - b 0 i| <=
            r (n + 1) * ∑ i : Fin d, |b (n + 1) i - b n i| +
              r (n + 1) * ∑ i : Fin d, |b n i - b 0 i| := by
        calc
          r _ * ∑ i : Fin d, |b _ i - b 0 i| <=
              r _ *
                (∑ i : Fin d, |b _ i - b n i| +
                  ∑ i : Fin d, |b n i - b 0 i|) :=
            mul_le_mul_of_nonneg_left htriangle (hr _).le
          _ = _ := by ring
      have hprevious :
          r (n + 1) * ∑ i : Fin d, |b n i - b 0 i| <=
            (1 / 2 : Real) *
              (((2 : Real) ^ alpha * C) * r n ^ alpha *
                (∑ k ∈ Finset.range n, q ^ k) * D) := by
        rw [hhalf]
        calc
          (r n / 2) * ∑ i : Fin d, |b n i - b 0 i| =
              (1 / 2) *
                (r n * ∑ i : Fin d, |b n i - b 0 i|) := by ring
          _ <= (1 / 2) *
              (((2) ^ alpha * C) * r n ^ alpha *
                (∑ k ∈ Finset.range n, q ^ k) * D) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
      have hCscale : C * r n ^ alpha =
          ((2 : Real) ^ alpha * C) * r (n + 1) ^ alpha := by
        calc
          C * r n ^ alpha = C * r n ^ alpha * 1 := by ring
          _ = C * r n ^ alpha *
              ((2) ^ alpha * (2) ^ (-alpha)) := by rw [htwo]
          _ = ((2) ^ alpha * C) *
              (r n ^ alpha * (2) ^ (-alpha)) := by ring
          _ = ((2) ^ alpha * C) * r _ ^ alpha := by rw [hscale]
      calc
        r _ * ∑ i : Fin d, |b _ i - b 0 i| <=
            r _ * ∑ i : Fin d, |b _ i - b n i| +
              r _ * ∑ i : Fin d, |b n i - b 0 i| := hsplit
        _ <= C * r n ^ alpha * D +
            (1 / 2) *
              (((2) ^ alpha * C) * r n ^ alpha *
                (∑ k ∈ Finset.range n, q ^ k) * D) :=
          add_le_add (hstep n) hprevious
        _ = C * r n ^ alpha *
            (1 + ((1 / 2) * (2) ^ alpha) *
              (∑ k ∈ Finset.range n, q ^ k)) * D := by ring
        _ = C * r n ^ alpha *
            (1 + q * (∑ k ∈ Finset.range n, q ^ k)) * D := by rw [hweight]
        _ = C * r n ^ alpha *
            (∑ k ∈ Finset.range _, q ^ k) * D := by rw [hgeom]
        _ = ((2) ^ alpha * C) * r _ ^ alpha *
            (∑ k ∈ Finset.range _, q ^ k) * D := by rw [hCscale]

private theorem parabolicELpNorm_le_parabolicSmoothJetELpNorm
     :
    parabolicELpNorm d u <= parabolicSmoothJetELpNorm d u := by
  calc
    parabolicELpNorm d u <= parabolicELpNorm d u +
        parabolicELpNorm d _ := le_add_of_nonneg_right bot_le
    _ <= parabolicELpNorm d u + parabolicELpNorm d _ +
        ∑ i : Fin d, parabolicELpNorm d _ :=
      le_add_of_nonneg_right bot_le
    _ <= parabolicELpNorm d u + parabolicELpNorm d _ +
        ∑ i : Fin d, parabolicELpNorm d _ +
          ∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNorm d _ :=
      le_add_of_nonneg_right bot_le

private theorem parabolicLpNorm_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicLpNorm d u <= parabolicSmoothJetLpNorm d u := ENNReal.toReal_mono (parabolicSmoothJetELpNorm_ne_top hu)
    (parabolicELpNorm_le_parabolicSmoothJetELpNorm d u)


private theorem parabolicLpMeanNormOn_root_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicLpMeanNormOn d u (parabolicBox 1 1 0 (0 : PDE.Vec d))
        (memLp_parabolicNormalizedVolumeOn_of_memLp
          (volume_parabolicMorreyBox_pos 0 0 (by norm_num))
          (hu.1.mono_measure Measure.restrict_le_self)) <=
      parabolicSmoothJetLpNorm d u := by
  let Q  := parabolicBox 1 1 0 (0 : PDE.Vec d)
  let hraw : MemLp u _ (volume.restrict Q) :=
    hu.1.mono_measure Measure.restrict_le_self
  let hmean : MemLp u _ (parabolicNormalizedVolumeOn Q) :=
    memLp_parabolicNormalizedVolumeOn_of_memLp
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num)) hraw
  have hfactor : ((volume Q).toReal)⁻¹ ^ (1 / parabolicExponent d).toReal <= 1 := by
    rw [show (volume Q).toReal = (2 : Real) ^ d by
      simpa using
        volume_parabolicMorreyBox_toReal (d := d) 0 _
          (r := 1) (by norm_num)]
    apply Real.rpow_le_one
    · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
    · exact (inv_le_one₀ (pow_pos (by norm_num) _)).mpr
        (one_le_pow₀ (by norm_num))
    · positivity
  have hrestriction  :=
    parabolicLpNormOn_le_parabolicLpNorm u Q hu.1
  have hlocal : parabolicLpMeanNormOn d u Q hmean <= parabolicLpNorm d u := by
    rw [parabolicLpMeanNormOn_eq_volume_toReal_inv_rpow_mul_parabolicLpNormOn
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num))
      (volume_parabolicMorreyBox_lt_top 0 0 (by norm_num)) u hraw]
    calc
      ((volume Q).toReal)⁻¹ ^ (1 / parabolicExponent d).toReal *
          parabolicLpNormOn d u Q <= 1 * parabolicLpNormOn d u Q :=
        mul_le_mul_of_nonneg_right hfactor ENNReal.toReal_nonneg
      _ <= 1 * parabolicLpNorm d u :=
        mul_le_mul_of_nonneg_left hrestriction (by norm_num)
      _ = parabolicLpNorm d u := by ring
  exact hlocal.trans (parabolicLpNorm_le_parabolicSmoothJetLpNorm hu)

/-- A finite selected dyadic chain has a radius-weighted velocity-slope tail.
This is finite only; it asserts neither convergence nor a limiting slope. -/
theorem exists_parabolicMorreyDyadicContainingRadiusWeightedSlopeTailConst
     (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (hz : z ∈ parabolicDyadicReferenceCell d)
        (u : TimeVelocity d -> Real),
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
  refine ⟨(2) ^ parabolicMorreyExponent d * C, by positivity, ?_⟩
  intro z hz u hu huc n
  let r  := fun k =>
    (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).radius
  let b  := fun k i =>
    parabolicMorreyBoxVelocitySlope
      (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).baseTime
      (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).center
      (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz k).2).radius u i
  let D  := parabolicMorreyDerivativeLpNorm d u
  have huJet  :=
    parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
  have hr : ∀ k, 0 < r k := fun k =>
    parabolicDyadicSourceBox_radius_pos _
  have hhalf : ∀ k, r (k + 1) = r k / 2 := by
    intro k
    let parent := parabolicDyadicIndexContaining d z hz k
    let child  :=
      parabolicDyadicIndexContaining d z hz _ (Fin.last k)
    have hparent := parabolicDyadicParent_indexContaining_succ d z hz k
    have hindex  := by
      calc
        parabolicDyadicIndexContaining d z hz _ =
            parabolicDyadicChildIndex
              _ child := by
              simpa only [child] using
                (parabolicDyadicChildIndex_parent_last
                  _).symm
        _ = parabolicDyadicChildIndex parent child := by rw [hparent]
    calc
      r _ = (parabolicDyadicSourceBox
          _).radius := by
        simp only [r, parabolicDyadicAddressContaining, hindex]
      _ = (parabolicDyadicSourceBox parent).radius / 2 :=
        parabolicDyadicSourceBox_radius_childIndex parent child
      _ = r k / 2 := by simp only [r, parent, parabolicDyadicAddressContaining]
  have hscale : ∀ k, r k ^ parabolicMorreyExponent d *
      (2) ^ (-parabolicMorreyExponent d) =
        r (k + 1) ^ parabolicMorreyExponent d := by
    intro k
    let index := parabolicDyadicIndexContaining d z hz (k + 1)
    have htrunc  := by
      have hparent := parabolicDyadicParent_indexContaining_succ d z hz k
      calc
        parabolicDyadicTruncate (Nat.le_succ k) index =
            parabolicDyadicParent index := by
              funext j
              apply congrArg index
              exact Fin.ext (by rfl)
        _ = parabolicDyadicIndexContaining d z hz k := hparent
    simpa only [r, parabolicDyadicAddressContaining, index, htrunc,
      Nat.succ_sub (Nat.le_refl k), Nat.sub_self, pow_one] using
      (parabolicDyadicSourceBox_radius_rpow_truncate_mul (Nat.le_succ k) index
        _)
  have hstep : ∀ k, r (k + 1) * ∑ i : Fin d, |b (k + 1) i - b k i| <=
      C * r k ^ parabolicMorreyExponent d * D := by
    intro k
    let parent := parabolicDyadicIndexContaining d z hz k
    let child  :=
      parabolicDyadicIndexContaining d z hz _ (Fin.last k)
    have hparent := parabolicDyadicParent_indexContaining_succ d z hz k
    have hindex  := by
      calc
        parabolicDyadicIndexContaining d z hz _ =
            parabolicDyadicChildIndex
              _ child := by
              simpa only [child] using
                (parabolicDyadicChildIndex_parent_last
                  _).symm
        _ = parabolicDyadicChildIndex parent child := by rw [hparent]
    have hraw := hchild k parent child u hu
    have hslope  := by
      calc
        _ <= |parabolicMorreyBoxAverage
              _
              _
              _ u -
            parabolicMorreyBoxAffineProjection
              _
              _
              _ u
              _| +
            (parabolicDyadicSourceBox
              _).radius *
              ∑ i : Fin d,
                |parabolicMorreyBoxVelocitySlope
                    _
                    _
                    _ u i -
                  parabolicMorreyBoxVelocitySlope
                    _
                    _
                    _ u i| :=
          le_add_of_nonneg_left (abs_nonneg _)
        _ <= _ := by
          simpa only [parabolicMorreyDerivativeLpNormOn] using hraw
    have hnorm := parabolicMorreyDerivativeLpNormOn_le u
      (parabolicBox 1 (parabolicDyadicSourceBox parent).radius
        (parabolicDyadicSourceBox parent).baseTime
        (parabolicDyadicSourceBox parent).center) huJet
    have hglobal  := hslope.trans (mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg hCpos.le (Real.rpow_nonneg
          (parabolicDyadicSourceBox_radius_pos parent).le _)))
    simpa only [r, b, D, parabolicDyadicAddressContaining, hindex, hparent] using hglobal
  simpa only [r, b, D] using
    finite_radius_weighted_slope_tail C _ D
      _ r b hCpos
      (parabolicMorreyDerivativeLpNorm_nonneg d u) hr hhalf hscale rfl hstep n

/-- The root moment-projection coefficients are bounded by the full selected
smooth-jet norm. -/
theorem parabolicMorreyRootAffineCoefficient_le_parabolicSmoothJetLpNorm
    
    (hu : ContDiff Real 2 u) (huc : HasCompactSupport u) :
    |parabolicMorreyBoxAverage 0 (0 : PDE.Vec d) 1 u| +
        ∑ i : Fin d,
          |parabolicMorreyBoxVelocitySlope 0 (0 : PDE.Vec d) 1 u i| <=
      (1 + 3 * (d : Real)) * parabolicSmoothJetLpNorm d u := by
  have huJet  :=
    parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
  have hmean : MemLp u _
      (parabolicNormalizedVolumeOn (parabolicBox 1 1 0 _)) :=
    memLp_parabolicNormalizedVolumeOn_of_memLp
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num))
      (huJet.1.mono_measure Measure.restrict_le_self)
  have hcoefficient := parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
    0 _ (by norm_num) u hmean
  calc
    |parabolicMorreyBoxAverage 0 _ 1 u| +
        ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope 0 _ 1 u i| =
        |parabolicMorreyBoxAverage 0 _ 1 u| +
          1 * ∑ i : Fin d,
            |parabolicMorreyBoxVelocitySlope 0 _ 1 u i| := by ring
    _ <= (1 + 3 * d) *
        parabolicLpMeanNormOn d u _ hmean :=
      hcoefficient
    _ <= (1 + 3 * d) * parabolicSmoothJetLpNorm d u :=
      mul_le_mul_of_nonneg_left
        (parabolicLpMeanNormOn_root_le_parabolicSmoothJetLpNorm huJet) (by positivity)

end HypoellipticAleksandrov.Parabolic
