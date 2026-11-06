module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Profile
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
public import PDEFoundation.Calculus.RegularityOrder


section
open private HypoellipticAleksandrov.Parabolic.timePlateau_support_subset from HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
private alias _sharedProof_29_0 := HypoellipticAleksandrov.Parabolic.timePlateau_support_subset
end
section
open private HypoellipticAleksandrov.Parabolic.timePlateau_eq_one_on from HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
private alias _sharedProof_34_0 := HypoellipticAleksandrov.Parabolic.timePlateau_eq_one_on
end


/-!
# Reverse-time scalar plateau cutoffs

This module constructs a smooth reverse-time scalar test that is one on a
closed inner interval and has topological support strictly inside a prescribed
outer interval.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Function Set

private def timePlateauEll (a b : ℝ) : ℝ :=
  (a + b) / 2

private def timePlateauR (c d : ℝ) : ℝ :=
  (c + d) / 2

private def timePlateauLeft (a b : ℝ) : ℝ → ℝ :=
  fun tau => PDE.smoothTransitionProfile
    ((tau - timePlateauEll a b) / (b - timePlateauEll a b))

private def timePlateauRight (c d : ℝ) : ℝ → ℝ :=
  fun tau => PDE.smoothTransitionProfile
    ((timePlateauR c d - tau) / (timePlateauR c d - c))

private def timePlateau (a b c d : ℝ) : ℝ → ℝ :=
  fun tau => timePlateauLeft a b tau * timePlateauRight c d tau

private theorem timePlateauLeft_contDiff (a b : ℝ) :
    ContDiff ℝ PDE.smoothOrder (timePlateauLeft a b) := by
  unfold timePlateauLeft
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_id.sub contDiff_const).div_const _)

private theorem timePlateauRight_contDiff (c d : ℝ) :
    ContDiff ℝ PDE.smoothOrder (timePlateauRight c d) := by
  unfold timePlateauRight
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_const.sub contDiff_id).div_const _)

private theorem timePlateau_contDiff (a b c d : ℝ) :
    ContDiff ℝ PDE.smoothOrder (timePlateau a b c d) := by
  unfold timePlateau
  exact
    (timePlateauLeft_contDiff a b).mul (timePlateauRight_contDiff c d)

variable (a b c d tau : ℝ)

private theorem timePlateau_nonneg  :
    0 ≤ timePlateau a b c d tau := by
  unfold timePlateau timePlateauLeft timePlateauRight
  exact mul_nonneg (PDE.smoothTransitionProfile.nonneg _)
    (PDE.smoothTransitionProfile.nonneg _)

private theorem timePlateau_le_one  :
    timePlateau a b c d tau ≤ 1 := by
  unfold timePlateau timePlateauLeft timePlateauRight
  exact mul_le_one₀ (PDE.smoothTransitionProfile.le_one _)
    (PDE.smoothTransitionProfile.nonneg _)
    (PDE.smoothTransitionProfile.le_one _)





private theorem timePlateau_eq_one_on
    {a b c d tau : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (htau : tau ∈ Icc b c) :
    timePlateau a b c d tau = 1 := (_sharedProof_34_0 hab hbc hcd htau)






section
variable {a b c d : ℝ} (hab : a < b) (hcd : c < d)

include hab hcd
private theorem timePlateau_support_subset
     :
    support (timePlateau a b c d) ⊆
      Icc (timePlateauEll a b) (timePlateauR c d) := (_sharedProof_29_0 hab hcd)


private theorem timePlateau_tsupport_subset
     :
    tsupport (timePlateau a b c d) ⊆
      Icc (timePlateauEll a b) (timePlateauR c d) := by
  rw [tsupport]
  exact closure_minimal (timePlateau_support_subset hab hcd) isClosed_Icc

private theorem timePlateau_hasCompactSupport
     :
    HasCompactSupport (timePlateau a b c d) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact timePlateau_support_subset hab hcd

private theorem timePlateau_Icc_subset_outer
     :
    Icc (timePlateauEll a b) (timePlateauR c d) ⊆ Ioo a d := by
  intro tau htau
  constructor
  ·
    exact (show a < timePlateauEll a b by
        unfold timePlateauEll
        linarith).trans_le htau.1
  ·
    exact lt_of_le_of_lt htau.2 (by
        unfold timePlateauR
        linarith)
end


private theorem timePlateau_outer_subset_reverseTime
    {T a d : ℝ} (ha0 : 0 ≤ a) (hdT : d ≤ T) :
    Ioo a d ⊆ reverseTimeOpenInterval T := (fun ⦃tau⦄ htau => id ⟨lt_of_le_of_lt ha0 htau.left, lt_of_lt_of_le htau.right hdT⟩)

/-- A smooth reverse-time test with values in `[0, 1]`, a closed inner
plateau, and topological support strictly inside the prescribed outer interval. -/
theorem exists_reverseTimeScalarTest_plateau
    (T a b c d : ℝ)
    (ha0 : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (hdT : d ≤ T) :
    ∃ eta : ReverseTimeScalarTest T,
      (∀ tau : ℝ, 0 ≤ eta tau) ∧
      (∀ tau : ℝ, eta tau ≤ 1) ∧
      (∀ tau ∈ Set.Icc b c, eta tau = 1) ∧
      tsupport (eta : ℝ → ℝ) ⊆ Set.Ioo a d := (Exists.intro
  { toFun := timePlateau a b c d, contDiff' := timePlateau_contDiff a b c d,
    hasCompactSupport' := timePlateau_hasCompactSupport hab hcd,
    tsupport_subset' :=
      LE.le.trans (timePlateau_tsupport_subset hab hcd)
        (LE.le.trans (timePlateau_Icc_subset_outer hab hcd) (timePlateau_outer_subset_reverseTime ha0 hdT)) }
  ⟨timePlateau_nonneg a b c d,
    ⟨timePlateau_le_one a b c d,
      ⟨fun tau htau => id (timePlateau_eq_one_on hab hbc hcd htau),
        id (LE.le.trans (timePlateau_tsupport_subset hab hcd) (timePlateau_Icc_subset_outer hab hcd))⟩⟩⟩)

end HypoellipticAleksandrov.Parabolic.Dirichlet
