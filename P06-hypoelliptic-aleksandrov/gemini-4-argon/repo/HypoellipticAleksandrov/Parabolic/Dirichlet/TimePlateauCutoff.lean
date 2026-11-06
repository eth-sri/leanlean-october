module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Profile

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

private theorem timePlateauRight_contDiff (c d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateauRight c d) := by
  unfold timePlateauRight
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_const.sub contDiff_id).div_const _)

private theorem timePlateau_contDiff (a b c d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateau a b c d) := by
  unfold timePlateau
  have _h_inl_12 : ContDiff ℝ (⊤ : ℕ∞) (timePlateauLeft a b) := by
    unfold timePlateauLeft
    exact PDE.smoothTransitionProfile.smooth.comp
      ((contDiff_id.sub contDiff_const).div_const _)
  exact
    _h_inl_12.mul (timePlateauRight_contDiff c d)

private theorem timePlateau_support_subset
    {a b c d } (hab : a < b) (hcd : c < d) :
    support (timePlateau a b c d) ⊆
      Icc (timePlateauEll a b) (timePlateauR c d) := by
  intro tau hsupport
  change timePlateau a b c d tau ≠ 0 at hsupport
  constructor
  · by_contra hnot
    have hlt := lt_of_not_ge hnot
    have hzero : timePlateauLeft a b tau = 0 := by
      apply PDE.smoothTransitionProfile.zero_of_nonpos
      unfold timePlateauEll
      unfold timePlateauEll at hlt
      apply le_of_lt
      apply div_neg_of_neg_of_pos <;> linarith
    exact hsupport (by simp only [timePlateau, hzero, zero_mul])
  · by_contra hnot
    have hlt := lt_of_not_ge hnot
    have hzero : timePlateauRight c d tau = 0 := by
      apply PDE.smoothTransitionProfile.zero_of_nonpos
      unfold timePlateauR
      unfold timePlateauR at hlt
      apply le_of_lt
      apply div_neg_of_neg_of_pos <;> linarith
    exact hsupport (by simp only [timePlateau, hzero, mul_zero])

private theorem timePlateau_tsupport_subset
    {a b c d } (hab : a < b) (hcd : c < d) :
    tsupport (timePlateau a b c d) ⊆
      Icc (timePlateauEll a b) (timePlateauR c d) := by
  rw [tsupport]
  exact closure_minimal (timePlateau_support_subset hab hcd) isClosed_Icc

private theorem timePlateau_hasCompactSupport
    {a b c d } (hab : a < b) (hcd : c < d) :
    HasCompactSupport (timePlateau a b c d) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact timePlateau_support_subset hab hcd

private theorem timePlateau_Icc_subset_outer
    {a b c d } (hab : a < b) (hcd : c < d) :
    Icc (timePlateauEll a b) (timePlateauR c d) ⊆ Ioo a d := by
  intro tau htau
  constructor
  · have hell : a < timePlateauEll a b := by
      unfold timePlateauEll
      linarith
    exact hell.trans_le htau.1
  · have hr : timePlateauR c d < d := by
      unfold timePlateauR
      linarith
    exact lt_of_le_of_lt htau.2 hr

theorem exists_reverseTimeScalarTest_plateau
    (T a b c d : ℝ)
    (ha0 : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (hdT : d ≤ T) :
    ∃ eta : ReverseTimeScalarTest T,
      (∀ tau : ℝ, 0 ≤ eta tau) ∧
      (∀ tau : ℝ, eta tau ≤ 1) ∧
      (∀ tau ∈ Set.Icc b c, eta tau = 1) ∧
      tsupport (eta : ℝ → ℝ) ⊆ Set.Ioo a d := by
  have _h_inl_26 : Ioo a d ⊆ reverseTimeOpenInterval T := by
    intro tau htau
    change tau ∈ Ioo 0 T
    exact ⟨lt_of_le_of_lt ha0 htau.1, lt_of_lt_of_le htau.2 hdT⟩
  let eta : ReverseTimeScalarTest T :=
    { toFun := timePlateau a b c d
      contDiff' := timePlateau_contDiff a b c d
      hasCompactSupport' := timePlateau_hasCompactSupport hab hcd
      tsupport_subset' := (timePlateau_tsupport_subset hab hcd).trans
        ((timePlateau_Icc_subset_outer hab hcd).trans
          _h_inl_26) }
  refine ⟨eta, ?_, ?_, ?_, ?_⟩
  · intro tau
    change 0 ≤ timePlateau a b c d tau
    unfold timePlateau timePlateauLeft timePlateauRight
    exact mul_nonneg (PDE.smoothTransitionProfile.nonneg _)
      (PDE.smoothTransitionProfile.nonneg _)
  · intro tau
    change timePlateau a b c d tau ≤ 1
    unfold timePlateau timePlateauLeft timePlateauRight
    exact mul_le_one₀ (PDE.smoothTransitionProfile.le_one _)
      (PDE.smoothTransitionProfile.nonneg _)
      (PDE.smoothTransitionProfile.le_one _)
  · intro tau htau
    change timePlateau a b c d tau = 1
    have _h_inl_17 : timePlateauLeft a b tau = 1 := by
      have hbt := htau.1
      apply PDE.smoothTransitionProfile.one_of_one_le
      unfold timePlateauEll
      have hden : 0 < b - (a + b) / 2 := by
        linarith
      rw [le_div_iff₀ hden]
      linarith
    have _h_inl_14 : timePlateauRight c d tau = 1 := by
      have htc := htau.2
      apply PDE.smoothTransitionProfile.one_of_one_le
      unfold timePlateauR
      have hden : 0 < (c + d) / 2 - c := by
        linarith
      rw [le_div_iff₀ hden]
      linarith
    have hvalue : timePlateau a b c d tau = 1 := by
      simp only [timePlateau, _h_inl_17,
        _h_inl_14, one_mul]
    exact (show b ≤ c ∧ timePlateau a b c d tau = 1 from ⟨hbc, hvalue⟩).2
  · change tsupport (timePlateau a b c d) ⊆ Ioo a d
    exact (timePlateau_tsupport_subset hab hcd).trans
      (timePlateau_Icc_subset_outer hab hcd)

end HypoellipticAleksandrov.Parabolic.Dirichlet
