module

public import HypoellipticAleksandrov.Parabolic.OrdinaryWeakDerivativeFamilyView
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLeibniz
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing


/-!
# Localization of finite higher weak-derivative families

This module localizes a finite parabolic weak-derivative family by a smooth
compact plateau.  Its representatives are the full multi-index Leibniz sums.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic




/-- Every representative in the weak Leibniz family is supported in the
topological support of its classical multiplier. -/
theorem parabolicWeakMulRepresentative_tsupport_subset
    {d L : ℕ}
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    {U : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    tsupport (parabolicWeakMulRepresentative b D beta) ⊆ tsupport b := by
  apply closure_minimal
  · intro z hz
    by_contra hzb
    apply hz
    unfold parabolicWeakMulRepresentative
    apply Finset.sum_eq_zero
    intro gamma hgamma
    have hderiv :
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left b z = 0 := by
      by_contra hne
      exact hzb (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset gamma.left b
        (subset_closure hne))
    rw [hderiv, mul_zero, zero_mul]
  · exact isClosed_closure

/-- On an open plateau, the ordinary representatives of the full weak
Leibniz family agree pointwise with the original ordinary representatives. -/
theorem ParabolicWeakDerivativeFamily.mulContDiffOn_ordinaryRepresentative_eqOn
    {d m : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (hV : IsOpen V)
    (B : ParabolicDerivativeIndex d (2 * m) → ℝ)
    (hB : ∀ alpha, 0 ≤ B alpha)
    (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hbFinite : ContDiffOn ℝ (2 * m) b U)
    (hbOne : Set.EqOn b 1 V)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u)
    (hbBound :
      ∀ (alpha : ParabolicDerivativeIndex d (2 * m)) z,
        z ∈ U →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 b z| ≤
            B alpha)
    (beta : TimeVelocityDerivativeIndex d m) :
    Set.EqOn
      ((D.mulContDiffOn hU B hB b hbFinite hbBound).ordinaryRepresentative beta)
      (D.ordinaryRepresentative beta) V := by
  classical
  intro z hz
  change parabolicWeakMulRepresentative b D beta.toParabolic z = _
  unfold parabolicWeakMulRepresentative
  rw [Fintype.sum_eq_single
    (default : TimeVelocityMultiIndex.Split beta.toParabolic.1)]
  · have hleft :
        (default : TimeVelocityMultiIndex.Split beta.toParabolic.1).left = 0 := rfl
    have hright : ParabolicDerivativeIndex.splitRight beta.toParabolic default =
        beta.toParabolic := by
      apply Subtype.ext
      funext c
      change beta.1 c - 0 = beta.1 c
      exact Nat.sub_zero _
    rw [hleft, hright]
    simp only [TimeVelocityMultiIndex.choose_zero_right,
      Nat.cast_one, one_mul, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero]
    change b z * D.representative beta.toParabolic z =
      D.representative beta.toParabolic z
    have hbz : b z = (1 : ℝ) := by exact hbOne hz
    rw [hbz, one_mul]
  · intro gamma hne

    have hconst := TimeVelocityMultiIndex.coordinateIteratedFDeriv_congr_of_eqOn
      V hV gamma.left hbOne z hz


    rw [(hconst.trans (show TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
          (fun _  ↦ (1 )) z = 0 by
        have horder : gamma.left.order ≠ 0 := by
          obtain ⟨c, hc⟩ := Function.ne_iff.mp (by
              intro hleft
              apply hne
              funext c
              apply Fin.ext
              change gamma.left c = 0
              exact congr_fun hleft c)

          have hcpos  := Nat.pos_of_ne_zero (by exact hc)
          have hle : gamma.left c ≤ gamma.left.order := by
            cases c with
            | inl t =>
              cases t
              simp [TimeVelocityMultiIndex.order,
                TimeVelocityMultiIndex.timeOrder,
                TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
                timeCoord]
            | inr i =>
              have hsum  :=
                Finset.single_le_sum (fun j _ ↦ Nat.zero_le
                  (gamma.left (Sum.inr j))) (Finset.mem_univ i)
              change gamma.left (Sum.inr i) ≤
                gamma.left (Sum.inl ()) + ∑ j, gamma.left (Sum.inr j)
              exact hsum.trans (Nat.le_add_left _ _)
          omega
        unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
        rw [iteratedFDeriv_const_of_ne (by simpa using horder) (1 : ℝ)]
        rfl)), mul_zero, zero_mul]

variable {d : ℕ} (alpha : TimeVelocityMultiIndex d) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)

private theorem coordinateIteratedFDeriv_continuous
     (hf : ContDiff ℝ PDE.smoothOrder f) :
    Continuous (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) := by
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hi := hf.iteratedFDeriv_right
    (m := 0) (i := alpha.coordinateList.length) (by exact_mod_cast le_top)
  exact ((contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi).continuous




/-- A compact subset of an open carrier admits a smooth compact plateau whose
full finite weak Leibniz family is supported in the plateau support and agrees
with the original ordinary family on a strictly smaller closed collar. -/
theorem exists_localizedHigherJetFamily
    {d m : ℕ} {U C : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u) :
    ∃ (δ : ℝ) (_ : 0 < δ)
      (b : HypoellipticAleksandrov.Parabolic.ScalarField d)
      (_ : ContDiff ℝ PDE.smoothOrder b)
      (_ : HasCompactSupport b)
      (_ : tsupport b ⊆ U)
      (_ : Set.EqOn b 1 (Metric.cthickening δ C))
      (B : ParabolicDerivativeIndex d (2 * m) → ℝ)
      (_ : ∀ alpha, 0 ≤ B alpha)
      (_ : ∀ (alpha : ParabolicDerivativeIndex d (2 * m)) z,
        z ∈ U →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 b z| ≤
            B alpha)
      (Dloc :
        ParabolicWeakDerivativeFamily d (2 * m) U (fun z ↦ b z * u z)),
      (∀ beta,
          Dloc.representative beta =
            parabolicWeakMulRepresentative b D beta) ∧
      (∀ beta, tsupport (Dloc.representative beta) ⊆ tsupport b) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        ∀ beta : TimeVelocityDerivativeIndex d m,
          Set.EqOn
            (Dloc.ordinaryRepresentative beta)
            (D.ordinaryRepresentative beta)
            (Metric.cthickening ρ C) := by
  classical
  obtain ⟨δ, hδ, b, hbSmooth, hbCompact, hbSupport, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset hU hC hCU
  have hbFinite : ContDiffOn ℝ (2 * m) b U := by
    apply hbSmooth.contDiffOn.of_le
    apply WithTop.coe_le_coe.mpr
    exact le_top
  have hbound (alpha : ParabolicDerivativeIndex d (2 * m)) :
      ∃ M : ℝ, ∀ z,
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 b z| ≤ M := by
    obtain ⟨M, hM⟩ :=
      (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport alpha.1 b hbCompact).exists_bound_of_continuous
        (coordinateIteratedFDeriv_continuous alpha.1 b hbSmooth)
    exact ⟨M, hM⟩
  let B  := fun alpha ↦
    max 0 (Classical.choose (hbound alpha))
  have hB : ∀ alpha, 0 ≤ B alpha := fun alpha ↦ le_max_left _ _
  have hbBound : ∀ (alpha : ParabolicDerivativeIndex d (2 * m)) z,
      z ∈ U →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 b z| ≤ B alpha := by
    intro alpha z hz
    exact (Classical.choose_spec (hbound alpha) z).trans (le_max_right _ _)

  refine ⟨δ, hδ, b, hbSmooth, hbCompact, hbSupport, hbOne,
    B, hB, hbBound, (D.mulContDiffOn hU B hB b hbFinite hbBound), ?_, ?_, δ / 2, by positivity, by linarith, ?_⟩
  · intro beta
    rfl
  · intro beta
    exact parabolicWeakMulRepresentative_tsupport_subset b D beta
  · intro beta


    exact (D.mulContDiffOn_ordinaryRepresentative_eqOn hU Metric.isOpen_thickening B hB b
      hbFinite (hbOne.mono (Metric.thickening_subset_cthickening δ C)) hbBound beta).mono
        (Metric.cthickening_subset_thickening' hδ (by linarith) C)

end HypoellipticAleksandrov.Parabolic
