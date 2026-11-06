module

public import HypoellipticAleksandrov.Parabolic.OrdinaryWeakDerivativeFamilyView
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLeibniz
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing

/-!
# Localization of finite higher weak-derivative families

This module localizes a finite parabolic weak-derivative family by a smooth
compact plateau.  Its representatives are the full multi-index Leibniz sums.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

variable {d : ℕ} (alpha : TimeVelocityMultiIndex d) (f : TimeVelocity d → ℝ)

private theorem coordinateIteratedFDeriv_tsupport_subset
     :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) ⊆
      tsupport f := by
  apply closure_minimal
  · intro z hz
    by_contra hzf
    apply hz
    unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    have hi : iteratedFDeriv ℝ alpha.coordinateList.length f z = 0 := by
      by_contra hi0
      exact hzf (support_iteratedFDeriv_subset alpha.coordinateList.length hi0)
    simp_all
  · exact isClosed_closure

/-- Every representative in the weak Leibniz family is supported in the
topological support of its classical multiplier. -/
theorem parabolicWeakMulRepresentative_tsupport_subset
    {d L : ℕ}
    (b : TimeVelocity d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    tsupport (parabolicWeakMulRepresentative b D beta) ⊆ tsupport b := by
  apply closure_minimal
  · intro z hz
    by_contra hzb
    apply hz
    apply Finset.sum_eq_zero
    intro gamma hgamma
    have hderiv :
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left b z = 0 := by
      by_contra hne
      exact hzb (coordinateIteratedFDeriv_tsupport_subset gamma.left b
        (subset_closure hne))
    simp_all
  · exact isClosed_closure

/-- On an open plateau, the ordinary representatives of the full weak
Leibniz family agree pointwise with the original ordinary representatives. -/
theorem ParabolicWeakDerivativeFamily.mulContDiffOn_ordinaryRepresentative_eqOn
    {d m : ℕ} {U V : Set (TimeVelocity d)}
    (hU : IsOpen U) (hV : IsOpen V)
    (B : ParabolicDerivativeIndex d (2 * m) → ℝ)
    (hB : ∀ alpha, 0 ≤ B alpha)
    (b : TimeVelocity d → ℝ)
    (hbFinite : ContDiffOn ℝ (2 * m) b U)
    (hbOne : Set.EqOn b 1 V)
    {u : TimeVelocity d → ℝ}
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
    default]
  · have hleft :
        (default : TimeVelocityMultiIndex.Split beta.toParabolic.1).left = 0 := rfl
    aesop
  · intro gamma hne
    have hleft_ne : gamma.left ≠ 0 := by
      intro hleft
      apply hne
      funext c
      apply Fin.ext
      exact congr_fun hleft c
    have hconst := TimeVelocityMultiIndex.coordinateIteratedFDeriv_congr_of_eqOn
      V hV gamma.left hbOne z hz
    have hconst_zero :
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
          (fun _ : TimeVelocity d ↦ (1)) z = 0 := by
      have horder : gamma.left.order ≠ 0 := by
        obtain ⟨c, hc⟩ := Function.ne_iff.mp hleft_ne
        have hc' : gamma.left c ≠ 0 := by omega
        have hle : gamma.left c ≤ gamma.left.order := by
          cases c with
          | inl t =>
            cases t
            simp [TimeVelocityMultiIndex.order,
              TimeVelocityMultiIndex.timeOrder,
              timeCoord]
          | inr i =>
            have hsum : gamma.left (Sum.inr i) ≤
                ∑ j, gamma.left (Sum.inr j) :=
              Finset.single_le_sum (fun j _ ↦ Nat.zero_le
                (gamma.left (Sum.inr j))) (Finset.mem_univ i)
            change gamma.left (Sum.inr i) ≤
              gamma.left (Sum.inl ()) + ∑ j, gamma.left (Sum.inr j)
            omega
        omega
      unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
      rw [iteratedFDeriv_const_of_ne (by simp_all)]
      rfl
    aesop

private theorem coordinateIteratedFDeriv_continuous
     (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) := by
  have hi := hf.iteratedFDeriv_right
    (m := 0) (i := alpha.coordinateList.length) (by simp)
  exact ((contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    _)).clm_apply hi).continuous


/-- A compact subset of an open carrier admits a smooth compact plateau whose
full finite weak Leibniz family is supported in the plateau support and agrees
with the original ordinary family on a strictly smaller closed collar. -/
theorem exists_localizedHigherJetFamily
    {d m : ℕ} {U C : Set (TimeVelocity d)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u) :
    ∃ (δ : ℝ) (_ : 0 < δ)
      (b : TimeVelocity d → ℝ)
      (_ : ContDiff ℝ (⊤ : ℕ∞) b)
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
    simp
  have hbound (alpha : ParabolicDerivativeIndex d (2 * m)) :
      ∃ M : ℝ, ∀ z,
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 b z| ≤ M := by
    obtain ⟨M, hM⟩ :=
      (coordinateIteratedFDeriv_hasCompactSupport alpha.1 b hbCompact).exists_bound_of_continuous
        (coordinateIteratedFDeriv_continuous alpha.1 b hbSmooth)
    aesop
  let B  := fun alpha ↦
    max 0 (Classical.choose (hbound alpha))
  have hB : ∀ alpha, 0 ≤ B alpha := fun alpha ↦ le_max_left _ _
  have hbBound : ∀ (alpha : ParabolicDerivativeIndex d _) z,
      z ∈ U →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 b z| ≤ B alpha := by
    grind
  let Dloc  :=
    D.mulContDiffOn hU B hB b hbFinite hbBound
  refine ⟨δ, hδ, b, hbSmooth, hbCompact, hbSupport, hbOne,
    B, hB, hbBound, Dloc, ?_, ?_, δ / 2, by positivity, by linarith, ?_⟩
  · aesop
  · intro beta
    exact parabolicWeakMulRepresentative_tsupport_subset b D beta
  · intro beta
    have hopen : IsOpen (Metric.thickening δ C) := Metric.isOpen_thickening
    have honeOpen : Set.EqOn b 1 (Metric.thickening δ C) :=
      hbOne.mono (Metric.thickening_subset_cthickening δ C)
    exact (D.mulContDiffOn_ordinaryRepresentative_eqOn hU hopen B hB b
      hbFinite honeOpen hbBound beta).mono
        (Metric.cthickening_subset_thickening' hδ (by linarith) C)

end HypoellipticAleksandrov.Parabolic
