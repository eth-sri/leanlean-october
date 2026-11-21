module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.Regularity.IntegerOrderEstimateTransfer

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity

open MeasureTheory
open KPContLocalNorm KPContLocalEnergy

export SobolevIteration.Raw (SmoothNearClosedBall BoundedCoefficientDerivatives WeakIntegerEstimate)

open SobolevIteration (restrictCoefficients)

theorem restrictCoefficients_smooth {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hAB : A.carrier ⊆ B.carrier) (hclosed : Metric.closedBall A.center A.radius ⊆ B.carrier)
    (D : Coefficients B cρ Cρ κ Λ) : SmoothNearClosedBall (restrictCoefficients hAB D) :=
  ⟨B.carrier, Metric.isOpen_ball, hclosed, D.density_smooth, D.matrix_smooth⟩

private theorem coordDerivList_contDiffOn {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (l : List (Fin n)) {f : Space n → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) U := by
  induction l with
  | nil => exact hf
  | cons i is ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem boundedCoefficientDerivatives_of_smoothNearClosedBall
    {n : ℕ} {outer : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients outer cρ Cρ κ Λ) (hD : SmoothNearClosedBall D) (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ BoundedCoefficientDerivatives D k L := by
  classical
  obtain ⟨U, hU, hsub, hρ, hA⟩ := hD
  have hρC : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (D.density y : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hρ
  have hAprod : ∀ i j : Fin n,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) U := by
    intro i j
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn (hρ.mul (hA i j)) using 1
    ext y
    simp
  have hK : IsCompact (Metric.closedBall outer.center outer.radius) :=
    isCompact_closedBall _ _
  have hbound : ∀ (f : Space n → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) f U →
      ∃ C : ℝ, ∀ x ∈ Metric.closedBall outer.center outer.radius, ‖f x‖ ≤ C := by
    intro f hf
    exact hK.exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  have hbd : ∀ α : MultiIndex n k, ∃ B : ℝ, 0 ≤ B ∧
      (∀ x ∈ Metric.closedBall outer.center outer.radius,
        ‖coordinateDerivative α (fun y => (D.density y : ℂ)) x‖ ≤ B) ∧
      (∀ q : Fin n × Fin n, ∀ x ∈ Metric.closedBall outer.center outer.radius,
        ‖coordinateDerivative α
          (fun y => ((D.density y * D.matrix y q.1 q.2 : ℝ) : ℂ)) x‖ ≤ B) := by
    intro α
    have hα : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivative α (fun y => (D.density y : ℂ))) U :=
      coordDerivList_contDiffOn hU α.directions hρC
    obtain ⟨B0, hB0⟩ := hbound _ hα
    have hq : ∀ q : Fin n × Fin n, ∃ C : ℝ,
        ∀ x ∈ Metric.closedBall outer.center outer.radius,
          ‖coordinateDerivative α
            (fun y => ((D.density y * D.matrix y q.1 q.2 : ℝ) : ℂ)) x‖ ≤ C := by
      intro q
      exact hbound _ (coordDerivList_contDiffOn hU α.directions (hAprod q.1 q.2))
    choose C hC using hq
    refine ⟨max B0 0 + ∑ q : Fin n × Fin n, max (C q) 0, ?_, ?_, ?_⟩
    · have h1 : (0 : ℝ) ≤ max B0 0 := le_max_right _ _
      have h2 : (0 : ℝ) ≤ ∑ q : Fin n × Fin n, max (C q) 0 :=
        Finset.sum_nonneg (fun q _ => le_max_right _ _)
      linarith
    · intro x hx
      calc ‖coordinateDerivative α (fun y => (D.density y : ℂ)) x‖ ≤ B0 := hB0 x hx
        _ ≤ max B0 0 := le_max_left _ _
        _ ≤ max B0 0 + ∑ q : Fin n × Fin n, max (C q) 0 :=
            le_add_of_nonneg_right (Finset.sum_nonneg (fun q _ => le_max_right _ _))
    · intro q x hx
      calc ‖coordinateDerivative α
            (fun y => ((D.density y * D.matrix y q.1 q.2 : ℝ) : ℂ)) x‖ ≤ C q := hC q x hx
        _ ≤ max (C q) 0 := le_max_left _ _
        _ ≤ ∑ q : Fin n × Fin n, max (C q) 0 :=
            Finset.single_le_sum (fun q _ => le_max_right _ _) (Finset.mem_univ q)
        _ ≤ max B0 0 + ∑ q : Fin n × Fin n, max (C q) 0 :=
            le_add_of_nonneg_left (le_max_right _ _)
  choose B hB0 hBd hBp using hbd
  refine ⟨∑ α : MultiIndex n k, B α, Finset.sum_nonneg (fun α _ => hB0 α), ?_⟩
  intro α x hx
  have hx' : x ∈ Metric.closedBall outer.center outer.radius :=
    Metric.ball_subset_closedBall hx
  refine ⟨?_, ?_⟩
  · calc ‖coordinateDerivative α (fun y => (D.density y : ℂ)) x‖ ≤ B α := hBd α x hx'
      _ ≤ ∑ α : MultiIndex n k, B α :=
          Finset.single_le_sum (fun α _ => hB0 α) (Finset.mem_univ α)
  · intro i j
    calc ‖coordinateDerivative α
          (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x‖ ≤ B α := hBp α (i, j) x hx'
      _ ≤ ∑ α : MultiIndex n k, B α :=
          Finset.single_le_sum (fun α _ => hB0 α) (Finset.mem_univ α)

end DedekindZetaZeroFree.KPContLocalRegularity

namespace DedekindZetaZeroFree

open KPContLocalNorm KPContLocalEnergy KPContLocalRegularity

theorem kp_cont_local_regularity_iterate_fixed_coefficients (n : ℕ)
    (inner outer : LocalBall n) (hcenter : inner.center = outer.center)
    (hradii : inner.radius < outer.radius) (cρ Cρ κ Λ M : ℝ)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (D : Coefficients outer cρ Cρ κ Λ) (hD : SmoothNearClosedBall D) :
    ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
      WeakIntegerEstimate inner outer D r M C := by
  intro r

  obtain ⟨L, hL, hbd⟩ :=
    boundedCoefficientDerivatives_of_smoothNearClosedBall D hD (r + 1)
  obtain ⟨C, hC, hmain⟩ := KPContLocalRegularity.SobolevIteration.quantitative_weak_integer_gain n r inner.dimension_pos
    inner.radius outer.radius cρ Cρ κ Λ L M inner.radius_pos hradii hcρ hκ hL hM
  exact ⟨C, hC, hmain inner outer hcenter rfl rfl D hD hbd⟩

end DedekindZetaZeroFree

end
