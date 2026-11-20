module

public import NearlyMinimax.DyadicPilotPointwise
public import NearlyMinimax.PairDesignMarginal


@[expose] public section

/-! Actual pre-centering parent-cell support and original weighted-pair
design localization. These are the geometric inputs of U7. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {d ℓ k j : ℕ} {x : Covariate d}

theorem preconditionedPilotFeature_zero_off_cell
    (a : LocalPilotIndex d ℓ) {z : Observation d} (hz : z.1 ∉ dyadicPilotCell j x) :
    preconditionedPilotFeature j x a z = 0 := by
  simp_all [preconditionedPilotFeature, dyadicPilotFeature]

theorem dyadicIncrementRawVector_zero_off_parent
    {z : Observation d} (hz : z.1 ∉ dyadicPilotCell (j - 1) x) :
    dyadicIncrementRawVector (ℓ := ℓ) j x z = 0 := by
  have hj : j ≠ 0 := by
    intro h
    subst j
    apply hz
    change _ = regularGridCell 1 (by positivity) x
    exact Subsingleton.elim _ _
  have hcur  := fun h => hz (dyadicPilotCell_subset_parent j x h)
  funext a
  change dyadicIncrementFeature .. = 0
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a = v
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      exact preconditionedPilotFeature_zero_off_cell _ hcur
    | inr v =>
      simpa only [dyadicIncrementFeature, if_neg hj] using
        preconditionedPilotFeature_zero_off_cell
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) hz
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response
    all_goals first
      | exact preconditionedPilotFeature_zero_off_cell (Sum.inr (Sum.inl (anchoredFinIndex i))) hcur
      | exact preconditionedPilotFeature_zero_off_cell (Sum.inr (Sum.inr (anchoredFinIndex i))) hcur
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell (Sum.inr (Sum.inl (anchoredFinIndex i))) hz
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell (Sum.inr (Sum.inr (anchoredFinIndex i))) hz

/-- Raw derivative kernels on different actual parent cells are orthogonal
before any centering. No covariance orthogonality is postulated. -/
theorem dyadic_increment_raw_kernels_disjoint (hk : 0 < k)
    (j : ℕ) (x y : Covariate d)
    (hcell : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) y)
    (H G : ContinuousMultilinearMap ℝ
      (fun _ => Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) ℝ)
    (z : Fin k → Observation d) :
    H (fun t => dyadicIncrementRawVector j x (z t)) *
      G (fun t => dyadicIncrementRawVector j y (z t)) = 0 := by
  let i : Fin k := ⟨0, hk⟩
  by_cases hz : (z i).1 ∈ dyadicPilotCell (j - 1) x
  · have hzy : (z i).1 ∉ dyadicPilotCell (j - 1) y := by
      intro h
      apply hcell
      exact ((dyadicPilotLabel_eq_iff (j - 1) x (z i).1).mpr hz).symm.trans
        ((dyadicPilotLabel_eq_iff (j - 1) y (z i).1).mpr h)
    rw [(G.map_coord_zero i (dyadicIncrementRawVector_zero_off_parent hzy) :
        (G fun t => dyadicIncrementRawVector j y (z t)) = 0), mul_zero]
  · rw [(H.map_coord_zero i (dyadicIncrementRawVector_zero_off_parent hz) :
      (H fun t => dyadicIncrementRawVector j x (z t)) = 0), zero_mul]

/-- Each actual parent-anchor block has weighted-pair mass at most
`p₊² / K_parent`, the localization gain required by U7. -/
theorem regularPairDesignMeasure_parent_block_mass {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) (j : ℕ)
    (c : Fin d → Fin (2 ^ (j - 1))) :
    (regularPairDesignMeasure θ k hk).real
      {w | regularGridCell (2 ^ (j - 1)) (by positivity) w.1 = c} ≤
        C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
  let := cubeVolume_isProbability d
  let A  := (regularGridCell _ (by positivity)) ⁻¹' {c}
  have hfirst : (regularPairDesignMeasure θ k hk).real (Prod.fst ⁻¹' A) ≤
      C.densityUpper ^ 2 * (cubeVolume d).real A := by
    rw [← map_measureReal_apply measurable_fst (measurableSet_singleton c |>.preimage (regular_grid_cell_measurable _ _))]
    have ht := ENNReal.toReal_mono
      (show (ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d) A ≠ ⊤ by
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (cubeVolume d) A))
      ((regularPairDesignMeasure_fst_cube_le hθ hk) A)
    simpa only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)] using ht
  have hvol : (cubeVolume d).real A ≤ (1 / (2 ^ (j - 1))) ^ d := by
    have ht := ENNReal.toReal_mono (by finiteness) (regular_grid_fiber_volume_le (by positivity) c)
    simpa [measureReal_def,   Nat.cast_pow] using ht
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left hvol (sq_nonneg _)).trans_eq
  simp [dyadicPilotScale] <;> ring

end NearlyMinimax
