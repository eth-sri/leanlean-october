module

public import NearlyMinimax.DyadicPilotPointwise
public import NearlyMinimax.PairDesignMarginal
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual pre-centering parent-cell support and original weighted-pair
design localization. These are the geometric inputs of U7. -/

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
𝚨
𝚭
𝚩

𝗃 𝔒 ἀ j x
theorem preconditionedPilotFeature_zero_off_cell j x
    (a : 𝗬₂) z (hz : z.1 ∉ 𝔒 dyadicPilotCell) :
    𝔒 preconditionedPilotFeature a z = 0 := by
  simp [preconditionedPilotFeature, dyadicPilotFeature, hz]

𝗇 𝔄 𝘮
𝗇 𝔅 incrementVariables 𝚃
𝗇 𝔉 Sum.inr $ Sum.inl $ anchoredFinIndex i
𝗇 𝔊 Sum.inr $ Sum.inr $ anchoredFinIndex i
𝗇 𝔎 (Fintype.equivFin 𝔅).symm a
theorem dyadicIncrementRawVector_zero_off_parent j x
    (z : Observation d) (hz : z.1 ∉ dyadicPilotCell 𝔄 x) :
    dyadicIncrementRawVector (ℓ := ℓ) j x z = 0 := by
  have hj : j ≠ 0 := by
    intro h
    subst j
    apply hz
    change regularGridCell 1  𝖠₃  z.1 = regularGridCell 1  𝖠₃  x
    bound
  have hcur := fun h => hz $ 𝔒 dyadicPilotCell_subset_parent h
  funext a
  change 𝔒 dyadicIncrementFeature
    𝔎 z = 0
  generalize 𝔎 = v
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      exact 𝔒 preconditionedPilotFeature_zero_off_cell _ z hcur
    | inr v =>
      simpa only [dyadicIncrementFeature, if_neg hj] using
        preconditionedPilotFeature_zero_off_cell 𝔄 x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z hz
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response
    all_goals first
      | simpa [dyadicIncrementFeature, hj] using
          𝔒 preconditionedPilotFeature_zero_off_cell 𝔉 z hcur
      | simpa [dyadicIncrementFeature, hj] using
          𝔒 preconditionedPilotFeature_zero_off_cell 𝔊 z hcur
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell 𝔄 x 𝔉 z hz
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell 𝔄 x 𝔊 z hz

𝗇 𝔇 𝚄₁
𝗃 𝔑 fun t => dyadicIncrementRawVector j ἀ $ z t
𝗇 𝔈 𝔑 x
𝗇 𝔏 Fin (Fintype.card 𝔅) → ℝ
theorem dyadic_increment_raw_kernel_zero_off_parent j (x : Covariate d)
    (H : ContinuousMultilinearMap ℝ
      (fun _ : Fin k => 𝔏) ℝ)
    (z : Fin k → Observation d) i (hz : 𝔇 ∉ dyadicPilotCell 𝔄 x) :
    H 𝔈 = 0 :=
  H.map_coord_zero i $ 𝔒 dyadicIncrementRawVector_zero_off_parent (z i) hz

/-- Raw derivative kernels on different actual parent cells are orthogonal
before any centering. No covariance orthogonality is postulated. -/
theorem dyadic_increment_raw_kernels_disjoint (hk : 𝖰)
    j x y
    (hcell : dyadicPilotLabel 𝔄 x ≠ dyadicPilotLabel 𝔄 y)
    (H G : ContinuousMultilinearMap ℝ
      (fun _ => 𝔏) ℝ)
    (z : Fin k → Observation d) :
    H 𝔈 *
      G 𝔑 y = 0 := by
  let i : Fin k := ⟨0, hk⟩
  by_cases hz : 𝔇 ∈ dyadicPilotCell 𝔄 x
  · have hzy : 𝔇 ∉ dyadicPilotCell 𝔄 y := by
      intro h
      apply hcell
      exact ((dyadicPilotLabel_eq_iff 𝔄 x 𝔇).mpr hz).symm.trans
        $ (dyadicPilotLabel_eq_iff 𝔄 y 𝔇).mpr h
    rw [dyadic_increment_raw_kernel_zero_off_parent j y G z i hzy, mul_zero]
  · rw [𝔒 dyadic_increment_raw_kernel_zero_off_parent H z i hz, zero_mul]

𝗇 𝔍 2 ^ 𝔄
𝗇 𝔐 (𝗪₁).real
/-- Each actual parent-anchor block has weighted-pair mass at most
`p₊² / K_parent`, the localization gain required by U7. -/
theorem regularPairDesignMeasure_parent_block_mass C
    θ (hθ : 𝙟) k hk j
    c :
    𝔐
      {w : 𝙩 | regularGridCell ( 2 ^ 𝔄)  𝖠₃  w.1 = c} ≤
        C.densityUpper ^ 2 / dyadicPilotScale d 𝔄 := by
  let := cubeVolume_isProbability d
  let A := regularGridCell 𝔍  𝖠₃  ⁻¹' 𝚕₂
  have hmap := regularPairDesignMeasure_fst_cube_le C θ hθ k hk
  have hfirst : 𝔐 (Prod.fst ⁻¹' A) ≤
      C.densityUpper ^ 2 * 𝘣₂ A := by
    rw [← map_measureReal_apply measurable_fst $ measurableSet_singleton c |>.preimage (regular_grid_cell_measurable ..) ]
    have ht := ENNReal.toReal_mono
      ( by
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top $ measure_ne_top (cubeVolume d) A )
      $ hmap A
    simpa only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal $ sq_nonneg _ ] using ht
  have hvol : 𝘣₂ A ≤ (1 / 𝔍) ^ d := by
    have ht := ENNReal.toReal_mono (by finiteness) $ regular_grid_fiber_volume_le 𝔍  𝖠₃  c
    aesop
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left hvol $ sq_nonneg _ ).trans_eq
  aesop
