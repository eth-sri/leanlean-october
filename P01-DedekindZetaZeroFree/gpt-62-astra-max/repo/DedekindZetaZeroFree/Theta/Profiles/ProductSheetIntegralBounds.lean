module

public import DedekindZetaZeroFree.Theta.Profiles.ArchimedeanRescaling

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem product_sheet_integrals (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R)
    (σ : ℝ) (hσ : -(1 / 4 : ℝ) < σ) (A : ℝ) (hA : max σ 0 < A)
    (M : ℝ) (hM : 0 < M) :
    letI : MeasurableSpace R.A.G1 := borel _;
    (∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
      Integrable (fun y : R.A.G1 => productPowerMajorant R.A M A
        (y.val * radial R.A u)) R.probe.domain.measure ∧
      (∫ y : R.A.G1, productPowerMajorant R.A M A
        (y.val * radial R.A u) ∂ R.probe.domain.measure) ≤ K * Real.exp (-σ * u)) ∧
    (∀ u : ℝ, ∃ s ∈ nhds u, ∃ E : R.A.G1 → ℝ,
      Integrable E R.probe.domain.measure ∧ ∀ᵐ y ∂ R.probe.domain.measure,
        ∀ t ∈ s, productPowerMajorant R.A M A (y.val * radial R.A t) ≤ E y) := by
  letI : MeasurableSpace R.A.G1 := borel _
  obtain ⟨K, hK, hb⟩ := uniform_power_bound R N σ A M hσ ((le_max_left σ 0).trans_lt hA) hM
  have hi (u : ℝ) : Integrable (fun y : R.A.G1 =>
      productPowerMajorant R.A M A (y.val * radial R.A u)) R.probe.domain.measure :=
    (hb ⟨Real.exp u, Real.exp_pos u⟩).1
  refine ⟨⟨K, hK, ?_⟩, ?_⟩
  · intro u
    refine ⟨hi u, ?_⟩
    have he : Real.exp u ^ (-σ) = Real.exp (-σ * u) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm]
    simpa only [radial, he] using (hb ⟨Real.exp u, Real.exp_pos u⟩).2
  · intro u
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
      (continuous_rescaleCost R.A A u).continuousOn
    let D := max C 0
    refine ⟨Set.Ioo (u - 1) (u + 1),
      Ioo_mem_nhds (by linarith) (by linarith),
      fun y => D * productPowerMajorant R.A M A (y.val * radial R.A u),
      (hi u).const_mul D, ?_⟩
    filter_upwards [] with y
    intro t ht
    exact (product_rescale R.A M A u t y.val).trans
      (mul_le_mul_of_nonneg_right ((hC ⟨t, (⟨ht.1.le, ht.2.le⟩), rfl⟩).trans (le_max_left _ _)) (productPowerMajorant_nonneg R.A M A _))

end DedekindZetaZeroFree.SheetRescaling

end
