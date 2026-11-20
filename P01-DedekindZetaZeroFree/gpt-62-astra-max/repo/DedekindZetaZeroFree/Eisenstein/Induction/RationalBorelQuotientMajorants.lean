module
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.TwoCellFormulaAndOutgoingProfiles
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuity

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds

@[expose] public section

section

noncomputable section
open scoped Classical NumberField NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
    {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

private alias normalized_mem := Actual.FlatSectionContinuity.normalized_mem

theorem source_radial_norm (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (s : ℂ) (r : KPMsFixedHaarDisintegration.Radius)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D)
    (g : KPMsRationalCompactCrossPairing.NormOne F ζ hζ D) :
    ‖(A.sourceFlat s f).val
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (A.atlasLevel U)).radial.slot r * g.val)‖ =
      r.val ^ ((2 : ℝ) / 3 + s.re) * ‖A.fullSourceAngular f (Quotient.mk _ g)‖ := by
  rw [(KPMsRationalCompactCrossPairing.full_radial_angular_decomposition
    (A := A) U s r f 0 g).1, norm_mul]
  congr 1
  rw [KPGlobalExceptionalParameter.realLogPower, Complex.norm_exp,
    Real.rpow_def_of_pos r.property]
  simp [Complex.mul_re, mul_comm]

theorem source_iwasawa_norm_bound (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s g,
      ‖(A.sourceFlat s f).val g‖ ≤
        B * (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) ^
          ((2 : ℝ) / 3 + s.re) := by
  letI := A.fullCompact
  let c : C(KPMsRationalCompactCrossPairing.FullOmega F ζ hζ D, ℂ) :=
    ⟨A.fullSourceAngular f, KPMsRationalCompactCrossPairing.actual_full_source_continuous A f⟩
  refine ⟨‖c‖, norm_nonneg _, ?_⟩
  intro s g
  let r : KPMsFixedHaarDisintegration.Radius :=
    ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ),
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩
  let a := KPMsFixedHaarDisintegration.radialSection F ζ hζ
    (H.disintegration (A.atlasLevel U)).radial.slot r
  let k : KPMsRationalCompactCrossPairing.NormOne F ζ hζ D :=
    ⟨a⁻¹ * g, normalized_mem A U g⟩
  have hg : a * k.val = g := by dsimp [k]; group
  have hs := source_radial_norm A U s r f k
  rw [hg] at hs
  rw [hs]
  exact (mul_le_mul_of_nonneg_left (c.norm_coe_le_norm (Quotient.mk _ k))
    (Real.rpow_nonneg (le_of_lt r.property) _)).trans_eq (mul_comm _ _)
end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm

end
end

section

noncomputable section
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm
open KPLiteralExceptionalResidue KPChamberHeight
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
    {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

theorem source_actual_height_decay (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : KPMsRationalCompactCrossPairing.G F ζ hζ,
      ‖(A.sourceFlat s f).val g‖ ≤ B * (KPChamberHeight.height F (actualBaseRowLine F)
        (coveredHeightProjection F ζ hζ g)) ^ (-2 * (2 / 3 + s.re)) := by
  obtain ⟨B, hB, hb⟩ := source_iwasawa_norm_bound A U f
  obtain ⟨m, M, hm, hmM, hdist⟩ := actualBaseRowHeight_compact_upper_bounds F ζ hζ D.K D.compact
  have hM := hm.trans_le hmM
  let a := 2 / 3 + s.re
  refine ⟨B * (M⁻¹) ^ (-2 * a), mul_nonneg hB (Real.rpow_nonneg (inv_nonneg.mpr hM.le) _), fun g => ?_⟩
  obtain ⟨t, x, k, hg⟩ := D.decomposition g
  obtain ⟨C, hC, hproj⟩ := (covered_torus_root_upper F ζ hζ t x)
  have hd := (hdist C k hC).2
  rw [hproj, ← map_mul, ← hg] at hd
  let h := KPChamberHeight.height F (actualBaseRowLine F) (coveredHeightProjection F ζ hζ g)
  let ht := KPChamberHeight.height F (actualBaseRowLine F)
    (coveredHeightProjection F ζ hζ (t.val * KPGlobalTorusFunctionData.N F ζ hζ x))
  have hh : 0 < h := height_pos F _ _
  have hdelta : (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a = ht ^ (-2 * a) := by
    rw [← actualBaseRowHeight_torus_root_modulus F ζ hζ t x]
    simpa only [Int.cast_neg, Int.cast_ofNat] using (Real.rpow_intCast_mul (height_pos F _ _).le (-2) a).symm
  calc
    _ ≤ B * (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a := by
      have hn := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ D t x k
      rw [← hg] at hn
      simpa only [hn, a] using (hb s g)
    _ = B * ht ^ (-2 * a) := by rw [hdelta]
    _ ≤ B * (M⁻¹ * h) ^ (-2 * a) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos (inv_pos.mpr hM) hh) ((inv_mul_le_iff₀ hM).mpr hd) (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by dsimp [a]; linarith))) hB
    _ = (B * (M⁻¹) ^ (-2 * a)) * h ^ (-2 * a) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hM.le) hh.le]; ring

end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm

end
end

noncomputable section
open MeasureTheory
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def rationalEquiv : Matrix.ProjGenLinGroup (Fin 2) F ≃* KPRationalAdelicSplitting.RationalPGL2 F :=
  QuotientGroup.quotientMulEquivOfEq Matrix.GeneralLinearGroup.center_eq_range_scalar
@[simp] private theorem rationalEquiv_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalEquiv F (Matrix.ProjGenLinGroup.mk m) = KPRationalAdelicSplitting.rationalPGLQuotient F m := QuotientGroup.quotientMulEquivOfEq_mk _ m
@[simp] private theorem rationalEquiv_lift (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (rationalEquiv F g) = KPLiteralRaw.rationalLift F ζ hζ g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk m =>
    rw [rationalEquiv_mk, KPLiteralExceptionalResidue.rationalLift_eq_constructed]
    rfl

variable {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
    {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

 theorem literal_compact_majorants
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D)
    (C : Set (KPMsRationalCompactCrossPairing.G F ζ hζ)) (hC : IsCompact C) :
    ∃ b : KPChamberBruhatTwoCells.RationalQuotient F → ℝ, Summable b ∧ ∀ q g, g ∈ C →
      ‖(A.sourceFlat s f).val
        (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) * g)‖ ≤ b q := by
  obtain ⟨B, hB, hb⟩ := source_actual_height_decay A U f s hs
  obtain ⟨m, M, hm, hmM, hdist⟩ := KPChamberHeight.compact_uniform_height F
    ((KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ) '' C)
    (hC.image (KPLiteralExceptionalResidue.coveredHeightProjection_continuous F ζ hζ))
  obtain ⟨d, hd, hcompare⟩ := KPChamberHeight.height_one_compare F
  let a := 2 / 3 + s.re
  have ha : 1 < a := by dsimp [a]; linarith
  let index := fun q => KPLiteralExceptionalResidue.chamberCosetIndex F q
  have hinj :=
    (KPLiteralExceptionalResidue.chamberCosetIndex_injective F).comp Function.injective_id
  refine ⟨fun q => (B * m ^ (-2 * a)) * KPHeightSeries.term Projectivization.mulHeight a (index q),
    ((KPHeightSeries.relativeHeight_summable_tail F a ha).1.comp_injective hinj).mul_left _, ?_⟩
  intro q g hg
  have hl : m * Projectivization.mulHeight (index q) ≤
      KPChamberHeight.height F
        (KPChamberHeight.bottomRow F (Quotient.out q))
        (KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ g) := by
    dsimp [index]
    rw [KPLiteralExceptionalResidue.chamberCosetIndex_mulHeight_out]
    exact (mul_le_mul_of_nonneg_left (hcompare _).2.1 hm.le).trans
      (hdist _ _ ⟨g, hg, rfl⟩).1
  have he := hb (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) * g)
  rw [KPLiteralExceptionalResidue.actualBaseRowHeight_rational_mul] at he
  have hp := Real.rpow_le_rpow_of_nonpos
    (mul_pos hm (Projectivization.mulHeight_pos (index q))) hl (show -2 * a ≤ 0 by linarith)
  refine he.trans ((mul_le_mul_of_nonneg_left hp hB).trans_eq ?_)
  rw [Real.mul_rpow hm.le (Projectivization.mulHeight_pos _).le]
  dsimp [KPHeightSeries.term, a]
  ring

end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual

end
