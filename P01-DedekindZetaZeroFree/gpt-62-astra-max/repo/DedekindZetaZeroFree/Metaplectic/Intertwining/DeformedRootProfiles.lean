module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RelativeBorelRootProfiles

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation

variable (F : Type) [Field F] [NumberField F]
 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)

local notation "LocalCompletion" => LocalField F q

private theorem scalar_deformation_value
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP f s).val g).val 1 =
      normPower LocalCompletion
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) * f.val g := KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.deformedTest_scalar_value
    F ζ hζ q S P hP (scalarCoordinateEquiv F ζ hζ q S P hP)
    (fun _ _ _ => rfl) f s g

def diagonalAnchorTwist (π : LocalCompletionˣ) (i : Fin 3) (s : ℂ) : ℂ :=
  normPower LocalCompletion
    (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))))
    (sourceParameter .minus s)

theorem eventual_deformed_test_root_profile
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : LocalCompletionˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (f : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m f →
      ∀ (s : ℂ) (t : LocalCompletion),
      ((deformedTest F ζ hζ q S P hP f s).val
        (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) t)).val 1 =
        diagonalAnchorTwist F ζ hζ q S π i s *
          (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ)) t := by
  obtain ⟨M, hM⟩ := eventual_normalized_test_root_profile F ζ hζ q S P hP htame π hπ
  obtain ⟨D, hD⟩ :=
    KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.eventually_split_subset_open
      F ζ hζ q (S.iwasawa.compact.toOpenSubgroup : Set (ActualCover F ζ hζ q))
      S.iwasawa.compact.toOpenSubgroup.isOpen S.iwasawa.compact.toOpenSubgroup.one_mem
  refine ⟨max M D, fun m hm i f hf s t => ?_⟩
  rw [scalar_deformation_value, hM m ((le_max_left M D).trans hm) i f hf t]
  by_cases ht : t ∈ rootLevelSet F ζ hζ q m
  · have hk := hD m ((le_max_right M D).trans hm) ht
    rw [Set.indicator_of_mem ht]
    unfold diagonalAnchorTwist normPower
    rw [KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.iwasawa_norm_right_compact
      F ζ hζ q S _ ⟨_, hk⟩]
  · simp only [Set.indicator_of_notMem ht, mul_zero]

theorem diagonalAnchorTwist_eq
    (π : LocalCompletionˣ) (i : Fin 3) (s : ℂ) :
    diagonalAnchorTwist F ζ hζ q S π i s =
      normPower LocalCompletion (π ^ i.val) (sourceParameter .minus s) *
        diagonalAnchorTwist F ζ hζ q S π 0 s := by
  let t : actualTorus F ζ hζ q :=
    ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ i.val), by
      refine ⟨KubotaRankTwo.d LocalCompletion (π ^ i.val) 1, ?_, ?_, ?_⟩
      · rfl
      · simp [KubotaRankTwo.d]
      · simp [KubotaRankTwo.d]⟩
  have ht : (S.borel.torus t : ActualCover F ζ hζ q) = eta F ζ hζ q π i := by
    rw [S.torus_full]
    simp [t, eta]
  have hc : S.borel.coordinate (S.borel.retract (S.borel.torus t)) = π ^ i.val := by
    rw [S.borel.retract_torus]
    exact S.coordinate_lift t _ rfl
  have he : eta F ζ hζ q π (0 : Fin 3) = 1 := by
    change KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ 0) = 1
    rw [pow_zero]
    have h1 : KPPGLLocalCover.A F ζ hζ (Sum.inr q) 1 =
        ((S.borel.cubeLift 1 : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) := by
      rw [S.cube_actual]; simp
    rw [h1, map_one]; rfl
  unfold diagonalAnchorTwist normPower
  rw [he, one_mul, ← ht,
    KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.iwasawa_norm_left_borel
      F ζ hζ q S (S.borel.torus t), hc]
  rw [Real.log_mul (ne_of_gt (localAbs_pos LocalCompletion _))
    (ne_of_gt (localAbs_pos LocalCompletion _))]
  push_cast
  rw [mul_add, Complex.exp_add]

theorem eventual_deformed_test_kernel_profile
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : LocalCompletionˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (f : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m f →
      ∀ (u : LocalCompletionˣ) (b : BL F ζ hζ q S P),
      (b : ActualCover F ζ hζ q) =
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : LocalCompletionˣ) : LocalCompletion) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) →
      ∀ (s : ℂ) (x : LocalCompletion),
      ((deformedTest F ζ hζ q S P hP f s).val
        (kernelW LocalCompletion S.borel .minus *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) (u : LocalCompletion) *
          (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 =
        (chi F ζ hζ q S P hP .minus b *
          normPower LocalCompletion (u⁻¹ ^ (2 : ℕ)) (sourceParameter .minus s)) *
        (diagonalAnchorTwist F ζ hζ q S π i s *
          (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ))
            (x + ((π ^ i.val : LocalCompletionˣ) : LocalCompletion) / (u : LocalCompletion))) := by
  obtain ⟨M, hM⟩ := eventual_deformed_test_root_profile F ζ hζ q S P hP htame π hπ
  refine ⟨M, fun m hm i f hf u b hb s x => ?_⟩
  have hc : S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b)) =
      u⁻¹ ^ (2 : ℕ) := relative_borel_coordinate F ζ hζ q S P u b hb
  rw [signed_double_kernel_diagonal_index, ← hb, diagonalLift_index_zero_eq_eta]
  have hw : KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q)
      (x + ((π ^ i.val : LocalCompletionˣ) : LocalCompletion) / (u : LocalCompletion)) *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) =
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q)
        (x + ((π ^ i.val : LocalCompletionˣ) : LocalCompletion) / (u : LocalCompletion)) := by
    exact ((mul_inv_eq_iff_eq_mul).mp
      (KPRankOneJacquetZeroCompactCoefficients.weyl_conjugates_upper F ζ hζ q _)).symm
  simp only [mul_assoc]
  rw [hw]
  have hcov :=
    KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.deformedTest_scalar_borel_covariance
      F ζ hζ q S P hP (scalarCoordinateEquiv F ζ hζ q S P hP) (fun _ _ _ => rfl)
      f b s (eta F ζ hζ q π i *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.N F ζ hζ (Sum.inr q)
          (x + ((π ^ i.val : LocalCompletionˣ) : LocalCompletion) / (u : LocalCompletion))))
  change ((deformedTest F ζ hζ q S P hP f s).val _).val 1 =
    _ * ((deformedTest F ζ hζ q S P hP f s).val _).val 1 at hcov
  rw [hcov, hc, ← mul_assoc, hM m hm i f hf]
  ring

theorem eventual_deformed_test_outer_mass_transport
    (μ : Measure LocalCompletion) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : LocalCompletionˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (f₀ fᵢ : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0, 0)) m f₀ →
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m fᵢ →
      ∀ (u : LocalCompletionˣ) (b : BL F ζ hζ q S P),
      (b : ActualCover F ζ hζ q) =
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : LocalCompletionˣ) : LocalCompletion) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) → ∀ s : ℂ,
      (∫ x in lowShell F q,
        ((deformedTest F ζ hζ q S P hP fᵢ s).val
          (kernelW LocalCompletion S.borel .minus *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) (u : LocalCompletion) *
            (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 ∂μ) =
        normPower LocalCompletion (π ^ i.val) (sourceParameter .minus s) *
      (∫ x in lowShell F q,
        ((deformedTest F ζ hζ q S P hP f₀ s).val
          (kernelW LocalCompletion S.borel .minus *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) (u : LocalCompletion) *
            (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 ∂μ) := by
  obtain ⟨M, hM⟩ := eventual_deformed_test_kernel_profile F ζ hζ q S P hP htame π hπ
  obtain ⟨D, hD⟩ :=
    KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry
      F ζ hζ q S P hP htame π hπ .minus
  refine ⟨max M D, fun m hm i f₀ fᵢ hf₀ hfᵢ u b hb s => ?_⟩
  have hmM := (le_max_left M D).trans hm
  obtain ⟨K, hK, hc, hn, hd, hr, ho, hz, hs, hchart⟩ := hD m ((le_max_right M D).trans hm)
  have hv := RootResidualGeometry.relative_diagonal_exponent_dvd
    F ζ hζ q S P hP b u (relative_borel_coordinate F ζ hζ q S P u b hb)
  have hφ : Function.support
      ((rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ))) ⊆
      (valuation LocalCompletion).integer := by
    intro x hx
    apply hs
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  simp_rw [hM m hmM i fᵢ hfᵢ u b hb,
    hM m hmM (0 : Fin 3) f₀ (by simpa only [Fin.val_zero, Int.ofNat_zero] using hf₀) u b hb]
  simp only [Fin.val_zero, pow_zero, Units.val_one, one_div]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have heq : (∫ x in lowShell F q,
      (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ))
        (x + ((π ^ i.val : LocalCompletionˣ) : LocalCompletion) / (u : LocalCompletion)) ∂μ) =
      ∫ x in lowShell F q,
        (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ)) (x + (u : LocalCompletion)⁻¹) ∂μ :=
    RootResidualGeometry.diagonal_root_residual_integral_eq LocalCompletion
      μ π hπ u hv i _ hφ
  rw [heq, diagonalAnchorTwist_eq F ζ hζ q S π i s]
  ring

theorem diagonal_deformation_eq_evaluation_monomial
    (π : LocalCompletionˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (s : ℂ) :
    normPower LocalCompletion (π ^ i.val) (sourceParameter .minus s) =
      (evaluationUnit LocalCompletion .minus s : ℂ) ^ (i.val : ℤ) := by
  have hp : localAbs LocalCompletion π = (residueCardinality LocalCompletion : ℝ)⁻¹ := by
    simp [localAbs, hπ, Real.rpow_neg_one]
  rw [normPower, (KPLocalPrincipalSeriesNormWeights.absolute_pow
    (localAbs LocalCompletion) (localAbs_one _) (localAbs_mul _) π i.val), Real.log_pow, hp, Real.log_inv]
  change Complex.exp (-s * ((i.val : ℝ) * -Real.log
      (residueCardinality LocalCompletion : ℝ) : ℝ)) =
    (Complex.exp (-s * (Real.log (residueCardinality LocalCompletion : ℝ) : ℂ)))⁻¹ ^ i.val
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end
