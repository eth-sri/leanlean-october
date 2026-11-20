module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.InducingDataConversions
public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CubicShellCoefficientsAndBorelPhases
public import DedekindZetaZeroFree.Analysis.GeometricDenominator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RadialMajorantsAndProductIntegrability

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.TameQiConditionalObstruction
open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation KPTameTransposeLiteral
open KPTameTransposeBaseChart KPTameTransposeBaseChart.AugmentationSteps
open KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
variable (F : Type) [Field F] [NumberField F]
 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)
local notation "LocalCompletion" => LocalField F q

def unitRegion : Set LocalCompletion :=
 ((valuation LocalCompletion).integer : Set LocalCompletion) \
  ((valuation LocalCompletion).integer.subtype ''
   (IsLocalRing.maximalIdeal (valuation LocalCompletion).integer : Set (valuation LocalCompletion).integer))
theorem anchor_monomial (π : LocalCompletionˣ) :
 ∃ d : ℤ, ∀ s : ℂ, diagonalAnchorTwist F ζ hζ q S π 0 s =
 (evaluationUnit LocalCompletion .minus s : ℂ)^d := by
 let y := S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart
  (eta F ζ hζ q π 0 * KPPGLLocalCover.W F ζ hζ (Sum.inr q))))
 let d := WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
  LocalCompletion (valuation LocalCompletion (y : LocalCompletion)))
 refine ⟨-d, fun s => ?_⟩
 have hqpos : 0 < (residueCardinality LocalCompletion : ℝ) := by exact_mod_cast Nat.card_pos
 have hl : (Real.log (localAbs LocalCompletion y) : ℂ) =
  (d : ℂ) * (Real.log (residueCardinality LocalCompletion : ℝ) : ℂ) := by
  rw [localAbs, Real.log_rpow hqpos]
  simp only [d]
  push_cast
  rfl
 change normPower LocalCompletion y (-s) = _
 simp only [normPower, hl, evaluationUnit, reduceCtorEq, ite_false,
  rUnit, Units.val_inv_eq_inv_val, Units.val_mk0, r, ← Complex.exp_neg]
 rw [← Complex.exp_int_mul]
 congr 1
 push_cast
 ring
include hP in
theorem eventual_all_tests
 (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
 (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
 ∃ M : ℕ, ∀ m ≥ M, ∃ f : Fin 3 → scalarSections F ζ hζ q S P hP .minus,
 ∀ i : Fin 3, IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π ((i.val : ℤ),0)) m (f i) := by
 obtain ⟨M, hM⟩ := KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry F ζ hζ q S P hP htame π hπ .minus
 refine ⟨M, fun m hm => ?_⟩
 obtain ⟨K, hK, _hc, hw, hd, _⟩ := hM m hm
 obtain ⟨f, hf⟩ := KPTameJacquetBruhatTests.BruhatScalarTests.scalar_characteristic_sections F ζ hζ q S P hP .minus π m K hK hw hd
 have heta (i : Fin 3) : KPTameJacquetBruhatTests.Raw.eta F ζ hζ q π i = diagonalLift F ζ hζ q π ((i.val : ℤ),0) := by
  simp [KPTameJacquetBruhatTests.Raw.eta, diagonalLift, KPPGLLocalCover.A, KPStandardLocalRootLifts.A]
 have h1 : (1 : ActualCover F ζ hζ q) ∈ splitCongruenceSet F ζ hζ q m := by
  refine ⟨1, ?_⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (1 : KPLocalCube.LocalGL2 F q)) = 1
  rw [show KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (1 : KPLocalCube.LocalGL2 F q) = 1 from rfl, map_one]
 refine ⟨f, fun i => ⟨(hf.1 i).1, ?_, ?_⟩⟩
 · intro g hg
   obtain ⟨b, k, hk, rfl⟩ := (hf.1 i).2 hg
   exact ⟨b, k, hk, by rw [heta]⟩
 · rw [← heta]
   simpa using (hf.2.2 i 1 h1)
include hP in
theorem eventual_cleared_base_value
 (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
 (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
 (hnormalized : RawNormalizedExtension F ζ hζ q S P)
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
 (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
 ∃ M : ℕ, ∀ m ≥ M, ∀ s : ℂ, convergenceHalfPlane .minus s →
 denominator (LocalField F q) .minus s * baseChartChamberIntegral F ζ hζ q S P hP μ π m s =
 diagonalAnchorTwist F ζ hζ q S π 0 s * ((rootMass F ζ hζ q μ m : ℂ) * (μ.real (unitRegion F q) : ℂ)) := by
 obtain ⟨M₁, hM₁⟩ := CubeShell.eventual_baseChart_cube_shell_decomposition F ζ hζ q S P hP μ htame π hπ
 obtain ⟨M₂, hM₂⟩ := CubeShell.eventual_baseChart_reverse_cube_shell_coefficient F ζ hζ q S P hP μ htame hnormalized π hπ
 refine ⟨max M₁ M₂, fun m hm => ?_⟩
 let valuation₀ := valuation (LocalField F q)
 let c : ℂ := (rootMass F ζ hζ q μ m : ℂ) *
   (μ.real (((valuation₀).integer : Set (LocalField F q)) \
     ((valuation₀).integer.subtype ''
       (IsLocalRing.maximalIdeal (valuation₀).integer :
         Set (valuation₀).integer))) : ℂ)
 let a : ℂ → ℂ := fun s =>
   KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry.diagonalAnchorTwist
     F ζ hζ q S π (0 : Fin 3) s
 have hchamber (s : ℂ) (hs : convergenceHalfPlane .minus s) :
     denominator (LocalField F q) .minus s *
       baseChartChamberIntegral F ζ hζ q S P hP μ π m s = a s * c := by
   let z : ℂ := (residueCardinality (LocalField F q) : ℂ) *
     (evaluationUnit (LocalField F q) .minus s : ℂ) ^ 6
   have hz : z = (t (LocalField F q) s)⁻¹ := by
     change (residueCardinality (LocalField F q) : ℂ) *
       (KPRankOneRootParameter.r (LocalField F q) s)⁻¹ ^ 6 = (t (LocalField F q) s)⁻¹
     simp [t, mul_inv_rev, inv_pow, mul_comm]
   have hnorm : ‖z‖ < 1 := by
     rw [hz]
     simpa using
       (convergence_iff_geometric (LocalField F q) .minus s).mp hs
   have hden : denominator (LocalField F q) .minus s = 1 - z := rfl
   rw [hM₁ m (le_trans (le_max_left _ _) hm) s hs]
   simp_rw [hM₂ m (le_trans (le_max_right _ _) hm) _ s hs]
   rw [hden]
   change (1 - z) * (∑' k : ℕ, a s * (c * z ^ k)) = a s * c
   simp_rw [← mul_assoc]
   exact CubeShell.geometric_denominator_tsum z (a s * c) hnorm
 exact hchamber
end DedekindZetaZeroFree.TameQiConditionalObstruction

end
