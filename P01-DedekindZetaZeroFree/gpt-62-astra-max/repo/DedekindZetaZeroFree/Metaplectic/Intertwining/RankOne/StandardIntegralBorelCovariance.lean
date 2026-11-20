module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CompactBorelHeisenbergAction
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AffineInvariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellActualBorel
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

local notation "LocalCompletion" => LocalField F q

private theorem localAbs_inv (a : LocalCompletionˣ) :
    localAbs LocalCompletion a⁻¹ = (localAbs LocalCompletion a)⁻¹ := by
  have hh := localAbs_mul LocalCompletion a a⁻¹
  rw [mul_inv_cancel, localAbs_one] at hh
  exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hh.symm)

private theorem scalar_weyl (s : ℂ) (b : S.borel.B) :
    (localAbs LocalCompletion (S.borel.coordinate (S.borel.retract b)) : ℂ) *
      inducingScalar S.borel s (S.borel.torus (S.borel.weyl (S.borel.retract b))) =
        inducingScalar S.borel (-s) b := by
  let a := S.borel.coordinate (S.borel.retract b)
  have hc : (localAbs LocalCompletion a : ℂ) =
      Complex.exp (Real.log (localAbs LocalCompletion a) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (localAbs_pos LocalCompletion a)]
  simp only [inducingScalar, deltaHalf, normPower, S.borel.retract_torus,
    KPRankOneReversePairGeneric.GraphTwist.coordinate_weyl_inverse,
    localAbs_inv, Real.log_inv, Complex.ofReal_neg]
  rw [hc, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem source_weyl_action_jacobian (ε : Sign) (s : ℂ) (b : S.borel.B)
    (v : InducedModule P) :
    (localAbs LocalCompletion (S.borel.coordinate (S.borel.retract b)) : ℂ) •
      inducingAction S.borel P (sourceSign ε) s
        (S.borel.torus (S.borel.weyl (S.borel.retract b))) v =
      inducingAction S.borel P (targetSign ε) (-s) b v := by
  let torus₀ := S.borel.torus (S.borel.weyl (S.borel.retract b))
  change (localAbs LocalCompletion (S.borel.coordinate (S.borel.retract b)) : ℂ) •
    (inducingScalar S.borel s (torus₀) •
      borelAction S.borel P (sourceSign ε)
        (torus₀) v) =
    inducingScalar S.borel (-s) b • borelAction S.borel P (targetSign ε) b v
  rw [smul_smul, (scalar_weyl F ζ hζ q S s b)]
  congr 1
  cases ε with
  | plus =>
    change tau P (S.borel.retract (torus₀)) v =
      tau P (S.borel.weyl (S.borel.retract b)) v
    rw [S.borel.retract_torus]
  | minus =>
    change tau P (S.borel.weyl (S.borel.retract
      (torus₀))) v = tau P (S.borel.retract b) v
    rw [S.borel.retract_torus, CompactBorel.weyl_involutive F ζ hζ q S P]

theorem integral_affine_jacobian (μ : Measure LocalCompletion) [μ.IsAddHaarMeasure]
    (a : LocalCompletionˣ) (t : LocalCompletion) (f : LocalCompletion → ℂ) :
    (∫ x, f ((a : LocalCompletion) * x + t) ∂μ) =
      ((localAbs LocalCompletion a)⁻¹ : ℂ) * ∫ x, f x ∂μ := by
  have he : MeasurableEmbedding (fun x : LocalCompletion => (a : LocalCompletion) * x) :=
    (Homeomorph.mulLeft₀ (a : LocalCompletion) a.ne_zero).isClosedEmbedding.measurableEmbedding
  have hh := he.integral_map (μ := μ) (fun x => f (x + t))
  rw [NonarchimedeanHaarScaling.map_mul LocalCompletion μ a a.ne_zero,
    ← actualAbs_units F q a, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (localAbs_pos LocalCompletion a).le,
    integral_add_right_eq_self f t] at hh
  simpa [Complex.real_smul] using hh.symm

variable (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure] (ε : Sign) (s : ℂ)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε)) (b : S.borel.B) (g : ActualCover F ζ hζ q)
    (h : actualTorus F ζ hζ q)

theorem standardIntegral_borel_covariance :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ (b * g) h =
      ∫ x : LocalField F q,
        (inducingAction S.borel P (targetSign ε) (targetParameter ε s) b
          ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ).val
            (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * g))).val h ∂μ := by
  let f := compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition b
  let a := (S.borel.coordinate (S.borel.retract b))⁻¹
  let T : LocalField F q → ℂ := fun x =>
    (inducingAction S.borel P (sourceSign ε) (sourceParameter ε s)
      (S.borel.torus (S.borel.weyl (S.borel.retract b)))
      (f.val (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * g))).val h
  have hp (x : LocalField F q) :
      (f.val (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * (b * g))).val h =
        T ((a : LocalField F q) * x + Multiplicative.toAdd t) := by
    have hh := congrArg (fun z : ActualCover F ζ hζ q => z * g)
      (CompactBorel.kernel_borel F ζ hζ q S P ε b t ht x)
    simp only [mul_assoc] at hh ⊢
    rw [hh, f.property.1]
    simp only [T, a, mul_assoc]
  change (∫ x, (f.val (kernelW (LocalField F q) S.borel ε *
    S.borel.upperRoot (Multiplicative.ofAdd x) * (b * g))).val h ∂μ) = _
  simp_rw [hp]
  rw [integral_affine_jacobian F q μ a (Multiplicative.toAdd t) T,
    localAbs_inv]
  simp only [Complex.ofReal_inv, inv_inv]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  exact congrArg (fun v : InducedModule P => v.val h)
    (source_weyl_action_jacobian F ζ hζ q S P ε (sourceParameter ε s) b
      (f.val (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * g)))

theorem standardIntegral_borel_coordinate :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ (b * g) h =
      inducingScalar S.borel (targetParameter ε s) b *
        standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ g
          (h * (if targetSign ε = .plus then S.borel.retract b else S.borel.weyl (S.borel.retract b))) := by
  rw [standardIntegral_borel_covariance F ζ hζ q S P μ ε s φ b g h]
  unfold standardIntegralCoordinate
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  cases ε <;> rfl

end DedekindZetaZeroFree.KPRankOneShellActualBorel

end
