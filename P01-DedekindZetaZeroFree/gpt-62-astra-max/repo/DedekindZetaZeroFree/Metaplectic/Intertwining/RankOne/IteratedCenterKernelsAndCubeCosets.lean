module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.JointMellinBetaIntegrability
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicCharacterProjection

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneLiftedDiagonal

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private theorem central_inducing_plus (B : Binding F ζ hζ q A P)
    (hcentral : ∀ e : rootsOfUnity 3 F, B.centralTorus e ∈ T.C)
    (hcharacter : ∀ e : rootsOfUnity 3 F, T.ω ⟨B.centralTorus e, hcentral e⟩ = B.eta e)
    (z : ℂ) (e : rootsOfUnity 3 F) (V : CenterModule T) :
    centerInducingAction F ζ hζ q T A .plus z (A.torus (B.centralTorus e)) V =
      (B.eta e : ℂ) • V := by
  apply Subtype.ext
  funext h
  change inducingScalar A z (A.torus (B.centralTorus e)) * V.val (h * A.retract (A.torus (B.centralTorus e))) =
    (B.eta e : ℂ) * V.val h
  rw [A.retract_torus]
  rw [(Subgroup.mem_center_iff.mp (T.central (hcentral e)) h), V.property ⟨B.centralTorus e, hcentral e⟩ h]
  simp [inducingScalar, deltaHalf, A.retract_torus, B.central_coordinate, normPower,
    localAbs_one, hcharacter]
local notation "LocalCompletion" => LocalField F q

private theorem modulus_root (v : LocalCompletionˣ) :
    normPower LocalCompletion (v ^ 2) (1 / 2) =
      (KPCubicHaar.abs LocalCompletion (v : LocalCompletion) : ℂ) := by
  have he : localAbs LocalCompletion v = KPCubicHaar.abs LocalCompletion v := by
    simp only [localAbs, KPCubicHaar.abs, if_neg v.ne_zero, Real.rpow_intCast]
    rfl
  have hpow : localAbs LocalCompletion (v ^ 2) = localAbs LocalCompletion v ^ 2 := by
    simp [pow_two, localAbs_mul]
  rw [normPower, hpow, Real.log_pow]
  have hx : (1 / 2 : ℂ) * ((2 : ℝ) * Real.log (localAbs LocalCompletion v) : ℝ) =
      (Real.log (localAbs LocalCompletion v) : ℂ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat] at ⊢
  rw [hx, ← Complex.ofReal_exp, Real.exp_log (localAbs_pos LocalCompletion v), he]
private theorem root_inducing_plus (B : Binding F ζ hζ q A P)
    (z : ℂ) (v : LocalCompletionˣ) (V : CenterModule T) :
    centerInducingAction F ζ hζ q T A .plus z (A.torus (B.rootTorus v)) V =
      (KPCubicHaar.abs LocalCompletion (v : LocalCompletion) : ℂ) •
        (normPower LocalCompletion (v ^ 2) z •
          centerTorus F ζ hζ q T A .plus (B.rootTorus v) V) := by
  change (inducingScalar A z (A.torus (B.rootTorus v))) •
    centerTorus F ζ hζ q T A .plus (A.retract (A.torus (B.rootTorus v))) V = _
  simp only [inducingScalar, deltaHalf, A.retract_torus, B.coordinate_eq, smul_smul]
  rw [modulus_root F q v]
private theorem upper_inducing_plus (z : ℂ) (x : LocalCompletion) (V : CenterModule T) :
    centerInducingAction F ζ hζ q T A .plus z
      (A.upperRoot (Multiplicative.ofAdd x)) V = V := by
  simp [centerInducingAction, inducingScalar, deltaHalf, A.retract_upperRoot,
    normPower, localAbs_one]

theorem center_induced_bruhat_plus (B : Binding F ζ hζ q A P)
    (hcentral : ∀ e : rootsOfUnity 3 F, B.centralTorus e ∈ T.C)
    (hcharacter : ∀ e : rootsOfUnity 3 F, T.ω ⟨B.centralTorus e, hcentral e⟩ = B.eta e)
    (z : ℂ) (f : centerSectionSpace F ζ hζ q T A .plus z)
    (s : LocalCompletion) (v : LocalCompletionˣ) :
    f.val (kernelW LocalCompletion A .plus * nLift F ζ hζ q
      (-((v⁻¹ : LocalCompletionˣ) : LocalCompletion)) * openCoordinate F ζ hζ q s) =
      (B.eta (kappa F ζ hζ q v s) : ℂ) •
        ((KPCubicHaar.abs LocalCompletion (v : LocalCompletion) : ℂ) •
          (normPower LocalCompletion (v ^ 2) z •
            centerTorus F ζ hζ q T A .plus (B.rootTorus v)
              (f.val (openCoordinate F ζ hζ q (s + (v : LocalCompletion)))))) := by
  simp only [kernelW, B.weyl_eq]
  change f.val ((signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q _ *
    ((signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q s)) = _
  rw [← mul_assoc, (lifted_bruhat_identity F ζ hζ q v s)]
  rw [← B.central_eq, ← B.torus_eq, ← B.upper_eq]
  simp only [mul_assoc]
  rw [f.property.1, f.property.1, f.property.1]
  rw [upper_inducing_plus, root_inducing_plus F ζ hζ q T A P B,
    central_inducing_plus F ζ hζ q T A P B hcentral hcharacter]
  rfl

theorem center_forward_kernel (I : IwasawaData A)
    (μ : Measure LocalCompletion) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ)
    (B : Binding F ζ hζ q A P)
    (hcentral : ∀ e : rootsOfUnity 3 F, B.centralTorus e ∈ T.C)
    (hcharacter : ∀ e : rootsOfUnity 3 F, T.ω ⟨B.centralTorus e, hcentral e⟩ = B.eta e)
    (z : ℂ) (hz : convergenceHalfPlane .plus z)
    (f : centerSectionSpace F ζ hζ q T A .plus z)
    (s : LocalCompletion) (h : H) :
    Integrable (fun v : LocalCompletionˣ =>
      (B.eta (kappa F ζ hζ q v s) : ℂ) * normPower LocalCompletion (v ^ 2) z *
        (centerTorus F ζ hζ q T A .plus (B.rootTorus v)
          (f.val (openCoordinate F ζ hζ q (s + (v : LocalCompletion))))).val h)
      (multiplicativeMeasure F q μ) ∧
    ((J.op .plus z f).val (openCoordinate F ζ hζ q s)).val h =
      ∫ v : LocalCompletionˣ,
        (B.eta (kappa F ζ hζ q v s) : ℂ) * normPower LocalCompletion (v ^ 2) z *
          (centerTorus F ζ hζ q T A .plus (B.rootTorus v)
            (f.val (openCoordinate F ζ hζ q (s + (v : LocalCompletion))))).val h
        ∂multiplicativeMeasure F q μ := by
  have hj := J.integral_eq .plus z hz f (openCoordinate F ζ hζ q s) h
  have hs := KPRankOneBruhatKernelTransport.inverse_substitution LocalCompletion μ
    (fun x => (f.val (kernelW LocalCompletion A .plus * nLift F ζ hζ q x *
      openCoordinate F ζ hζ q s)).val h)
    (fun v => (B.eta (kappa F ζ hζ q v s) : ℂ) * normPower LocalCompletion (v ^ 2) z *
      (centerTorus F ζ hζ q T A .plus (B.rootTorus v)
        (f.val (openCoordinate F ζ hζ q (s + (v : LocalCompletion))))).val h)
    hj.1 (by
      intro v
      rw [center_induced_bruhat_plus F ζ hζ q T A P B hcentral hcharacter]
      change (B.eta (kappa F ζ hζ q v s) : ℂ) *
        ((KPCubicHaar.abs LocalCompletion v : ℂ) *
          (normPower LocalCompletion (v ^ 2) z * _)) = _
      ring)
  exact ⟨hs.1, hj.2.trans hs.2⟩

theorem joint_cone_forward_convergence (r t₀ : ℂˣ)
    (ht₀ : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ))
    (lam : ℂ) (hlam : KPJointRegulator.cone LocalCompletion t₀ lam) :
    convergenceHalfPlane .plus (KPRankOneReverseRegulatorShells.additiveParameter F q r) := by
  apply (convergence_iff_geometric LocalCompletion .plus _).mpr
  have ht : KPRankOneRootParameter.t LocalCompletion
      (KPRankOneReverseRegulatorShells.additiveParameter F q r) = (t₀ : ℂ) := by
    rw [KPRankOneRootParameter.t,
      KPRankOneReverseRegulatorShells.root_parameter_additiveParameter]
    exact ht₀.symm
  simpa only [if_true, ht] using hlam.2.2.2

set_option maxHeartbeats 800000 in

theorem center_iterated_kernel (I : IwasawaData A)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ)
    (B : Binding F ζ hζ q A P)
    (hcentral : ∀ e : rootsOfUnity 3 F, B.centralTorus e ∈ T.C)
    (hcharacter : ∀ e : rootsOfUnity 3 F, T.ω ⟨B.centralTorus e, hcentral e⟩ = B.eta e)
    (rep : D → H) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (lam : ℂ)
    (hz : convergenceHalfPlane .plus (KPRankOneReverseRegulatorShells.additiveParameter F q r))
    (h : H) :
    KPRankOneReverseRegulatorShells.H F ζ hζ q T A P I μ J B
      rep hrep d φ hφ hcφ r lam h =
      ∫ b : (LocalField F q)ˣ, (∫ a : (LocalField F q)ˣ,
        (B.eta (kappa F ζ hζ q b 0) : ℂ) *
        (B.eta (kappa F ζ hζ q a (b : LocalField F q)) : ℂ) *
        normPower (LocalField F q) (b ^ 2) (-KPRankOneReverseRegulatorShells.additiveParameter F q r) *
        normPower (LocalField F q) (a ^ 2) (KPRankOneReverseRegulatorShells.additiveParameter F q r) *
        ((centerTorus F ζ hζ q T A .minus (B.rootTorus b))
          ((centerTorus F ζ hζ q T A .plus (B.rootTorus a))
            ((centerCoordinates T rep hrep).symm
              (φ ((b : LocalField F q) + (a : LocalField F q)) • Pi.single d (1 : ℂ))))).val h *
        normPower (LocalField F q) b lam ∂multiplicativeMeasure F q μ)
        ∂multiplicativeMeasure F q μ := by
  unfold KPRankOneReverseRegulatorShells.H KPRankOneReverseRegulatorShells.reverseIntegrand
  apply integral_congr_ae
  filter_upwards [] with b
  let actualSection₀ := KPRankOneReverseRegulatorShells.actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r
  have hf := (center_forward_kernel F ζ hζ q T A P I μ J B hcentral hcharacter
    _ hz (actualSection₀) b (h * A.weyl (B.rootTorus b))).2
  have hv (x : LocalField F q) :
      (actualSection₀).val (openCoordinate F ζ hζ q x) =
        (centerCoordinates T rep hrep).symm (φ x • Pi.single d (1 : ℂ)) := (centerCoordinates T rep hrep).injective
      ((KPRankOneReverseRegulatorShells.actualSection_spec F ζ hζ q T A P B
        rep hrep d φ hφ hcφ r).1 x |>.trans
        ((centerCoordinates T rep hrep).apply_symm_apply _).symm)
  change (B.eta (kappa F ζ hζ q b 0) : ℂ) *
    (normPower (LocalField F q) (b ^ 2) (-KPRankOneReverseRegulatorShells.additiveParameter F q r) *
      (((J.op .plus (KPRankOneReverseRegulatorShells.additiveParameter F q r)
        (actualSection₀)).val (openCoordinate F ζ hζ q b)).val
          (h * A.weyl (B.rootTorus b)))) * normPower (LocalField F q) b lam = _
  rw [hf]
  simp_rw [hv]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with a
  have he (V : CenterModule T) :
      (centerTorus F ζ hζ q T A .minus (B.rootTorus b) V).val h =
        V.val (h * A.weyl (B.rootTorus b)) := rfl
  rw [he]
  ring

end
end DedekindZetaZeroFree.KPRankOneLiftedDiagonal
