module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.CubicUnitConjugationOfBruhatTests

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (q : HeightOneSpectrum (𝓞 F))
local notation "K" => LocalField F q
local notation "v" => Sum.inr q
private lemma B1 (y : Kˣ) : KPHilbert.B3 F ζ hζ v 1 y = 1 :=
    KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 y
private lemma B2 (y : Kˣ) : KPHilbert.B3 F ζ hζ v y 1 = 1 :=
    KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 y
private lemma A_N (y : Kˣ) (x : K) :
    KPPGLLocalCover.A F ζ hζ v y * KPPGLLocalCover.N F ζ hζ v x =
      KPPGLLocalCover.N F ζ hζ v ((y : K) * x) * KPPGLLocalCover.A F ζ hζ v y := by
  have hm : KubotaRankTwo.d K y 1 * KubotaRankTwo.n K x =
      KubotaRankTwo.n K ((y : K) * x) * KubotaRankTwo.d K y 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hs1 : KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.d K y 1) (KubotaRankTwo.n K x) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, B1, B2]
  have hs2 : KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.n K ((y : K) * x)) (KubotaRankTwo.d K y 1) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, B1, B2]
  change KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) *
    KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) = _
  rw [← map_mul, KPLocalCover.sectionMap_mul, hs1, map_one, one_mul, hm]
  symm
  change KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) *
    KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) = _
  rw [← map_mul, KPLocalCover.sectionMap_mul, hs2, map_one, one_mul]
private lemma w_d (y : Kˣ) : KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.d K y 1 =
      KPScalarSplitCentral.scalarMatrix F v y *
        (KubotaRankTwo.d K y⁻¹ 1 * KPStandardLocalRootLifts.weylSwap K) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        KPScalarSplitCentral.scalarMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply]
private lemma X_wd (y : Kˣ) :
      KubotaRankTwo.X K (KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.d K y 1) = y := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, y.ne_zero]
private lemma X_dw (y : Kˣ) :
      KubotaRankTwo.X K (KubotaRankTwo.d K y 1 * KPStandardLocalRootLifts.weylSwap K) = 1 := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
private lemma swap_det : KubotaRankTwo.det K (KPStandardLocalRootLifts.weylSwap K) = -1 := by
  apply Units.ext
  simp [KubotaRankTwo.det, KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
private lemma swap_X : KubotaRankTwo.X K (KPStandardLocalRootLifts.weylSwap K) = 1 := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
private lemma Bminus (y : Kˣ) : KPHilbert.B3 F ζ hζ v (-1) y = 1 := by
  rw [(KPHilbert.B3_laws F ζ hζ v).2.2.1]
  simp [(KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2]
private lemma sigma_wd (y : Kˣ) :
      KPLocalCover.sigmaTwo F ζ hζ v (KPStandardLocalRootLifts.weylSwap K) (KubotaRankTwo.d K y 1) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_wd,
      B1, B2, swap_X, swap_det]
    have hn : y / (-1 : Kˣ) = -y := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one, div_neg, div_one]
    rw [Bminus F ζ hζ q y, hn, ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 y).2.2]
    simp
private lemma sigma_dw (y : Kˣ) :
      KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.d K y 1) (KPStandardLocalRootLifts.weylSwap K) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_dw,
      B1, B2, swap_det, (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2]
private lemma sigma_scalar_dw (y : Kˣ) :
      KPLocalCover.sigmaTwo F ζ hζ v (KPScalarSplitCentral.scalarMatrix F v y)
        (KubotaRankTwo.d K y⁻¹ 1 * KPStandardLocalRootLifts.weylSwap K) = 1 := by
    have hx : KubotaRankTwo.X K (KPScalarSplitCentral.scalarMatrix F v y) = y := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix,
        Matrix.scalar, Matrix.diagonal_apply]
    have hd : KubotaRankTwo.det K (KPScalarSplitCentral.scalarMatrix F v y) = y^2 := by
      apply Units.ext
      simp [KubotaRankTwo.det, KPScalarSplitCentral.scalarMatrix,
        Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, pow_two]
    have hb : KPHilbert.B3 F ζ hζ v (y ^ 2) y⁻¹ = 1 := by
      rw [KubotaDefectSymbolAlgebra.inv_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1]
      simp only [pow_two, (KPHilbert.B3_laws F ζ hζ v).1,
        ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 y).1, one_mul, inv_one]
    have hb' : KPHilbert.B3 F ζ hζ v (y ^ 2) (y⁻¹ * -1) = 1 := by
      rw [(KPHilbert.B3_laws F ζ hζ v).2.1, hb,
        ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 (y ^ 2)).2.1, one_mul]
    have hn : y⁻¹ * (-1 : Kˣ) = -y⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, Units.val_one, mul_neg, mul_one]
    rw [hn] at hb'
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_dw,
      ← w_d F q y, X_wd, hx, hd, B1, B2, hb, hb', swap_det]
private lemma W_A (y : Kˣ) :
      KPPGLLocalCover.W F ζ hζ v * KPPGLLocalCover.A F ζ hζ v y =
        KPPGLLocalCover.A F ζ hζ v y⁻¹ * KPPGLLocalCover.W F ζ hζ v := by
    have hr : KPStandardLocalRootLifts.W F ζ hζ v * KPStandardLocalRootLifts.A F ζ hζ v y =
        KPScalarSplitCentral.scalarHom F ζ hζ v y *
          (KPStandardLocalRootLifts.A F ζ hζ v y⁻¹ * KPStandardLocalRootLifts.W F ζ hζ v) := by
      rw [KPStandardLocalRootLifts.W, KPStandardLocalRootLifts.A,
        KPStandardLocalRootLifts.A, KPLocalCover.sectionMap_mul, sigma_wd,
        map_one, one_mul, KPLocalCover.sectionMap_mul, sigma_dw, map_one, one_mul]
      change _ = KPLocalCover.sectionMap F ζ hζ v
        (KPScalarSplitCentral.scalarMatrix F v y) * _
      rw [KPLocalCover.sectionMap_mul, sigma_scalar_dw, map_one, one_mul, w_d F q y]
    have hs : KPPGLLocalCover.coverQuotient F ζ hζ v
        (KPScalarSplitCentral.scalarHom F ζ hζ v y) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
    simpa only [map_mul, hs, one_mul, KPPGLLocalCover.W, KPPGLLocalCover.A] using (congrArg (KPPGLLocalCover.coverQuotient F ζ hζ v) hr)

private lemma cube_A_inv (S : CanonicalFiniteInducingData F ζ hζ q) (c : Kˣ) :
    (KPPGLLocalCover.A F ζ hζ v (c^3))⁻¹ = KPPGLLocalCover.A F ζ hζ v (c⁻¹^3) := by
  rw [← S.cube_actual c, ← S.cube_actual c⁻¹, map_inv]
  rfl

set_option maxHeartbeats 1200000 in
private lemma word_identity (S : CanonicalFiniteInducingData F ζ hζ q)
    (a c : Kˣ) (u x : K) :
    KPPGLLocalCover.A F ζ hζ v (c^3) *
      (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v u *
        (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
          KPPGLLocalCover.N F ζ hζ v x)) *
      (KPPGLLocalCover.A F ζ hζ v (c^3))⁻¹ =
    kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v ((c⁻¹^3 : Kˣ) * u) *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v ((c^3 : Kˣ) * x)) := by
  let T := KPPGLLocalCover.A F ζ hζ v (c^3)
  let w := kernelW K S.borel .minus
  let N := KPPGLLocalCover.N F ζ hζ v
  let b := KPPGLLocalCover.A F ζ hζ v a
  let W := KPPGLLocalCover.W F ζ hζ v
  let cube_A_inv₀ := cube_A_inv F ζ hζ q S c
  have hkw : T * w = w * T⁻¹ := by
    dsimp only [T, w]
    rw [cube_A_inv₀]
    have he := congrArg (fun h : actualTorus F ζ hζ q => (S.borel.torus h : ActualCover F ζ hζ q))
      (congrArg (fun z : S.heisenberg.C => (z : actualTorus F ζ hζ q)) (S.borel.weyl_cube c))
    rw [S.borel.weylCenter_coe, S.borel.weyl_from_lift,
      S.torus_full, S.torus_full, S.cube_actual, S.cube_actual] at he
    change KPPGLLocalCover.A F ζ hζ v (c^3) * S.borel.liftedW =
      S.borel.liftedW * KPPGLLocalCover.A F ζ hζ v (c⁻¹^3)
    rw [← he]
    group
  let N₀ := N ((c⁻¹^3 : Kˣ) * u)
  have hn : T⁻¹ * N u = N₀ * T⁻¹ := by
    dsimp only [T, N]
    rw [cube_A_inv₀]
    exact A_N F ζ hζ q (c⁻¹^3) u
  have hb : T⁻¹ * b = b * T⁻¹ := by
    dsimp only [T, b]
    rw [cube_A_inv₀]
    let c := c⁻¹
    rw [KPPGLLocalCover.A_mul, KPPGLLocalCover.A_mul,
      ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 c a).1,
      ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 a c).2]
    simp [mul_comm]
  have hw : T⁻¹ * W = W * T := by
    have h := W_A F ζ hζ q (c^3)
    change W * T = KPPGLLocalCover.A F ζ hζ v ((c^3)⁻¹) * W at h
    rw [← inv_pow, ← cube_A_inv₀] at h
    exact h.symm
  have hn' : T * N x = N ((c^3 : Kˣ) * x) * T := A_N F ζ hζ q (c^3) x
  change T * (w * N u * (b * W * N x)) * T⁻¹ = w * N _ * (b * W * N _)
  calc
    T * (w * N u * (b * W * N x)) * T⁻¹ = (T * w) * N u * b * W * N x * T⁻¹ := by group
    _ = w * (T⁻¹ * N u) * b * W * N x * T⁻¹ := by rw [hkw]; group
    _ = w * N₀ * (T⁻¹ * b) * W * N x * T⁻¹ := by rw [hn]; group
    _ = w * N₀ * b * (T⁻¹ * W) * N x * T⁻¹ := by rw [hb]; group
    _ = w * N₀ * b * W * (T * N x) * T⁻¹ := by rw [hw]; group
    _ = w * N₀ * (b * W * N ((c^3 : Kˣ) * x)) := by rw [hn']; group

variable (S : CanonicalFiniteInducingData F ζ hζ q)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]

set_option maxHeartbeats 1200000 in

theorem reverse_integral_cubic_unit_change_variable
    (a : (LocalField F q)ˣ) (c : (LocalField F q)ˣ)
    (hc : localAbs (LocalField F q) c = 1)
    (φ : ActualCover F ζ hζ q → ℂ)
    (hφ : ∀ g : ActualCover F ζ hζ q,
      φ (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3) * g *
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3))⁻¹) = φ g)
    (x : LocalField F q) :
    (∫ u : LocalField F q,
      φ (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) a *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) ((c ^ 3 : (LocalField F q)ˣ) * x))) ∂μ) =
    (∫ u : LocalField F q,
      φ (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) a *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) ∂μ) := by
  let d : Kˣ := c⁻¹ ^ 3
  have hci : localAbs K c⁻¹ = 1 := by
    have h := localAbs_mul K c c⁻¹
    simpa only [mul_inv_cancel, localAbs_one, hc, one_mul] using h.symm
  have hd : localAbs K d = 1 := by
    dsimp only [d]
    simp only [pow_succ, pow_zero, localAbs_mul, localAbs_one, hci, one_mul]
  have habs : KPCubicHaar.abs K (d : K) = 1 := by
    have he : localAbs K d = KPCubicHaar.abs K (d : K) := by
      simp only [localAbs, KPCubicHaar.abs, if_neg d.ne_zero, Real.rpow_intCast]
      rfl
    rw [← he, hd]
  let e : K ≃ᵐ K :=
    { toEquiv :=
        { toFun := fun u => (d : K) * u
          invFun := fun u => (d⁻¹ : Kˣ) * u
          left_inv := by intro u; simp [mul_assoc]
          right_inv := by intro u; simp [mul_assoc] }
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }
  have hmap : Measure.map e μ = μ := by
    change Measure.map (fun u : K => (d : K) * u) μ = μ
    rw [NonarchimedeanHaarScaling.map_mul K μ (d : K) d.ne_zero, habs]
    simp
  let H : K → ℂ := fun u =>
    φ (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v u *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v ((c^3 : Kˣ) * x)))
  have hp (u : K) : H (e u) =
    φ (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v u *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v x)) := by
    dsimp only [H]
    change φ (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v ((c⁻¹^3 : Kˣ) * u) *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v ((c^3 : Kˣ) * x))) = _
    rw [← word_identity F ζ hζ q S a c u x]
    exact hφ _
  change (∫ u : K, H u ∂μ) = _
  calc
    (∫ u : K, H u ∂μ) = ∫ u : K, H (e u) ∂μ := by
      conv_lhs => rw [← hmap]
      exact integral_map_equiv e H
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hp)

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (q : HeightOneSpectrum (𝓞 F))

private alias valuation_norm_le := DedekindZetaZeroFree.KPTameJacquetBruhatTests.TameStableWhittakerIntegrals.valuation_norm_le
local notation "LocalCompletion" => LocalField F q

private theorem ball_norm (π : LocalCompletionˣ) (r : ℕ) (x : LocalCompletion) :
    x ∈ expandingBall F q π r ↔ ‖x‖ ≤ ‖(π : LocalCompletion)‖⁻¹ ^ r := by apply @DedekindZetaZeroFree.KPTameJacquetBruhatTests.TameStableWhittakerIntegrals.expandingBall_norm <;> assumption

theorem high_shell_translation_is_cubic_unit_multiple
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : LocalCompletionˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ))
    (r : ℕ) (hr : 2 ≤ r)
    (x : LocalCompletion)
    (hx : x ∈ expandingBall F q π r \ expandingBall F q π (r - 1))
    (t : LocalCompletion) (ht : t ∈ expandingBall F q π 1) :
    ∃ c : LocalCompletionˣ, localAbs LocalCompletion c = 1 ∧
      x + t = (c ^ 3 : LocalCompletionˣ) * x := by
  have hv : valuation LocalCompletion (π : LocalCompletion) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion 1
    rw [hπ, map_one]
    norm_num
  have hp := norm_pos_iff.mpr π.ne_zero
  have hp1 : ‖(π : LocalCompletion)‖ < 1 := by
    have h := not_le.mpr hv
    rw [← map_one (valuation LocalCompletion), valuation_norm_le] at h
    simpa using not_le.mp h
  have hb := le_of_lt ((one_lt_inv₀ hp).mpr hp1)
  have hxt : ‖t‖ < ‖x‖ := by
    have hxn :=
      lt_of_not_ge (fun h => hx.2 ((ball_norm F q π (r-1) x).mpr h))
    have htn : ‖t‖ ≤ ‖(π : LocalCompletion)‖⁻¹ := by
      simpa using (ball_norm F q π 1 t).mp ht
    exact lt_of_le_of_lt (htn.trans (by
      simpa using pow_le_pow_right₀ hb (show 1 ≤ r - 1 by omega))) hxn
  have hx0 : x ≠ 0 := by
    intro h
    exact (not_lt_of_ge (norm_nonneg t)) (by simpa [h] using hxt)
  have hy : valuation LocalCompletion (t / x) < 1 := by
    have hn : ‖t / x‖ < ‖(1 : LocalCompletion)‖ := by
      rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr hx0)]
      exact hxt
    have h := not_le.mpr hn
    rw [← valuation_norm_le] at h
    simpa using not_le.mp h
  let z : KPTameCompact.O F q := ⟨1 + t / x, by
    rw [Valuation.mem_integer_iff]
    exact le_of_eq ((valuation LocalCompletion).map_one_add_of_lt hy)⟩
  have hz : valuation LocalCompletion (z : LocalCompletion) = 1 :=
    (valuation LocalCompletion).map_one_add_of_lt hy
  letI : HenselianRing (KPTameCompact.O F q) (KPTameCompact.p F q) :=
    (LocalFieldTheory.localCompleteDVF LocalCompletion).henselianRing
  let Q := Ideal.Quotient.mk (KPTameCompact.p F q)
  have heq : Q z = 1 := by
    have hm : z - 1 ∈ KPTameCompact.p F q := by
      change z - 1 ∈ IsLocalRing.maximalIdeal (KPTameCompact.O F q)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      simpa [z] using hy
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact sub_eq_zero.mp (by simpa [map_sub, Q] using h)
  let P : Polynomial (KPTameCompact.O F q) := Polynomial.X ^ 3 - Polynomial.C z
  have hm : P.Monic := by
    exact Polynomial.monic_X_pow_sub_C z (by decide)
  have he : P.eval 1 ∈ KPTameCompact.p F q := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Q (P.eval 1) = 0
    simp [P, heq]
  have hthree : IsUnit (3 : KPTameCompact.O F q) := by
    letI : Nontrivial (KPTameCompact.O F q ⧸ KPTameCompact.p F q) :=
      Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (KPTameCompact.O F q)).ne_top
    letI : (KPTameCompact.p F q).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (KPTameCompact.O F q)
    letI : IsLocalHom Q := IsLocalHom.of_surjective Q Ideal.Quotient.mk_surjective
    apply isUnit_of_map_unit Q
    letI : Field (KPTameCompact.O F q ⧸ KPTameCompact.p F q) := Ideal.Quotient.field (KPTameCompact.p F q)
    apply isUnit_iff_ne_zero.mpr
    simpa only [Q, map_ofNat, Nat.cast_ofNat] using
      CharP.cast_ne_zero_of_ne_of_prime (KPTameCompact.O F q ⧸ KPTameCompact.p F q) Nat.prime_three htame
  have hd : IsUnit (Q (P.derivative.eval 1)) := by
    have h : P.derivative.eval 1 = (3 : KPTameCompact.O F q) := by
      simp [P, Polynomial.derivative_sub, Polynomial.derivative_pow]
    rw [h]
    exact hthree.map Q
  obtain ⟨w, hw, hwp⟩ := HenselianRing.is_henselian P hm 1 he hd
  have hw3 : w ^ 3 = z := by
    simpa only [Polynomial.IsRoot, P, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hw
  have hwf : (w : LocalCompletion) ^ 3 = (z : LocalCompletion) :=
    congrArg (fun a : KPTameCompact.O F q => (a : LocalCompletion)) hw3
  have hwv : valuation LocalCompletion (w : LocalCompletion) = 1 := by
    have h : valuation LocalCompletion (w : LocalCompletion) ^ 3 = 1 := by
      rw [← map_pow, hwf, hz]
    exact (pow_eq_one_iff_of_nonneg (zero_le : 0 ≤ valuation LocalCompletion (w : LocalCompletion)) (by decide : (3 : ℕ) ≠ 0)).mp h
  have hw0 : (w : LocalCompletion) ≠ 0 := by
    intro h
    simpa [h] using hwv
  refine ⟨Units.mk0 (w : LocalCompletion) hw0, ?_, ?_⟩
  · simp [localAbs, hwv]
  · change x + t = (w : LocalCompletion) ^ 3 * x
    rw [hwf]
    change x + t = (1 + t / x) * x
    field_simp

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (coordinates : ∀ ε : Sign,
    sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
  (hcoordinates : ∀ ε f g, (coordinates ε f).val g = (f.val g).val 1)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

alias deformedTest_vector_value := CubicUnitConjugationOfBruhatTests.support_vector_value

include hcoordinates in

theorem deformedTest_scalar_value
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) * f.val g := by
  rw [deformedTest_vector_value]
  change _ * (((coordinates .minus).symm f).val g).val 1 = _
  have hc := hcoordinates .minus ((coordinates .minus).symm f) g
  rw [LinearEquiv.apply_symm_apply] at hc
  rw [← hc]

include hcoordinates in

theorem deformedTest_scalar_support
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ) :
    Function.support (fun g =>
      ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1) =
      Function.support f.val := by
  ext g
  rw [Function.mem_support, Function.mem_support, deformedTest_scalar_value
    F ζ hζ q S P hP coordinates hcoordinates]
  have hn : normPower (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
      (sourceParameter .minus s) ≠ 0 := Complex.exp_ne_zero _
  simp only [ne_eq, mul_eq_zero, hn, false_or]

include hcoordinates in

theorem deformedTest_support_of_minusTest
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f) (s : ℂ) :
    Function.support (fun g =>
      ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1) ⊆
      testSupport F ζ hζ q S P a m := by
  rw [deformedTest_scalar_support F ζ hζ q S P hP coordinates hcoordinates]
  exact hf.2.1

alias iwasawa_norm_right_compact := DedekindZetaZeroFree.KPRankOneShellRepair.OpenCellNonzero.BruhatConstruction.ZeroMapNonvanishing.norm_right_compact

theorem minusTest_bruhat_value
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f)
    (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q)
    (hk : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m) :
    f.val (b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      chi F ζ hζ q S P hP .minus b := by
  let w := KPPGLLocalCover.W F ζ hζ (Sum.inr q)
  have hfixed := congrArg
    (fun v : scalarSections F ζ hζ q S P hP .minus => v.val (a * w))
    (hf.1 (w⁻¹ * k * w) hk)
  change f.val ((a * w) * (w⁻¹ * k * w)) = f.val (a * w) at hfixed
  have he : (a * w) * (w⁻¹ * k * w) = a * k * w := by group
  rw [he, hf.2.2] at hfixed
  rw [show b * a * k * w =
      b * (a * k * w) by group,
    f.property.1, hfixed, mul_one]

include hcoordinates in

theorem deformedTest_bruhat_scalar_value
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f)
    (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q)
    (hk : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (s : ℂ) :
    let g := b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)
    ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) * chi F ζ hζ q S P hP .minus b := by
  dsimp only
  rw [deformedTest_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    minusTest_bruhat_value F ζ hζ q S P hP a m f hf b k hk]

alias iwasawa_norm_left_borel := CubicUnitConjugationOfBruhatTests.support_norm_left

include hcoordinates in

theorem deformedTest_scalar_borel_covariance
    (f : scalarSections F ζ hζ q S P hP .minus)
    (b : BL F ζ hζ q S P) (s : ℂ) (g : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP coordinates f s).val (b * g)).val 1 =
      (chi F ζ hζ q S P hP .minus b *
        normPower (LocalField F q)
          (S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b)))
          (sourceParameter .minus s)) *
        ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 := by
  rw [deformedTest_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    deformedTest_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    f.property.1]
  have hn := iwasawa_norm_left_borel F ζ hζ q S
    (inBorel F ζ hζ q S P b) g
  change localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (b * g)))) = _ at hn
  unfold normPower
  rw [hn, Real.log_mul
    (ne_of_gt (localAbs_pos (LocalField F q) _))
    (ne_of_gt (localAbs_pos (LocalField F q) _))]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end

end
