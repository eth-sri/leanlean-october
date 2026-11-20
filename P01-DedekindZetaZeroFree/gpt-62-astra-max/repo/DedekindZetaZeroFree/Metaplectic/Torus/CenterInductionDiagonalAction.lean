module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction

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

private alias winv := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.winv

alias CenterInductionDiagonalAction.winv := winv
private alias Xwinv := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.Xwinv

alias CenterInductionDiagonalAction.Xwinv := Xwinv
private alias Xwnw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.Xwnw

alias CenterInductionDiagonalAction.Xwnw := Xwnw

private alias BoneL := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.BoneL

alias CenterInductionDiagonalAction.BoneL := BoneL
private alias BoneR := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.BoneR

alias CenterInductionDiagonalAction.BoneR := BoneR
private alias BnegR := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.BnegR

alias CenterInductionDiagonalAction.BnegR := BnegR
private alias sigmanR := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.sigmanR
private alias sigww := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.sigww
private alias sigwnw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.sigwnw
private alias Xdnw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.Xdnw

alias CenterInductionDiagonalAction.Xdnw := Xdnw
private alias Bselfpow := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.Bselfpow
private alias BnegL := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.BnegL

alias CenterInductionDiagonalAction.BnegL := BnegL
private alias sigdnw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.sigdnw
private alias Xscalar := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.Xscalar

alias CenterInductionDiagonalAction.Xscalar := Xscalar
private alias Xscalar_mul := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.Xscalar_mul

alias CenterInductionDiagonalAction.Xscalar_mul := Xscalar_mul
private alias sigscalar := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.sigscalar
private alias kappa_eq_one := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.kappa_eq_one

namespace WeylAux
local notation "K" => LocalField F q
local notation "v" => Sum.inr q
private alias w_d := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.w_d
private alias X_wd := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.X_wd
private alias X_dw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.X_dw
private lemma B1 (y : Kˣ) : KPHilbert.B3 F ζ hζ v 1 y = 1 := by apply @DedekindZetaZeroFree.KPRankOneLiftedDiagonal.BoneL <;> assumption
private lemma B2 (y : Kˣ) : KPHilbert.B3 F ζ hζ v y 1 = 1 := by apply @DedekindZetaZeroFree.KPRankOneLiftedDiagonal.BoneR <;> assumption
private alias sigma_wd := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.sigma_wd
private alias sigma_dw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.sigma_dw
private alias sigma_scalar_dw := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.sigma_scalar_dw
private alias raw_w_A := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.raw_w_A

private alias signedW_conjugates_A := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.SignedWeylInversion.signedW_conjugates_A

end WeylAux

variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T) (B : Binding F ζ hζ q A P)
local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
private lemma torus_inj {x y : H} (h : (A.torus x : Cover F ζ hζ q) = A.torus y) : x = y :=
  A.torus_injective (Subtype.ext h)
include P B in
private lemma proj_eq (g : Cover F ζ hζ q) : A.projection g = KPLocalSmoothRepresentation.projection F ζ hζ q g := by
  induction g using QuotientGroup.induction_on with | _ g =>
    exact B.projection_eq g
private alias pgl_inj := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.SignedWeylInversion.pgl_inj
include P B in
private lemma fiber (x y : Cover F ζ hζ q) (he : A.projection x = A.projection y) :
    ∃ e, x = KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e * y := by
  have hp : KPPGLLocalCover.projection F ζ hζ (Sum.inr q) (x * y⁻¹) = 1 := by
    apply pgl_inj F q
    change KPLocalSmoothRepresentation.projection F ζ hζ q (x * y⁻¹) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q 1
    rw [← proj_eq F ζ hζ q T A P B, map_mul, map_inv, he, mul_inv_cancel, map_one]
  have hm : x * y⁻¹ ∈ (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).range := by
    rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
    exact hp
  obtain ⟨e, he⟩ := hm
  exact ⟨e, (eq_mul_inv_iff_mul_eq.mp he).symm⟩
private lemma weyl_root (y : (LocalField F q)ˣ) :
    A.weyl (B.rootTorus y) = B.rootTorus y⁻¹ := by
  apply torus_inj F ζ hζ q T A
  rw [A.weyl_from_lift, B.weyl_eq, B.torus_eq, B.torus_eq]
  change (signedWeyl F ζ hζ q)⁻¹ * KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 2) *
    signedWeyl F ζ hζ q = KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y⁻¹ ^ 2)
  have hw : signedWeyl F ζ hζ q = KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) := by
    unfold signedWeyl
    rw [signedWeyl_eq_prescribed_signed]
    rfl
  rw [hw, WeylAux.signedW_conjugates_A]
  simp
include P B in
private lemma cube_sheet (y : (LocalField F q)ˣ) :
    (A.torus (A.cubeLift y : H) : Cover F ζ hζ q) = KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) := by
  let c := (A.torus (A.cubeLift y : H) : Cover F ζ hζ q)
  let d := KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3)
  have hp : A.projection c = A.projection d := by
    rw [A.torus_projection, A.cube_coordinate]
    change _ = A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (y ^ 3)))
    rw [B.projection_eq]
    rfl
  obtain ⟨e, he⟩ := fiber F ζ hζ q T A P B c d hp
  have hi : d⁻¹ = KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y⁻¹ ^ 3) := by
    apply inv_eq_of_mul_eq_one_right
    rw [KPPGLLocalCover.A_mul]
    have hB : KPHilbert.B3 F ζ hζ (Sum.inr q) (y ^ 3) (y⁻¹ ^ 3) = 1 := by
      rw [pow_succ, pow_succ, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1,
        (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1]
      simp only [pow_one]
      rw [← pow_two, ← pow_succ]
      exact Subtype.ext (KPHilbert.B3 F ζ hζ (Sum.inr q) y (y⁻¹ ^ 3)).property
    simp only [hB, one_pow, map_one, one_mul]
    rw [← mul_pow, mul_inv_cancel, one_pow]
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) 1) = 1
    rw [KPStandardLocalRootLifts.A_one, map_one]
  have hw : A.liftedW = KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) := by
    rw [B.weyl_eq]
    unfold signedWeyl
    rw [signedWeyl_eq_prescribed_signed]
    rfl
  have hc : A.liftedW⁻¹ * c * A.liftedW = c⁻¹ := by
    rw [← A.weyl_from_lift, ← A.weylCenter_coe, A.weyl_cube, map_inv,
      Subgroup.coe_inv, map_inv]
    rfl
  have hd : A.liftedW⁻¹ * d * A.liftedW = d⁻¹ := by
    rw [hw, WeylAux.signedW_conjugates_A, hi]
    simp
  let z := KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e
  have hz := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e, rfl⟩)
  have he2 : z = z⁻¹ := by
    rw [he] at hc
    change A.liftedW⁻¹ * (z * d) * A.liftedW = (z * d)⁻¹ at hc
    rw [← mul_assoc, hz A.liftedW⁻¹, mul_assoc z, mul_assoc z, hd,
      mul_inv_rev, ← hz d⁻¹] at hc
    exact mul_left_cancel hc
  have h2 : e ^ 2 = 1 := by
    apply KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q)
    rw [map_pow, map_one]
    change z ^ 2 = 1
    rw [pow_two]
    conv_lhs => lhs; rw [he2]
    exact inv_mul_cancel _
  have h3 : e ^ 3 = 1 := Subtype.ext e.property
  have he1 : e = 1 := by
    simpa [pow_succ, h2] using h3
  simpa [he1] using he
private alias BcubeL := DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.BcubeL
private lemma Bself (x : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) x⁻¹ x = 1 := by
  rw [KubotaDefectSymbolAlgebra.inv_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1]
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 x |>.1, inv_one]
section

variable (a u v : (LocalField F q)ˣ)

private lemma Bdiag :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (((-a) * v ^ 3)⁻¹ ^ 2) ((a * u ^ 3) ^ 2) = 1 := by
  have hn : ((-a) * v ^ 3)⁻¹ ^ 2 = a⁻¹ ^ 2 * (v⁻¹ ^ 2) ^ 3 := by
    simp only [mul_inv_rev, mul_pow, inv_pow, Even.neg_pow (show Even 2 from by decide)]
    rw [← pow_mul, ← pow_mul]
    ac_rfl
  have hp : (a * u ^ 3) ^ 2 = a ^ 2 * (u ^ 2) ^ 3 := by simp [mul_pow, ← pow_mul]
  rw [hn, hp, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1, BcubeL, mul_one,
    (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1]
  have hR : KPHilbert.B3 F ζ hζ (Sum.inr q) (a⁻¹ ^ 2) ((u ^ 2) ^ 3) = 1 := by
    rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1, BcubeL, inv_one]
  rw [hR, mul_one, inv_pow, Bself]
private lemma diagonal_word :
    A.weyl (B.rootTorus ((-a) * v ^ 3)) * B.rootTorus (a * u ^ 3) =
      (A.cubeLift ((u / v) ^ 2) : H) := by
  apply torus_inj F ζ hζ q T A
  simp only [map_mul, Subgroup.coe_mul]
  rw [weyl_root F ζ hζ q T A P B, B.torus_eq, B.torus_eq, cube_sheet F ζ hζ q T A P B]
  rw [hLift, hLift, KPPGLLocalCover.A_mul, Bdiag, one_pow, map_one, one_mul]
  congr 1
  simp only [mul_pow, inv_pow, Even.neg_pow (show Even 2 from by decide), div_pow, div_eq_mul_inv]
  simp only [← pow_mul]
  group
  ac_rfl
private lemma center_diagonal (V : CenterModule T) (h : H) :
    ((centerTorus F ζ hζ q T A .minus (B.rootTorus ((-a) * v ^ 3)))
      ((centerTorus F ζ hζ q T A .plus (B.rootTorus (a * u ^ 3))) V)).val h =
      normPower (LocalField F q) (((u / v) ^ 2) ^ 3) (1 / 6) * V.val h := by
  change V.val (h * A.weyl (B.rootTorus ((-a) * v ^ 3)) * B.rootTorus (a * u ^ 3)) = _
  rw [mul_assoc, diagonal_word F ζ hζ q T A P B]
  rw [(Subgroup.mem_center_iff.mp (T.central (A.cubeLift ((u / v) ^ 2)).property) h), V.property]
  change (T.ω (A.cubeLift _) : ℂ) * _ = _
  rw [A.exceptional_cube]

end

private lemma norm_mul (x y : (LocalField F q)ˣ) (z : ℂ) :
    normPower (LocalField F q) (x * y) z =
      normPower (LocalField F q) x z * normPower (LocalField F q) y z := by
  rw [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ x))
    (ne_of_gt (localAbs_pos _ y)), Complex.ofReal_add, mul_add, Complex.exp_add]
  rfl
section

variable (x : (LocalField F q)ˣ)

local notation "LocalCompletion" => LocalField F q

private lemma norm_neg (z : ℂ) :
    normPower LocalCompletion (-x) z = normPower LocalCompletion x z := by
  simp [normPower, localAbs, Valuation.map_neg]
private lemma norm_pow (n : ℕ) (z : ℂ) :
    normPower LocalCompletion (x ^ n) z = normPower LocalCompletion x (n * z) := by
  have ha : localAbs LocalCompletion (x ^ n) = localAbs LocalCompletion x ^ n := by
    induction n with
    | zero => simp [localAbs_one]
    | succ n ih => rw [pow_succ, localAbs_mul, ih, pow_succ]
  simp only [normPower, ha, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  ring
private lemma norm_inv (z : ℂ) :
    normPower LocalCompletion x⁻¹ z = (normPower LocalCompletion x z)⁻¹ := by
  have ha : localAbs LocalCompletion x⁻¹ = (localAbs LocalCompletion x)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
  simp [normPower, ha, Real.log_inv, Complex.exp_neg, mul_neg]
private lemma norm_add (z w : ℂ) :
    normPower LocalCompletion x (z + w) = normPower LocalCompletion x z * normPower LocalCompletion x w := by
  simp [normPower, add_mul, Complex.exp_add]

end
private lemma norm_unram (r t₀ : ℂˣ)
    (ht₀ : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ)) (x : (LocalField F q)ˣ) :
    normPower (LocalField F q) x (1 + 6 * KPRankOneReverseRegulatorShells.additiveParameter F q r) =
      KPCubicExpansion.omega (LocalField F q) t₀ x := by
  let z := KPRankOneReverseRegulatorShells.additiveParameter F q r
  let L := Real.log (residueCardinality (LocalField F q) : ℝ)
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos)
  have hl : (Real.log (localAbs (LocalField F q) x) : ℂ) =
      -(KPCubicExpansion.valuationExponent (LocalField F q) x : ℂ) * L := by
    simp only [localAbs, KPCubicExpansion.valuationExponent]
    rw [Real.log_rpow hq]
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_neg, neg_neg]
  have ht : Complex.exp (-(1 + 6 * z) * L) = (t₀ : ℂ) := by
    rw [show -(1 + 6 * z) * L = -L + 6 * (-z * L) by ring,
      Complex.exp_add]
    rw [show (6 : ℂ) = ((6 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul]
    have hr := KPRankOneReverseRegulatorShells.root_parameter_additiveParameter F q r
    change Complex.exp (-z * L) = (r : ℂ) at hr
    rw [hr, ht₀, KPRankOneReverseRegulatorShells.t]
    congr 1
    rw [Complex.exp_neg]
    congr 1
    exact (Complex.ofReal_exp (Real.log (residueCardinality (LocalField F q) : ℝ))).symm |>.trans
      (congrArg Complex.ofReal (Real.exp_log hq))
  rw [normPower, hl]
  rw [show (1 + 6 * z) * (-(KPCubicExpansion.valuationExponent (LocalField F q) x : ℂ) * L) =
    (KPCubicExpansion.valuationExponent (LocalField F q) x : ℂ) * (-(1 + 6 * z) * L) by ring,
    Complex.exp_int_mul, ht]
  simp [KPCubicExpansion.omega]

theorem diagonal_center_action (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
    {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommGroup D] [Finite D] [DecidableEq D]
    (T : LocalHeisenbergData H D)
    (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T) (B : Binding F ζ hζ q A P)
    (hcentral : ∀ e : rootsOfUnity 3 F, B.centralTorus e ∈ T.C)
    (hcharacter : ∀ e : rootsOfUnity 3 F,
      T.ω ⟨B.centralTorus e, hcentral e⟩ = B.eta e)
    (r t₀ : ℂˣ)
    (ht₀ : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ))
    (a u v : (LocalField F q)ˣ) (V : CenterModule T) (h : H) :
    (B.eta (kappa F ζ hζ q ((-a) * v ^ 3) 0) : ℂ) *
      (B.eta (kappa F ζ hζ q (a * u ^ 3) (((-a) * v ^ 3 : (LocalField F q)ˣ) : LocalField F q)) : ℂ) *
      normPower (LocalField F q) (((-a) * v ^ 3) ^ 2)
        (-KPRankOneReverseRegulatorShells.additiveParameter F q r) *
      normPower (LocalField F q) ((a * u ^ 3) ^ 2)
        (KPRankOneReverseRegulatorShells.additiveParameter F q r) *
      ((centerTorus F ζ hζ q T A .minus (B.rootTorus ((-a) * v ^ 3)))
        ((centerTorus F ζ hζ q T A .plus (B.rootTorus (a * u ^ 3))) V)).val h =
      KPCubicExpansion.omega (LocalField F q) t₀ u *
        (KPCubicExpansion.omega (LocalField F q) t₀ v)⁻¹ * V.val h := by
  rw [kappa_eq_one, kappa_eq_one]
  simp only [map_one, Units.val_one, one_mul]
  rw [center_diagonal F ζ hζ q T A P B]
  let z := KPRankOneReverseRegulatorShells.additiveParameter F q r
  have hn (x : (LocalField F q)ˣ) : normPower (LocalField F q) x (-z) =
      (normPower (LocalField F q) x z)⁻¹ := by
    simp [normPower, neg_mul, Complex.exp_neg]
  have hnon (x : (LocalField F q)ˣ) : normPower (LocalField F q) x z ≠ 0 := Complex.exp_ne_zero _
  have hs : normPower (LocalField F q) (((-a) * v ^ 3) ^ 2) (-z) *
      normPower (LocalField F q) ((a * u ^ 3) ^ 2) z *
      normPower (LocalField F q) (((u / v) ^ 2) ^ 3) (1 / 6) =
        KPCubicExpansion.omega (LocalField F q) t₀ u *
          (KPCubicExpansion.omega (LocalField F q) t₀ v)⁻¹ := by
    simp only [norm_pow, norm_mul, norm_neg, div_eq_mul_inv, norm_inv]
    have h6 : (2 : ℂ) * ((3 : ℂ) * (1 / 6)) = 1 := by norm_num
    norm_num only [Nat.cast_ofNat, one_mul] at *
    have h2 : (2 : ℂ) * -z = -(2 * z) := by ring
    rw [h2]
    have hneg (x : (LocalField F q)ˣ) (w : ℂ) : normPower (LocalField F q) x (-w) =
        (normPower (LocalField F q) x w)⁻¹ := by simp [normPower, neg_mul, Complex.exp_neg]
    rw [hneg, mul_neg, hneg]
    have h6z : (3 : ℂ) * (2 * z) = 6 * z := by ring
    rw [h6z]
    rw [← norm_unram F q r t₀ ht₀ u, ← norm_unram F q r t₀ ht₀ v,
      norm_add, norm_add]
    have ha : normPower (LocalField F q) a (2 * z) ≠ 0 := Complex.exp_ne_zero _
    have hv : normPower (LocalField F q) v (6 * z) ≠ 0 := Complex.exp_ne_zero _
    have hv1 : normPower (LocalField F q) v 1 ≠ 0 := Complex.exp_ne_zero _
    dsimp [z] at *
    field_simp
    <;> ring
  calc
    _ = (normPower (LocalField F q) (((-a) * v ^ 3) ^ 2) (-z) *
        normPower (LocalField F q) ((a * u ^ 3) ^ 2) z *
        normPower (LocalField F q) (((u / v) ^ 2) ^ 3) (1 / 6)) * V.val h := by ring
    _ = _ := by rw [hs]

end
end DedekindZetaZeroFree.KPRankOneLiftedDiagonal
