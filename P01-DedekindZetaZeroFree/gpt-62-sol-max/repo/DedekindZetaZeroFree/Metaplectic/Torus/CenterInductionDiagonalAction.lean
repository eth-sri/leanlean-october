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
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

open DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra (kappa_eq_one cube_sheet BcubeL norm_mul norm_pow norm_inv norm_add norm_neg)

variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T) (B : Binding F ζ hζ q A P)
local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
private lemma torus_inj {x y : H} (h : (A.torus x : Cover F ζ hζ q) = A.torus y) : x = y :=
  A.torus_injective (Subtype.ext h)
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
  rw [hw, DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.signedW_conjugates_A]
  simp
private lemma Bself (x : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) x⁻¹ x = 1 := by
  rw [KubotaDefectSymbolAlgebra.inv_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1]
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 x |>.1, inv_one]
private lemma Bdiag (a u v : (LocalField F q)ˣ) :
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
private lemma diagonal_word (a u v : (LocalField F q)ˣ) :
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
private lemma center_diagonal (a u v : (LocalField F q)ˣ) (V : CenterModule T) (h : H) :
    ((centerTorus F ζ hζ q T A .minus (B.rootTorus ((-a) * v ^ 3)))
      ((centerTorus F ζ hζ q T A .plus (B.rootTorus (a * u ^ 3))) V)).val h =
      normPower (LocalField F q) (((u / v) ^ 2) ^ 3) (1 / 6) * V.val h := by
  change V.val (h * A.weyl (B.rootTorus ((-a) * v ^ 3)) * B.rootTorus (a * u ^ 3)) = _
  rw [mul_assoc, diagonal_word F ζ hζ q T A P B]
  have hc := Subgroup.mem_center_iff.mp (T.central (A.cubeLift ((u / v) ^ 2)).property) h
  rw [hc, V.property]
  change (T.ω (A.cubeLift _) : ℂ) * _ = _
  rw [A.exceptional_cube]

private lemma norm_unram (r t₀ : ℂˣ)
    (ht₀ : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ)) (x : (LocalField F q)ˣ) :
    normPower (LocalField F q) x (1 + 6 * KPRankOneReverseRegulatorShells.additiveParameter F q r) =
      KPCubicExpansion.omega (LocalField F q) t₀ x := by
  let z := KPRankOneReverseRegulatorShells.additiveParameter F q r
  let L : ℂ := Real.log (residueCardinality (LocalField F q) : ℝ)
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField F q)).integer))
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
  change Complex.exp ((1 + 6 * z) * (-(KPCubicExpansion.valuationExponent (LocalField F q) x : ℂ) * L)) = _
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
