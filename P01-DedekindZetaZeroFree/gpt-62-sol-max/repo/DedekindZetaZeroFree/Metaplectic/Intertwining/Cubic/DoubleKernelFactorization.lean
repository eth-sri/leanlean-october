module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.DoubleCocycleAndBetaArithmetic

@[expose] public section

namespace DedekindZetaZeroFree.KPActualFullKernelArithmetic

open scoped NumberField Valued
open NumberField IsDedekindDomain
open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneOpenCellKernel KPRankOneLiftedRegulatedDiagonalAlgebra
open KPActualScalarBinding
open KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

open DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra (kappa_eq_one Bpow BoneR norm_mul norm_pow)

private lemma ratio_phase (c x y : (LocalField F q)ˣ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) ((c*x)^2)⁻¹ ((x*y^3)^2) ^ 2 =
      KPHilbert.B3 F ζ hζ (Sum.inr q) c x := by
  have hL := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1
  have hR := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1
  have hcube := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1
  have hm : ((c*x)^2)⁻¹ = c^(-2:ℤ)*x^(-2:ℤ) := by simp [mul_pow, mul_inv_rev, zpow_neg]; ac_rfl
  have hn : (x*y^3)^2 = x^2*(y^2)^3 := by simp [mul_pow, ← pow_mul]
  rw [hm, hn, hR, (hcube _ _).2, mul_one, hL]
  have hs : KPHilbert.B3 F ζ hζ (Sum.inr q) (x^(-2:ℤ)) (x^2) = 1 := by
    have he := Bpow F ζ hζ q x x (-2) 2
    simp only [Int.reduceNeg, zpow_ofNat] at he
    rw [he, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 x |>.1]; simp
  rw [hs, mul_one]
  have hp := Bpow F ζ hζ q c x (-2) 2
  simp only [Int.reduceNeg, zpow_ofNat] at hp
  rw [hp]
  let w := KPHilbert.B3 F ζ hζ (Sum.inr q) c x
  have hw : w^3=1 := Subtype.ext w.property
  change (w^(-4:ℤ))^2=w
  have he : (-4:ℤ) = 2-2*3 := by omega
  rw [he, zpow_sub, zpow_mul]
  simp only [zpow_ofNat]
  rw [← pow_mul, show 2*3=3*2 by omega, pow_mul, hw]
  simp only [one_pow, inv_one, mul_one]
  rw [← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [show 4=3+1 by omega, pow_add, hw]; simp

private lemma actual_word
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (c x y : (LocalField F q)ˣ) :
    S.borel.weyl ((S.openCell P).rootTorus (c*x)) *
      (S.openCell P).rootTorus (x*y^3) =
    (S.central (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : _) *
      (S.borel.weyl ((S.openCell P).rootTorus c) *
        (S.openCell P).rootTorus 1) *
      (S.borel.cubeLift (y^2) : _) := by
  have hr (w : (LocalField F q)ˣ) :
      ((S.openCell P).rootTorus w : Cover F ζ hζ q) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (w^2) := by
    rw [← S.torus_full, (S.openCell P).torus_eq]; rfl
  have hw (w : (LocalField F q)ˣ) :
      (S.borel.weyl ((S.openCell P).rootTorus w) : Cover F ζ hζ q) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (w^2)⁻¹ := by
    rw [← S.torus_full, S.borel.weyl_from_lift, S.torus_full, hr,
      (S.openCell P).weyl_eq]
    have he : signedWeyl F ζ hζ q = KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) := by
      unfold signedWeyl; rw [signedWeyl_eq_prescribed_signed]; rfl
    rw [he, DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux.signedW_conjugates_A]
  apply Subtype.val_injective
  simp only [Subgroup.coe_mul, hw, hr, S.central_actual, S.cube_actual]
  rw [KPPGLLocalCover.A_mul, ratio_phase]
  simp only [one_pow]
  have hB1 : KPHilbert.B3 F ζ hζ (Sum.inr q) (c^2)⁻¹ 1 = 1 := BoneR F ζ hζ q _
  rw [KPPGLLocalCover.A_mul, hB1]
  simp only [one_pow, map_one, one_mul, mul_one]
  rw [mul_assoc, KPPGLLocalCover.A_mul,
    (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 _ _ |>.2]
  simp only [one_pow, map_one, one_mul]
  congr 2
  simp only [mul_pow, inv_pow]
  group
  rw [mul_right_comm (x^(-2:ℤ)), ← zpow_add, neg_add_cancel]
  simp

private lemma center_word_action
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (c x y : (LocalField F q)ˣ)
    (V : CenterModule S.heisenberg) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    ((centerTorus F ζ hζ q S.heisenberg S.borel .minus ((S.openCell P).rootTorus (c*x)))
      ((centerTorus F ζ hζ q S.heisenberg S.borel .plus
        ((S.openCell P).rootTorus (x*y^3))) V)).val h =
      (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
      normPower (LocalField F q) ((y^2)^3) (1/6) *
      ((centerTorus F ζ hζ q S.heisenberg S.borel .minus ((S.openCell P).rootTorus c))
        ((centerTorus F ζ hζ q S.heisenberg S.borel .plus
          ((S.openCell P).rootTorus 1)) V)).val h := by
  change V.val (h * S.borel.weyl ((S.openCell P).rootTorus (c*x)) *
    (S.openCell P).rootTorus (x*y^3)) = _
  rw [mul_assoc, actual_word F ζ hζ q S P]
  let e := KPHilbert.B3 F ζ hζ (Sum.inr q) c x
  let W := S.borel.weyl ((S.openCell P).rootTorus c) * (S.openCell P).rootTorus 1
  let C := S.borel.cubeLift (y^2)
  have hcent (z : S.heisenberg.C) (g : KPExceptionalRaw.actualTorus F ζ hζ q) :
      g * z = z * g := (Subgroup.mem_center_iff.mp (S.heisenberg.central z.property) g)
  change V.val (h * (((S.central e : _) * W) * (C : _))) = _
  rw [← mul_assoc, ← mul_assoc, hcent (S.central e), mul_assoc, mul_assoc,
    V.property]
  rw [← mul_assoc, hcent C, V.property]
  change (S.heisenberg.ω (S.central e) : ℂ) *
    ((S.heisenberg.ω (S.borel.cubeLift (y^2)) : ℂ) * V.val (h*W)) = _
  rw [S.central_character, S.borel.exceptional_cube]
  change _ = _ * _ * V.val (h * S.borel.weyl ((S.openCell P).rootTorus c) *
    (S.openCell P).rootTorus 1)
  simp [W, C, e, mul_assoc]

private lemma norm_unram_direct (s : ℂ) (r t : ℂˣ)
    (hr : (r : ℂ) = KPRankOneRootParameter.r (LocalField F q) s)
    (ht : (t : ℂ) = (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ)^6)
    (y : (LocalField F q)ˣ) :
    normPower (LocalField F q) y (1+6*s) = KPCubicExpansion.omega (LocalField F q) t y := by
  let L : ℂ := Real.log (residueCardinality (LocalField F q) : ℝ)
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField F q)).integer))
  have hl : (Real.log (localAbs (LocalField F q) y) : ℂ) =
      -(KPCubicExpansion.valuationExponent (LocalField F q) y : ℂ) * L := by
    simp only [localAbs, KPCubicExpansion.valuationExponent]
    rw [Real.log_rpow hq]
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_neg, neg_neg]
  have he : Complex.exp (-(1+6*s)*L) = (t:ℂ) := by
    rw [show -(1+6*s)*L = -L+6*(-s*L) by ring, Complex.exp_add]
    rw [show (6:ℂ)=((6:ℕ):ℂ) by norm_num, Complex.exp_nat_mul]
    change Complex.exp (-L) * KPRankOneRootParameter.r (LocalField F q) s ^ 6 = _
    rw [← hr, ht]; congr 1
    rw [Complex.exp_neg]; congr 1
    exact (Complex.ofReal_exp (Real.log (residueCardinality (LocalField F q) : ℝ))).symm |>.trans
      (congrArg Complex.ofReal (Real.exp_log hq))
  rw [normPower, hl]
  rw [show (1+6*s)*(-(KPCubicExpansion.valuationExponent (LocalField F q) y : ℂ)*L) =
    (KPCubicExpansion.valuationExponent (LocalField F q) y : ℂ)*(-(1+6*s)*L) by ring,
    Complex.exp_int_mul, he]
  simp [KPCubicExpansion.omega]

private lemma norm_weights (c x y : (LocalField F q)ˣ) (s ρ : ℂ) :
    normPower (LocalField F q) ((c*x)^2) (-s) *
      normPower (LocalField F q) ((x*y^3)^2) s *
      normPower (LocalField F q) ((y^2)^3) (1/6) *
      normPower (LocalField F q) (c*x) ρ =
    normPower (LocalField F q) y (1+6*s) * normPower (LocalField F q) c ρ *
      normPower (LocalField F q) (c^2) (-s) * normPower (LocalField F q) x ρ := by
  simp only [norm_pow, norm_mul]
  simp only [normPower]
  repeat rw [← Complex.exp_add]
  congr 1
  ring

theorem actual_doubleKernel_all_ratios
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    [DecidableEq S.D]
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (s ρ : ℂ) (r t : ℂˣ)
    (hr : (r : ℂ) = KPRankOneRootParameter.r (LocalField F q) s)
    (ht : (t : ℂ) = (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ) ^ 6)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q)
    (a b u v : (LocalField F q)ˣ) :
    doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h a b u v =
      KPCubicExpansion.omega (LocalField F q) t (u / v) *
        normPower (LocalField F q) (b / a) ρ *
        (KPExceptionalRaw.ordinaryIota F ζ hζ
          (KPHilbert.B3 F ζ hζ (Sum.inr q) (b / a) (a * v ^ 3)) : ℂ) *
        doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d (fun _ => 1) s 0 h 1 (b / a) 1 1 *
        φ (((a * v ^ 3 : (LocalField F q)ˣ) : LocalField F q) *
          (((u / v : (LocalField F q)ˣ) : LocalField F q) ^ 3 +
            ((b / a : (LocalField F q)ˣ) : LocalField F q))) *
        normPower (LocalField F q) (a * v ^ 3) ρ := by
  let c := b/a
  let x := a*v^3
  let y := u/v
  have hc : c*x = b*v^3 := by dsimp [c,x]; simp [← mul_assoc]
  have hx : x*y^3 = a*u^3 := by dsimp [x,y]; simp [div_eq_mul_inv, mul_pow, inv_pow, mul_comm, mul_left_comm, mul_assoc]
  have hφ : sourceTranslation F q a b u v =
      (x:LocalField F q)*((y:LocalField F q)^3+(c:LocalField F q)) := by
    dsimp [sourceTranslation,c,x,y]
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    field_simp
  dsimp only [doubleKernel, reverseIncrement]
  simp only [kappa_eq_one F ζ hζ q, S.openCell_ordinary, map_one, Units.val_one,
    one_mul, one_pow, mul_one]
  have n1 : ∀ z : ℂ, normPower (LocalField F q) 1 z = 1 := by
    intro z; simp [normPower, localAbs_one]
  have n0 : ∀ w : (LocalField F q)ˣ, normPower (LocalField F q) w 0 = 1 := by
    intro w; simp [normPower]
  simp only [n1, n0, mul_one]
  rw [hφ, ← hc, ← hx]
  simp only [map_smul]
  have hsval (z : ℂ) (V : CenterModule S.heisenberg) :
      (z • V).val h = z * V.val h := rfl
  simp only [hsval, one_smul]
  rw [center_word_action F ζ hζ q S P c x y]
  change _ = KPCubicExpansion.omega (LocalField F q) t y * normPower (LocalField F q) c ρ *
    (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
    (normPower (LocalField F q) (c^2) (-s) * _) * φ ((x:LocalField F q)*((y:LocalField F q)^3+(c:LocalField F q))) *
    normPower (LocalField F q) x ρ
  rw [← norm_unram_direct F q s r t hr ht]
  have he := norm_weights F q c x y s ρ
  linear_combination (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
    φ ((x:LocalField F q)*((y:LocalField F q)^3+(c:LocalField F q))) *
    (((centerTorus F ζ hζ q S.heisenberg S.borel .minus ((S.openCell P).rootTorus c))
      ((centerTorus F ζ hζ q S.heisenberg S.borel .plus ((S.openCell P).rootTorus 1))
        ((centerCoordinates S.heisenberg rep hrep).symm (Pi.single d 1)))).val h) * he

end
end DedekindZetaZeroFree.KPActualFullKernelArithmetic
