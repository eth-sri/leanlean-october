module
public import GafniTao.WooleyLemma63
public import GafniTao.WooleyThreeFactorHolder
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Wooley's initial conditioning argument

This file formalizes Lemma 6.1 of nested efficient congruencing.  The
diagonal and separated residue-pair contributions are kept as literal finite
sums, so that equations (6.6)--(6.9) can be audited against the source.
-/

open Finset

namespace GafniTao

noncomputable section

/-- The pointwise monomial identity behind the three-factor interpolation
in (6.8). -/
theorem wooley_critical_interpolation_term
    {s : ℕ} (hs : 2 ≤ s) {w u v : ℝ}
    (hw : 0 ≤ w) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    w ^ (((s : ℝ) - 2) / (s : ℝ)) *
        (w * u ^ 2 * v ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) *
          (w * v ^ 2 * u ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) =
      w * (u * u) * (v * v) := by
  have hsReal : (0 : ℝ) < s := by
    positivity
  pm_8873 hroot s
  by_cases hw0 : w = 0
  pm_2827 hw0
  by_cases hu0 : u = 0
  pm_2827 hu0
  by_cases hv0 : v = 0
  · calc
      w ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (w * u ^ 2 * v ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) *
            (w * v ^ 2 * u ^ (2 * (s - 1))) ^ (1 / (s : ℝ)) = 0 := by
        rw [show w * v ^ 2 * u ^ (2 * (s - 1)) = 0 by simp [hv0],
          Real.zero_rpow hroot.ne']
        ring
      _ = w * (u * u) * (v * v) := by simp [hv0]
  pm_485 hwpos w lt_of_le_of_ne hw Ne.symm hw0
  pm_485 hupos u lt_of_le_of_ne hu Ne.symm hu0
  pm_485 hvpos v lt_of_le_of_ne hv Ne.symm hv0
  rw [Real.mul_rpow (mul_nonneg hw (sq_nonneg u))
      (pow_nonneg hv _),
    Real.mul_rpow hw (sq_nonneg u),
    Real.mul_rpow (mul_nonneg hw (sq_nonneg v))
      (pow_nonneg hu _),
    Real.mul_rpow hw (sq_nonneg v)]
  simp only [← Real.rpow_natCast]
  pm_8656 hu hv
  have hwexp : ((s : ℝ) - 2) / (s : ℝ) + 1 / (s : ℝ) +
      1 / (s : ℝ) = 1 := by field_simp; ring
  have huexp : (2 : ℝ) * (1 / (s : ℝ)) +
      2 * (s - 1 : ℕ) * (1 / (s : ℝ)) = 2 := by
    pm_567 Nat.cast_sub s
    field_simp
    ring
  have hvexp : 2 * (s - 1 : ℕ) * (1 / (s : ℝ)) +
      (2 : ℝ) * (1 / (s : ℝ)) = 2 := by
    pm_567 Nat.cast_sub s
    field_simp
    ring
  have hcast : ((2 * (s - 1) : ℕ) : ℝ) = 2 * (s - 1 : ℕ) := by
    norm_num
  pm_7618 huTwo u
  pm_7618 hvTwo v
  calc
    w ^ (((s : ℝ) - 2) / (s : ℝ)) *
          (w ^ (1 / (s : ℝ)) * u ^ ((2 : ℝ) * (1 / (s : ℝ))) *
            v ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)))) *
          (w ^ (1 / (s : ℝ)) * v ^ ((2 : ℝ) * (1 / (s : ℝ))) *
            u ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)))) =
        (w ^ (((s : ℝ) - 2) / (s : ℝ)) * w ^ (1 / (s : ℝ)) *
          w ^ (1 / (s : ℝ))) *
        (u ^ ((2 : ℝ) * (1 / (s : ℝ))) *
          u ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)))) *
        (v ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ))) *
          v ^ ((2 : ℝ) * (1 / (s : ℝ)))) := by ring
    _ = w ^ ((((s : ℝ) - 2) / (s : ℝ)) + 1 / (s : ℝ) +
          1 / (s : ℝ)) *
        u ^ ((2 : ℝ) * (1 / (s : ℝ)) +
          (2 * (s - 1) : ℕ) * (1 / (s : ℝ))) *
        v ^ ((2 * (s - 1) : ℕ) * (1 / (s : ℝ)) +
          (2 : ℝ) * (1 / (s : ℝ))) := by
      rw [Real.rpow_add hwpos, Real.rpow_add hwpos,
        Real.rpow_add hupos, Real.rpow_add hvpos]
    _ = w * (u * u) * (v * v) := by
      pm_265 hcast hwexp huexp hvexp Real.rpow_one
      rw [huTwo, hvTwo]

/-- The exact three-factor Hölder inequality used before (6.8).  The two
last factors retain opposite orientations; their later equality is a
separate symmetry statement. -/
theorem wooley_pair_mixed_holder
    {ι : Type*} (t : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i)
    (hu : ∀ i ∈ t, 0 ≤ u i)
    (hv : ∀ i ∈ t, 0 ≤ v i)
    {s : ℕ} (hs : 2 ≤ s) :
    (∑ i ∈ t, w i * u i ^ 2 * v i ^ 2) ^ s ≤
      (∑ i ∈ t, w i) ^ (s - 2) *
        (∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1))) *
          (∑ i ∈ t, w i * v i ^ 2 * u i ^ (2 * (s - 1))) := by
  let f₀ : ι → ℝ := w
  pm_6122 f₁ u v
  pm_6122 f₂ v u
  have hf₀ : ∀ i ∈ t, 0 ≤ f₀ i := by
    intro i hi
    exact hw i hi
  pm_5126 hf₁ f₁ hv
  pm_5126 hf₂ f₂ hu
  have hholder := wooley_three_factor_holder_critical_real
    t f₀ f₁ f₂ hf₀ hf₁ hf₂ hs
  have hterm (i : ι) (hi : i ∈ t) :
      f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ)) =
        w i * u i ^ 2 * v i ^ 2 := by
    dsimp [f₀, f₁, f₂]
    simpa only [pow_two] using
      (wooley_critical_interpolation_term hs
        (hw i hi) (hu i hi) (hv i hi))
  have hsumTerm :
      (∑ i ∈ t,
        f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
          f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ))) =
        ∑ i ∈ t, w i * u i ^ 2 * v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  have hsub : (s : ℝ) - 2 = ((s - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hs]
    norm_num
  calc
    (∑ i ∈ t, w i * u i ^ 2 * v i ^ 2) ^ s =
        (∑ i ∈ t,
          f₀ i ^ (((s : ℝ) - 2) / (s : ℝ)) *
            f₁ i ^ (1 / (s : ℝ)) * f₂ i ^ (1 / (s : ℝ))) ^
              (s : ℝ) := by
      rw [Real.rpow_natCast, hsumTerm]
    _ ≤ (∑ i ∈ t, f₀ i) ^ ((s : ℝ) - 2) *
        (∑ i ∈ t, f₁ i) * (∑ i ∈ t, f₂ i) := hholder
    _ = (∑ i ∈ t, w i) ^ (s - 2) *
        (∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1))) *
          (∑ i ∈ t, w i * v i ^ 2 * u i ^ (2 * (s - 1))) := by
      dsimp [f₀, f₁, f₂]
      rw [hsub, Real.rpow_natCast]

/-- For residues at depth `nu`, Wooley's separation predicate is precisely
inequality of the residue classes. -/
theorem wooleyResiduesSeparated_same_iff_ne
    {p nu : ℕ} [NeZero p] (xi eta : ZMod (p ^ nu)) :
    wooleyResiduesSeparated nu xi eta ↔ xi ≠ eta := by
  unfold wooleyResiduesSeparated
  rw [Nat.mod_eq_of_lt (ZMod.val_lt xi),
    Nat.mod_eq_of_lt (ZMod.val_lt eta)]
  constructor
  · intro hval heq
    exact hval (congrArg ZMod.val heq)
  · intro hne hval
    apply hne
    apply ZMod.val_injective
    exact hval

/-- The literal ordered separated residue-pair set at depth `nu`. -/
def wooleySeparatedResiduePairs (p nu : ℕ) [NeZero p] :
    Finset (ZMod (p ^ nu) × ZMod (p ^ nu)) :=
  (Finset.univ.product Finset.univ).filter fun xy =>
    wooleyResiduesSeparated nu xy.1 xy.2

section
variable {p nu : ℕ} [NeZero p]
include p nu
theorem wooley_sum_separatedResiduePairs
    (F : ZMod (p ^ nu) → ZMod (p ^ nu) → ℝ) :
    ∑ xy ∈ wooleySeparatedResiduePairs p nu, F xy.1 xy.2 =
      ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with
          wooleyResiduesSeparated nu xi eta, F xi eta := by
  unfold wooleySeparatedResiduePairs
  simp only [Finset.sum_filter]
  simpa using
    (Finset.sum_product
      (Finset.univ : Finset (ZMod (p ^ nu)))
      (Finset.univ : Finset (ZMod (p ^ nu)))
      (fun xy => if wooleyResiduesSeparated nu xy.1 xy.2 then
        F xy.1 xy.2 else 0))

theorem wooley_sum_separatedResiduePairs_apply
    (F : ZMod (p ^ nu) × ZMod (p ^ nu) → ℝ) :
    ∑ xy ∈ wooleySeparatedResiduePairs p nu, F xy =
      ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with
          wooleyResiduesSeparated nu xi eta, F (xi, eta) := by
  simpa using wooley_sum_separatedResiduePairs
    (p := p) (nu := nu) (fun xi eta => F (xi, eta))
end

theorem wooleySeparatedResiduePairs_card_le (p nu : ℕ) [NeZero p] :
    #(wooleySeparatedResiduePairs p nu) ≤ (p ^ nu) ^ 2 := by
  calc
    #(wooleySeparatedResiduePairs p nu) ≤
        #((Finset.univ : Finset (ZMod (p ^ nu))).product Finset.univ) :=
      by
        unfold wooleySeparatedResiduePairs
        exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (p ^ nu) ^ 2 := by
      simp [pow_two]

/-- Cauchy followed by the exact critical three-factor Hölder inequality.
This is the abstract finite inequality underlying (6.8), including the
square-root descent used after the two orientations are identified. -/
theorem wooley_cauchy_three_factor_symmetric
    {ι : Type*} (t : Finset ι) (w u v : ι → ℝ)
    (q M : ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hw : ∀ i ∈ t, 0 ≤ w i)
    (hu : ∀ i ∈ t, 0 ≤ u i)
    (hv : ∀ i ∈ t, 0 ≤ v i)
    {s : ℕ} (hs : 2 ≤ s)
    (hcard : (#t : ℝ) ≤ q ^ 2)
    (hmass : (∑ i ∈ t, w i) ≤ M ^ 2)
    (hsymmetry :
      (∑ i ∈ t, w i * v i ^ 2 * u i ^ (2 * (s - 1))) =
        ∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1))) :
    (∑ i ∈ t, Real.sqrt (w i) * u i * v i) ^ s ≤
      q ^ s * M ^ (s - 2) *
        ∑ i ∈ t, w i * u i ^ 2 * v i ^ (2 * (s - 1)) := by
  pm_7084 i
  pm_7784
  let A : ℝ := ∑ i ∈ t, w i * u i ^ 2 * v i ^ 2
  pm_4965 F i u v
  pm_4965 G i v u
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hu i hi)) (hv i hi)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i hi => hw i hi
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _)) (sq_nonneg _)
  pm_5159 hF F hv
  pm_5159 hG G hu
  have hCauchy : S ^ 2 ≤ (#t : ℝ) * A := by
    have h := sum_mul_sq_le_sq_mul_sq (R := ℝ) t
      (fun _ : ι => 1)
      (fun i => Real.sqrt (w i) * u i * v i)
    have hsquares :
        (∑ i ∈ t, (Real.sqrt (w i) * u i * v i) ^ 2) = A := by
      dsimp [A]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow, mul_pow, Real.sq_sqrt (hw i hi)]
    dsimp [S]
    calc
      (∑ i ∈ t, Real.sqrt (w i) * u i * v i) ^ 2 ≤
          (#t : ℝ) *
            ∑ i ∈ t, (Real.sqrt (w i) * u i * v i) ^ 2 := by
        simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul,
          Nat.cast_ofNat, Nat.cast_card, mul_one] using h
      _ = (#t : ℝ) * A := by rw [hsquares]
  have hHolder : A ^ s ≤ W ^ (s - 2) * F * G := by
    simpa only [A, W, F, G] using
      (wooley_pair_mixed_holder t w u v hw hu hv hs)
  have hRaised := pow_le_pow_left₀ (sq_nonneg S) hCauchy s
  have hcardPow : (#t : ℝ) ^ s ≤ (q ^ 2) ^ s :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard s
  have hmassPow : W ^ (s - 2) ≤ (M ^ 2) ^ (s - 2) :=
    pow_le_pow_left₀ hW hmass (s - 2)
  have hSquare : (S ^ s) ^ 2 ≤
      (q ^ s * M ^ (s - 2) * F) ^ 2 := by
    calc
      (S ^ s) ^ 2 = (S ^ 2) ^ s := by
        calc
          (S ^ s) ^ 2 = S ^ (s * 2) := (pow_mul S s 2).symm
          _ = S ^ (2 * s) := by rw [Nat.mul_comm]
          _ = (S ^ 2) ^ s := pow_mul S 2 s
      _ ≤ ((#t : ℝ) * A) ^ s := hRaised
      _ = (#t : ℝ) ^ s * A ^ s := by rw [mul_pow]
      _ ≤ (#t : ℝ) ^ s * (W ^ (s - 2) * F * G) := by
        gcongr
      _ ≤ (q ^ 2) ^ s * ((M ^ 2) ^ (s - 2) * F * G) := by
        gcongr
      _ = (q ^ 2) ^ s * ((M ^ 2) ^ (s - 2) * F * F) := by
        rw [show G = F by simpa [G, F] using hsymmetry]
      _ = (q ^ s * M ^ (s - 2) * F) ^ 2 := by
        have hqpow : (q ^ 2) ^ s = (q ^ s) ^ 2 := by
          calc
            (q ^ 2) ^ s = q ^ (2 * s) := (pow_mul q 2 s).symm
            _ = q ^ (s * 2) := by rw [Nat.mul_comm]
            _ = (q ^ s) ^ 2 := pow_mul q s 2
        have hMpow : (M ^ 2) ^ (s - 2) =
            (M ^ (s - 2)) ^ 2 := by
          calc
            (M ^ 2) ^ (s - 2) = M ^ (2 * (s - 2)) :=
              (pow_mul M 2 (s - 2)).symm
            _ = M ^ ((s - 2) * 2) := by rw [Nat.mul_comm]
            _ = (M ^ (s - 2)) ^ 2 := pow_mul M (s - 2) 2
        rw [hqpow, hMpow, mul_pow, mul_pow]
        ring
  have hRight : 0 ≤ q ^ s * M ^ (s - 2) * F :=
    mul_nonneg (mul_nonneg (pow_nonneg hq _) (pow_nonneg hM _)) hF
  exact (sq_le_sq₀ (pow_nonneg hS s) hRight).mp hSquare

/-- Squaring the triangle inequality and separating the diagonal from the
ordered off-diagonal pairs.  This is the finite algebra used in (6.6). -/
theorem wooley_norm_sum_sq_le_diagonal_add_offDiagonal
    {ι : Type*} [DecidableEq ι] (t : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ t, z i‖ ^ 2 ≤
      (∑ i ∈ t, ‖z i‖ ^ 2) +
        ∑ i ∈ t, ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
  have hnorm : ‖∑ i ∈ t, z i‖ ≤ ∑ i ∈ t, ‖z i‖ :=
    norm_sum_le _ _
  have hnonneg : 0 ≤ ∑ i ∈ t, ‖z i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖∑ i ∈ t, z i‖ ^ 2 ≤ (∑ i ∈ t, ‖z i‖) ^ 2 := hsq
    _ = ∑ i ∈ t, ∑ j ∈ t, ‖z i‖ * ‖z j‖ := by
      pm_266 pow_two Finset.sum_mul Finset.sum_congr i hi
      rw [Finset.mul_sum]
    _ = (∑ i ∈ t, ‖z i‖ ^ 2) +
        ∑ i ∈ t, ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
      have hinner (i : ι) (hi : i ∈ t) :
          (∑ j ∈ t, ‖z i‖ * ‖z j‖) =
            ‖z i‖ ^ 2 + ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
        rw [← Finset.add_sum_erase t (fun j => ‖z i‖ * ‖z j‖) hi]
        congr 1
        · ring
        · apply Finset.sum_congr
          · ext j
            simp [and_comm]
          · intro j hj
            rfl
      calc
        (∑ i ∈ t, ∑ j ∈ t, ‖z i‖ * ‖z j‖) =
            ∑ i ∈ t,
              (‖z i‖ ^ 2 +
                ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hinner i hi
        _ = (∑ i ∈ t, ‖z i‖ ^ 2) +
            ∑ i ∈ t, ∑ j ∈ t with j ≠ i, ‖z i‖ * ‖z j‖ := by
          rw [Finset.sum_add_distrib]

/-- The separated pair mass is bounded by the square of the total mass;
the omitted diagonal has nonnegative weight. -/
theorem wooley_separated_pair_mass_le_square {Q : ℕ}
    (p nu : ℕ) [NeZero p] (gamma : Fin Q → ℂ) :
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta) ≤
      wooleyWeightedMassSq gamma ^ 2 := by
  pm_6248
  have hfilter (xi : ZMod (p ^ nu)) :
      (∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          w xi * w eta) ≤
        ∑ eta : ZMod (p ^ nu), w xi * w eta := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro eta heta hnot
    exact mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
      (wooleyWeightedResidueMassSq_nonneg gamma eta)
  calc
    (∑ xi : ZMod (p ^ nu),
      ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta) ≤
        ∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu), w xi * w eta := by
      apply Finset.sum_le_sum
      intro xi hxi
      simpa [w] using hfilter xi
    _ = (∑ xi : ZMod (p ^ nu), w xi) ^ 2 := by
      pm_266 pow_two Finset.sum_mul Finset.sum_congr xi hxi
      rw [Finset.mul_sum]
    _ = wooleyWeightedMassSq gamma ^ 2 := by
      rw [show (∑ xi : ZMod (p ^ nu), w xi) =
          wooleyWeightedMassSq gamma by
        simpa [w] using wooley_sum_weightedResidueMassSq
          (q := p ^ nu) gamma]

section
variable {M : ℝ} {s : ℕ} (hM : 0 < M)
include M s hM
theorem wooley_inv_pow_mul_pow_pred (hs : 1 ≤ s) :
    M⁻¹ ^ s * M ^ (s - 1) = M⁻¹ := by
  pm_645
  rw [inv_pow, hpow]
  field_simp

theorem wooley_inv_pow_mul_pow_sub_two (hs : 2 ≤ s) :
    M⁻¹ ^ s * M ^ (s - 2) = M⁻¹ ^ 2 := by
  have hpow : M ^ s = M ^ (s - 2) * M ^ 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_add]
  rw [inv_pow, hpow]
  field_simp
end

/-- The elementary convexity estimate used when equation (6.6) is raised
to the `s`-th power.  The constant is retained explicitly. -/
theorem wooley_add_pow_le_two_pow_pred_mul
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℕ} (hs : 1 ≤ s) :
    (a + b) ^ s ≤ 2 ^ (s - 1) * (a ^ s + b ^ s) := by
  let aa : NNReal := ⟨a, ha⟩
  let bb : NNReal := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow aa bb
    (p := (s : ℝ)) (by exact_mod_cast hs)
  have hr := (NNReal.coe_le_coe).mpr h
  change (a+b)^(s:ℝ) ≤ (2:ℝ)^((s:ℝ)-1)*(a^(s:ℝ)+b^(s:ℝ)) at hr
  have he : (s:ℝ)-1 = ((s-1:ℕ):ℝ) := by rw [Nat.cast_sub hs]; norm_num
  simpa only [he, Real.rpow_natCast] using hr

/-- Wooley's choice (6.5), using the natural ceiling convention. -/
def wooleyInitialNu (epsilon Lambda : ℝ) (H : ℕ) : ℕ :=
  ⌈4 * epsilon * (H : ℝ) / Lambda⌉₊

theorem wooley_initialNu_lower
    {epsilon Lambda : ℝ} {H : ℕ} :
    4 * epsilon * (H : ℝ) / Lambda ≤
      (wooleyInitialNu epsilon Lambda H : ℝ) := by
  exact Nat.le_ceil _

/-- Quantitative absorption of the contracted copy of `U`. -/
theorem wooley_absorb_contraction
    {U K c a : ℝ} (hU : 0 ≤ U)
    (hmain : U ≤ c * (a * U + K))
    (hsmall : 2 * c * a ≤ 1) :
    U ≤ 2 * c * K := by
  have hca : c * a ≤ (1 : ℝ) / 2 := by nlinarith
  have hcontract : c * a * U ≤ ((1 : ℝ) / 2) * U :=
    mul_le_mul_of_nonneg_right hca hU
  have hmain' : U ≤ c * a * U + c * K := by
    calc
      U ≤ c * (a * U + K) := hmain
      _ = c * a * U + c * K := by ring
  nlinarith

end

end GafniTao
