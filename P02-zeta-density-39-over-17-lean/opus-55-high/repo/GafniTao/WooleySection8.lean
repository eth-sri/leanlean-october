module
public import GafniTao.WooleySection8Arithmetic
public import GafniTao.WooleyPolynomialLemma63
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Wooley Section 8: the iterative Hölder step

This file formalizes the interpolation in equations (8.1)--(8.3) for the
literal polynomial-system moments.  The first lemma records the pointwise
exponent identity, keeping both residue factors and both natural-power
exponents visible.
-/

open Finset

namespace GafniTao

noncomputable section

/-- Ordered separated residue pairs at two (possibly different) depths. -/
def wooleySeparatedResiduePairsAt (p nu a b : ℕ) [NeZero p] :
    Finset (ZMod (p ^ a) × ZMod (p ^ b)) :=
  (Finset.univ.product Finset.univ).filter fun xy =>
    wooleyResiduesSeparated nu xy.1 xy.2

theorem wooleyResiduesSeparated_symm
    {p nu a b : ℕ} {xi : ZMod (p ^ a)} {eta : ZMod (p ^ b)} :
    wooleyResiduesSeparated nu xi eta ↔
      wooleyResiduesSeparated nu eta xi := by
  unfold wooleyResiduesSeparated
  exact ne_comm

theorem wooley_sum_separatedResiduePairsAt
    {p nu a b : ℕ} [NeZero p]
    (F : ZMod (p ^ a) → ZMod (p ^ b) → ℝ) :
    ∑ xy ∈ wooleySeparatedResiduePairsAt p nu a b, F xy.1 xy.2 =
      ∑ xi : ZMod (p ^ a),
        ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
          F xi eta := by
  unfold wooleySeparatedResiduePairsAt
  simp only [Finset.sum_filter]
  simpa using
    (Finset.sum_product
      (Finset.univ : Finset (ZMod (p ^ a)))
      (Finset.univ : Finset (ZMod (p ^ b)))
      (fun xy => if wooleyResiduesSeparated nu xy.1 xy.2 then
        F xy.1 xy.2 else 0))

theorem wooley_sum_separatedResiduePairsAt_swap
    {p nu a b : ℕ} [NeZero p]
    (F : ZMod (p ^ a) → ZMod (p ^ b) → ℝ) :
    ∑ xy ∈ wooleySeparatedResiduePairsAt p nu a b, F xy.1 xy.2 =
      ∑ yx ∈ wooleySeparatedResiduePairsAt p nu b a, F yx.2 yx.1 := by
  rw [wooley_sum_separatedResiduePairsAt,
    wooley_sum_separatedResiduePairsAt
      (F := fun eta xi => F xi eta)]
  pm_224 Finset.sum_filter Finset.sum_comm eta heta
  pm_2798
  by_cases h : wooleyResiduesSeparated nu xi eta
  grind
  grind

section
variable {ι : Type*} (t : Finset ι)
include ι t
/-- Hölder interpolation with the common finite-average normalizer retained.
This is the exact form needed for the `∮_{p^B}` normalization. -/
theorem wooley_scaled_two_factor_holder_real (f g : ι → ℝ)
    (hf : ∀ i ∈ t, 0 ≤ f i) (hg : ∀ i ∈ t, 0 ≤ g i)
    {u c : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hc : 0 < c) :
    c * (∑ i ∈ t, f i ^ u * g i ^ (1 - u)) ≤
      (c * ∑ i ∈ t, f i) ^ u *
        (c * ∑ i ∈ t, g i) ^ (1 - u) := by
  have hholder := wooley_two_factor_holder_real t f g hf hg hu0 hu1
  pm_2826
  have hscale := mul_le_mul_of_nonneg_left hholder hc.le
  calc
    c * (∑ i ∈ t, f i ^ u * g i ^ (1 - u)) ≤
        c * ((∑ i ∈ t, f i) ^ u * (∑ i ∈ t, g i) ^ (1 - u)) := hscale
    _ = (c * ∑ i ∈ t, f i) ^ u *
        (c * ∑ i ∈ t, g i) ^ (1 - u) := by
      rw [Real.mul_rpow hc.le hsumF, Real.mul_rpow hc.le hsumG]
      calc
        c * ((∑ i ∈ t, f i) ^ u * (∑ i ∈ t, g i) ^ (1 - u)) =
            (c ^ u * c ^ (1 - u)) *
              ((∑ i ∈ t, f i) ^ u * (∑ i ∈ t, g i) ^ (1 - u)) := by
                rw [← Real.rpow_add hc]
                norm_num
        _ = _ := by ring

/-- The weighted form of the normalized finite-average Hölder inequality.
The same nonnegative mass `w i` is retained in both interpolated moments,
exactly as in the second Hölder application following Wooley (8.3). -/
theorem wooley_scaled_weighted_two_factor_holder_real (w f g h : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hf : ∀ i ∈ t, 0 ≤ f i)
    (hg : ∀ i ∈ t, 0 ≤ g i)
    {u c : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hc : 0 < c)
    (hpoint : ∀ i ∈ t, h i ≤ f i ^ u * g i ^ (1 - u)) :
    c * (∑ i ∈ t, w i * h i) ≤
      (c * ∑ i ∈ t, w i * f i) ^ u *
        (c * ∑ i ∈ t, w i * g i) ^ (1 - u) := by
  pm_8874 F f
  pm_8874 G g
  pm_6560 hF F hf
  pm_6560 hG G hg
  have hweight (i : ι) (hi : i ∈ t) :
      F i ^ u * G i ^ (1 - u) =
        w i * (f i ^ u * g i ^ (1 - u)) := by
    dsimp [F, G]
    rw [Real.mul_rpow (hw i hi) (hf i hi),
      Real.mul_rpow (hw i hi) (hg i hi)]
    calc
      (w i ^ u * f i ^ u) * (w i ^ (1 - u) * g i ^ (1 - u)) =
          (w i ^ u * w i ^ (1 - u)) *
            (f i ^ u * g i ^ (1 - u)) := by ring
      _ = w i * (f i ^ u * g i ^ (1 - u)) := by
        rw [← Real.rpow_add' (hw i hi) (by norm_num : u + (1 - u) ≠ 0)]
        norm_num
  have hsum :
      (∑ i ∈ t, w i * h i) ≤
        ∑ i ∈ t, F i ^ u * G i ^ (1 - u) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hweight i hi]
    exact mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi)
  have hscaled := mul_le_mul_of_nonneg_left hsum hc.le
  exact hscaled.trans (by
    simpa only [F, G] using
      wooley_scaled_two_factor_holder_real t F G hF hG hu0 hu1 hc)
end

/-- The pointwise exponent identity used in the first Hölder application in
Wooley (8.3).  Here `x` is the `b'`-residue sum and `y` the `b`-residue sum. -/
theorem wooley_section8_integrand_identity
    {k r : ℕ} (hr : 1 ≤ r) (hrk : r < k)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((y ^ (2 * wooleyTriangular (k - r)) *
          x ^ (2 * (wooleyTriangular k - wooleyTriangular (k - r)))) ^
        (1 / ((k - r + 1 : ℕ) : ℝ))) *
      ((x ^ (2 * wooleyTriangular (r - 1)) *
          y ^ (2 * (wooleyTriangular k - wooleyTriangular (r - 1)))) ^
        (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ))) =
      x ^ (2 * wooleyTriangular r) *
        y ^ (2 * (wooleyTriangular k - wooleyTriangular r)) := by
  have htriSub : wooleyTriangular (k - r) ≤ wooleyTriangular k :=
    wooleyTriangular_sub_le k r
  have htriPred : wooleyTriangular (r - 1) ≤ wooleyTriangular k :=
    wooleyTriangular_pred_le (show r ≤ k by omega)
  pm_7114 htriR
  pm_111 hleft wooley_section8_left_exponent hr hrk hright wooley_section8_right_exponent
  have hleft' :
      ((2 * (wooleyTriangular k - wooleyTriangular (k - r)) : ℕ) : ℝ) *
            (1 / ((k - r + 1 : ℕ) : ℝ)) +
          ((2 * wooleyTriangular (r - 1) : ℕ) : ℝ) *
            (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) =
        ((2 * wooleyTriangular r : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm,
      mul_assoc] using hleft
  have hright' :
      ((2 * wooleyTriangular (k - r) : ℕ) : ℝ) *
            (1 / ((k - r + 1 : ℕ) : ℝ)) +
          ((2 * (wooleyTriangular k - wooleyTriangular (r - 1)) : ℕ) : ℝ) *
            (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) =
        ((2 * (wooleyTriangular k - wooleyTriangular r) : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm,
      mul_assoc] using hright
  pm_77 hrReal r hr
  have htriRReal : (0 : ℝ) < (wooleyTriangular r : ℕ) := by
    rw [wooleyTriangular_cast]
    positivity
  have htriR : 0 < wooleyTriangular r := by exact_mod_cast htriRReal
  have htriLtReal :
      (wooleyTriangular r : ℝ) < (wooleyTriangular k : ℕ) := by
    rw [wooleyTriangular_cast, wooleyTriangular_cast]
    have hprod : 0 < ((k : ℝ) - r) * ((k : ℝ) + r + 1) := by
      pm_5450 hkrReal r hrk
      exact mul_pos (sub_pos.mpr hkrReal) (by positivity)
    nlinarith
  have htriLt : wooleyTriangular r < wooleyTriangular k := by
    exact_mod_cast htriLtReal
  have hleftNe :
      ((2 * (wooleyTriangular k - wooleyTriangular (k - r)) : ℕ) : ℝ) *
            (1 / ((k - r + 1 : ℕ) : ℝ)) +
          ((2 * wooleyTriangular (r - 1) : ℕ) : ℝ) *
            (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) ≠ 0 := by
    rw [hleft']
    exact_mod_cast (show 2 * wooleyTriangular r ≠ 0 by positivity)
  have hrightNe :
      ((2 * wooleyTriangular (k - r) : ℕ) : ℝ) *
            (1 / ((k - r + 1 : ℕ) : ℝ)) +
          ((2 * (wooleyTriangular k - wooleyTriangular (r - 1)) : ℕ) : ℝ) *
            (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) ≠ 0 := by
    rw [hright']
    apply ne_of_gt
    exact_mod_cast (show 0 < 2 * (wooleyTriangular k - wooleyTriangular r) by
      exact Nat.mul_pos (by norm_num) (Nat.sub_pos_of_lt htriLt))
  rw [Real.mul_rpow (pow_nonneg hy _) (pow_nonneg hx _),
    Real.mul_rpow (pow_nonneg hx _) (pow_nonneg hy _)]
  simp_rw [← Real.rpow_natCast]
  pm_8656 hy hx
  calc
    _ =
        (x ^ (((2 * (wooleyTriangular k - wooleyTriangular (k - r)) : ℕ) : ℝ) *
              (1 / ((k - r + 1 : ℕ) : ℝ))) *
          x ^ (((2 * wooleyTriangular (r - 1) : ℕ) : ℝ) *
              (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)))) *
        (y ^ (((2 * wooleyTriangular (k - r) : ℕ) : ℝ) *
              (1 / ((k - r + 1 : ℕ) : ℝ))) *
          y ^ (((2 * (wooleyTriangular k - wooleyTriangular (r - 1)) : ℕ) : ℝ) *
              (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)))) := by ring
    _ = x ^ (((2 * (wooleyTriangular k - wooleyTriangular (k - r)) : ℕ) : ℝ) *
              (1 / ((k - r + 1 : ℕ) : ℝ)) +
            ((2 * wooleyTriangular (r - 1) : ℕ) : ℝ) *
              (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ))) *
        y ^ (((2 * wooleyTriangular (k - r) : ℕ) : ℝ) *
              (1 / ((k - r + 1 : ℕ) : ℝ)) +
            ((2 * (wooleyTriangular k - wooleyTriangular (r - 1)) : ℕ) : ℝ) *
              (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ))) := by
          rw [Real.rpow_add' hx hleftNe, Real.rpow_add' hy hrightNe]
    _ = _ := by rw [hleft', hright', Real.rpow_natCast, Real.rpow_natCast]

/-- The first Hölder application in Wooley (8.3), for a fixed separated
pair of residue classes.  Both terms on the right are the literal local
mixed moments from (3.20), with the residue roles interchanged in the first
factor. -/
theorem wooleyPolynomial_section8_local_holder
    {Q p B k r bPrime b : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (hr : 1 ≤ r) (hrk : r < k)
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ bPrime))
    (eta : ZMod (p ^ b)) :
    wooleyPolynomialMixedResidueGridMoment
        phi (wooleyTriangular k) r p B bPrime b gamma xi eta ≤
      (wooleyPolynomialMixedResidueGridMoment
          phi (wooleyTriangular k) (k - r) p B b bPrime gamma eta xi) ^
        (1 / ((k - r + 1 : ℕ) : ℝ)) *
      (wooleyPolynomialMixedResidueGridMoment
          phi (wooleyTriangular k) (r - 1) p B bPrime b gamma xi eta) ^
        (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) := by
  pm_2799
  pm_5482 x xi
  pm_5482 y eta
  let f (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
    y alpha ^ (2 * wooleyTriangular (k - r)) *
      x alpha ^
        (2 * (wooleyTriangular k - wooleyTriangular (k - r)))
  let g (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
    x alpha ^ (2 * wooleyTriangular (r - 1)) *
      y alpha ^
        (2 * (wooleyTriangular k - wooleyTriangular (r - 1)))
  pm_2840 c
  pm_61 hu0 u
  have hu1 : u ≤ 1 := by
    pm_2800
    have hdenPos : (0 : ℝ) < ((k - r + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hden
    pm_1447 div_le_iff₀ hdenPos one_mul hden
  have hc : 0 < c := by
    dsimp [c]
    have hpB : 0 < p ^ B := Nat.pos_of_ne_zero (NeZero.ne (p ^ B))
    have hpow : 0 < (p ^ B) ^ k := pow_pos hpB k
    exact inv_pos.mpr (by exact_mod_cast hpow)
  pm_5130 hf f
  pm_5130 hg g
  have hholder := wooley_scaled_two_factor_holder_real
    (Finset.univ : Finset (Fin k → ZMod (p ^ B))) f g hf hg hu0 hu1 hc
  have huv : 1 - u = v := by
    dsimp [u, v]
    exact wooley_section8_weight_complement hrk
  rw [huv] at hholder
  have hpoint (alpha : Fin k → ZMod (p ^ B)) :
      f alpha ^ u * g alpha ^ v =
        x alpha ^ (2 * wooleyTriangular r) *
          y alpha ^ (2 * (wooleyTriangular k - wooleyTriangular r)) := by
    dsimp [f, g, u, v]
    exact wooley_section8_integrand_identity hr hrk
      (norm_nonneg _) (norm_nonneg _)
  simp_rw [hpoint] at hholder
  simpa only [wooleyPolynomialMixedResidueGridMoment, x, y, f, g, c,
    u, v] using hholder

/-- Equation (8.3) for the literal polynomial-system mixed means.  This is
the second Hölder application in Wooley's proof, including the exact swap of
the two residue depths in the first factor. -/
theorem wooleyPolynomial_equation_8_3
    {Q p B k r bPrime b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (hr : 1 ≤ r) (hrk : r < k)
    (gamma : Fin Q → ℂ) :
    wooleyPolynomialMixedGridMean
        phi (wooleyTriangular k) r p B bPrime b nu gamma ≤
      (wooleyPolynomialMixedGridMean
          phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma) ^
        (1 / ((k - r + 1 : ℕ) : ℝ)) *
      (wooleyPolynomialMixedGridMean
          phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma) ^
        (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) := by
  unfold wooleyPolynomialMixedGridMean
  split_ifs with hmass
  · have hkrPos : 0 < k - r := Nat.sub_pos_of_lt hrk
    rw [Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
    norm_num
  · let pairs := wooleySeparatedResiduePairsAt p nu bPrime b
    let w : (ZMod (p ^ bPrime) × ZMod (p ^ b)) → ℝ := fun xy =>
      wooleyWeightedResidueMassSq gamma xy.1 *
        wooleyWeightedResidueMassSq gamma xy.2
    let f : (ZMod (p ^ bPrime) × ZMod (p ^ b)) → ℝ := fun xy =>
      wooleyPolynomialMixedResidueGridMoment
        phi (wooleyTriangular k) (k - r) p B b bPrime gamma xy.2 xy.1
    let g : (ZMod (p ^ bPrime) × ZMod (p ^ b)) → ℝ := fun xy =>
      wooleyPolynomialMixedResidueGridMoment
        phi (wooleyTriangular k) (r - 1) p B bPrime b gamma xy.1 xy.2
    let h : (ZMod (p ^ bPrime) × ZMod (p ^ b)) → ℝ := fun xy =>
      wooleyPolynomialMixedResidueGridMoment
        phi (wooleyTriangular k) r p B bPrime b gamma xy.1 xy.2
    let u : ℝ := 1 / ((k - r + 1 : ℕ) : ℝ)
    let c : ℝ := (wooleyWeightedMassSq gamma)⁻¹ ^ 2
    pm_61 hu0 u
    have hu1 : u ≤ 1 := by
      pm_2800
      have hdenPos : (0 : ℝ) < ((k - r + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le zero_lt_one hden
      pm_1447 div_le_iff₀ hdenPos one_mul hden
    have huv : 1 - u =
        ((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ) := by
      dsimp [u]
      exact wooley_section8_weight_complement hrk
    pm_8789 hmassPos wooleyWeightedMassSq gamma wooleyWeightedMassSq_nonneg hmass
    pm_64 hc c
    pm_5289 pairs
    pm_6821 hf' f
    pm_6821 hg g
    have hpoint : ∀ xy ∈ pairs,
        h xy ≤ f xy ^ u * g xy ^ (1 - u) := by
      intro xy hxy
      have hlocal := wooleyPolynomial_section8_local_holder
        (Q := Q) (p := p) (B := B) (k := k) (r := r)
        (bPrime := bPrime) (b := b)
        (phi := phi) (hr := hr) (hrk := hrk) (gamma := gamma)
        (xi := xy.1) (eta := xy.2)
      dsimp [h, f, g, u]
      rw [huv]
      exact hlocal
    have hmain := wooley_scaled_weighted_two_factor_holder_real
      pairs w f g h hw hf' hg hu0 hu1 hc hpoint
    have hH :
        (∑ xy ∈ pairs, w xy * h xy) =
          ∑ xi : ZMod (p ^ bPrime),
            ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
              wooleyWeightedResidueMassSq gamma xi *
                wooleyWeightedResidueMassSq gamma eta *
                  wooleyPolynomialMixedResidueGridMoment
                    phi (wooleyTriangular k) r p B bPrime b gamma xi eta := by
      simpa only [pairs, w, h] using
        wooley_sum_separatedResiduePairsAt
          (p := p) (nu := nu) (a := bPrime) (b := b)
          (fun xi eta =>
            wooleyWeightedResidueMassSq gamma xi *
              wooleyWeightedResidueMassSq gamma eta *
                wooleyPolynomialMixedResidueGridMoment
                  phi (wooleyTriangular k) r p B bPrime b gamma xi eta)
    have hG :
        (∑ xy ∈ pairs, w xy * g xy) =
          ∑ xi : ZMod (p ^ bPrime),
            ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
              wooleyWeightedResidueMassSq gamma xi *
                wooleyWeightedResidueMassSq gamma eta *
                  wooleyPolynomialMixedResidueGridMoment
                    phi (wooleyTriangular k) (r - 1) p B bPrime b gamma xi eta := by
      simpa only [pairs, w, g] using
        wooley_sum_separatedResiduePairsAt
          (p := p) (nu := nu) (a := bPrime) (b := b)
          (fun xi eta =>
            wooleyWeightedResidueMassSq gamma xi *
              wooleyWeightedResidueMassSq gamma eta *
                wooleyPolynomialMixedResidueGridMoment
                  phi (wooleyTriangular k) (r - 1) p B bPrime b gamma xi eta)
    have hF :
        (∑ xy ∈ pairs, w xy * f xy) =
          ∑ eta : ZMod (p ^ b),
            ∑ xi : ZMod (p ^ bPrime) with wooleyResiduesSeparated nu eta xi,
              wooleyWeightedResidueMassSq gamma eta *
                wooleyWeightedResidueMassSq gamma xi *
                  wooleyPolynomialMixedResidueGridMoment
                    phi (wooleyTriangular k) (k - r) p B b bPrime gamma eta xi := by
      calc
        (∑ xy ∈ pairs, w xy * f xy) =
            ∑ yx ∈ wooleySeparatedResiduePairsAt p nu b bPrime,
              wooleyWeightedResidueMassSq gamma yx.1 *
                wooleyWeightedResidueMassSq gamma yx.2 *
                  wooleyPolynomialMixedResidueGridMoment
                    phi (wooleyTriangular k) (k - r) p B b bPrime
                      gamma yx.1 yx.2 := by
          simpa only [pairs, w, f, mul_assoc, mul_comm, mul_left_comm] using
            wooley_sum_separatedResiduePairsAt_swap
              (p := p) (nu := nu) (a := bPrime) (b := b)
              (fun xi eta =>
                wooleyWeightedResidueMassSq gamma xi *
                  wooleyWeightedResidueMassSq gamma eta *
                    wooleyPolynomialMixedResidueGridMoment
                      phi (wooleyTriangular k) (k - r) p B b bPrime
                        gamma eta xi)
        _ = _ := wooley_sum_separatedResiduePairsAt
          (p := p) (nu := nu) (a := b) (b := bPrime)
          (fun eta xi =>
            wooleyWeightedResidueMassSq gamma eta *
              wooleyWeightedResidueMassSq gamma xi *
                wooleyPolynomialMixedResidueGridMoment
                  phi (wooleyTriangular k) (k - r) p B b bPrime gamma eta xi)
    rw [hH, hF, hG] at hmain
    rw [huv] at hmain
    simpa only [pairs, w, f, g, h, u, c] using hmain

/-- At `r = 0` the local mixed moment is independent of its first residue
class.  This is the exact simplification used in the endpoint case of
Lemma 8.1. -/
theorem wooleyPolynomialMixedResidueGridMoment_zero
    {Q p B k s a b : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : Fin Q → ℂ)
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) :
    wooleyPolynomialMixedResidueGridMoment
        phi s 0 p B a b gamma xi eta =
      (((p ^ B) ^ k : ℕ) : ℝ)⁻¹ *
        ∑ alpha : Fin k → ZMod (p ^ B),
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi (p ^ B) gamma alpha eta‖ ^ (2 * s) := by
  simp [wooleyPolynomialMixedResidueGridMoment, wooleyTriangular_zero]

/-- The literal definition with a separated-pair filter gives the estimate
`K^0_{a,b} ≤ U^{B,b}`.  This is the inequality actually required for
Wooley (8.2); it also records rather than hides the paper's harmless use of
an equality after dropping the separated-pair restriction. -/
theorem wooleyPolynomialMixedGridMean_zero_le_conditioned
    {Q p B k s a b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : Fin Q → ℂ) :
    wooleyPolynomialMixedGridMean phi s 0 p B a b nu gamma ≤
      wooleyPolynomialConditionedGridMean phi s (p ^ B) (p ^ b) gamma := by
  unfold wooleyPolynomialMixedGridMean wooleyPolynomialConditionedGridMean
  split_ifs with hmass
  · exact le_rfl
  · let L (eta : ZMod (p ^ b)) : ℝ :=
      (((p ^ B) ^ k : ℕ) : ℝ)⁻¹ *
        ∑ alpha : Fin k → ZMod (p ^ B),
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi (p ^ B) gamma alpha eta‖ ^ (2 * s)
    have hL (eta : ZMod (p ^ b)) : 0 ≤ L eta := by
      dsimp [L]
      positivity
    have hlocal (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) :
        wooleyPolynomialMixedResidueGridMoment
            phi s 0 p B a b gamma xi eta = L eta := by
      exact wooleyPolynomialMixedResidueGridMoment_zero phi gamma xi eta
    simp_rw [hlocal]
    have hrewrite :
        (∑ xi : ZMod (p ^ a),
          ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
            wooleyWeightedResidueMassSq gamma xi *
              wooleyWeightedResidueMassSq gamma eta * L eta) =
          ∑ eta : ZMod (p ^ b),
            (wooleyWeightedResidueMassSq gamma eta * L eta) *
              ∑ xi : ZMod (p ^ a) with
                wooleyResiduesSeparated nu eta xi,
                  wooleyWeightedResidueMassSq gamma xi := by
      simp_rw [Finset.sum_filter]
      pm_223 Finset.sum_comm eta heta Finset.mul_sum
      pm_2798
      by_cases hs : wooleyResiduesSeparated nu xi eta
      · rw [ite_eq_left hs, ite_eq_left (hsep.mp hs)]
        ring
      · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hsep.mpr h))]
        ring
    rw [hrewrite]
    have hxi (eta : ZMod (p ^ b)) :
        (∑ xi : ZMod (p ^ a) with wooleyResiduesSeparated nu eta xi,
          wooleyWeightedResidueMassSq gamma xi) ≤
            wooleyWeightedMassSq gamma := by
      calc
        (∑ xi : ZMod (p ^ a) with wooleyResiduesSeparated nu eta xi,
            wooleyWeightedResidueMassSq gamma xi) ≤
            ∑ xi : ZMod (p ^ a),
              wooleyWeightedResidueMassSq gamma xi := by
          exact Finset.sum_le_univ_sum_of_nonneg fun xi =>
            wooleyWeightedResidueMassSq_nonneg gamma xi
        _ = wooleyWeightedMassSq gamma :=
          wooley_sum_weightedResidueMassSq gamma
    have hsum :
        (∑ eta : ZMod (p ^ b),
          (wooleyWeightedResidueMassSq gamma eta * L eta) *
            ∑ xi : ZMod (p ^ a) with wooleyResiduesSeparated nu eta xi,
              wooleyWeightedResidueMassSq gamma xi) ≤
          wooleyWeightedMassSq gamma *
            ∑ eta : ZMod (p ^ b),
              wooleyWeightedResidueMassSq gamma eta * L eta := by
      calc
        _ ≤ ∑ eta : ZMod (p ^ b),
            (wooleyWeightedResidueMassSq gamma eta * L eta) *
              wooleyWeightedMassSq gamma := by
          apply Finset.sum_le_sum
          intro eta heta
          exact mul_le_mul_of_nonneg_left (hxi eta)
            (mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma eta) (hL eta))
        _ = _ := by
          pm_4886 eta heta
    pm_8789 hmassPos wooleyWeightedMassSq gamma wooleyWeightedMassSq_nonneg hmass
    have hscaled := mul_le_mul_of_nonneg_left hsum
      (sq_nonneg (wooleyWeightedMassSq gamma)⁻¹)
    calc
      (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
          ∑ eta : ZMod (p ^ b),
            (wooleyWeightedResidueMassSq gamma eta * L eta) *
              ∑ xi : ZMod (p ^ a) with wooleyResiduesSeparated nu eta xi,
                wooleyWeightedResidueMassSq gamma xi ≤
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (wooleyWeightedMassSq gamma *
              ∑ eta : ZMod (p ^ b),
                wooleyWeightedResidueMassSq gamma eta * L eta) := hscaled
      _ = (wooleyWeightedMassSq gamma)⁻¹ *
          ∑ eta : ZMod (p ^ b),
            wooleyWeightedResidueMassSq gamma eta * L eta := by
        field_simp [ne_of_gt hmassPos]
      _ = _ := by rfl

end

end GafniTao
