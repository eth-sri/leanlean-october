module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.LowerAliasScale
public import NearlyMinimax.HigherBandActivityConversion

@[expose] public section

/-! Full-product spatial energy for the actual all-count ordinary fine-band
alias expression. All bounds are uniform in the tuple-dependent nuisance
values; the spatial kernel is the constructed cardinal band. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {d n F M r R : ℕ}

/-- The exact raw target-r ordinary fine-band expression produced by the
finite density selector and finite response matrix action. -/
def ordinaryFineAliasRawAction (ad bd lam L T : ℝ) (M r q : ℕ)
    (C a V η : ℝ) (U : DesignSample d n) (p g w : Fin n → ℝ)
    (c : HighFrameVector d F) (y : TernaryVector n) : ℝ :=
  densityCountCoefficient ad bd M r n *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (∏ i ∈ S, p i) * responseMatrixAction q C
        (globalCardinalBandMatrix lam L T (spatialSubsetConfiguration S U)) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)

/-- Genuine uniform selector-product bound at every count. -/
theorem ordinary_count_product_abs_bound {ad bd : ℝ}
    (ha : 0 < ad) (hab : ad < bd) (M r : ℕ) (hr : 1 ≤ r)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    {S : Finset (Fin n)} (hS : S.card = r) :
    |densityCountCoefficient ad bd M r n * (∏ i ∈ S, p i)| ≤
      bd^n * (ordinaryDensityActivityBase ad bd)^r *
        Real.exp ((M : ℝ) * intervalExteriorTau ad bd) := by
  have hbd  := ha.trans hab
  have hcard : r ≤ n := by simpa only [hS, Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S
  have hm  := abs_pos.mpr (densityMargin_zero_ne ad bd ha hab)
  have hτ : 0 ≤ intervalExteriorTau ad bd := by
    rw [exteriorTau_sqrt_ratio ha hab]
    exact (densityIntervalExponent_pos ha hab).le
  have hprod : |∏ i ∈ S, p i| ≤ bd^r := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i ∈ S, bd := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
        grind)
      _ = _ := by rw [Finset.prod_const, hS]
  have hcoeff := densityCountCoefficient_abs_bound ad bd ha hab M r n hr
  have hcosh : Real.cosh ((M+r : ℕ)*intervalExteriorTau ad bd) ≤
      Real.exp ((M+r : ℕ)*intervalExteriorTau ad bd) := by
    rw [Real.cosh_eq]
    have he := Real.exp_le_exp.mpr (show -((M+r : ℕ)*intervalExteriorTau ad bd) ≤
      ((M+r : ℕ)*intervalExteriorTau ad bd) by
        have hh := mul_nonneg (Nat.cast_nonneg (M+r)) hτ
        linarith)
    linarith
  have hj : (bd-ad)/4 ≤ bd := by linarith
  have he : Real.exp (intervalExteriorTau ad bd) ≤
      Real.exp (1+intervalExteriorTau ad bd) := Real.exp_le_exp.mpr (by linarith)
  have hb : (bd-ad)/4/|densityMargin ad bd 0| * Real.exp (intervalExteriorTau ad bd) ≤
      ordinaryDensityActivityBase ad bd := by
    unfold ordinaryDensityActivityBase
    rw [abs_div, abs_of_pos hbd]
    exact (mul_le_mul (div_le_div_of_nonneg_right hj hm.le) he
      (Real.exp_pos _).le (div_nonneg hbd.le hm.le)).trans_eq (by ring)
  have h1 := mul_le_mul hcoeff hprod (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left hcosh
    (show 0 ≤ (bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r by positivity)
  have hid : ((bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r)*
      Real.exp ((M+r : ℕ)*intervalExteriorTau ad bd) =
      bd^n * (((bd-ad)/4/|densityMargin ad bd 0|)*Real.exp (intervalExteriorTau ad bd))^r *
        Real.exp ((M : ℝ)*intervalExteriorTau ad bd) := by
    have heq : Real.exp ((M+r : ℕ)*intervalExteriorTau ad bd) =
        Real.exp ((M : ℝ)*intervalExteriorTau ad bd) *
          (Real.exp (intervalExteriorTau ad bd))^r := by
      rw [Nat.cast_add, add_mul, Real.exp_add]
      simpa using Real.exp_nat_mul (intervalExteriorTau ad bd) r
    rw [heq]
    generalize (bd-ad)/4 = J
    generalize |densityMargin ad bd 0| = H
    generalize Real.exp (intervalExteriorTau ad bd) = X
    generalize Real.exp ((M : ℝ)*intervalExteriorTau ad bd) = Y
    rw [mul_pow, div_pow]
    have hpw : bd^(n-r)*bd^r = bd^n := by rw [← pow_add, Nat.sub_add_cancel hcard]
    grind
  have h3 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb r) (pow_nonneg hbd.le n))
    (Real.exp_pos ((M : ℝ)*intervalExteriorTau ad bd)).le
  grind

/-- Fixed constants bound every actual shrinking interval and every bounded
fine target, before the exterior degree or sample size is chosen. -/
theorem ordinary_count_product_shrunk_abs_bound
    {ad bd c0 : ℝ} (ha : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    {S : Finset (Fin n)} (hS : S.card = r) :
    |densityCountCoefficient (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) M r n * (∏ i ∈ S, p i)| ≤
      (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
        Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hab : ad < bd := by linarith
  have hap : 0 < ad+(M : ℝ)⁻¹ := by linarith
  have hbp  := hap.trans hshrink
  have he : intervalExteriorTau (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) = shrunkDensityExponent ad bd M := by
    rw [exteriorTau_sqrt_ratio hap hshrink]
    rfl
  have hb := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have hbn : (bd-(M : ℝ)⁻¹)^n ≤ (1+bd)^n :=
    pow_le_pow_left₀ hbp.le (by linarith) n
  have hBr : (ordinaryDensityActivityBase (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))^r ≤
      (1+uniformOrdinaryDensityActivityBase ad bd c0)^R := by
    have hbase : 0 ≤ ordinaryDensityActivityBase (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) := by
      unfold ordinaryDensityActivityBase
      positivity
    exact (pow_le_pow_left₀ hbase (hb.trans (by linarith)) r).trans
      (pow_le_pow_right₀ (by linarith) hrR)
  have h := ordinary_count_product_abs_bound
    hap hshrink M r hr hp hS
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hbn hBr
      (pow_nonneg (by unfold ordinaryDensityActivityBase; positivity) r)
      (pow_nonneg (by linarith) n)) (Real.exp_pos _).le)

def ordinaryAliasResponseConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  (2*C^2) * responseVariation q * highSeparatedDerivativeBudget a ρ

/-- Uniform pointwise all-count response and selector control. The primitive
nuisance guards hold at this tuple; no norm bound is supplied as a premise. -/
theorem ordinaryFineAliasRawAction_abs_bound_of_chart
    (ad bd c0 lam L T : ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) {C a V η ρ : ℝ} (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    {U : DesignSample d n} (hU : ∀ i l, |U i l| ≤ 2)
    {p g w : Fin n → ℝ}
    (hpD : ∀ i, p i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    {c : HighFrameVector d F} (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : TernaryVector n) :
    let scale := (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R
    |ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) lam L T M r q C a V η U p g w c y| ≤
      (scale *
        Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          spatialMatrixL1 (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U)) := by
  intro scale
  unfold ordinaryFineAliasRawAction
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, S.card = r :=
    fun S hS => (Finset.mem_powersetCard.mp hS).2
  have hterm (S) (hmem : S ∈ Finset.univ.powersetCard r) :=
    ordinary_count_product_shrunk_abs_bound haD hshrink htau hr hrR hpD (hS S hmem)
  have hresponse (S : Finset (Fin n)) := high_response_matrix_all_count_bound q hn
    (lt_of_lt_of_le zero_lt_one hC) ha hη hρ hηρ
    (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U)) y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one hC (hU i) hv) hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hmem
  have hh := mul_le_mul (hterm S hmem) (hresponse S) (abs_nonneg _)
    (show 0 ≤ scale *
      Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M) by
        grind)
  simpa only [abs_mul, mul_assoc] using hh.trans_eq (by
    unfold ordinaryAliasResponseConstant highSeparatedDerivativeBudget spatialMatrixL1
    ring)

/-- Exact subset lifting of the constructed fine-band matrix envelope. -/
theorem ordinaryFineAliasKernel_sum_square_integrable_and_le
    (hd : 5 ≤ d) (hr : 2 ≤ r) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U : DesignSample d n =>
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U)))^2) (fullSpatialPatchDesign d n) ∧
    (∫ U : DesignSample d n,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U)))^2 ∂fullSpatialPatchDesign d n) ≤
      (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r L) := by
  let f := fun (S : Finset (Fin n)) (V : Fin S.card → Covariate d) =>
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T V)
  have hf (S : Finset (Fin n)) : Measurable (f S) := by
    exact Finset.measurable_sum _ (fun γ _ => Finset.measurable_sum _
      (fun δ _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT γ δ).measurable.abs))
  have hs (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r)  :=
    (Finset.mem_powersetCard.mp hS).2
  have hi (S) (hS : S ∈ Finset.univ.powersetCard r) :
      Integrable (fun V => f S V^2) (fullSpatialPatchDesign d S.card) :=
    globalCardinalBandMatrix_square_integrable hd (by rw [hs S hS]; exact hr) hL hT hLT
  constructor
  · exact finite_sum_square_integrable (fullSpatialPatchDesign d n)
      (Finset.univ.powersetCard r)
      (fun S U => f S (spatialSubsetConfiguration S U))
      (fun S _ => (hf S).comp (spatialSubsetConfiguration_measurable S))
      (fun S hS => spatial_subset_square_integrable_enumerated (hi S hS))
  · exact spatial_subset_sum_square_integral_le _ (fun S _ => hf S) hi
      (fun S hS => by
        have h := globalCardinalBandMatrix_square_integral_le (D := F) hd
          (show 2 ≤ S.card by rw [hs S hS]; exact hr) hL hT hLT
        grind)

def ordinaryFineAliasSpatialBudget (d n M r R q : ℕ) (ad bd c0 C a ρ η L : ℝ) : ℝ :=
  (((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
      Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
    (ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2))^2 *
      ((n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r L))

/-- The exact binomial, response-polynomial and unused-coordinate factors
are absorbed into one fixed exponential base. -/
theorem ordinary_alias_count_factors_le {bd : ℝ} (hbd : 0 ≤ bd) :
    ((1+bd)^n)^2 * (n : ℝ)^4 * (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) ≤
      (64*(2 : ℝ)^d*(1+bd)^2)^n := by
  have hn : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hc : (n.choose r : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast Nat.choose_le_two_pow n r
  have hn4 : (n : ℝ)^4 ≤ 16^n := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
    convert h using 1 <;> rw [← pow_mul, Nat.mul_comm n 4, pow_mul] <;> norm_num
  have hc2 : (n.choose r : ℝ)^2 ≤ (4 : ℝ)^n := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
    convert h using 1 <;> rw [← pow_mul, Nat.mul_comm n 2, pow_mul] <;> norm_num
  have hv : (2 : ℝ)^(d*(n-r)) ≤ ((2 : ℝ)^d)^n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by bound)
  have h := mul_le_mul (mul_le_mul (mul_le_mul (le_refl (((1+bd)^n)^2)) hn4
      (by positivity) (by positivity)) hc2 (by positivity) (by positivity)) hv (by positivity) (by positivity)
  apply h.trans_eq
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  ring

end

section
variable (d q R : ℕ) (ad bd c0 C a ρ : ℝ)

def ordinaryAliasSpatialPrefactor : ℝ :=
  ((1+uniformOrdinaryDensityActivityBase ad bd c0)^R)^2 *
    (ordinaryAliasResponseConstant q C a ρ)^2 * lowerAliasSpatialA d R

def ordinaryAliasSpatialCountBase : ℝ :=
  64*(2 : ℝ)^d*(1+bd)^2

def ordinaryAliasSpatialResponseBase : ℝ :=
  3*ordinaryAliasSpatialCountBase d bd

theorem ordinaryAliasSpatialPrefactor_nonneg :
    0 ≤ ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (lowerAliasSpatialA_nonneg d R)

end

/-- Genuine cardinal-band integration and elementary count factors give the
source alias scale, with constants fixed before M,n or nuisance values. -/
theorem ordinaryFineAliasSpatialBudget_source_scale_le {d n M r R : ℕ}
    (hd : 5 ≤ d) (hrR : r ≤ R) {ad bd c0 C a ρ η D K N : ℝ}
    (hbd : 0 ≤ bd) (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0)
    (hDK : D ≤ K*M) (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (q : ℕ) :
    ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N*Real.exp (-c0*D)) ≤
      ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ *
        η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n := by
  have hkernel := cardinalBandSquareBudget_cutoff_le (by omega : 4 ≤ d) hrR
    (Nat.cast_nonneg M) hD hK hc0 hDK hN hell hH
  have hcount := ordinary_alias_count_factors_le (d := d) (n := n) (r := r) hbd
  let P := ((1+uniformOrdinaryDensityActivityBase ad bd c0)^R)^2 *
    (ordinaryAliasResponseConstant q C a ρ)^2 * η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M)
  have hP : 0 ≤ P := by positivity
  have he : (Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M))^2 =
      Real.exp (2*shrunkDensityExponent ad bd M*M) := by
    rw [← Real.exp_nat_mul]
    ring
  have hid : ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N*Real.exp (-c0*D)) =
      P * (((1+bd)^n)^2 * (n : ℝ)^4 * (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r))) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r (N*Real.exp (-c0*D))) := by
    unfold ordinaryFineAliasSpatialBudget P
    grind
  rw [hid]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hcount hP) hkernel (by
      unfold cardinalBandSquareBudget
      have := cardinalBandDimensionConstant_nonneg d
      bound) (by positivity)
  exact hh.trans_eq (by unfold P ordinaryAliasSpatialPrefactor ordinaryAliasSpatialCountBase; ring)

end NearlyMinimax
