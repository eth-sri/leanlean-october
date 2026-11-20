module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.HighUnionFisher
public import NearlyMinimax.HighSourceCanonicalResponse

@[expose] public section

/-! The local guards for a complete source are fixed once. They apply to
all sample counts, both for exact cancellation and for the large-count cap. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

structure HighFrameOriginalLocalGuards (d k D : ℕ) [NeZero k] (Cfr eta rho : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) : Prop where
  amplitude_nonneg : 0 ≤ eta
  amplitude_half : eta ≤ rho/2
  coefficient_ball : ∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹
  weight_abs : ∀ j x, |highPeriodicTensor d k j x| ≤ 1
  without_abs : ∀ j x, |highLocalFieldWithout d k D eta c j x| ≤ rho/2
  profile_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |∑ γ, highLocalFrameFeature k j x γ*v γ| ≤ 1
  regression_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |highLocalFieldWithout d k D eta c j x + eta*highPeriodicTensor d k j x*
      (∑ γ, highLocalFrameFeature k j x γ*v γ)| ≤ rho

private theorem highFrame_original_local_guards {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ Cfr cf : ℝ,
      Cfr0 ≤ Cfr → 0 ≤ cf → cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      ∀ c : HighWindowLabels d k → HighFrameIndex d D → ℝ,
      (∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹) →
      HighFrameOriginalLocalGuards d k D Cfr (cf*(k : ℝ)^(-C.smoothness)) Q.ρ c := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let eta0 := Q.ρ/(2*((2 : ℝ)^d+1))
  refine ⟨Cfr0,eta0,hfr0,div_pos Q.ρ_pos (by positivity),?_⟩
  intro k D hk0 hk Cfr cf hfr hcf heta c hc
  letI := hk0
  let eta := cf*(k : ℝ)^(-C.smoothness)
  have hfr1 := hfr0.trans hfr
  have hen : 0 ≤ eta := by positivity
  have hamp : ((2 : ℝ)^d+1)*eta ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*((2 : ℝ)^d+1))).mp heta
    change eta*(2*((2 : ℝ)^d+1)) ≤ Q.ρ at ht
    nlinarith
  have hehalf : eta ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (j) : frameCoefficientL1 (highFramePolynomial (c j)) ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (hc j).trans ((inv_le_inv₀ (by linarith : 0 < Cfr) (by linarith : 0 < Cfr0)).mpr hfr)
  have hF := (hfield k hk0 hk cf hcf (fun j => highFramePolynomial (c j)) hP).1
  have hw (j) (x) : |highPeriodicTensor d k j x| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j x)]
    exact highPeriodicTensor_le_one d k (by omega) j x
  have hprof (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |∑ γ, highLocalFrameFeature k j x γ*v γ| ≤ 1 :=
    highLocalFrameFeature_ball_abs_le_one k j x Cfr hfr1 v hv
  have hterm (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |eta*highPeriodicTensor d k j x*(∑ γ, highLocalFrameFeature k j x γ*v γ)| ≤ eta := by
    rw [abs_mul,abs_mul,abs_of_nonneg hen]
    have ht := mul_le_mul (hw j x) (hprof j v hv x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left ht hen]
  have hg (j) (x) : |highLocalFieldWithout d k D eta c j x| ≤ Q.ρ/2 := by
    have hd := highFrameField_local_decomposition d k D hk eta c j x
    have he : highLocalFieldWithout d k D eta c j x =
        highFrameField d k eta (fun l => highFramePolynomial (c l)) x -
          eta*highPeriodicTensor d k j x*(∑ γ, highLocalFrameFeature k j x γ*c j γ) := by
      linarith [hd]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hF x) (hterm j (c j) (hc j) x)).trans
      (by linarith))
  refine ⟨hen,hehalf,hc,hw,hg,hprof,?_⟩
  intro j v hv x
  exact (abs_add_le _ _).trans (by linarith only [hg j x,hterm j v hv x,hehalf])

section
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  {C : ModelConstants d} {Q : LowSmoothnessTernaryConstants C} {Cfr ell N mu eta V : ℝ}
  (hD : 3 ≤ D) (hq : 1 ≤ q) (hell : 0 < ell) (hellN : ell < N)

local notation "lam" => spatialInterpolationLambda d
local notation "rows" => completeSourceRows C k D M q Cfr lam ell N mu
local notation "ad" => C.densityLower + 1/(M : ℝ)
local notation "bd" => C.densityUpper - 1/(M : ℝ)
local notation "Chi" => highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1

variable (G : HighUnionSourceGuards C (M : ℝ) Cfr
    (completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu))
  (h : HighCompleteSourceHistory C k D M q Cfr (spatialInterpolationLambda d) ell N mu)

local notation "coeff" => Prod.snd (highUnionSourceState C rows h)

variable (H : HighFrameOriginalLocalGuards d k D Cfr eta Q.ρ
    (highUnionSourceState C (completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu) h).2)
  (hV : |V-Q.v| ≤ Q.ρ) (j : HighWindowLabels d k)
  {n : ℕ} (x : Fin n → Covariate d)

local notation "chart" => highPatchProductChart d k j x
local notation "p" => (fun i => highUnionSourceDensity C rows h (x i))
local notation "g" => (fun i => highLocalFieldWithout d k D eta coeff j (x i))
local notation "w" => (fun i => highPeriodicTensor d k j (x i))
local notation "raw" => highUnionSourceRawNumerator C rows n Q.a V eta h j
local notation "signedRaw" => completeSourceRawNumerator ad bd lam ell N mu D M q Cfr Q.a V eta chart p g w (coeff j)

private theorem chart_bound (i : Fin n) (r : Fin d) : |chart i r| ≤ 2 :=
  (highLocalCoordinates_abs_le_one d k j (x i) r).trans (by norm_num)

include G in
private theorem density_interval (i : Fin n) : p i ∈ Icc ad bd :=
  highUnionSourceDensity_interval C rows G h (x i)

include hV in
private theorem mass_nonneg (f : ℝ) (hf : |f| ≤ Q.ρ) (b : Fin 3) : 0 ≤ ternaryMass Q.a f V b :=
  Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 b)

include hD hq hell hellN G H hV in
private theorem raw_eq_canonical (hx : ∀ i, x i ∈ highTorusPatch d k j) (y : Fin n → Fin 3) :
    raw x y = signedRaw y :=
  completeSourceRawNumerator_eq_canonical C hD hq G.resolution Cfr lam ell N mu
    G.frame hell hellN j h x hx Q.a V eta Q.a_pos.ne' g w
    (fun v hv i => mass_nonneg hV _ (H.regression_abs j v hv (x i))) y

include hD hq hell hellN G H hV in
private theorem raw_large_count (hn : 1 ≤ n) :
    selectedRawSquareEnergy raw x ≤ (3*Chi^2)^n*eta^4*(highRowTotalMass (rows).rowMass+1)^2 := by
  apply crude_raw_square_energy_pointwise Chi eta (highRowTotalMass (rows).rowMass)
  intro y
  exact completeSourceNumerator_all_count_exponential_bound C hD hq G.resolution Cfr lam ell N mu
    G.frame hell hellN hn j h Q.a V eta Q.ρ x g w (fun i => highLocalFrameFeature k j (x i))
    ⟨zero_lt_one.trans_le G.frame, Q.a_pos, H.amplitude_nonneg, H.amplitude_half,
      (fun i => H.without_abs j (x i)), (fun i => H.weight_abs j (x i)),
      (fun v hv i => H.profile_abs j v hv (x i)), mass_nonneg hV⟩ y

end

theorem completeSource_original_all_geometry {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 1 ≤ ell → ell < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 →
      (∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu) →
      (∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ ordinaryFineAliasTargetSet d D ell N mu, 1 ≤ r ∧ r ≤ Rbound) →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HighCompleteSourceHistory C k D M q Cfr (spatialInterpolationLambda d) ell N mu,
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let eta := cf*(k : ℝ)^(-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        (⟨D, M, Rbound, q, C.densityLower, C.densityUpper, c0, ell, N, mu, Cfr, Q.a, Q.ρ, eta⟩ : SourceGeometry d).envelope
          Chi (highRowTotalMass R.rowMass) n (highPatchProductChart d k j x) := by
  obtain ⟨C0,e0,hC0,he0,hguards⟩ := highFrame_original_local_guards C Q
  refine ⟨C0,e0,hC0,he0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n x hx
  letI := hk0
  letI := horder
  let lam := spatialInterpolationLambda d
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hellp := zero_lt_one.trans_le hell
  have hq1 : 1 ≤ q := by omega
  have G := (completeSourceRows_guards C k D M q hD hq1 hM Cfr lam ell N mu (hC0.trans hfr) hellp hellN).1
  have H := hguards k D hk0 hk Cfr cf hfr hcf heta c (highUnionSourceState_coefficient_ball C R G h)
  let S : SourceGeometry d := ⟨D, M, Rbound, q, C.densityLower, C.densityUpper, c0, ell, N, mu, Cfr, Q.a, Q.ρ, eta⟩
  change selectedRawSquareEnergy _ x ≤ S.envelope Chi _ n _
  by_cases hnD : n ≤ D
  swap
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 3 := ⟨n-3, by omega⟩
    simpa only [SourceGeometry.envelope, S, ite_eq_right hnD] using
      raw_large_count hD hq1 hellp hellN G h H hV j x (by omega)
  let U := highPatchProductChart d k j x
  let p := fun i => highUnionSourceDensity C R h (x i)
  let g := fun i => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i => highPeriodicTensor d k j (x i)
  let ad := C.densityLower + (M : ℝ)⁻¹
  let bd := C.densityUpper - (M : ℝ)⁻¹
  have hU := chart_bound j x
  have hp : ∀ i, p i ∈ Icc ad bd := by simpa only [one_div] using density_interval G h x
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C _ hM
  simp only [one_div] at ha hab
  have hCfr : Cfr ≠ 0 := by linarith [G.frame]
  have hraw (y : Fin n → Fin 3) : highUnionSourceRawNumerator C R n Q.a V eta h j x y =
      completeSourceRawNumerator ad bd lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y := by
    simpa only [one_div] using raw_eq_canonical hD hq1 hellp hellN G h H hV j x hx y
  change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤ _
  calc
    _ = ∑ y : Fin n → Fin 3, completeSourceRawNumerator ad bd lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y ^ 2 :=
      Finset.sum_congr (by ext y; simp) (fun y _ => congrArg (· ^ 2) (hraw y))
    _ ≤ _ := ?_
  rcases n with _|_|_|n
  · simp_rw [completeSourceRawNumerator_count_zero ad bd lam ell N mu ha hab D M q (by omega)
      Cfr Q.a V eta U p g w (c j)]
    simp [SourceGeometry.envelope]
  · simp_rw [completeSourceRawNumerator_count_one ad bd lam ell N mu ha hab D M q (by omega)
      hq1 Cfr Q.a V eta hCfr U hU p g w hp (c j)]
    simp [SourceGeometry.envelope]
  · have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C _ hM).1
    have hQ (i : Fin 2) : U i ∈ hyperplaneCube d := highLocalCoordinates_abs_le_one d k j (x i)
    simp_rw [completeSourceRawNumerator_count_two ad bd lam ell N mu ha hab D M q hD Cfr Q.a V eta U hU p g w hp (c j)]
    exact finePairCountTwoRawNumerator_sum_square_le_geometry hD ad bd ell N ha hab hellp.le hellN.le D M q
      (by omega) hM2 hq Cfr Q.a V eta Q.ρ hCfr Q.a_pos Q.ρ_pos.le U hQ p g w hp
      (fun i => H.weight_abs j (x i)) (c j) (fun i => H.regression_abs j (c j) (H.coefficient_ball j) (x i))
  · simp only [SourceGeometry.envelope, S, ite_eq_left hnD]
    exact completeSourceRawNumerator_higher_square_le_geometry S C.densityLower_pos hell
      hab htau (by omega) hnD hq1 hnu hFine hI V G.frame Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half U hU p g w hp
      (fun i => H.without_abs j (x i)) (fun i => H.weight_abs j (x i)) (c j) (H.coefficient_ball j) (mass_nonneg hV)

end NearlyMinimax
