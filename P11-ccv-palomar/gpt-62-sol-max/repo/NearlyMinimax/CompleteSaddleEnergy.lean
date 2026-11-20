module

public import NearlyMinimax.CompleteSaddleGeometry
public import NearlyMinimax.CompleteSaddleEnergyGuards
public import NearlyMinimax.CompleteGeometryEnergyAssembly
public import NearlyMinimax.LowerRawCostReduction


@[expose] public section

/-! Actual full-count geometry energy at the canonical rounded saddle.
The constants are numerical model data and precede the saddle shift. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

 def completeSaddleScoreFactor {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  highFixedScoreDenominator C.densityLower Q.c*(2 : ℝ)^d
 def completeSaddleDegreeFactor (d : ℕ) : ℝ := ((d : ℝ)+8)/4+1
 def completeSaddleOrdinaryConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  ordinaryFineAliasFactorialConstant C.smoothness d (lowerSaddleResponseOrder C.smoothness d)
    C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleScoreFactor C Q)
 def completeSaddleDefectConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryDefectConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleScoreFactor C Q)
 def completeSaddleFieldConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryFieldConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleScoreFactor C Q)
 def completeSaddleAliasConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryAliasConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleDegreeFactor d) (completeSaddleScoreFactor C Q) (completeSaddleOrdinaryConstant C Q Cfr)
 def completeSaddleExteriorConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  completeGeometryExteriorConstant d (completeSaddleScoreFactor C Q)
    (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)

 def completeSaddleEnergyBudget {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (Cfr cf Cω : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleRawEnergyBound C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf (completeSaddleDefectConstant C Q Cfr)
    (completeSaddleAliasConstant C Q Cfr) (completeSaddleFieldConstant C Q Cfr) (completeSaddleExteriorConstant C Q)
    (completeSourceSaddleActivity C (lowerSaddleResponseOrder C.smoothness d) Cfr (spatialInterpolationLambda d) Cω n)
    (shrunkDensityExponent C.densityLower C.densityUpper) n

 section
variable {d : ℕ}

section
variable (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)

theorem completeSaddleScoreFactor_pos :
    0 < completeSaddleScoreFactor C Q := by
  unfold completeSaddleScoreFactor highFixedScoreDenominator
  positivity [C.densityLower_pos, Q.c_pos]
 section
variable (Cfr : ℝ)

theorem completeSaddleDefectConstant_pos :
    0 < completeSaddleDefectConstant C Q Cfr := by apply completeGeometryDefectConstant_pos
 theorem completeSaddleAliasConstant_pos :
    0 < completeSaddleAliasConstant C Q Cfr := by apply completeGeometryAliasConstant_pos
 theorem completeSaddleFieldConstant_pos :
    0 < completeSaddleFieldConstant C Q Cfr := by apply completeGeometryFieldConstant_pos

end
 theorem completeSaddleExteriorConstant_pos :
    0 < completeSaddleExteriorConstant C Q := completeGeometryExteriorConstant_pos _ _ _

 theorem completeSaddleEnergyBudget_nonneg
    (Cfr cf Cω : ℝ) (n : ℕ) : 0 ≤ completeSaddleEnergyBudget C Q Cfr cf Cω n := by
  unfold completeSaddleEnergyBudget lowerSaddleRawEnergyBound
  have h5 := (completeSaddleDefectConstant_pos C Q Cfr).le
  have h6 := (completeSaddleAliasConstant_pos C Q Cfr).le
  have h7 := (completeSaddleFieldConstant_pos C Q Cfr).le
  have hch := (completeSaddleExteriorConstant_pos C Q).le
  have hN := lowerSaddleN_positive C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) n
  have hmu : 0 ≤ lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n := by
    unfold lowerSaddleMu
    positivity [lowerSaddleH_positive d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n]
  positivity

end

 theorem eventually_completeSaddleGeometry_factorial [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (hs : 1 < C.smoothness)
    (hd : 4*C.smoothness < (d : ℝ)) {cf : ℝ} (hcf : 0 < cf) (Cfr Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.range (n+1), poissonCountWeight
        (completeSaddleScoreFactor C Q*completeSaddleMu C Cω n) r *
        ∫ U, completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U ∂fullSpatialPatchDesign d r) ≤
          completeSaddleEnergyBudget C Q Cfr cf Cω n := by
  have hCs := (completeSaddleScoreFactor_pos C Q).le
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by simp_all
    omega
  have hbd := (zero_lt_one.trans C.one_lt_densityUpper).le
  have hOrdConst : 0 ≤ completeSaddleOrdinaryConstant C Q Cfr :=
    zero_le_one.trans (ordinaryFineAliasFactorialConstant_ge_one hbd hCs)
  have hCal : 0 ≤ finePairSaddleAliasFactorialConstant d (lowerSaddleResponseOrder C.smoothness d)
      C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C) (completeSaddleDegreeFactor d)
        (3*completeSaddleScoreFactor C Q) := by
    unfold finePairSaddleAliasFactorialConstant aliasTailConstant
    have hP := finePairUniformSpatialPrefactor_nonneg d (lowerSaddleResponseOrder C.smoothness d)
      C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C)
    have hI := spatialInverseFourConstant_nonneg d
    have hB := finePairAliasGeometricBase_nonneg d C.densityUpper
    positivity
  filter_upwards [eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
      hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω cf
      (lowerSaddleResponseOrder C.smoothness d) Cfr Q.a Q.ρ (completeSaddleScoreFactor C Q) hCs)] with n G hO
  let S := completeSaddleGeometryParameters C Q Cfr cf Cω n
  let M := S.M
  let D := S.D
  let q := S.q
  let N := S.N
  let mu := S.mu
  let ell := S.ell
  let eta := S.eta
  let tau := completeSaddleTau C n
  let c0 := S.c0
  let Cs := completeSaddleScoreFactor C Q
  let K := completeSaddleDegreeFactor d
  let R := S.R
  let Cord := completeSaddleOrdinaryConstant C Q Cfr
  let Bl := completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hD := G.degree_min
  have had : S.ad = completeSaddleAD C n := by
    simp only [S, completeSaddleGeometryParameters, SourceGeometry.ad, completeSaddleAD, one_div]
  have hbd_eq : S.bd = completeSaddleBD C n := by
    simp only [S, completeSaddleGeometryParameters, SourceGeometry.bd, completeSaddleBD, one_div]
  have hext : S.tau = tau := by
    rw [SourceGeometry.tau, had, hbd_eq]
    have h := exteriorTau_sqrt_ratio (completeSaddleAD C n) (completeSaddleBD C n) G.ad_positive G.density_interval
    simpa only [tau,completeSaddleTau,shrunkDensityExponent,densityIntervalExponent,
      completeSaddleAD,completeSaddleBD,one_div] using h
  have hfield : Real.exp (2*S.tau*M)*(ell^(2-(d : ℝ)))^2*mu^4 ≤ mu^2*N^(-(d : ℝ)) := by
    rw [hext]
    convert G.field_scale_square using 1 <;>
      dsimp only [M,ell,mu,N,S,completeSaddleGeometryParameters] <;> ring
  have hOrd : (∑ j ∈ Finset.range (D-M), poissonCountWeight (Cs*mu) (M+1+j) *
      ∫ U, S.ordinary U ∂fullSpatialPatchDesign d (M+1+j)) ≤
      Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) := by
    simpa only [ordinaryFineAliasSaddleGeometryEnvelope,ordinaryFineAliasSaddleCoefficient,ordinaryFineAliasSaddleTheta,
      M,D,q,N,mu,ell,eta,tau,c0,Cs,R,Cord,S,completeSaddleGeometryParameters,SourceGeometry.ordinary,completeSaddleOrdinaryConstant,
      highCompleteSourceSaddleCoefficient,highCompleteSourceSaddleTheta,completeSaddleM,completeSaddleD,
      completeSaddleN,completeSaddleMu,completeSaddleEll,completeSaddleEta,completeSaddleTau,completeSaddleC0] using hO (fun _ => D)
  have hHigher := S.higherEnvelope_factorial_le hd5 hD K Cs _ C.densityLower_pos Q.a_pos
    (by rw [had, hbd_eq]; exact G.density_interval) (hext.trans_le G.tau_le)
    (by dsimp [S,completeSaddleGeometryParameters,completeSaddleC0]; linarith [densityIntervalExponent_pos C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)])
    (by dsimp [K,completeSaddleDegreeFactor]; positivity) hCs G.ell_one G.ell_lt_N.le rfl G.degree_multiple
    G.mu_positive G.mu_one G.mu_log G.response_taylor hfield hOrd
  have h := S.envelope_factorial_from_higher (NeZero.pos d) n hD K Chi Bl Cs Cord tau
    (lt_of_lt_of_le zero_lt_one G.N_one) hCs G.mu_positive.le G.mu_one
    (hbd_eq.symm ▸ G.bd_nonneg) (sub_le_self _ (by positivity))
    hOrdConst hCal G.tau_nonneg hHigher
  convert h using 1 <;> (try dsimp only [completeSaddleGeometryEnvelope,completeSaddleEnergyBudget,
    completeSaddleDefectConstant,completeSaddleAliasConstant,completeSaddleFieldConstant,completeSaddleExteriorConstant,
    lowerSaddleRawEnergyBound,M,D,q,N,mu,ell,eta,tau,c0,Cs,K,R,Cord,Bl,Chi,S,completeSaddleGeometryParameters,
    completeSaddleM,completeSaddleD,completeSaddleN,completeSaddleMu,completeSaddleEll,
    completeSaddleEta,completeSaddleTau,completeSaddleC0]) <;> (try simp only [poissonCountWeight]) <;> ring

end

end NearlyMinimax
