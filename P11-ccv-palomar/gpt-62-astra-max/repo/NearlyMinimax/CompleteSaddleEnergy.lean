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

 variable {d : ℕ} {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ)

def completeSaddleScoreFactor : ℝ :=
  highFixedScoreDenominator C.densityLower Q.c*(2 : ℝ)^d
 def completeSaddleDegreeFactor (d : ℕ) : ℝ := ((d : ℝ)+8)/4+1
 def completeSaddleOrdinaryConstant : ℝ :=
  ordinaryFineAliasFactorialConstant C.smoothness d (lowerSaddleResponseOrder C.smoothness d)
    C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleScoreFactor Q)
 def completeSaddleDefectConstant : ℝ :=
  completeGeometryDefectConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleScoreFactor Q)
 def completeSaddleFieldConstant : ℝ :=
  completeGeometryFieldConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleScoreFactor Q)
 def completeSaddleAliasConstant : ℝ :=
  completeGeometryAliasConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleDegreeFactor d) (completeSaddleScoreFactor Q) (completeSaddleOrdinaryConstant Q Cfr)
 def completeSaddleExteriorConstant : ℝ :=
  completeGeometryExteriorConstant d (completeSaddleScoreFactor Q)
    (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)

 def completeSaddleEnergyBudget (n : ℕ) : ℝ :=
  lowerSaddleRawEnergyBound C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf (completeSaddleDefectConstant Q Cfr)
    (completeSaddleAliasConstant Q Cfr) (completeSaddleFieldConstant Q Cfr) (completeSaddleExteriorConstant Q)
    (completeSourceSaddleActivity C (lowerSaddleResponseOrder C.smoothness d) Cfr (spatialInterpolationLambda d) Cω n)
    (shrunkDensityExponent C.densityLower C.densityUpper) n

 theorem completeSaddleAliasConstant_pos :
    0 < completeSaddleAliasConstant Q Cfr := completeGeometryAliasConstant_pos _ _ _ _ _ _ _ _ _ _ _
 theorem completeSaddleEnergyBudget_nonneg (n : ℕ) : 0 ≤ completeSaddleEnergyBudget Q Cfr cf Cω n := by
  unfold completeSaddleEnergyBudget lowerSaddleRawEnergyBound
  have h5 := ((completeGeometryDefectConstant_pos .. : 0 < completeSaddleDefectConstant Q Cfr)).le
  have h6 := (completeSaddleAliasConstant_pos Q Cfr).le
  have h7 := ((completeGeometryFieldConstant_pos .. : 0 < completeSaddleFieldConstant Q Cfr)).le
  have hch := ((completeGeometryExteriorConstant_pos .. : 0 < completeSaddleExteriorConstant Q)).le
  have hN := lowerSaddleN_positive C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) n
  have hmu : 0 ≤ lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n := by
    unfold lowerSaddleMu
    positivity [lowerSaddleH_positive d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n]
  positivity

 theorem eventually_completeSaddleGeometry_factorial [NeZero d]
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C) (hs : 1 < C.smoothness)
    (hd : 4*C.smoothness < (d : ℝ)) {cf : ℝ} (hcf : 0 < cf) (Cfr Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.range (n+1), poissonCountWeight
        (completeSaddleScoreFactor Q*completeSaddleMu C Cω n) r *
        ∫ U, completeSaddleGeometryEnvelope Q Cfr cf Cω n r U ∂fullSpatialPatchDesign d r) ≤
          completeSaddleEnergyBudget Q Cfr cf Cω n := by
  have hCs := ((by unfold completeSaddleScoreFactor highFixedScoreDenominator; positivity [C.densityLower_pos, Q.c_pos] : 0 < completeSaddleScoreFactor Q)).le
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by bound
    have h' : 4<d := by exact_mod_cast h
    omega
  have hbd  := (zero_lt_one.trans C.one_lt_densityUpper).le
  have hOrdConst : 0 ≤ completeSaddleOrdinaryConstant Q Cfr :=
    zero_le_one.trans (aliasTailConstant_ge_one
        (ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _) hCs
        (by unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity))
  have hCal : 0 ≤ finePairSaddleAliasFactorialConstant d (lowerSaddleResponseOrder C.smoothness d)
      C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C) (completeSaddleDegreeFactor d)
        (3*completeSaddleScoreFactor Q) := by
    unfold finePairSaddleAliasFactorialConstant aliasTailConstant
    have hP := finePairUniformSpatialPrefactor_nonneg d (lowerSaddleResponseOrder C.smoothness d)
      C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C)
    have hI := spatialInverseFourConstant_nonneg d
    have hB := finePairAliasGeometricBase_nonneg d C.densityUpper
    positivity
  filter_upwards [eventually_completeSaddleEnergyGuards hs hd hcf Cω,
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
      hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω cf
      (lowerSaddleResponseOrder C.smoothness d) Cfr Q.a Q.ρ (completeSaddleScoreFactor Q) hCs),
    tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters hs hd hcf
      (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) Cω)] with n G hO hphysical
  let M := completeSaddleM C n
  let D := completeSaddleD C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let N := completeSaddleN C Cω n
  let mu := completeSaddleMu C Cω n
  let ell := completeSaddleEll C Cω n
  let eta := completeSaddleEta C Cω cf n
  let tau := completeSaddleTau C n
  let c0 := completeSaddleC0 C
  let Cs := completeSaddleScoreFactor Q
  let K := completeSaddleDegreeFactor d
  let R := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  let Cord := completeSaddleOrdinaryConstant Q Cfr
  let Bl := completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hD  := hphysical.2.1
  have hext : intervalExteriorTau (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) = tau := by
    have h := exteriorTau_sqrt_ratio G.ad_positive G.density_interval
    simpa only [tau,completeSaddleTau,shrunkDensityExponent,densityIntervalExponent,completeSaddleAD,completeSaddleBD,one_div] using h
  have hfield : Real.exp (2*intervalExteriorTau (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹)*M)*(ell^(2-(d : ℝ)))^2*mu^4 ≤
      mu^2*N^(-(d : ℝ)) := by
    rw [hext]
    convert G.field_scale_square using 1 <;> ring
  have hOrd : (∑ j ∈ Finset.range (D-M), poissonCountWeight (Cs*mu) (M+1+j) *
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M+1+j) (F := D)
        (ordinaryFineAliasTargetSet d D ell N mu) M R q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M+1+j)) ≤
      Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) := by
    exact hO (fun _ => D)
  have hHigher := finite_complete_higher_geometry_energy_le hd5 hD (K := K) (ell := ell) (N := N) (mu := mu)
    (M := M) (R := R) (q := q) (C := Cfr) (a := Q.a) (rho := Q.ρ) (eta := eta) (Cs := Cs) (Eord := _) C.densityLower_pos Q.a_pos
    (by simpa only [completeSaddleAD,completeSaddleBD,one_div] using G.density_interval) (hext.trans_le G.tau_le)
    (by linarith [densityIntervalExponent_pos C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)])
    (by dsimp [K,completeSaddleDegreeFactor]; positivity) hCs G.ell_one G.ell_lt_N.le rfl G.degree_multiple
    G.mu_positive G.mu_one G.mu_log G.response_taylor hfield hOrd
  have h := completeSourceGeometryEnvelope_factorial_from_higher (NeZero.pos d) D M R q n hD Chi Bl Cs Cord tau
    (lt_of_lt_of_le zero_lt_one G.N_one) hCs G.mu_positive.le G.mu_one
    (by simpa using G.bd_nonneg) (by simp)
    hOrdConst hCal G.tau_nonneg hHigher
  convert h using 1 <;> (try dsimp [completeSaddleGeometryEnvelope, completeSaddleEnergyBudget, completeSaddleDefectConstant, completeSaddleAliasConstant, completeSaddleFieldConstant, completeSaddleExteriorConstant, lowerSaddleRawEnergyBound, completeSaddleM, completeSaddleD, completeSaddleN, completeSaddleMu, completeSaddleEll, completeSaddleEta, completeSaddleTau, completeSaddleC0]) <;> (try simp [poissonCountWeight]) <;> ring

end NearlyMinimax
