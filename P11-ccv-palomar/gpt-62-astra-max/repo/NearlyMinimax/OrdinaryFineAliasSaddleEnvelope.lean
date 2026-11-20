module

public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope
public import NearlyMinimax.OrdinaryFineAliasFactorialTail

@[expose] public section

/-! Canonical rounded-saddle deterministic ordinary-alias envelope and its
actual spatial/factorial moments. No nuisance functions or chart inverses
occur in this universal geometry envelope. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def ordinaryFineAliasSaddleGeometryEnvelope (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a rho x : ℝ) (n F : ℕ) (U : DesignSample d n) : ℝ :=
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  let c0 := densityIntervalExponent ad bd+1
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let L := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
  let R := ordinaryFineAliasSaddleTargetBound s d ad bd
  let eta := lowerSaddleEta s d m theta Cw cf x
  ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) (ordinaryFineAliasTargetSet d D L N mu)
    M R q ad bd c0 C a rho eta L (fun r => higherBandTargetScale d r N mu) U

variable {s ad bd : ℝ} {d : ℕ} (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd)
    (Cw cf : ℝ) (q : ℕ) (C a rho Csharp : ℝ)
include hs hd haD hab

/-- True universal Q^n envelope moment, at all counts and frame degrees.
The fixed constant is chosen before x, n, F or nuisance data. -/
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le
    :
    let coefficient := ordinaryFineAliasSaddleCoefficient s d ad bd
    ∀ᶠ x in atTop, ∀ n F,
      Integrable (ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F)
        (fullSpatialPatchDesign d n) ∧
      (∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F U
        ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho *
          (lowerSaddleEta s d (coefficient)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw cf x)^4 *
          Real.exp (2*shrunkDensityExponent ad bd
            (lowerSaddleM (coefficient) x)*
            (lowerSaddleM (coefficient) x)) *
          (lowerSaddleN s d (coefficient)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)^(4-(d : ℝ)) *
          Real.exp (ordinaryFineAliasSaddleTailExponent s d ad bd*
            (lowerSaddleM (coefficient) x)) *
          (ordinaryAliasSpatialResponseBase d bd)^n := by
  filter_upwards [eventually_ordinaryFineAlias_saddle_guards hs hd haD hab Cw] with x G
  intro n F
  exact ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le G.dimension G.targets
    ad bd _ C a rho _ _ _ _ (haD.trans hab).le (Nat.cast_nonneg _) (by positivity)
    (by linarith [densityIntervalExponent_pos haD hab]) G.degree (lowerSaddleN_positive ..)
    G.cutoff G.logarithm (fun r hr => (Finset.mem_filter.mp hr).2.2.le) q

/-- The deterministic geometry envelope has the actual factorial-tail
moment, at the paper's rounded M/D/N/mu and eta=cf*h^s. No nuisance or
conditional pointwise norm premise is needed. -/
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
    (hCs : 0 ≤ Csharp) :
    ∀ᶠ x in atTop,
      let m := ordinaryFineAliasSaddleCoefficient s d ad bd
      let theta := ordinaryFineAliasSaddleTheta s d ad bd
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
      let mu := lowerSaddleMu d m theta Cw x
      let eta := lowerSaddleEta s d m theta Cw cf x
      let C6 := ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp
      ∀ F : ℕ → ℕ,
        (∑ j ∈ Finset.range (D-M), poissonCountWeight (Csharp*mu) (M+1+j) *
          (∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x
            (M+1+j) (F (M+1+j)) U ∂fullSpatialPatchDesign d (M+1+j))) ≤
        C6 * (eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))) *
          poissonCountWeight (C6*mu) (M+1) := by
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  have htau  := densityIntervalExponent_pos haD hab
  have hm  := lowerSaddleCoefficient_pos hs hd htau
  have htheta  := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ)<d := by linarith
  have hd4 : 4 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le hs hd haD hab ..,
    (lowerSaddleMu_tends_zero hd0 hm htheta Cw).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_gt_atTop 0] with x henergy hmu1 hx
  dsimp
  intro F
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let eta := lowerSaddleEta s d m theta Cw cf x
  let A := ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho
  let L := ordinaryFineAliasSaddleTailExponent s d ad bd
  let B := ordinaryAliasSpatialResponseBase d bd
  let P := eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))
  have hmu0 : 0 ≤ mu := by dsimp [mu]; rw [lowerSaddleMu_eq_exp hx]; positivity
  have hA : 0 ≤ A := ordinaryAliasFamilySpatialPrefactor_nonneg ..
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (Real.rpow_nonneg (lowerSaddleN_positive ..).le _)
  have hB : 0 ≤ B := by unfold B ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
  apply finite_alias_energy_tail_le hA hP hCs hB (lowerAliasSpatialFixedL_nonneg hd4 _ (by linarith)) hmu0 hmu1.le M (D-M)
    (fun n => ∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x
      n (F n) U ∂fullSpatialPatchDesign d n)
  intro j hj
  have he := (henergy (M+1+j) (F (M+1+j))).2
  convert he using 1 <;> simp only [A,P,L,B,m,theta,M,D,N,mu,eta,
    ordinaryFineAliasSaddleTailPrefactor, ordinaryFineAliasSaddleTailExponent,
    ordinaryFineAliasSaddleTargetBound, ordinaryFineAliasSaddleCoefficient, ordinaryFineAliasSaddleTheta] <;> ring

end NearlyMinimax
