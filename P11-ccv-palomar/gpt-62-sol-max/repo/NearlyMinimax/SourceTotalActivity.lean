module

public import NearlyMinimax.SourceActivitySummation


@[expose] public section

/-! Total activity of the actual finite source family, including singleton,
three genuine pair rows, and every selected higher target. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem finePairTotalMass_activity_bound (d : ℕ) [NeZero d] (k D M q : ℕ) (hD : 1 ≤ D)
    (a b C ℓ N : ℝ) (ha : 0 < a) (hab : a < b) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (hunit : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) ≤ N^2)
    (hcoarse : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2 ≤ 2*N^2) :
    highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass ≤
      (ordinaryDensityActivityBase a b)^2 * sourceResponseCost q C * (1+512*(d : ℝ)) *
        N^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) := by
  let K := (ordinaryDensityActivityBase a b)^2 * sourceResponseCost q C
  let EM := Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a)))
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (sourceResponseCost_nonneg q C)
  have hEM : 1 ≤ EM := source_exterior_exp_ge_one ha hab _
  have hu : finePairRowMass d D M q a b C ℓ N .unit ≤ K*N^2 := by
    apply (finePairRowMass_unit_le d D M q hD a b ha hab C ℓ N).trans
    calc
      _ = K*((D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))) := by ring
      _ ≤ K*N^2 := mul_le_mul_of_nonneg_left hunit hK
  have hc : finePairRowMass d D M q a b C ℓ N .coarse ≤ 256*(d : ℝ)*K*N^2 := by
    apply (finePairRowMass_coarse_le d D M q hD a b ha hab C ℓ N hℓ).trans
    calc
      _ = (128*(d : ℝ)*K)*((D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2) := by ring
      _ ≤ (128*(d : ℝ)*K)*(2*N^2) := mul_le_mul_of_nonneg_left hcoarse (by positivity)
      _ = _ := by ring
  have hf := finePairRowMass_fine_le d D M q a b ha hab C ℓ N hℓ hℓN
  have hu' := hu.trans (le_mul_of_one_le_right (by positivity : 0 ≤ K*N^2) hEM)
  have hc' := hc.trans (le_mul_of_one_le_right (by positivity : 0 ≤ 256*(d : ℝ)*K*N^2) hEM)
  change (∑ i, finePairRowMass d D M q a b C ℓ N i) ≤ _
  simp only [show (Finset.univ : Finset FinePairRowTag) = {.unit,.coarse,.fine} from rfl]
  simp only [Finset.sum_insert (by decide : FinePairRowTag.unit ∉ ({.coarse,.fine} : Finset FinePairRowTag)),
    Finset.sum_insert (by decide : FinePairRowTag.coarse ∉ ({.fine} : Finset FinePairRowTag)), Finset.sum_singleton]
  grind

def sourceActivityConstant (d q : ℕ) (C B lam : ℝ) : ℝ :=
  B^2 * sourceResponseCost q C * (1+512*(d : ℝ)) + B * sourceResponseCost q C +
    4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)

theorem sourceActivityConstant_nonneg (d q : ℕ) (C B lam : ℝ) (hB : 0 ≤ B) :
    0 ≤ sourceActivityConstant d q C B lam := by
  unfold sourceActivityConstant higherBandGeometricPrefactor higherBandInterpolationBase sourceResponseCost
  positivity

/-- The actual complete finite row family has a fixed total activity constant.
The hypotheses are elementary inequalities on the computed source scales. -/
theorem sourceRows_activity_bound {d k D M q : ℕ} [NeZero d] (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B q1 q2 : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hq1 : q1 = higherBandSourceRatio d D B lam N μ 1)
    (hq2 : q2 = higherBandSourceRatio d D B lam N μ 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1)
    (hcoarse : Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ ≤ N)
    (hsingle : (D : ℝ)*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) ≤ N)
    (hpair : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2 ≤ 2*N^2) :
    highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass ≤
      sourceActivityConstant d q C B lam * N^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) := by
  let A := ordinaryDensityActivityBase a b
  let EM := Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a)))
  let ED := Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))
  have hA : 0 ≤ A := by dsimp [A, ordinaryDensityActivityBase]; positivity
  have hED : 1 ≤ ED := source_exterior_exp_ge_one ha hab _
  have hEM : 1 ≤ EM := source_exterior_exp_ge_one ha hab _
  have hunit : (D : ℝ)^2*ED ≤ N^2 := by
    have h1 := mul_le_mul_of_nonneg_left hED (by positivity : 0 ≤ (D : ℝ)^2*ED)
    have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ (D : ℝ)*ED) hsingle 2
    nlinarith only [h1, h2]
  have hp := finePairTotalMass_activity_bound d k D M q hD a b C ℓ N ha hab hℓ hℓN hunit hpair
  have hC := sourceResponseCost_nonneg q C
  have hp' : highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass ≤
      B^2*sourceResponseCost q C*(1+512*(d : ℝ))*N^2*EM := by
    refine hp.trans ?_
    gcongr
  have hs : singletonRowMass d D q a b C ≤ A*sourceResponseCost q C*((D : ℝ)*ED) := by
    convert singletonRowMass_exponential_bound d D q hD a b ha hab C using 1
    unfold A ED ordinaryDensityActivityBase sourceResponseCost
    ring
  have hN2 : N ≤ N^2*EM :=
    (show N ≤ N^2 by nlinarith).trans (le_mul_of_one_le_right (sq_nonneg N) hEM)
  have hs' : singletonRowMass d D q a b C ≤ B*sourceResponseCost q C*(N^2*EM) := by
    exact hs.trans (mul_le_mul (mul_le_mul_of_nonneg_right hbB hC) (hsingle.trans hN2)
      (by positivity) (mul_nonneg hB hC))
  have hh := higherBandFamily_activity_bound (k := k) (M := M) (q := q) hD
    a b C lam ℓ N μ B q1 q2 ha hab hℓ hN hμ hbase1 hB hbB hq1 hq2 hq1h hq21 hsmall hcoarse
  rw [sourceRowTotalMass_eq]
  dsimp [sourceActivityConstant]
  change _ ≤ _*N^2*EM
  nlinarith only [hp', hs', hh]

end NearlyMinimax
