module

public import NearlyMinimax.OrdinaryFineAliasSpatialEnergy

@[expose] public section

/-! Finite aggregation of the genuine all-count ordinary fine aliases.
The source's actual target scales and rounded saddle supply the guards. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable (d q R : ℕ) (ad bd c0 C a rho : ℝ)

def ordinaryFineAliasTargetSet (D : ℕ) (L N mu : ℝ) : Finset ℕ :=
  (Finset.range (D+1)).filter (fun r => 3 ≤ r ∧ L < higherBandTargetScale d r N mu)

def ordinaryFineAliasFamilyRawAction {d n F : ℕ} (I : Finset ℕ)
    (ad bd lam L : ℝ) (T : ℕ → ℝ) (M q : ℕ) (C a V eta : ℝ)
    (U : DesignSample d n) (p g w : Fin n → ℝ)
    (c : HighFrameVector d F) (y : TernaryVector n) : ℝ :=
  ∑ r ∈ I, ordinaryFineAliasRawAction ad bd lam L (T r) M r q C a V eta U p g w c y

def ordinaryAliasFamilySpatialPrefactor : ℝ :=
  (R+1 : ℕ)^2 * ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho

theorem ordinaryAliasFamilySpatialPrefactor_nonneg :
    0 ≤ ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho :=
  mul_nonneg (sq_nonneg _) (ordinaryAliasSpatialPrefactor_nonneg ..)

end

/-- Numerical guards for the actual canonical fine-alias scale. -/
structure OrdinaryFineAliasSaddleGuards (s : ℝ) (d : ℕ) (ad bd Cw x : ℝ) : Prop where
  dimension : 5 ≤ d
  shrunkInterval : ad+(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)⁻¹ <
    bd-(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)⁻¹
  exponent : shrunkDensityExponent ad bd
    (lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x) ≤ densityIntervalExponent ad bd+1
  degree : (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)
  cutoff : 1 ≤ lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
    (shrunkDensityExponent ad bd) x
  logarithm : Real.log (1+Real.log (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)) ≤
      lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x
  targets : ∀ r ∈ ordinaryFineAliasTargetSet d
    (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x)
    (lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
      (shrunkDensityExponent ad bd) x)
    (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)
    (lowerSaddleMu d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw x),
    2 ≤ r ∧ r ≤ lowerAliasFineTargetBound d
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) (densityIntervalExponent ad bd+1)

/-- All guards come from the canonical rounded saddle and actual shrunk
endpoints, with a fixed number of fine targets before count/spatial tuples. -/
theorem eventually_ordinaryFineAlias_saddle_guards {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < d) (haD : 0 < ad) (hab : ad < bd) (Cw : ℝ) :
    ∀ᶠ x in atTop, OrdinaryFineAliasSaddleGuards s d ad bd Cw x := by
  let tau := densityIntervalExponent ad bd
  have htau  := densityIntervalExponent_pos haD hab
  have hM := lowerSaddleM_tendsto_atTop (lowerSaddleCoefficient_pos hs hd htau)
  have hsmall := hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : 0<(bd-ad)/2))
  filter_upwards [actual_lowerAlias_hierarchy hs hd haD hab (Cact := 1) (Cs := 1)
      (by norm_num) (by norm_num) Cw,
    hM.eventually (eventually_ge_atTop 1), hsmall] with x hh hM1 hsmall
  simp at hsmall
  rcases hh with ⟨hell,hτ,_hbase,hlog,_hgap,_hq21,_hq1,_hDq,_hco,_hsingle,_hRM,hactive⟩
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  refine ⟨hd5, by linarith,
    hτ, lowerSaddleD_le_fixed_linear (by linarith) hM1, hell.le, hlog, ?_⟩
  intro r hr
  have hrmem := (Finset.mem_filter.mp hr).2
  refine ⟨by omega, hactive r ?_⟩
  exact hrmem.2

end NearlyMinimax
