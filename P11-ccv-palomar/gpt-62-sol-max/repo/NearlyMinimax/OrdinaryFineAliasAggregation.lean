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

def ordinaryFineAliasTargetSet (d D : ℕ) (L N mu : ℝ) : Finset ℕ :=
  (Finset.range (D+1)).filter (fun r => 3 ≤ r ∧ L < higherBandTargetScale d r N mu)

def ordinaryFineAliasFamilyRawAction {d n F : ℕ} (I : Finset ℕ)
    (ad bd lam L : ℝ) (T : ℕ → ℝ) (M q : ℕ) (C a V eta : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∑ r ∈ I, ordinaryFineAliasRawAction ad bd lam L (T r) M r q C a V eta U p g w c y

def ordinaryAliasFamilySpatialPrefactor (d q R : ℕ) (ad bd c0 C a rho : ℝ) : ℝ :=
  ((R+1 : ℕ) : ℝ)^2 * ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho

theorem ordinaryAliasFamilySpatialPrefactor_nonneg (d q R : ℕ) (ad bd c0 C a rho : ℝ) :
    0 ≤ ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho :=
  mul_nonneg (sq_nonneg _) (ordinaryAliasSpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)

section
variable (s : ℝ) (d : ℕ) (ad bd Cw x : ℝ)
local notation "τ" => densityIntervalExponent ad bd
local notation "m" => lowerSaddleCoefficient s d τ
local notation "θ" => lowerSaddleTheta s d τ
local notation "M" => lowerSaddleM m x
local notation "N" => lowerSaddleN s d m θ Cw (shrunkDensityExponent ad bd) x
local notation "ell" => lowerAliasCutoff s d m θ Cw (τ+1) (shrunkDensityExponent ad bd) x

/-- Numerical guards for the actual canonical fine-alias scale. -/
structure OrdinaryFineAliasSaddleGuards : Prop where
  dimension : 5 ≤ d
  shrunkInterval : ad + (M : ℝ)⁻¹ < bd - (M : ℝ)⁻¹
  exponent : shrunkDensityExponent ad bd M ≤ τ+1
  degree : (lowerSaddleD d m x : ℝ) ≤ (((d : ℝ) + 8)/4+1) * (M : ℝ)
  cutoff : 1 ≤ ell
  logarithm : Real.log (1 + Real.log N) ≤ M
  targets : ∀ r ∈ ordinaryFineAliasTargetSet d (lowerSaddleD d m x) ell N (lowerSaddleMu d m θ Cw x),
    2 ≤ r ∧ r ≤ lowerAliasFineTargetBound d θ (τ+1)

end

/-- All guards come from the canonical rounded saddle and actual shrunk
endpoints, with a fixed number of fine targets before count/spatial tuples. -/
theorem eventually_ordinaryFineAlias_saddle_guards {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd) (Cw : ℝ) :
    ∀ᶠ x in atTop, OrdinaryFineAliasSaddleGuards s d ad bd Cw x := by
  let tau := densityIntervalExponent ad bd
  let m := lowerSaddleCoefficient s d tau
  have htau := densityIntervalExponent_pos haD hab
  have hm := lowerSaddleCoefficient_pos hs hd htau
  have hM := lowerSaddleM_tendsto_atTop hm
  have hsmall := hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : (0 : ℝ)<(bd-ad)/2))
  filter_upwards [actual_lowerAlias_guards hs hd haD hab Cw,
    hM.eventually (eventually_ge_atTop (1 : ℝ)), hsmall] with x hh hM1 hsmall
  simp only [Pi.inv_apply] at hsmall
  have hd0 : (0 : ℝ)<d := by linarith
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  refine ⟨hd5, by change ad+(lowerSaddleM m x : ℝ)⁻¹<bd-(lowerSaddleM m x : ℝ)⁻¹; linarith,
    hh.exponent_le, lowerSaddleD_le_fixed_linear hd0 hM1, hh.cutoff.le, hh.log_le, ?_⟩
  intro r hr
  have hrmem := (Finset.mem_filter.mp hr).2
  refine ⟨by omega, hh.active_le r ?_⟩
  exact hrmem.2

end NearlyMinimax
