/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SameStageCalibration
public import VaughtConjecture.Knight.SharpWitnessComposition
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.CountedEncoding
public import VaughtConjecture.Knight.RestrictedComposition

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Transform

/-- **Replacement above a block start**: for `y` strictly above the limit `ξ`, its replacement
at `(j+1, j+1)` is strictly above `ξ + j`. -/
theorem evr_succ_gt_of_gt_limit {ξ : Ordinal.{0}} (hξ : limitPart ξ = ξ) {y : ExtOrd}
    (hy : ofOrd ξ < y) (j : ℕ) :
    ofOrd (ξ + j) < extVisibilityReplace y (j + 1) (j + 1) := by
  have hstep : ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) :=
    by simp
  rcases ExtOrd.cases y with rfl | rfl | ⟨η, rfl⟩
  · exact absurd hy not_lt_bot
  · simp
  · rw [ofOrd_lt_ofOrd] at hy
    have hl : ξ ≤ limitPart η := by
      have := limitPart_mono hy.le
      rwa [hξ] at this
    by_cases hfp : j + 1 ≤ finitePart η
    · rw [extVisibilityReplace_of_le_finitePart hfp]
      apply ofOrd_lt_ofOrd.mpr
      calc ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) := hstep
        _ ≤ limitPart η + ((j + 1 : ℕ) : Ordinal.{0}) := add_le_add_left hl _
        _ ≤ limitPart η + (finitePart η : Ordinal.{0}) := add_le_add_right (Nat.cast_le.mpr hfp) _
        _ = η := limitPart_add_finitePart η
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)]
      apply ofOrd_lt_ofOrd.mpr
      calc ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) := hstep
        _ ≤ limitPart η + ((j + 1 : ℕ) : Ordinal.{0}) := add_le_add_left hl _

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- **A finite stable top value is an anchor at infinity** at threshold `j + 1`, with the
source inequality strict already at owner grade `j + 1`. -/
theorem isInfinityAnchor_of_stable (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (hXi : p.label Xi = ⊤) {j : ℕ}
    (hs : R.stableValue t p Xi = ofOrd (α.1 + j)) : R.IsInfinityAnchor t p Xi (j + 1) := by
  refine ⟨hXi, ?_⟩
  intro m s f q hfs hq hpq Θ hΘgr hΘtop Sig hSig hXi'
  suffices hlt : q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi'⟩ <
      extVisibilityReplace (q.scheme.rows.E Θ Sig) (j + 1) (j + 1) from ⟨hlt.le, fun _ => hlt⟩
  -- the stable labelling of the extension
  have hσr : RespectsSemantics q.scheme.rows (fun d => R.stableValue s q d) :=
    stableLiftRespects hM hq
  have hσa : R.stableValue s q (mapCell hpq Xi) = ofOrd (α.1 + j) := by
    rw [stableValue_mapCell hM.consistent hM.covering hpt hq hfs hpq Xi, hs]
  have hjN : j < q.scheme.scheme.grade Θ := hΘgr
  have hσΘ : ofOrd (α.1 + q.scheme.scheme.grade Θ) ≤ R.stableValue s q Θ :=
    stable_ge_of_top hM hq hΘtop
  have hσS : ofOrd (α.1 + q.scheme.scheme.grade Sig.1) ≤ R.stableValue s q Sig.1 :=
    stable_ge_of_top hM hq hSig
  have hαjΘ : ofOrd (α.1 + j) ≤ R.stableValue s q Θ := (stage_add_lt hjN).le.trans hσΘ
  obtain ⟨τ, hτ, -, hread⟩ := hσr.rowWitness Θ
  have hτa : τ (q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi'⟩) = ofOrd (α.1 + j) := by
    grind
  have hτS : ofOrd (α.1 + ((1 : ℕ) : Ordinal.{0})) ≤ τ (q.scheme.rows.E Θ Sig) := by
    have h := hread Sig
    change τ _ = min (R.stableValue s q Sig.1) (R.stableValue s q Θ) at h
    rw [h]
    refine le_min ?_ ?_
    · exact (ofOrd_le_ofOrd.mpr (add_le_add_right
        (Nat.cast_le.mpr (q.scheme.scheme.grade_pos Sig.1)) _)).trans hσS
    · exact (ofOrd_le_ofOrd.mpr (add_le_add_right
        (Nat.cast_le.mpr (q.scheme.scheme.grade_pos Θ)) _)).trans hσΘ
  -- pin the source of `Xi`
  have hlimit : limitPart α.1 = α.1 := limitPart_stage
  obtain ⟨v, hEa, horbit⟩ := read_strip_at (u := α.1) hτ.bounded hjN (by rwa [hlimit])
  rw [hlimit] at horbit
  let ξ := limitPart v
  have hξ : limitPart ξ = ξ := limitPart_idem v
  have hτξ : τ (ofOrd ξ) = ofOrd α.1 := by
    simpa only [ξ, Nat.cast_zero, add_zero] using horbit 0 (Nat.zero_le _)
  -- the source of `Σ` lies strictly above `ξ`
  have hSξ : ofOrd ξ < q.scheme.rows.E Θ Sig := by
    by_contra hle
    have h := hτ.mono (not_lt.mp hle)
    rw [hτξ] at h
    have h1 : ofOrd (α.1 + ((1 : ℕ) : Ordinal.{0})) ≤ ofOrd α.1 := hτS.trans h
    aesop
  rw [hEa]
  exact evr_succ_gt_of_gt_limit hξ hSξ j

/-- **Stable identity in hollow models**: every actual stable label equals its ordinary label.
The literal `IsHollow` (no anchor at any threshold) is used; the finite-characteristic vacuity
of anchors above a bounded characteristic arity is not repaired here. -/
theorem stableValue_eq_label_of_hollow (hM : R.IsModel) (hh : R.IsHollow) {n : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} (hpt : R.eval t = some p) (Xi : Cell p.scheme.scheme) :
    R.stableValue t p Xi = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rcases R.hasStableValue_stableValue t p Xi with ⟨hlt, -⟩ | ⟨heq, -⟩
    · exfalso
      have hge := le_stableValue_of_top (R := R) hpt htop
      obtain ⟨j, hj⟩ := exists_nat_of_band hge hlt
      exact hh ⟨n, t, p, hpt, Xi, j + 1, isInfinityAnchor_of_stable hM hpt htop hj⟩
    lia
  · exact stableValue_of_ne_top hM.consistent hM.covering hpt htop

end VaughtConjecture.Knight
