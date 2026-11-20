/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Coface
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CapObservation
public import VaughtConjecture.Knight.CappedLifting

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCoverReceiving

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace

variable {α : LimitStage}

/-- Strict truncation below the stage does not change caps below the stage. -/
theorem min_truncExt_of_lt {γ : ExtOrd} (hγ : γ < ofOrd α.1) (x : ExtOrd) :
    min (truncExt α.1 x) γ = min x γ :=
  min_truncExt_of_le hγ.le x

/-- An ordinal is at most its sum with a natural number. -/
theorem le_add_nat (ν : Ordinal.{0}) (m : ℕ) : ν ≤ ν + m := by simp

/-- Adding a finite offset stays below a nonzero limit stage. -/
theorem add_nat_lt_limitStage {ν : Ordinal.{0}} (hν : ν < α.1) (m : ℕ) : ν + m < α.1 := by
  induction m with
  | zero => simpa using hν
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    exact α.2.succ_lt ih

/-- `ofOrd (ν + m)` is self-visible at `m`. -/
theorem selfVis_ofOrd_add_nat (ν : Ordinal.{0}) (m : ℕ) : SelfVis m (ofOrd (ν + m)) := by
  rw [selfVis_ofOrd_iff]
  have h : ν + (m : Ordinal.{0}) = limitPart ν + ((finitePart ν + m : ℕ) : Ordinal.{0}) := by
    conv_lhs => rw [← limitPart_add_finitePart ν]
    rw [add_assoc, Nat.cast_add]
  rw [h, finitePart_limitPart_add_nat]
  exact Nat.le_add_left m _

/-- Stage-valued capped repair on any visible face, including the empty and full face. -/
theorem exists_stage_extends_capped_emb {k m : ℕ} (D : SemScheme m)
    (g : Fin k ↪ Fin m) (hv : Finset.univ.image g ∈ D.scheme.plan) (p : S α.1 k)
    (hs : D.restrictFace g hv = p.scheme) {v : Cell D.scheme → ExtOrd}
    (hlaw : RespectsSemantics D.rows v) {γ : ExtOrd} (hγ : SelfVis m γ)
    (hγα : γ < ofOrd α.1)
    (hcap : ∀ i, min (v (toCell D.scheme g hv i)) γ =
      min (p.label (SemScheme.castCell hs i)) γ) :
    ∃ Q : S α.1 m, ∃ he : Q.scheme = D, typeMap g Q = some p ∧
      ∀ d, min (Q.label d) γ = min (v (SemScheme.castCell he d)) γ := by
  have hp : RespectsSemantics (D.restrictFace g hv).rows (fun d => p.label (SemScheme.castCell hs d)) := by
    obtain ⟨ps, pl, pb, pr⟩ := p
    dsimp only at hs ⊢
    cases hs
    exact pr
  obtain ⟨l, hl, hlγ, hlp⟩ := D.extend_capped g hv hp hlaw hγ hcap
  exact ⟨ofRespects α.2 D l hl, rfl, typeMap_ofRespects α.2 g hv hs hl hlp,
    fun d => (min_truncExt_of_lt hγα (l d)).trans (hlγ d)⟩

end VaughtConjecture.Knight.FiniteCoverReceiving
