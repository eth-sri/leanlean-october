/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationSemantics
public import VaughtConjecture.Knight.CoatomBoundaryExtension

@[expose] public section

namespace VaughtConjecture.Knight.ScopeReplicationLifting

open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier

open ScopeReplicationSemantics CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (S : Frame A)

local notation "D" => S.base
local notation "B" => S.left
local notation "C" => S.right
local notation "sem" => S.sem

def fullErase (j : ℕ) (d : (scheme S).below (A, j)) : (D).below (A, j) :=
  ⟨erase S d.1, (D).scope_subset _,
    (erase_grade S d.1).le.trans d.2.2⟩

def duplicate {j : ℕ} (p : (D).below (A, j) → ExtOrd) : (scheme S).below (A, j) → ExtOrd :=
  p ∘ fullErase S j

theorem duplicate_lawful {j : ℕ} {p : (D).below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, j) p) :
    RespectsSemanticsBelow (rows S) (A, j) (duplicate S p) :=
  duplicateBelow_respects S (fun d => (fullErase S j d).2) hp

/-- Every auxiliary copy is retained individually, not reconstructed from
field readouts or a selected profile. -/
theorem duplicate_restrict {j : ℕ} {p : (scheme S).below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow (rows S) (A, j) p) :
    duplicate S (p ∘ oldBelow S (A, j)) = p := by
  funext d
  apply (copy_eq S hp d (oldBelow S (A, j) (fullErase S j d))
    ?_ ?_).symm
  · change (scheme S).scope d.1 ⊆ (scheme S).scope (old S (erase S d.1))
    simpa only [CellScheme.scope, old_index] using scope_le_erase S d.1
  · exact (erase_old S (erase S d.1)).symm

/-- A single-copy original-face lift gives a replicated full-target lift at
the same external cap, bottom and top included. -/
theorem lift_to_full {I : Finset ι × ℕ} {j : ℕ} (h : GradedLe I (A, j))
    (hside : I.1 ⊆ B ∨ I.1 ⊆ C) (hl : CappedLift sem h) :
    CappedLift (rows S) h := by
  intro p q γ hp hq hγ hag
  let p' := p ∘ oldBelow S I
  let q' := q ∘ oldBelow S (A, j)
  have hp' : RespectsSemanticsBelow sem I p' := restrict_respects S hp
  have hq' : RespectsSemanticsBelow sem (A, j) q' := restrict_respects S hq
  obtain ⟨r, hr, hcap, hread⟩ := hl p' q' γ hp' hq' hγ (fun d => hag (oldBelow S I d))
  refine ⟨duplicate S r, duplicate_lawful S hr, ?_, ?_⟩
  · intro d
    have hc := hcap (fullErase S j d)
    have he := congrFun (duplicate_restrict S hq) d
    exact hc.trans (congrArg (fun x => min x γ) he)
  · intro d
    rcases cases S d.1 with ⟨c, hc⟩ | ⟨a, ha⟩
    · have hcI : GradedLe ((D).cell c) I := by rw [← old_index S c, ← hc]; exact d.2
      have he : oldBelow S I ⟨c, hcI⟩ = d := Subtype.ext hc.symm
      rw [← he]
      change r (fullErase S j (CellScheme.below.mono h
        (oldBelow S I ⟨c, hcI⟩))) = p' ⟨c, hcI⟩
      have hf : fullErase S j (CellScheme.below.mono h
          (oldBelow S I ⟨c, hcI⟩)) = CellScheme.below.mono h ⟨c, hcI⟩ :=
        Subtype.ext (erase_old S c)
      exact (congrArg r hf).trans (hread ⟨c, hcI⟩)
    · have hs : a.1.1.1 ⊆ I.1 := by
        simpa only [ha, added_index] using d.2.1
      exact (hside.elim (fun hb => a.2.2.1.1 (hs.trans hb))
        (fun hc => a.2.2.1.2 (hs.trans hc))).elim

end

end VaughtConjecture.Knight.ScopeReplicationLifting
