
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveSemantics

/-! # Literal-top boundary sections on the constructed recursive carrier

Finite outer coding gives a proper source profile; decoding recovers every
current old-boundary coordinate literally. No lower lifting or output
bountifulness is assumed. Future old fields outside the target are not part
of this prescription.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveTopSections
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : AvoidsValue D.scope A)
variable (n : ℕ) (hA : n + 3 ≤ A.card)

local notation "below₀" => D.below (A, n + 3)

def boundaryTarget (d : below₀) : (carrier sem n hA).below (A, n + 3) :=
  ⟨boundary sem n hA d.1, by
    rw [CanonicalRecursiveInventory.boundary_cell]
    exact d.2⟩

/-- Arbitrary lawful current boundary values, including literal top, extend
through every recursive controller. This is section supply, not cap lifting. -/
theorem exists_section {p : below₀ → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, n + 3) p) :
    ∃ r ,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (A, n + 3) r ∧
      ∀ d, r (boundaryTarget sem n hA d) = p d := by 
  classical
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ := hpr.exists_coded_representative
    (fun d => d.2.2) (le_refl (Nat.card (below₀)))
  let v  := fun d => if hd : D.grade d ≤ n + 3 then
    u ⟨d, D.scope_subset d, hd⟩ else ⊥
  have hv (d : below₀) : v d.1 = u d := dite_eq_left d.2.2
  have hvr : RespectsSemanticsBelow sem (A, n + 3) (fun d => v d.1) := by
    simpa only [hv] using hu
  have hvt (d : Cell D) : v d ≠ ⊤ := by
    dsimp  [v]
    split_ifs with hd
    · rcases mem_codedAlphabet_iff.mp
        (hcode ⟨d, D.scope_subset d, hd⟩) with
        hb | ⟨b, i, _, _, he⟩
      · exact hb.trans_ne bot_ne_top
      · exact he.trans_ne (ofOrd_ne_top _)
    · exact bot_ne_top
  let T := CanonicalRecursiveSemantics.state sem hp n hA
  let w := T.sectionOf le_rfl hvr hvt ∅ ⊤
  have hw : RespectsSemanticsBelow T.rows (A, n + 3) (fun d => w d.1) :=
    T.section_lawful le_rfl hvr hvt (by simp [VisibleOn]) (extVisibilityReplace_top)
  let core1 := canonicalDecoder S (n + 3)
  refine ⟨fun d => core1 (w d.1),
    hw.decoded S (fun d => d.2.2), ?_⟩
  intro d
  have hr := T.section_boundary le_rfl hvr hvt (G := ∅) (by simp [VisibleOn])
    (extVisibilityReplace_top) d.1
  
  exact (congrArg core1 (hr.trans (hv d))).trans (hdecode d)

