/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.PositiveFloor

/-! # Literal-top boundary sections on the constructed recursive carrier

Finite outer coding gives a proper source profile; decoding recovers every
current old-boundary coordinate literally. No lower lifting or output
bountifulness is assumed. Future old fields outside the target are not part
of this prescription.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveTopSections
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : D.AvoidsScope A)
variable (n : ℕ) (hA : n ≤ A.card)

def boundaryTarget (d : D.below (A, n)) : (carrier sem n hA).below (A, n) :=
  ⟨boundary sem n hA d.1, by
    rw [CanonicalRecursiveInventory.boundary_cell]
    grind⟩

/-- Arbitrary lawful current boundary values, including literal top, extend
through every recursive controller. This is section supply, not cap lifting. -/
theorem exists_section {p : D.below (A, n) → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, n) p) :
    ∃ r : (carrier sem n hA).below (A, n) → ExtOrd,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (A, n) r ∧
      ∀ d, r (boundaryTarget sem n hA d) = p d := by
  classical
  letI := Fintype.ofFinite (D.below (A,n))
  let u := TerminalProfile.capped p n 0
  have hu := hpr.cap (TerminalProfile.visible p n 0)
  let v := fun d => if hd : D.grade d ≤ n then
    u ⟨d, D.scope_subset d, hd⟩ else ⊥
  have hv (d : D.below (A, n)) : v d.1 = u d := dite_eq_left d.2.2
  have hvr : RespectsSemanticsBelow sem (A, n) (fun d => v d.1) := by
    simpa [hv] using hu
  have hvt (d : Cell D) : v d ≠ ⊤ := by
    dsimp [v]
    split_ifs with hd
    · exact TerminalProfile.proper p n 0 _
    · exact bot_ne_top
  let T := CanonicalRecursiveSemantics.state sem hp n hA
  let w := T.sectionOf le_rfl hvr hvt ∅ ⊤
  have hw : RespectsSemanticsBelow T.rows (A, n) (fun d => w d.1) :=
    T.section_lawful le_rfl hvr hvt (by simp) (extVisibilityReplace_top _ _)
  let δ := collapseBlock (TerminalProfile.floor p 0)
  refine ⟨fun d => δ (w d.1), map_respects_of_bottom_reflecting hw (fun d => d.2.2)
    (SharpWitnessComposition.boundedMap_of_witness (collapseBlock_witness n (TerminalProfile.limit p 0)))
    (collapseBlock_reflects_bottom _), ?_⟩
  intro d
  have hr := T.section_boundary le_rfl hvr hvt (G := ∅) (by simp)
    (extVisibilityReplace_top n n) d.1
  change δ (w (boundary sem n hA d.1)) = p d
  exact (congrArg (δ) (hr.trans (hv d))).trans (TerminalProfile.collapse p n 0 d)

end
end VaughtConjecture.Knight.CanonicalRecursiveTopSections
