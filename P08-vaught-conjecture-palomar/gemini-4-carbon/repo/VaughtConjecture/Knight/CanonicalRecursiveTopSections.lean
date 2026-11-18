/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics

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
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

def boundaryTargetAt (m : ℕ) (hA : m + 2 ≤ A.card) (d : D.below (A, m + 2)) :
    (carrierAt sem m hA).below (A, m + 2) :=
  ⟨boundaryAt sem m hA d.1, by
    rw [CanonicalRecursiveInventory.boundary_cell]
    exact d.2⟩

theorem exists_sectionAt (m : ℕ) (hA : m + 2 ≤ A.card)
    {p : D.below (A, m + 2) → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, m + 2) p) :
    ∃ r : (carrierAt sem m hA).below (A, m + 2) → ExtOrd,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rowsAt sem hp m hA) (A, m + 2) r ∧
      ∀ d, r (boundaryTargetAt sem m hA d) = p d := by
  classical
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ := hpr.exists_coded_representative
    (fun d => d.2.2) (le_refl (Nat.card (D.below (A, m + 2))))
  let v : Cell D → ExtOrd := fun d => if hd : D.grade d ≤ m + 2 then
    u ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩ else ⊥
  have hv (d : D.below (A, m + 2)) : v d.1 = u d := dite_eq_left d.2.2
  have hvr : RespectsSemanticsBelow sem (A, m + 2) (fun d => v d.1) := by
    simpa only [hv] using hu
  have hvt (d : Cell D) : v d ≠ ⊤ := by
    dsimp only [v]
    split_ifs with hd
    · rcases mem_codedAlphabet_iff.mp
        (hcode ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩) with
        hb | ⟨b, i, _, _, he⟩
      · exact hb.trans_ne bot_ne_top
      · exact he.trans_ne (ofOrd_ne_top _)
    · exact bot_ne_top
  let T := CanonicalRecursiveSemantics.stateAt sem hp m hA
  let w := T.sectionOf le_rfl hvr hvt ∅ ⊤
  have hw : RespectsSemanticsBelow T.rows (A, m + 2) (fun d => w d.1) :=
    T.section_lawful le_rfl hvr hvt (by simp) (extVisibilityReplace_top _ _)
  refine ⟨fun d => canonicalDecoder S (m + 2) (w d.1),
    hw.decoded S (fun d => d.2.2), ?_⟩
  intro d
  have hr := T.section_boundary le_rfl hvr hvt (G := ∅) (by simp)
    (extVisibilityReplace_top (m + 2) (m + 2)) d.1
  change canonicalDecoder S (m + 2) (w (boundaryAt sem m hA d.1)) = p d
  exact (congrArg (canonicalDecoder S (m + 2)) (hr.trans (hv d))).trans (hdecode d)

abbrev boundaryTarget (n : ℕ) (hA : n + 3 ≤ A.card) := boundaryTargetAt sem (n + 1) hA

theorem exists_section (n : ℕ) (hA : n + 3 ≤ A.card)
    {p : D.below (A, n + 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, n + 3) p) :
    ∃ r : (carrier sem n hA).below (A, n + 3) → ExtOrd,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (A, n + 3) r ∧
      ∀ d, r (boundaryTarget sem n hA d) = p d :=
  exists_sectionAt sem hp (n + 1) hA hpr

end
end VaughtConjecture.Knight.CanonicalRecursiveTopSections
