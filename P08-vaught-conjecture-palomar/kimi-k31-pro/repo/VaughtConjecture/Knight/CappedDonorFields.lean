/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorReceiving

/-! # The complete field vector of the receiving family (the compiler-facing adapter)

The receiving-input family of `Knight/CappedDonorReceiving.lean` read as **one fixed field
inventory** with numerical and persistent components, the cross-grade restriction of states, and
the non-top readback of notes32 §8.

**Field inventory** (`Field`): one field per request cell (`req`), one per private cell
(`priv`), and the gate.  Each field has a grade (`Field.grade`): the cell's grade, and `1` for
the gate.  A field is *present* at cutoff `j` when its grade is at most `j`
(`present_req_iff`, `present_priv_iff`: the request and private lower sets `effP`, `effC` are
exactly the present cells).  A state at cutoff `j` has

* a **numerical value** at every present field (`State.numeric`), and
* a **persistent value** at every field, present or future (`State.persistent`): the gate itself
  and the numerical `1`-visible shadows.

For an admissible state the numerical value of a present field is self-visible at the field's
grade (`numeric_selfVis`), every persistent value is `1`-visible (`persistent_selfVis`), and the
persistent value of a present field carries exactly the field's numerical support
(`persistent_ne_bot_iff`).  The cap receipts of both fibres are receipts for **every** persistent
field, present or not (`capReceipts_iff`).

**Restriction across grades** (`restrict`): lowering the cutoff drops the numerical fields above
it and retains every persistent field; admissibility is preserved (`Admissible.restrict`) — the
face, the guard and the relation are forgotten only where their fields disappear — and the
persistent vector is unchanged (`restrict_persistent`), the numerical vector is the restriction
(`restrict_numeric`); restriction is coherent (`restrict_restrict`, `restrict_self`).

**Non-top readback** (notes32 §8, the receiving half): in any admissible state at a cutoff where
the cap is present, with a positive gate and with the actual cap and reference values, every
request field with a non-top donor label reads back the donor label literally, every donor-top
field reads at least the actual cut, and every donor-bottom field is bottom
(`nonTop_readback`).  The cut is `cut_actual`, the maximum of the reference-block endpoints —
not the private cap — so this is proper-cut correctness at the block endpoints; with no proper
block the cut is bottom and bottom-label correctness comes from the support guard alone, not from
cancellation at a positive cut.  The existence of a physical probe realizing such a state is a
separate obligation, not asserted here.

**Where the numerical relation first activates.**  Every request field has grade below `N`, so
the request vector is complete at cutoff `N - 1`, before the cap is numerically present; at the
step `N - 1 → N` only the private fields of grade `N` are added.  The cross-grade completion
property at that step is not derived here from the two same-grade fibres. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

/-! ## The field inventory -/

/-- The field inventory: request fields, private fields, and the gate. -/
inductive Field {nP J : ℕ} (P : SemScheme (nP + 1)) (C : SemScheme J)
  | req (d : Cell P.scheme)
  | priv (d : Cell C.scheme)
  | gate

variable {nP J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

/-- The grade of a field: the cell's grade, and `1` for the gate. -/
def Field.grade : Field P C → ℕ
  | .req d => P.scheme.grade d
  | .priv d => C.scheme.grade d
  | .gate => 1

/-- A request cell is present at cutoff `j` exactly when its grade is at most `j`. -/
theorem present_req_iff (j : ℕ) (d : Cell P.scheme) :
    GradedLe (P.scheme.cell d) (effP nP j) ↔ P.scheme.grade d ≤ j :=
  ⟨fun h => h.2.trans (min_le_left _ _),
    fun h => ⟨Finset.subset_univ _, le_min h (Ref.gradeP_le d)⟩⟩

/-- A private cell is present at cutoff `j` exactly when its grade is at most `j`. -/
theorem present_priv_iff (j : ℕ) (d : Cell C.scheme) :
    GradedLe (C.scheme.cell d) (effC J j) ↔ C.scheme.grade d ≤ j :=
  ⟨fun h => h.2.trans (min_le_left _ _), fun h => ⟨Finset.subset_univ _, le_min h (gradeC_le d)⟩⟩

namespace Ref

variable {I : Type*} [Fintype I] {N : ℕ} {R : Ref I nP N J P C}

/-- The numerical value of a present field. -/
def State.numeric {j : ℕ} (st : R.State j) : (f : Field P C) → f.grade ≤ j → ExtOrd
  | .req d, h => st.u ⟨d, (present_req_iff j d).mpr h⟩
  | .priv d, h => st.v ⟨d, (present_priv_iff j d).mpr h⟩
  | .gate, _ => st.gate

/-- The persistent value of every field: the gate and the numerical shadows. -/
def State.persistent {j : ℕ} (st : R.State j) : Field P C → ExtOrd
  | .req d => st.shadowP d
  | .priv d => st.shadowC d
  | .gate => st.gate


/-- Persistent values are `1`-visible. -/
theorem Admissible.persistent_selfVis {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    (f : Field P C) : SelfVis 1 (st.persistent f) := by
  cases f with
  | req d => exact hst.shadowP_vis d
  | priv d => exact hst.shadowC_vis d
  | gate => exact hst.gate_vis

/-- The cap receipts are receipts for every persistent field, present or future. -/
theorem capReceipts_iff {j : ℕ} (γ : ExtOrd) (st st₁ : R.State j) :
    R.CapReceipts γ st st₁ ↔
      ∀ f : Field P C, min (st₁.persistent f) γ = min (st.persistent f) γ := by
  constructor
  · rintro ⟨hg, hP, hC⟩ f
    cases f with
    | req d => exact hP d
    | priv d => exact hC d
    | gate => exact hg
  · intro h
    exact ⟨h .gate, fun d => h (.req d), fun d => h (.priv d)⟩

/-! ## Restriction across grades -/

theorem effC_mono {j' j : ℕ} (h : j' ≤ j) : GradedLe (effC J j') (effC J j) :=
  ⟨Finset.Subset.refl _, min_le_min_right _ h⟩

/-! ## The non-top readback (notes32 §8) -/

/-- The cut depends only on the cap and reference values. -/
theorem cut_congr {v₁ v₂ : R.Low → ExtOrd} (hcap : v₁ R.capL = v₂ R.capL)
    (href : ∀ i, v₁ (R.lowRef i) = v₂ (R.lowRef i)) : R.cut v₁ = R.cut v₂ := by grind [cut]

/-- The selector depends only on the cap and reference values. -/
theorem sel_congr {v₁ v₂ : R.Low → ExtOrd} (hcap : v₁ R.capL = v₂ R.capL)
    (href : ∀ i, v₁ (R.lowRef i) = v₂ (R.lowRef i)) (d : Cell P.scheme) :
    R.sel v₁ d = R.sel v₂ d := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h, R.sel_of_proper h, cut_congr hcap href, href]
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, R.sel_of_bot hb]
  · have ht := not_not.mp fun ht => h ⟨hb, ht⟩
    rw [R.sel_of_top ht, R.sel_of_top ht, cut_congr hcap href]



