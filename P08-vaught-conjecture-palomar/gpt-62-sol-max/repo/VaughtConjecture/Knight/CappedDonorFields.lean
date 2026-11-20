/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorReceiving

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

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

theorem effC_mono {j' j : ℕ} (h : j' ≤ j) : GradedLe (effC J j') (effC J j) :=
  ⟨Finset.Subset.refl _, min_le_min_right _ h⟩

/-- The cut depends only on the cap and reference values. -/
theorem cut_congr {v₁ v₂ : R.Low → ExtOrd} (hcap : v₁ R.capL = v₂ R.capL)
    (href : ∀ i, v₁ (R.lowRef i) = v₂ (R.lowRef i)) : R.cut v₁ = R.cut v₂ := by
  unfold cut
  grind

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

end Ref

end CappedDonor

end VaughtConjecture.Knight
