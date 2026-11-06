/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreeDiagonal

/-! # Arbitrary ambients represented grade by grade

Availability promotes each label to a full-scope controller at the same grade.
Taking a maximum among those finitely many controllers yields one controller
dominating the entire grade. Normalizing its actual locality witness then reads
that grade exactly, and all lower grades capped at its own label. This strengthens
the per-cell availability observation in `Knight/Producer.lean` to an exact
grade-by-grade representation on arbitrary lower domains, without assuming a
bountiful scheme or that the ambient is one of its semantic rows.

At an external cap, a grade is frozen if its maximum lies strictly below the
cap. Otherwise any replacement maximum must be a controller whose *old* label
already reaches the cap. The eligible set is preserved exactly. These facts do
not assume a designated controller stays maximal, nor that one controller
dominates labels at other grades.

The charts are extracted from respect, not a converse characterization of it.
Recombining or changing charts still requires every controller locality and
availability. In particular their shifters are not asserted bottom-reflecting,
and no unrestricted composition of faithful transformations is used.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AmbientGradeCharts

open Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- A normalized witness at a controller dominating its own grade. -/
structure Chart (sem : Semantics D) (BJ : Finset ι × ℕ) (q : D.below BJ → ExtOrd)
    (k : ℕ) where
  owner : D.below BJ
  index : D.cell owner.1 = (BJ.1, k)
  dominates : ∀ d : D.below BJ, D.grade d.1 = k → q d ≤ q owner
  shift : ExtOrd → ExtOrd
  witness : Witness (gTop k) shift
  bounded : ∀ x, shift x ≤ q owner
  read : ∀ d : D.below (D.cell owner.1),
    shift (sem.E owner.1 d) = min (q (CellScheme.below.incl owner d)) (q owner)

namespace Chart

variable {k : ℕ} (C : Chart sem BJ q k)

theorem grade : D.grade C.owner.1 = k := congrArg Prod.snd C.index

/-- Every occurrence of grade at most `k` lies below this full-scope owner. -/
def occurrence (d : D.below BJ) (hd : D.grade d.1 ≤ k) : D.below (D.cell C.owner.1) :=
  ⟨d.1, by rw [C.index]; exact ⟨d.2.1, hd⟩⟩

section
variable (d : D.below BJ)

theorem read_capped (hd : D.grade d.1 ≤ k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd)) = min (q d) (q C.owner) :=
  C.read (C.occurrence d hd)

/-- Exact readback on the owner's grade, including all its sibling controllers. -/
theorem read_grade (hd : D.grade d.1 = k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd.le)) = q d := by
  rw [C.read_capped, min_eq_left (C.dominates d hd)]

end

/-- If this grade's maximum reaches the external cap, its one witness recovers
the externally capped labels at every lower grade as well. -/
theorem read_under_cap {γ : ExtOrd} (hactive : γ ≤ q C.owner)
    d hd :
    min (C.shift (sem.E C.owner.1 (C.occurrence d hd))) γ = min (q d) γ := by
  rw [C.read_capped, min_assoc, min_eq_right hactive]

end Chart

/-- One full-scope controller suffices to make the maximizing set nonempty.
Availability, not a cross-grade domination assumption, supplies the final bound. -/
theorem exists_maximizer (hq : RespectsSemanticsBelow sem BJ q) {k}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    ∃ c, D.cell c.1 = (BJ.1, k) ∧
      ∀ d, D.grade d.1 = k → q d ≤ q c := by
  classical
  let _ := Fintype.ofFinite (D.below BJ)
  let s := Finset.univ.filter (fun c : D.below BJ => D.cell c.1 = (BJ.1, k))
  have hs : s.Nonempty := by
    obtain ⟨c, hc⟩ := hfull
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image s q hs
  have hci : D.cell c.1 = (BJ.1, k) := (Finset.mem_filter.mp hc).2
  refine ⟨c, hci, ?_⟩
  intro d hd
  have hscope : D.scope d.1 ⊆ D.scope c.1 := by
    change D.scope d.1 ⊆ (D.cell c.1).1
    rw [hci]
    exact d.2.1
  have hgrade : D.grade d.1 = D.grade c.1 := hd.trans (congrArg Prod.snd hci).symm
  obtain ⟨e, he, hde⟩ := hq.availability d c hscope hgrade
  exact hde.trans (hmax e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.trans hci⟩))

/-- Extract an actual bounded faithful witness; bottom and literal top need no exclusion. -/
theorem exists_chart (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    Nonempty (Chart sem BJ q k) := by
  obtain ⟨c, hc, hmax⟩ := exists_maximizer hq hfull
  let self : D.below (D.cell c.1) := ⟨c.1, GradedLe.refl _⟩
  let p : D.below (D.cell c.1) → ExtOrd := fun d => q (CellScheme.below.incl c d)
  have hm : ∀ d : D.below (D.cell c.1), D.grade d.1 ≤ D.grade self.1 := fun d => d.2.2
  have hv : SelfVis (D.grade self.1) (p self) := (hq.orderly c).symm
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness hm hv (hq.locality c)
  have hg : D.grade self.1 = k := congrArg Prod.snd hc
  exact ⟨⟨c, hc, hmax, τ, hg ▸ hτ, hb, hr⟩⟩

/-! ## Exact cap-preservation obligations -/

section
variable {a b γ : ExtOrd}

/-- The literal part of a cap equation; this statement also applies at cap top. -/
theorem eq_of_cap_below (h : min a γ = min b γ) (hb : b < γ) : a = b := by
  rw [min_eq_left hb.le] at h
  have ha : a < γ := (min_lt_iff.mp (h.trans_lt hb)).resolve_right (lt_irrefl γ)
  rwa [min_eq_left ha.le] at h

theorem cap_reaches_iff (h : min a γ = min b γ) : γ ≤ a ↔ γ ≤ b := by
  constructor
  · intro ha
    apply min_eq_right_iff.mp
    exact h.symm.trans (min_eq_right ha)
  · intro hb
    apply min_eq_right_iff.mp
    exact h.trans (min_eq_right hb)

end

/-- Source-side cap agreement transfers through a monotone shifter once the
image of the source cap reaches the output cap. Bottom reflection is unnecessary
for this equation; no preservation of respect is asserted. -/
theorem map_cap_agreement {τ} (hτ : Monotone τ)
    {a b δ γ : ExtOrd} (hab : min a δ = min b δ) (hγ : γ ≤ τ δ) :
    min (τ a) γ = min (τ b) γ := by
  calc
    min (τ a) γ = min (τ (min a δ)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hγ]
    _ = min (τ (min b δ)) γ := by rw [hab]
    _ = min (τ b) γ := by rw [hτ.map_min, min_assoc, min_eq_right hγ]

end VaughtConjecture.Knight.AmbientGradeCharts
