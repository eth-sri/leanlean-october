/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreeDiagonal

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
  read : ∀ d : D.below (D.cell owner.1),
    shift (sem.E owner.1 d) = min (q (CellScheme.below.incl owner d)) (q owner)

namespace Chart

variable {k : ℕ} (C : Chart sem BJ q k)

theorem grade : D.grade C.owner.1 = k := congrArg Prod.snd C.index

/-- Every occurrence of grade at most `k` lies below this full-scope owner. -/
def occurrence (d : D.below BJ) (hd : D.grade d.1 ≤ k) : D.below (D.cell C.owner.1) :=
  ⟨d.1, by rw [C.index]; exact ⟨d.2.1, hd⟩⟩

theorem read_capped (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd)) = min (q d) (q C.owner) :=
  C.read (C.occurrence d hd)

/-- Exact readback on the owner's grade, including all its sibling controllers. -/
theorem read_grade (d : D.below BJ) (hd : D.grade d.1 = k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd.le)) = q d := by
  rw [C.read_capped, min_eq_left (C.dominates d hd)]

/-- If this grade's maximum reaches the external cap, its one witness recovers
the externally capped labels at every lower grade as well. -/
theorem read_under_cap {γ : ExtOrd} (hactive : γ ≤ q C.owner)
    (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    min (C.shift (sem.E C.owner.1 (C.occurrence d hd))) γ = min (q d) γ := by
  rw [C.read_capped, min_assoc, min_eq_right hactive]

end Chart

/-- One full-scope controller suffices to make the maximizing set nonempty.
Availability, not a cross-grade domination assumption, supplies the final bound. -/
theorem exists_maximizer (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k) ∧
      ∀ d : D.below BJ, D.grade d.1 = k → q d ≤ q c := by
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
  have hgrade : D.grade d.1 = D.grade c.1 := by simp_all
  obtain ⟨e, he, hde⟩ := hq.availability d c hscope hgrade
  grind

/-- Extract an actual bounded faithful witness; bottom and literal top need no exclusion. -/
theorem exists_chart (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    Nonempty (Chart sem BJ q k) := by
  obtain ⟨c, hc, hmax⟩ := exists_maximizer hq hfull
  obtain ⟨τ, hτ, -, hr⟩ := hq.rowWitness c
  have hg : D.grade c.1 = k := congrArg Prod.snd hc
  exact ⟨⟨c, hc, hmax, τ, hg ▸ hτ, hr⟩⟩

/-- Read a maximizing chart from a parametrized family of full rows. -/
theorem exists_chart_of_rows {U : Type*} {k : ℕ} {q : D.below (A, k) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (A, k) q) (a₀ : U) (leaf : U → Cell D)
    (index : ∀ a, D.cell (leaf a) = (A, k))
    (cover : ∀ c, D.cell c = (A, k) → ∃ a, c = leaf a)
    (source : U → Cell D → ExtOrd)
    (row : ∀ a (d : D.below (D.cell (leaf a))), sem.E (leaf a) d = source a d.1) :
    ∃ a σ M, Witness (gTop k) σ ∧ (∀ d, D.grade d.1 = k → q d ≤ M) ∧
      ∀ d, σ (source a d.1) = min (q d) M := by
  obtain ⟨H⟩ := exists_chart hq ⟨⟨leaf a₀, (index a₀).symm ▸ GradedLe.refl _⟩, index a₀⟩
  obtain ⟨a, ha⟩ := cover H.owner.1 H.index
  have hr (c : Cell D) (hc : c = leaf a) (d : D.below (D.cell c)) :
      sem.E c d = source a d.1 := by
    subst c
    exact row a d
  exact ⟨a, H.shift, q H.owner, H.witness, H.dominates, fun d =>
    (congrArg H.shift (hr _ ha (H.occurrence d d.2.2))).symm.trans (H.read_capped d d.2.2)⟩

/-- The literal part of a cap equation; this statement also applies at cap top. -/
theorem eq_of_cap_below {a b γ : ExtOrd} (h : min a γ = min b γ) (hb : b < γ) : a = b := by grind

theorem cap_reaches_iff {a b γ : ExtOrd} (h : min a γ = min b γ) : γ ≤ a ↔ γ ≤ b := by aesop

/-- Source-side cap agreement transfers through a monotone shifter once the
image of the source cap reaches the output cap. Bottom reflection is unnecessary
for this equation; no preservation of respect is asserted. -/
theorem map_cap_agreement {τ : ExtOrd → ExtOrd} (hτ : Monotone τ)
    {a b δ γ : ExtOrd} (hab : min a δ = min b δ) (hγ : γ ≤ τ δ) :
    min (τ a) γ = min (τ b) γ := by
  calc
    min (τ a) γ = min (τ (min a δ)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hγ]
    _ = min (τ (min b δ)) γ := by rw [hab]
    _ = min (τ b) γ := by rw [hτ.map_min, min_assoc, min_eq_right hγ]

end VaughtConjecture.Knight.AmbientGradeCharts
