/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.PrivateRowFactorization

@[expose] public section

namespace VaughtConjecture.Knight.FinalGateLayer.Input

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]

variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (I : Input D N X Q)

theorem master_eq_source (q : SourcePrefixLayer.Controller I.carrier N) (d : Cell I.carrier) :
    WeightedSourcePrefixLayer.master I.data I.weight q d = I.source (I.member q).1 d := by
  unfold source WeightedSourcePrefixLayer.master ScopedSourcePrefixLayer.Data.profile
  simp only [data, SourceAttachment.data, SourceAttachment.member_controller]
  rfl

variable (hsupport : ∀ a d, D.grade d ≤ N →
  OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))

include hsupport in
/-- All marked columns are included, regardless of whether they are selected. -/
theorem decode_source_prefix (a b : Q) {h : ExtOrd} (hh : h ∈ I.grid) (hpos : h ≠ ⊥)
    (hag : Agree (I.fields b) (I.fields a) h)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop N) ν) (hreach : h ≤ ν h)
    (hgrid : ∀ z ∈ I.grid, z < h → ν z = z)
    (hfields : ∀ x, I.fields a x < h → ν (I.fields a x) = I.fields a x) :
    RespectsSemanticsBelow I.rows (A, N) (fun d => ν (I.source b d.1)) ∧
      ∀ d : I.carrier.below (A, N),
        min (ν (I.source b d.1)) h = min (I.source a d.1) h :=
  OrbitPrefixSupport.decode_respects_of_positive_cut hν
    (I.source_lawful a) (I.source_lawful b) (fun d => d.2.2)
    (I.grid_visible h hh) hpos hreach hgrid hfields
    (fun d => I.source_supported hsupport a d.1 d.2.2) (I.source_prefix b a hh hag)

variable (hfields : ∀ a x, Short N (I.fields a x))

variable (hgrid : ∀ z ∈ I.grid, Short N z)

include hsupport hfields hgrid in
theorem source_short (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    Short N (I.source a d) := by
  rcases I.source_supported hsupport a d hd with hz | hg | ⟨x, i, hi, he⟩
  · exact Or.inl hz
  · exact hgrid _ hg
  · rw [he]
    exact PrivateRowFactorization.short_replace (hfields a x) le_rfl hi

include hsupport hfields hgrid in
/-- Shortness is asserted only for the new owners, at their own grade. -/
theorem added_row_short (q : SourcePrefixLayer.Controller I.carrier N)
    (d : I.carrier.below (I.carrier.cell q.1)) : Short N (I.rows.E q.1 d) := by
  rw [WeightedSourcePrefixLayer.row_new, I.master_eq_source]
  have hs := I.source_short hsupport hfields hgrid (I.member q).1 d.1
    (by simpa only [CellScheme.grade, q.2] using d.2.2)
  rcases le_total (I.source (I.member q).1 d.1) (I.weight q) with h | h
  · rwa [min_eq_left h]
  · rw [min_eq_right h]
    rcases I.weight_kind q with hw | ⟨x, hw⟩
    · rw [hw]; exact hgrid _ I.ceiling_mem
    · rw [hw]; solve_by_elim

include hsupport hfields hgrid in
/-- Long predecessor rows use their independently established decoded lawfulness;
only the new own-grade-short rows use repaired witness composition. -/
theorem decoded_respects (a : Q) {ν : ExtOrd → ExtOrd} (hν : Witness (gTop N) ν)
    (hlower : RespectsSemanticsBelow I.sem (A, N) (fun d => ν (I.lower a d.1))) :
    RespectsSemanticsBelow I.rows (A, N) (fun d => ν (I.source a d.1)) := by
  apply map_respects_of_short_or_local (I.source_lawful a) (fun d => d.2.2) hν
  intro c
  by_cases hc : I.carrier.cell c.1 = (A, N)
  · left
    intro d
    change Short (I.carrier.cell c.1).2 (I.rows.E c.1 d)
    rw [hc]
    exact I.added_row_short hsupport hfields hgrid ⟨c.1, hc⟩ d
  · right
    obtain ⟨x, hx⟩ := I.attachment.old_occurrence hc
    have hxc : GradedLe (D.cell x) (A, N) := by
      simpa only [hx, I.old_index] using c.2
    have ho : RespectsSemanticsBelow I.rows (I.carrier.cell (I.old x))
        (fun d => ν (I.source a d.1)) := by
      apply (WeightedSourcePrefixLayer.old_respects_iff I.data I.weight I.weight_visible
        (I.attachment.old_not_full x)).mpr
      apply (I.attachment.base_respects x (fun d => ν (I.source a d))).mpr
      simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
        I.source_old, CellScheme.below.mono] using hlower.mono hxc
    rcases c with ⟨c, hcl⟩
    dsimp only at hx
    subst c
    exact ho.locality ⟨I.old x, GradedLe.refl _⟩

end

end VaughtConjecture.Knight.FinalGateLayer.Input
