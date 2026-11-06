
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalCodingSupport
import VaughtConjecture.Knight.HighGradeSource
import VaughtConjecture.Knight.HighLayerBountiful

/-! # A coded, active maximal full-scope apex

The mute-base transport follows the integration lane's `MuteFullLayer` proof.
The actual output is not mute: the high-grade source constructor gives its
apex literal top while retaining the entire old lawful display and all old rows.
-/

namespace VaughtConjecture.Knight.MaximalFullLayer
open Transform Value  AmalgamationPlan SourceLayerCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
  (sem : Semantics D) (K l : ℕ) (hK : BoundedBy D.grade K)
  (hKl : K < l) (hlA : l ≤ A.card)

variable {K l} in
abbrev positive : 0 < l := (Nat.zero_le K).trans_lt hKl
abbrev separated := HighLayerBountiful.separated D l K hK hKl
abbrev scheme := SourceLayerCarrier.scheme D Unit l (positive hKl) hlA
local notation "toCell₀" => toCell D Unit l (positive hKl) hlA

abbrev old d := toCell₀ (.inl d)
local notation "scheme₀" => scheme D K l hKl hlA

abbrev apex : Cell (scheme₀) :=
  toCell₀ (.inr ())
local notation "separated₀" => separated D K l hK hKl

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D Unit l
  (positive hKl) hlA (separated₀)
abbrev base := SeparatedSourceLayerCarrier.base D Unit l
  (positive hKl) hlA (separated₀) sem

local notation "old₀" => old D K l hKl hlA

variable {D K l} in
theorem old_index d : (scheme₀).cell (old₀ d) =
    D.cell d := cell_toCell _ _ _ _ _ _
local notation "apex₀" => apex D K l hKl hlA

variable {K l} in
theorem apex_index : (scheme₀).cell (apex₀) = (A, l) :=
  cell_toCell _ _ _ _ _ _

local notation "base₀" => base D sem K l hK hKl hlA

local notation "ownerEquiv₀" => ownerEquiv D K l hK hKl hlA

variable {D sem K l hK hKl hlA} in
theorem inherited_row c d :
    (base₀).E (old₀ c)
      (ownerEquiv₀ c d) = sem.E c d :=
  SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d

local notation "inherited_row₀" => inherited_row

theorem consistent (hs : sem.IsConsistent) : (base₀).IsConsistent := by
  intro c
  obtain ⟨x, rfl⟩ := (enumeration).surjective c
  change RespectsSemanticsBelow base₀
    ((scheme₀).cell (toCell₀ x))
    ((base₀).E (toCell₀ x))
  cases x with
  | inl c =>
    apply (SeparatedSourceLayerCarrier.base_respects_iff separated₀ sem c _).mpr
    have he : (base₀).E (old₀ c) ∘
        ownerEquiv₀ c = sem.E c :=
      funext (inherited_row₀ c)
    rw [he]
    exact hs c
  | inr u =>
    have he : (base₀).E
        (toCell₀ (.inr u)) = fun _ => ⊥ := by
      simp_all [SeparatedSourceLayerCarrier.base, SeparatedSourceLayerCarrier.oldTable]
    rw [he]
    refine ⟨fun _ => (extVisibilityReplace_bot _ _).symm, ?_,
      fun _ b _ _ => ⟨b, rfl, le_rfl⟩⟩
    intro b
    simpa only [min_self] using TransformsTo.to_bot

def bountiful (hpos : 0 < K) (hb : sem.IsBountiful) :=
  HighLayerBountiful.bountiful D Unit l (positive hKl) hlA K hK hKl sem
    (base₀) (inherited_row₀) hpos hb

theorem coded (hc : sem.IsCoded) : (base₀).IsCoded := by
  apply CanonicalCodingSupport.layer hc inherited_row₀
  intro u d
  apply Or.inl
  simp  [ SeparatedSourceLayerCarrier.base, 
    SeparatedSourceLayerCarrier.oldTable]

variable {D K l} in
variable {hKl hlA} in
theorem complete (hc : ∀ J ∈ Plan.gradedPlan D.plan, J ≠ (A, l) → ∃ d, D.cell d = J) :
    (scheme₀).IsComplete := by
  intro J hJ
  by_cases he : J = (A, l)
  · grind only [apex_index]
  · obtain ⟨d, hd⟩ := hc J hJ he
    exact ⟨old₀ d, (old_index hKl hlA d).trans hd⟩

/-- All old labels, not just either face separately, remain literal. -/
theorem exists_active (hk : 1 ≤ K) (hc : sem.IsConsistent) (hb : sem.IsBountiful)
    (hcode : sem.IsCoded) {p} (hp : RespectsSemantics sem p) :
    ∃ out q,
      out.IsConsistent ∧ out.IsBountiful ∧ out.IsCoded ∧ RespectsSemantics out q ∧
      (∀ c d, out.E (old₀ c) (ownerEquiv₀ c d) = sem.E c d) ∧
      (PointwiseEq (q ∘ old₀) p) ∧ q (apex₀) = ⊤ := by
  have hsep : ¬ GradedLe (A, l) (A, K) := fun h => (not_le_of_gt hKl) h.2
  let e := HighLayerBountiful.equiv D Unit l (positive hKl) hlA (A, K) hsep
  let low : (scheme₀).below (A, K) → ExtOrd := fun d => p (e.symm d).1
  have hlaw  :=
    (HighLayerBountiful.respects_iff D Unit l (positive hKl) hlA K hK hKl sem
      (base₀) (inherited_row₀)
      (A, K) hsep (fun d => p d.1)).mp (hp.toBelow (A, K))
  have hg : (scheme₀).grade (apex₀) = l :=
    congrArg Prod.snd (apex_index D hKl hlA)
  have hs  :=
    congrArg Prod.fst (apex_index D hKl hlA)
  obtain ⟨out, q, hoc, hob, hcod, hq, he, hread, htop⟩ :=
    HighGradeExtension.exists_extension base₀
      apex₀ (by rw [hg]; exact hKl) hs low hlaw ⊤
      rfl hk
      (consistent D sem K l hK hKl hlA hc)
      (bountiful D sem K l hK hKl hlA (Nat.zero_lt_of_lt hk) hb)
      (coded D sem K l hK hKl hlA hcode)
  refine ⟨out, q, hoc, hob, hcod, hq, ?_, ?_, htop⟩
  · intro c d
    rw [he _ (by change ((scheme₀).cell _).2 ≤ K
                 rw [old_index]; exact hK c)]
    exact inherited_row₀ c d
  · intro d
    let dlow : D.below (A, K) := ⟨d, D.scope_subset d, hK d⟩
    have hh := hread (e dlow)
    dsimp  [low] at hh
    rw [e.symm_apply_apply] at hh
    exact hh

