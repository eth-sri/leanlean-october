
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalFieldLayer
import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Prefix completion on the actual canonical lower layer

Unrepresented fields remain part of the normalization inventory and of every
controller agreement cut. A repaired physical boundary is extended to those
fields by retaining their old source values, not by dropping them.
-/

namespace VaughtConjecture.Knight.CanonicalFieldPrefix
open   ExtOrd SourcePrefixRows CanonicalFieldLayer
open CanonicalPairedInverse PairedSlotEncoding


variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A) (hg : BoundedBy D.grade j)

local notation "controller₀" => controller sem j X occ hj hA

local notation "scheme₀" => scheme sem j X occ hj hA

local notation "source₀" => source sem j X occ hj hA hproper hg

local notation "grid₀" => grid j

theorem exists_section (a : Profile sem j X occ)
    {p} (hp : RespectsSemantics sem (p ∘ occ)) (ht : AvoidsValue p ⊤)
    {B} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : CappedEq a.val p (grid₀ B)) :
    ∃ r ,
      RespectsSemantics (rows sem j X occ hj hA hproper hg) r ∧
      (∀ d, r (old sem j X occ hj hA d) = p (occ d)) ∧
      ∀ d, min (r d) (grid₀ B) =
        min (source₀ a d) (grid₀ B) := by
  let F := data sem j X occ hj hA hproper hg
  let b := encode hg hp ht
  have hb : CappedEq b.val a.val (grid₀ B) :=
    CanonicalPairedProfiles.normalize_cap a.property.2 hag
  have hgrid : grid₀ B ∈ PairedSlotComparison.sourceGrid j (Fintype.card X) :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hs := source_prefix sem j X occ hj hA hproper hg b a hgrid hb
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    exists_supported_inverse a.property.2 ht hag
  have hfixGrid : ∀ z ∈ PairedSlotComparison.sourceGrid j (Fintype.card X),
      z < grid₀ B → κ z = z := by
    
    intro z hz hzB
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw.bot
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
      apply hfix n
      by_contra hn
      have hBn  := Nat.le_of_not_gt hn
      exact (not_le_of_gt hzB) (ofOrd_le_ofOrd.mpr
        (add_le_add (by gcongr) le_rfl))
  have hfixBoundary (x : X) (hx : a.val x < grid₀ B) : κ (a.val x) = a.val x := by
    have hba := eq_of_cap_eq_lt (hb x).symm hx
    have hpa := eq_of_cap_eq_lt (hag x) hx
    exact (congrArg κ hba).trans ((hread x).trans hpa.symm)
  have hfixSource (d : Cell scheme₀)
      (hd : source₀ a d < grid₀ B) :
      κ (source₀ a d) =
        source₀ a d := by
    by_cases he : (scheme₀).cell d = (A, j)
    · have hh : source₀ a d ∈ F.grid := by
        change F.profile (controller₀ a) d ∈ F.grid
        rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ j).1 from rfl,
          F.profile_new]
        exact cut_mem F.bot_mem _ _
      exact hfixGrid _ hh hd
    · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ)
        j hj hA d he
      rw [source_old] at hd ⊢
      exact hfixBoundary (occ e) hd
  have hcaps : ∀ d, min (κ (source₀ b d)) (grid₀ B) =
      min (source₀ a d) (grid₀ B) := by
    apply hs.decode hw.mono monotone_id hreach le_rfl
    intro d hd
    have he := eq_of_cap_eq_lt (hs d) hd
    rw [he, hfixSource d (he ▸ hd)]
    rfl
  have hr := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    ((F.profile_respects (controller₀ b)).toBelow (A, j))
    ((F.profile_respects (controller₀ a)).toBelow (A, j))
    (fun d => F.max_grade d.1) (SharpWitnessComposition.boundedMap_of_witness hw)
    (ofOrd_ne_bot _) (fun d => hcaps d.1)
  refine ⟨fun d => κ (source₀ b d),
    hr.toRespects (fun d => ⟨(scheme₀).scope_subset d, F.max_grade d⟩), ?_, hcaps⟩
  intro d
  dsimp only
  rw [source_old]
  exact hread (occ d)

/-- Completion of physical occurrences, with all other fields retained before
normalization. Injectivity is occurrence injectivity, not label injectivity. -/
theorem exists_boundary_section (hinj : Function.Injective occ) (a : Profile sem j X occ)
    {p} (hp : RespectsSemantics sem p) (ht : AvoidsValue p ⊤)
    {B} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : ∀ d, min (a.val (occ d)) (grid₀ B) = min (p d) (grid₀ B)) :
    ∃ r ,
      RespectsSemantics (rows sem j X occ hj hA hproper hg) r ∧
      (∀ d, r (old sem j X occ hj hA d) = p d) ∧
      ∀ d, min (r d) (grid₀ B) =
        min (source₀ a d) (grid₀ B) := by
  
  let v := Function.extend occ p a.val
  have hv (d : Cell D) : v (occ d) = p d := hinj.extend_apply p a.val d
  have hvp : RespectsSemantics sem (v ∘ occ) := by
    aesop
  have hvt : AvoidsValue v ⊤ := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · aesop
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
      exact a.property.2.2 x
  have hva : CappedEq a.val v (grid₀ B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · grind
    · aesop
  obtain ⟨r, hr, hread, hcap⟩ := exists_section sem j X occ hj hA hproper hg
    a hvp hvt hB hva
  exact ⟨r, hr, fun d => (hread d).trans (hv d), hcap⟩


