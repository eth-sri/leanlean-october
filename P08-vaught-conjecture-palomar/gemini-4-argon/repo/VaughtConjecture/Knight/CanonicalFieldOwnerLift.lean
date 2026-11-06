/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.SourcePrefixAmbient
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # Arbitrary-ambient owner lifting on the complete-field lower catalogue

Only the two old faces supply lifting. Unrepresented fields are retained by
`CanonicalFieldPrefix`, so every lower controller's cap survives. The result
initially reads the prescription capped at its owner; grade one will choose
a maximal prescribed owner to obtain literal readback.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalFieldOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CanonicalFieldLayer CoatomBoundaryExtension SourcePrefixRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)
  (hj : 0 < j) (hA : j ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)

abbrev target := (scheme sem j X occ hj hA).below (A, j)

abbrev oldTarget (d : Cell D) : target sem j X occ hj hA :=
  SourcePrefixAmbient.occurrence (data sem j X occ hj hA hproper hg)
    (old sem j X occ hj hA d)

local notation "K" => scheme sem j X occ hj hA
local notation "dat" => data sem j X occ hj hA hproper hg
local notation "Rws" => rows sem j X occ hj hA hproper hg
local notation "src" => source sem j X occ hj hA hproper hg
local notation "ctrl" => controller sem j X occ hj hA
local notation "oldT" => oldTarget sem j X occ hj hA hproper hg

theorem source_short (a : Profile sem j X occ) (d : Cell K) : Short j (src a d) := by
  by_cases he : CellScheme.cell K d = (A, j)
  · exact grid_short j X (by
      change SourcePrefixLayer.Data.profile dat _ _ ∈ _
      rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ j).1 from rfl,
        SourcePrefixLayer.Data.profile_new]
      exact cut_mem (SourcePrefixLayer.Data.bot_mem dat) _ _)
  · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA d he
    rw [source_old]
    exact profile_short sem j X occ a (occ e)

theorem exists_capped_source {q : target sem j X occ hj hA → ExtOrd}
    (hq : RespectsSemanticsBelow Rws (A, j) q)
    (d : target sem j X occ hj hA) (hd : CellScheme.grade K d.1 = j)
    {γ : ExtOrd} (hγ : SelfVis j γ) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem j X occ) (τ : ExtOrd → ExtOrd),
      Witness (gTop j) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : target sem j X occ hj hA, τ (src a x.1) = min (q x) γ := by
  obtain ⟨c, τ, hτ, hb, hr⟩ := SourcePrefixAmbient.exists_active_source dat
    (ctrl (encode sem j X occ hg (p := fun _ => ⊥) (RespectsSemantics.bot sem) (fun _ => bot_ne_top)))
    hq d hd hγ hactive
  have ha : ctrl (member sem j X occ hj hA hproper c) = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv D (Profile sem j X occ) j hj hA
      (SeparatedSourceLayerCarrier.separated_of_proper D j hproper)).apply_symm_apply c
  refine ⟨member sem j X occ hj hA hproper c, τ, hτ, hb, fun x => ?_⟩
  change τ (SourcePrefixLayer.Data.profile dat (ctrl (member sem j X occ hj hA hproper c)) x.1) = _
  rw [ha]
  exact hr x

theorem exists_owner_capped_lift (hinj : Function.Injective occ)
    (c : Cell D) (hc : D.grade c = j)
    {p : D.below (D.cell c) → ExtOrd} (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : target sem j X occ hj hA → ExtOrd} (hq : RespectsSemanticsBelow Rws (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ = min (q (oldT e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ j) (hV : V.2 ≤ j) :
    ∃ r : target sem j X occ hj hA → ExtOrd,
      RespectsSemanticsBelow Rws (A, j) r ∧
      (∀ e : D.below (D.cell c), r (oldT e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  have hactive : γ ≤ q (oldT c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hb, ha⟩ := exists_capped_source sem j X occ hj hA hproper hg hq (oldT c)
    (by simpa only [oldTarget, SourcePrefixAmbient.occurrence, old, CellScheme.grade,
      SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hc) hγ hactive
  exact RetunedCutDecoding.owner_capped_lift occ c hc hg hp hq
    (fun d => (SourcePrefixLayer.Data.max_grade dat) d.1) oldT hγ hγb hag hpc
    hcover hcU hOU hOV hinter hleft hright hU hV
    a.property.2 a.property.1 hτ hb
    ((SourcePrefixLayer.Data.profile_respects dat (ctrl a)).toBelow _)
    (source_short sem j X occ hj hA hproper hg a)
    (source_old sem j X occ hj hA hproper hg a)
    ha fun hv hvt _ hB hva => by
      obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalFieldPrefix.exists_boundary_section
        sem j X occ hj hA hproper hg hinj a hv hvt hB hva
      exact ⟨w, hw.toBelow _, hwold, hwcap⟩
