
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalFieldPrefix
import VaughtConjecture.Knight.CanonicalOwnerBoundary
import VaughtConjecture.Knight.SourcePrefixAmbient
import VaughtConjecture.Knight.RetunedCutDecoding
import VaughtConjecture.Knight.OwnerCap

/-! # Arbitrary-ambient owner lifting on the complete-field lower catalogue

Only the two old faces supply lifting. Unrepresented fields are retained by
`CanonicalFieldPrefix`, so every lower controller's cap survives. The result
initially reads the prescription capped at its owner; grade one will choose
a maximal prescribed owner to obtain literal readback.
-/

namespace VaughtConjecture.Knight.CanonicalFieldOwnerLift
open  Value ExtOrd SharpWitnessComposition CanonicalFieldLayer
open CoatomBoundaryExtension SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A) (hg : BoundedBy D.grade j)

local notation "scheme₀" => scheme sem j X occ hj hA

abbrev target := (scheme₀).below (A, j)

local notation "data₀" => data sem j X occ hj hA hproper hg

abbrev oldTarget (d : Cell D) : target sem j X occ hj hA :=
  SourcePrefixAmbient.occurrence (data₀)
    (old sem j X occ hj hA d)

local notation "oldTarget₀" => oldTarget sem j X occ hj hA hproper hg

theorem oldTarget_grade d :
    (scheme₀).grade (oldTarget₀ d).1 =
      D.grade d := by
  simp only [ SourcePrefixAmbient.occurrence,  CellScheme.grade,
    SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

local notation "source₀" => source sem j X occ hj hA hproper hg

theorem source_short a
    d :
    Short j (source₀ a d) := by
  let F := data₀
  by_cases he : (scheme₀).cell d = (A, j)
  · have hh : source₀ a d ∈ F.grid := by
      change F.profile (controller sem j X occ hj hA a) d ∈ F.grid
      rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ j).1 from rfl, F.profile_new]
      exact cut_mem F.bot_mem _ _
    exact grid_short hh
  · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ)
      j hj hA d he
    rw [source_old]
    exact profile_short a (occ e)

private def seed : Profile sem j X occ := encode hg
  (p := fun _ => ⊥) (RespectsSemantics.bot sem) (fun _ => bot_ne_top)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows sem j X occ hj hA hproper hg) (A, j)

theorem exists_capped_source {q}
    (hq : RespectsSemanticsBelow₀ q)
    (d : target sem j X occ hj hA) (hd : (scheme₀).grade d.1 = j)
    {γ} (hγ : SelfVis j γ) (hactive : γ ≤ q d) :
    ∃ a τ,
      Witness (gTop j) τ ∧ (BoundedBy τ γ) ∧
      ∀ x ,
        τ (source₀ a x.1) = min (q x) γ := by 
  let F := data₀
  let core1 := controller sem j X occ hj hA
  obtain ⟨c, τ, _, hτ, hb, _, hr⟩ := SourcePrefixAmbient.exists_active_source F
    (core1 (seed sem j X occ hg)) hq d hd hγ hactive
  let a := member sem j X occ hj hA hproper c
  have ha : core1 a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv D (Profile sem j X occ) j hj hA
      (SeparatedSourceLayerCarrier.separated_of_proper D j hproper)).apply_symm_apply c
  refine ⟨a, τ, hτ, hb, ?_⟩
  intro x
  change τ (F.profile (core1 a) x.1) = _
  rw [ha]
  exact hr x

theorem exists_owner_capped_lift (hinj : Function.Injective occ)
    c (hc : D.grade c = j)
    {p}
    (hp : Semantics.RowLawful sem c p)
    {q}
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis j γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e , min (p e) γ =
      min (q (oldTarget₀ e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O}
    (hcover : ∀ d , GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d , GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ j) (hV : V.2 ≤ j) :
    ∃ r ,
      RespectsSemanticsBelow₀ r ∧
      (∀ e , r (oldTarget₀ e.1) =
        min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      CappedEq r q γ := by 
  classical
  let _ := Fintype.ofFinite (D.belowCell c)
  subst j
  let F := data sem (D.grade c) X occ hj hA hproper hg
  let M := p ⟨c, GradedLe.refl _⟩
  let pp : BelowLabels D (D.cell c) := fun e => min (p e) M
  have hactive  :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  let core2 := oldTarget sem (D.grade c) X occ hj hA hproper hg
  obtain ⟨a, τ, hτ, hb, ha⟩ := exists_capped_source sem (D.grade c) X occ hj hA hproper hg
    hq (core2 c)
    (oldTarget_grade sem (D.grade c) X occ hj hA hproper hg c) hγ hactive
  let core1 := source sem (D.grade c) X occ hj hA hproper hg a
  let core3 := old sem (D.grade c) X occ hj hA
  have hface (e : D.belowCell c) : τ (a.val (occ e.1)) = min (p e) γ := by
    have he := ha (core2 e.1)
    change τ (core1
      (core3 e.1)) = _ at he
    simp_rw [core1, core3, source_old] at he
    exact he.trans (hag e).symm
  obtain ⟨h, ρ, δ, u, _, _, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ :=
    CanonicalOwnerBoundary.exists_completion a.property.2 a.property.1 hp
      hcover hOU hinter hleft hright hU hV hτ hγ
      (bot_lt_iff_ne_bot.mpr hγb) hb hface hpc
  let tail := 2 * Fintype.card X + 1
  have hroom : h < ofOrd (Ordinal.omega0 * tail) := by
    rw [hBeq]
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (by dsimp [tail]; omega)) _)
  obtain ⟨v, hv, hvt, hvcap, hvface⟩ :=
    exists_topFree_aligned_completion hroom hu
      hg huface
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalFieldPrefix.exists_boundary_section
    sem (D.grade c) X occ hj hA hproper hg hinj a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact ((hvcap d).trans (hucap d)).symm)
  have hwcap' (d) : min (w d) h =
      min (core1 d) h := by
    rw [hBeq]; exact hwcap d
  apply RetunedCutDecoding.decode_lift
    ((F.profile_respects (controller sem (D.grade c) X occ hj hA a)).toBelow _)
    (hw.toBelow _) hq (fun d => F.max_grade d.1) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem (D.grade c) X occ hj hA hproper hg a d.1)).trans
      ((min_eq_left (hb _)).trans (ha d))
  · intro e
    change min (pp e) δ = min (ρ (core1
      (core3 e.1))) δ
    simp_rw [core3, core1, source_old]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => core1 d.1) ∘
        fun e : D.belowCell c => core2 e.1) =
        fun e => a.val (occ e.1) := by
      funext e
      exact source_old sem (D.grade c) X occ hj hA hproper hg a e.1
    rw [hs]
    change w (core3 e.1) = _
    simp_rw [core3, hwold, hvface e, huface] <;> rfl

