/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows
public import VaughtConjecture.AmalgamationPlan.Plan
public import VaughtConjecture.Knight.Domain
public import Mathlib.Logic.Equiv.Fin.Basic
public import VaughtConjecture.Knight.SharpWitnessComposition
public import VaughtConjecture.Knight.ReceivingCatalogueIncidences
public import VaughtConjecture.Knight.FullScopeBountiful

@[expose] public section

namespace VaughtConjecture.Knight.ReceivingCutDecoder

open Transform Value ExtOrd SharpWitnessComposition FullRowLifting

noncomputable section

/-- A finite visible ordered table plus its actual separating cut constructs
the clipped chart. No prescribed values are required at unused source points. -/
theorem exists_chart {X : Type*} [Finite X] {s v : X → ExtOrd} {δ γ : ExtOrd}
    (hs : ∀ f, SelfVis 1 (s f)) (hv : ∀ f, SelfVis 1 (v f))
    (hδ : SelfVis 1 δ) (hδb : δ ≠ ⊥) (hγ : SelfVis 1 γ)
    (hord : ∀ f g, s f ≤ s g → v f ≤ v g)
    (hbot : ∀ f, s f = ⊥ → v f = ⊥)
    (hcut : ∀ f, s f < δ ↔ v f < γ) :
    ∃ τ, BoundedMap 1 τ ∧ τ δ = γ ∧ ∀ f, τ (s f) = min (v f) γ := by
  let : Fintype X := Fintype.ofFinite X
  let E : Option X → ExtOrd := fun d => d.elim δ s
  let t : Option X → ExtOrd := fun d => d.elim γ (fun f => min (v f) γ)
  have hE : ∀ d, SelfVis 1 (E d) := by
    intro d
    cases d with
    | none => exact hδ
    | some f => exact hs f
  have ht : ∀ d, SelfVis 1 (t d) := by
    intro d
    cases d with
    | none => exact hγ
    | some f => grind
  have horder : ∀ d e, E d ≤ E e → t d ≤ t e := by
    intro d e h
    cases d with
    | none =>
      cases e with
      | none => exact le_rfl
      | some f =>
        grind
    | some f =>
      cases e with
      | none => exact min_le_right _ _
      | some g => aesop
  have hzero : ∀ d, E d = ⊥ → t d = ⊥ := by
    intro d hd
    cases d with
    | none => trivial
    | some f => aesop
  refine ⟨orderInterpolate E t, orderInterpolate_bounded hE ht,
    orderInterpolate_read horder hzero none, fun f => orderInterpolate_read horder hzero (some f)⟩

/-- Extending the clipped chart only needs bounded commutation. This does
not claim the literal function composite is a faithful witness. -/
theorem extend_bounded (S : Finset Ordinal.{0}) {b : ℕ} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (hτ : BoundedMap 1 τ) (hγ : SelfVis 1 γ) :
    BoundedMap 1 (PaddedSourceDecoder.extend S 1 b τ γ) := by
  apply PairedSlotIncoming.bounded_max
  · refine ⟨by rw [hτ.bot, min_bot_left], fun _ _ h => min_le_min_right _ (hτ.mono h), ?_⟩
    intro x k i hk hi
    rw [hτ.comm x k i hk hi, evr_min_of_selfVis hγ hk hi]
  · exact (PaddedSourceDecoder.witness_release
      (isStepShifter_canonicalDecoder (S := S) (K := 1)).normalizedWitness b).bounded

end

end VaughtConjecture.Knight.ReceivingCutDecoder
