
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.FinalGateLayer
import VaughtConjecture.Knight.FreeDiagonal

/-! # Actual serving charts and activation at the final grade

Availability and the installed parent rows produce a ceiling-leaf chart from
any lawful section and any specified grade-N occurrence. A positive marked node
then forces the serving source's gate field positive. No admission or
synchronization of the arbitrary section is assumed. The one chart retains
every physical coordinate at any external cap below its height.
-/

namespace VaughtConjecture.Knight.FinalGateLayer.Input
open     SourcePrefixLayer
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (I : Input D N X Q)

local notation "below₀" => I.carrier.below (A, N)

abbrev addedAt (a : Q) (marked : Bool) : below₀ :=
  ⟨I.added a marked, by rw [I.added_index]; exact GradedLe.refl _⟩

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow I.rows (A, N)

/-- The bound is forced by locality at the actual node, even at zero weight. -/
theorem node_le_leaf {v : below₀ → ExtOrd}
    (hv : RespectsSemanticsBelow₀ v) (a : Q) (marked : Bool) :
    v (I.addedAt a marked) ≤ v (I.addedAt a false) := by
  apply WeightedSourcePrefixLayer.le_parent I.data I.weight I.weight_visible I.weight_bound
    (GradedLe.refl _) hv (I.controller (a, marked)) (I.controller (a, false))
  · simp_all [VaughtConjecture.Knight.FinalGateLayer.Input.data]
  · simp_all [VaughtConjecture.Knight.FinalGateLayer.Input.weight] <;> aesop

local notation "Witness₀" => Witness (gTop N)

/-- Normalize the locality of one actual ceiling leaf over its whole domain. -/
theorem leaf_chart {v : below₀ → ExtOrd}
    (hv : RespectsSemanticsBelow₀ v) (a : Q) :
    ∃ τ , Witness₀ τ ∧
      (BoundedBy τ (v (I.addedAt a false))) ∧
      ∀ d ,
        τ (I.source a d.1) = min (v d) (v (I.addedAt a false)) := by
  let c := I.addedAt a false
  let self : I.carrier.belowCell c.1 := ⟨c.1, GradedLe.refl _⟩
  
  have hm : ∀ d : I.carrier.belowCell c.1,
      I.carrier.grade d.1 ≤ I.carrier.grade self.1 := fun d => d.2.2
  have hv'  := (hv.orderly c).symm
  have hg : I.carrier.grade self.1 = N := congrArg Prod.snd (I.added_index a false)
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness hm hv' (hv.locality c)
  refine ⟨τ, hg ▸ hτ, hb, ?_⟩
  intro d
  let e : I.carrier.below (I.carrier.cell (I.added a false)) :=
    ⟨d.1, by rw [I.added_index]; exact d.2⟩
  exact (congrArg τ (I.leaf_row a e)).symm.trans (hr e)

/-- Serving one retained owner is sufficient; no global maximum is required. -/
theorem exists_serving_chart {v : below₀ → ExtOrd}
    (hv : RespectsSemanticsBelow₀ v)
    (c : below₀) (hc : I.carrier.grade c.1 = N) (seed : Q) :
    ∃ a , v c ≤ v (I.addedAt a false) ∧
      ∃ τ , Witness₀ τ ∧
        (BoundedBy τ (v (I.addedAt a false))) ∧
        ∀ d ,
          τ (I.source a d.1) = min (v d) (v (I.addedAt a false)) := by
  obtain ⟨e, he, hce⟩ := hv.availability c (I.addedAt seed false)
    (by simpa only [CellScheme.scope,  I.added_index] using c.2.1)
    (by simpa only [CellScheme.grade,  I.added_index] using hc)
  have hei  := he.trans (I.added_index seed false)
  let q : Controller I.carrier N := ⟨e.1, hei⟩
  rcases hm : I.member q with ⟨a, marked⟩
  have heq : e = I.addedAt a marked := by
    apply Subtype.ext
    have hh := (congrArg Subtype.val
      ((SeparatedSourceLayerCarrier.controllerEquiv D (Node ) N
        I.positive I.height I.separated).apply_symm_apply q)).symm
    change e.1 = I.added (I.member q).1 (I.member q).2 at hh
    simpa only [hm] using hh
  refine ⟨a, hce.trans ?_, I.leaf_chart hv a⟩
  rw [heq]
  exact I.node_le_leaf hv a marked

/-- The marked reading detects source activation on every serving leaf. -/
theorem gate_pos_of_chart (a b : Q) {v : below₀ → ExtOrd}
    {τ : LabelMap} (hτ : Witness₀ τ)
    (hr : ∀ d ,
      τ (I.source a d.1) = min (v d) (v (I.addedAt a false)))
    (hh : v (I.addedAt a false) ≠ ⊥) (hz : v (I.addedAt b true) ≠ ⊥) :
    I.fields a I.gate ≠ ⊥ := by
  intro hzero
  have hs  :=
    le_bot_iff.mp ((I.source_marked_le a b).trans_eq hzero)
  have he := hr (I.addedAt b true)
  rw [(hs), hτ.bot] at he
  exact (min_ne_bot hz hh) he.symm

/-- One positive installed node activates a chart serving the retained cap. -/
theorem exists_active_chart {v : below₀ → ExtOrd}
    (hv : RespectsSemanticsBelow₀ v)
    (c : below₀) (hc : I.carrier.grade c.1 = N)
    (hpos : v c ≠ ⊥) (b : Q) (hz : v (I.addedAt b true) ≠ ⊥) :
    ∃ a , v c ≤ v (I.addedAt a false) ∧ I.fields a I.gate ≠ ⊥ ∧
      ∃ τ , Witness₀ τ ∧
        (BoundedBy τ (v (I.addedAt a false))) ∧
        ∀ d ,
          τ (I.source a d.1) = min (v d) (v (I.addedAt a false)) := by
  obtain ⟨a, hca, τ, hτ, hb, hr⟩ := I.exists_serving_chart hv c hc b
  have hh  := fun he =>
    hpos (le_bot_iff.mp (hca.trans_eq he))
  exact ⟨a, hca, I.gate_pos_of_chart a b hτ hr hh hz, τ, hτ, hb, hr⟩

/-- External-cap representation includes all nodes and every predecessor auxiliary. -/
theorem exists_cap_chart {v : below₀ → ExtOrd}
    (hv : RespectsSemanticsBelow₀ v)
    (c : below₀) (hc : I.carrier.grade c.1 = N) (seed : Q)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hreach : γ ≤ v c) :
    ∃ a τ, Witness₀ τ ∧ (BoundedBy τ γ) ∧
      ∀ d , τ (I.source a d.1) = min (v d) γ := by
  obtain ⟨a, hca, τ, hτ, -, hr⟩ := I.exists_serving_chart hv c hc seed
  refine ⟨a, fun x => min (τ x) γ, FreeDiagonal.clip_witness hτ hγ,
    fun _ => min_le_right _ _, ?_⟩
  intro d
  exact (congrArg (fun x => min x γ) (hr d)).trans (by
    grind)

