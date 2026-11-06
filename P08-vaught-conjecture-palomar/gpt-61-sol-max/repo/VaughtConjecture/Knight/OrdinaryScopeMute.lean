
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.MaximalFullLayer
import VaughtConjecture.Knight.HighLayerSections
import VaughtConjecture.Knight.OrbitSupportSubstitution

/-! # Completing an ordinary scope with a mute highest owner

Use the existing zero-row high layer, not its active-apex modification. The
renderer is specified on every occurrence: old values remain literal and the
only new value is bottom. Thus one external grid and original support inventory
survive scope completion unchanged. The predecessor's bountifulness is consumed;
no bountifulness of a prospective output is assumed.
-/

namespace VaughtConjecture.Knight.OrdinaryScopeMute
open    SourceLayerCarrier SourcePrefixRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
  (sem : Semantics D) (K l : ℕ) (hK : BoundedBy D.grade K)
  (hKl : K < l) (hlA : l ≤ A.card)

abbrev carrier := MaximalFullLayer.scheme D K l hKl hlA
abbrev old := MaximalFullLayer.old D K l hKl hlA
abbrev apex := MaximalFullLayer.apex D K l hKl hlA
abbrev rows := MaximalFullLayer.base D sem K l hK hKl hlA

local notation "carrier₀" => carrier D K l hKl hlA

def render (p : CellLabels D) : CellLabels (carrier₀) :=
  fun d => Sum.elim p (fun _ => ⊥)
    (toOcc D Unit l (MaximalFullLayer.positive hKl) hlA d)

local notation "old₀" => old D K l hKl hlA

local notation "render₀" => render D K l hKl hlA

theorem render_old p d :
    render₀ p (old₀ d) = p d := by
  simp  [render,    ]

local notation "apex₀" => apex D K l hKl hlA

theorem render_apex p :
    render₀ p (apex₀) = ⊥ := by
  simp  [render,    ]

theorem covered d :
    (∃ c, d = old₀ c) ∨ d = apex₀ := by
  obtain ⟨x, rfl⟩ := (enumeration).surjective d
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr u => cases u; exact Or.inr rfl

local notation "rows₀" => rows D sem K l hK hKl hlA

theorem render_lawful {p} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows₀) (render₀ p) := by
  obtain ⟨r, hr, hold, hnew⟩ := HighLayerBountiful.exists_zero_tail D Unit l
    (MaximalFullLayer.positive hKl) hlA K hK hKl sem
    rows₀ (MaximalFullLayer.inherited_row) hp
  have he : render₀ p = r := by
    funext d
    rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
    · simp_all [render_old]
    · exact (render_apex D K l hKl hlA p).trans (hnew ()).symm
  exact he.symm ▸ hr

theorem render_bound {p} {θ} (hp : BoundedBy p θ)
    d : render₀ p d ≤ θ := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact bot_le

/-- All cut equations survive, not just equations at represented fields. -/
theorem render_agreement {p q} {γ} (hpq : Agree p q γ) :
    Agree (render D K l hKl hlA p) (render D K l hKl hlA q) γ := by
  intro d
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · simp_all [render_old] <;> aesop
  · simp  [render_apex]

/-- No new grid point or supporting original field is introduced. -/
theorem render_supported {X : Type*} {v : X → ExtOrd} {k} {G}
    {p} (hp : ∀ d, OrbitPrefixSupport.Supported k G v (p d))
    d :
    OrbitPrefixSupport.Supported k G v (render₀ p d) := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact Or.inl rfl

theorem apex_row d :
    (rows₀).E (apex₀) d = ⊥ := by simp_all [SeparatedSourceLayerCarrier.base, SeparatedSourceLayerCarrier.oldTable]

theorem apex_short d :
    SharpWitnessComposition.Short l ((rows₀).E
      (apex₀) d) := by
  rw [apex_row]
  exact Or.inl rfl

theorem inherited_row c d :
    (rows₀).E (old₀ c)
      (MaximalFullLayer.ownerEquiv D K l hK hKl hlA c d) = sem.E c d :=
  MaximalFullLayer.inherited_row c d

/-- Existing short-row receipts transport, but inherited long rows are allowed. -/
theorem inherited_short c
    (hc : ∀ d , SharpWitnessComposition.Short (D.grade c) (sem.E c d))
    d :
    SharpWitnessComposition.Short ((carrier₀).grade (old₀ c))
      ((rows₀).E (old₀ c) d) := by
  obtain ⟨e, rfl⟩ := (MaximalFullLayer.ownerEquiv D K l hK hKl hlA c).surjective d
  rw [inherited_row]
  simpa only [CellScheme.grade,   cell_toCell, index] using hc e

theorem consistent (hs : sem.IsConsistent) : (rows₀).IsConsistent :=
  MaximalFullLayer.consistent D sem K l hK hKl hlA hs

theorem coded (hs : sem.IsCoded) : (rows₀).IsCoded :=
  MaximalFullLayer.coded D sem K l hK hKl hlA hs

theorem bountiful (hpos : 0 < K) (hs : sem.IsBountiful) :
    (rows₀).IsBountiful :=
  MaximalFullLayer.bountiful D sem K l hK hKl hlA hpos hs

theorem complete (hs : ∀ J ∈ AmalgamationPlan.Plan.gradedPlan D.plan,
    J ≠ (A, l) → ∃ d, D.cell d = J) : (carrier₀).IsComplete :=
  MaximalFullLayer.complete hs

/-- When the one missing level is the scope cardinality, there are no missing
proper indices at that level. This discharges the apex-completeness ledger. -/
theorem complete_last (hcard : A.card = l) (hnext : l = K + 1)
    (hs : ∀ J ∈ AmalgamationPlan.Plan.gradedPlan D.plan, J.2 ≤ K → ∃ d, D.cell d = J) :
    (carrier₀).IsComplete := by
  apply complete D K l hKl hlA
  intro J hJ hne
  apply hs J hJ
  have hmem := AmalgamationPlan.Plan.mem_gradedPlan.mp hJ
  have hgrade := hmem.2.2
  have hsub := D.isPlan.subset_of_mem hmem.1
  have hc := Finset.card_le_card hsub
  by_contra hn
  have hj : J.2 = l := by omega
  have he  := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hne (Prod.ext he hj)

