/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedAmbient
public import VaughtConjecture.Knight.CanonicalMixedPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # An arbitrary-ambient active-owner lift on the canonical carrier

Availability constructs the ambient source; owner locality constructs alignment;
the two old faces construct a boundary completion. A finite clipping ceiling
makes that coded boundary proper without changing its prescription or source
caps. The canonical supported-prefix operator extends it over BOTH controller
layers, then retuned decoding preserves every original ambient cap.

The conclusion reads the prescribed face capped at its owner. Literal readback
therefore follows when that owner dominates the face. Larger prescribed lower-
grade values remain a separate restoration obligation.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalMixedOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CanonicalMixedGradeLayers CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)
  (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
  (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

abbrev oldTarget (d : Cell D) : CanonicalMixedAmbient.target sem j hj hjA k hk hkA :=
  SourcePrefixAmbient.occurrence (data sem j hj hjA hproper k hg hk hkA hjk)
    (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d))

theorem oldTarget_grade (d : Cell D) :
    (scheme sem j hj hjA k hk hkA).grade
      (oldTarget sem j hj hjA hproper k hg hk hkA hjk d).1 = D.grade d := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).grade
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d)))) = _
  simp only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem exists_owner_capped_lift (c : Cell D) (hc : D.grade c = k)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ =
      min (q (oldTarget sem j hj hjA hproper k hg hk hkA hjk e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ k) (hV : V.2 ≤ k) :
    ∃ r : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      (∀ e : D.below (D.cell c),
        r (oldTarget sem j hj hjA hproper k hg hk hkA hjk e.1) =
          min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  have hactive : γ ≤ q (oldTarget sem j hj hjA hproper k hg hk hkA hjk c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hbound, hambient⟩ :=
    CanonicalMixedAmbient.exists_capped_source sem j hj hjA hproper k hg hk hkA hjk hq
      (oldTarget sem j hj hjA hproper k hg hk hkA hjk c)
      ((oldTarget_grade sem j hj hjA hproper k hg hk hkA hjk c).trans hc) hγ hactive
  let F := data sem j hj hjA hproper k hg hk hkA hjk
  exact RetunedCutDecoding.owner_capped_lift id c hc hg hp hq (fun d => F.max_grade d.1)
    (oldTarget sem j hj hjA hproper k hg hk hkA hjk) hγ hγb hag hpc
    hcover hcU hOU hOV hinter hleft hright hU hV
    a.property.2 a.property.1 hτ hbound
    ((F.profile_respects (controller sem j hj hjA k hk hkA a)).toBelow _)
    (source_short sem j hj hjA hproper k hg hk hkA hjk a)
    (source_boundary sem j hj hjA hproper k hg hk hkA hjk a)
    hambient fun hv hvt _ hB hva => by
      obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalMixedPrefix.exists_section sem j hj hjA hproper
        k hg hk hkA hjk a hv hvt hB hva
      exact ⟨w, hw.toBelow _, hwold, hwcap⟩
