/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrdinaryFinalRepair
import VaughtConjecture.Knight.MixedRowDecoding

/-! # Independent private bottom-cap supply on the ordinary final layer

The ordinary private fibre supplies a gate-off admitted vector for an arbitrary
lawful private prescription. Terminal insertion gives a catalogue member and
decoder with finite original-field bottom reflection. Mixed-row decoding proves
lawfulness on the actual physical carrier; no positive external cap, ambient
completion, or output bountifulness is used. Literal tops are allowed.

The scope predecessor's short-new/original-long classification is explicit,
as in the actual-display construction. Every marked gate, not just the selected
one, is bottom in the constructed section.
-/

namespace VaughtConjecture.Knight.OrdinaryFinalBottom
open   ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue


variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- Arbitrary private data, including literal top, has a lawful physical
extension with every marked gate off. No ambient or positive cap is required. -/
theorem exists_private_display
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d , Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.belowCell c.1, ∃ f , F.lower a d.1 = a.val f))
    (priv : Cell C.scheme ↪ Cell D)
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    {p : BelowLabels C.scheme (effC N N)}
    (hp : RespectsSemanticsBelow C.rows (effC N N) p) :
    ∃ b δ,
      Witness (gTop N) δ ∧
      RespectsSemanticsBelow F.rows (A, N) (fun d => δ (F.source b d.1)) ∧
      (∀ d , δ (F.source b (F.old (priv d.1))) = p d) ∧
      ∀ a , δ (F.source b (F.added a true)) = ⊥ := by
  obtain ⟨a, ha, hprivate, hgateOff, -⟩ := bottom_supply (R := R) hp
  obtain ⟨b₀, _, _, hprefix, _, hadm, hcan, δ, hδ, hread⟩ := ha.exists_terminal 0
  let b : OrdinaryFinalCatalogue.Member R := ⟨PairedSlotEncoding.normalize N b₀, hcan, hadm⟩
  have hreflect (f : Field P C) : δ (b.val f) = ⊥ ↔ b.val f = ⊥ := by
    
    rw [hread, PairedSlotEncoding.normalize_bot_iff]
    exact (bottom_pattern_of_cap_agreement (ofOrd_ne_bot 0) hprefix f).symm
  have hlower  := by
    apply map_respects_of_short_or_reflecting (F.lower_lawful b) (fun d => d.2.2) hδ
    intro c
    rcases howners b c with hs | ho
    · exact Or.inl hs
    · refine Or.inr ?_
      intro d
      obtain ⟨f, hf⟩ := ho d
      change δ (F.lower b d.1) = ⊥ ↔ F.lower b d.1 = ⊥
      rw [hf]
      exact hreflect f
  have hshort : ∀ a f, Short N (F.fields a f) := by
    intro a f
    rw [hfields]
    exact member_short R a f
  refine ⟨b, δ, hδ, F.decoded_respects hsupport hshort hgrid b hδ hlower, ?_, ?_⟩
  · intro d
    rw [F.source_old, hpriv]
    exact (hread (.priv d.1)).trans (hprivate d)
  · intro a'
    apply le_bot_iff.mp
    have hh := hδ.mono (F.source_marked_le b a')
    rw [hgate, hfields, hread, hgateOff] at hh
    exact hh


