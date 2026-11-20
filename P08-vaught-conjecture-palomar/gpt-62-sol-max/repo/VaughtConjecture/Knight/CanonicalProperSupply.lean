/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.PositiveNormalization

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D E : CellScheme A} {K : ℕ}
  {sem : Semantics D} {rows : Semantics E}

/-- A supply of sections for proper labels also supplies sections for arbitrary
labels, by extending a proper coded representative and decoding it. -/
theorem RespectsSemanticsBelow.supply_from_proper
    {p : D.below (A, K) → ExtOrd} (hp : RespectsSemanticsBelow sem (A, K) p)
    (embed : D.below (A, K) → E.below (A, K))
    (supply : ∀ {v : Cell D → ExtOrd}, RespectsSemantics sem v → (∀ d, v d ≠ ⊤) →
      ∃ w : E.below (A, K) → ExtOrd, RespectsSemanticsBelow rows (A, K) w ∧
        ∀ d, w (embed d) = v d.1) :
    ∃ r : E.below (A, K) → ExtOrd, RespectsSemanticsBelow rows (A, K) r ∧
      ∀ d, r (embed d) = p d := by
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ := hp.exists_coded_representative (fun d => d.2.2) le_rfl
  have ht : ∀ d, CellScheme.zeroAbove u d ≠ ⊤ := CellScheme.complete_cases
    (P := fun _ x => x ≠ ⊤) (fun d => by
      rcases mem_codedAlphabet_iff.mp (hcode d) with hb | ⟨b, i, _, _, he⟩ <;> simp_all)
    (fun _ _ => bot_ne_top)
  obtain ⟨w, hw, hread⟩ := supply hu.zeroAbove ht
  refine ⟨canonicalDecoder S K ∘ w, hw.decoded S (fun d => d.2.2), ?_⟩
  intro d
  simpa [Function.comp_apply, hread, CellScheme.zeroAbove_low] using hdecode d

end VaughtConjecture.Knight
