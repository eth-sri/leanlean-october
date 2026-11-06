/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteProfileRefinement

/-! # Finite normalized profile families with a preserved algebraic contract

`OrderLaw` records the properties of a class of lawful grade-one labellings
used by source refinement. `family` constructs a whole joint controller
family and proves those properties again for its output. These are row-layer
properties, not a support plan, mixed-grade bountifulness, or request forcing.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.NormalizedProfileFamily

open Transform Value ExtOrd SlotControllerFamily
open SlotPatternRefinement (mix)

/-- The algebraic input contract for finite source-profile saturation. Its
fields are proved for the constructed output below, not supplied anew. -/
structure OrderLaw (X : Type*) where
  holds : (X → ExtOrd) → Prop
  bottom : holds (fun _ => ⊥)
  visible : ∀ {p}, holds p → ∀ d, SelfVis 1 (p d)
  order : ∀ {p r}, holds p → (∀ d, SelfVis 1 (r d)) →
    (∀ d, p d = ⊥ → r d = ⊥) → (∀ d e, p d ≤ p e → r d ≤ r e) → holds r
  refine : ∀ {q b : X → ℕ} {a : ℕ}, 0 < a →
    holds (fun d => value (q d)) → holds (fun d => value (b d)) →
    (∀ d e, q d < a → a ≤ q e → b d < b e) → holds (fun d => value (mix q b a d))

variable {X : Type*} [Fintype X]

open Classical in
noncomputable def code (p : X → ExtOrd) (d : X) : ℕ :=
  if p d = ⊥ then 0 else FreshSourceSlots.rank p d + 1

theorem code_le (p : X → ExtOrd) (d : X) : code p d ≤ Fintype.card X := by
  classical
  have h := FreshSourceSlots.rank_lt_card p d
  unfold code
  split_ifs <;> omega

theorem code_zero (p : X → ExtOrd) (d : X) : code p d = 0 ↔ p d = ⊥ := by
  classical
  simp [code]

theorem code_order (p : X → ExtOrd) (d e : X) : code p d ≤ code p e ↔ p d ≤ p e := by
  classical
  by_cases hd : p d = ⊥
  · simp [code, hd]
  by_cases he : p e = ⊥
  · simp [code, hd, he]
  simp only [code, hd, he, ↓reduceIte, Nat.add_le_add_iff_right]
  exact FreshSourceSlots.rank_le_iff p d e

theorem value_code_bot (p : X → ExtOrd) (d : X) : value (code p d) = ⊥ ↔ p d = ⊥ := by
  rw [← le_bot_iff, show (⊥ : ExtOrd) = value 0 from rfl, value_le_iff,
    Nat.le_zero, code_zero]
  rfl

theorem rank_encoded (p : X → ExtOrd) (d : X) :
    FreshSourceSlots.rank (fun e => value (code p e)) d = FreshSourceSlots.rank p d := by
  classical
  unfold FreshSourceSlots.rank
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_iff_not_ge,
    value_le_iff, code_order]

theorem code_idempotent (p : X → ExtOrd) (d : X) :
    code (fun e => value (code p e)) d = code p d := by
  classical
  change (if value (code p d) = ⊥ then 0 else
    FreshSourceSlots.rank (fun e => value (code p e)) d + 1) = code p d
  simp only [value_code_bot, rank_encoded]
  rfl

variable (L : OrderLaw X)

theorem encoded_lawful {p : X → ExtOrd} (hp : L.holds p) :
    L.holds (fun d => value (code p d)) := by
  apply L.order hp (fun _ => value_visible _)
  · intro d hd
    rw [(code_zero p d).mpr hd]
    rfl
  · intro d e hde
    exact value_mono ((code_order p d e).mpr hde)

def Profile := {p : X → Fin (Fintype.card X + 1) //
  L.holds (fun d => value (p d).val) ∧ ∀ d, code (fun e => value (p e).val) d = (p d).val}

instance : Finite (Profile L) := by unfold Profile; infer_instance
noncomputable instance : Fintype (Profile L) := Fintype.ofFinite (Profile L)

noncomputable def encode {p : X → ExtOrd} (hp : L.holds p) : Profile L :=
  ⟨fun d => ⟨code p d, Nat.lt_succ_of_le (code_le p d)⟩,
    encoded_lawful L hp, code_idempotent p⟩

instance : Nonempty (Profile L) := ⟨encode L L.bottom⟩

end VaughtConjecture.Knight.NormalizedProfileFamily
