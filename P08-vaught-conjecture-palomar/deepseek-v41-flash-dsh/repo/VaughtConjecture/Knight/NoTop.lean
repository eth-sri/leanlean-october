/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import VaughtConjecture.TypeTower.Slot

/-! # No countable model of `S^{ω₁}` (Knight, Lemma 11.1.1)

The Knight instance of the cardinal slot bound `TypeTower/Slot.lean` (#44; experiment A1,
`docs/DESIGN.md`).  Knight's Lemma 11.1.1 says that `S^{ω₁}` has no countable model; the
argument uses only covering (Def. 3.2.1(3)), the Uniformity clause (Def. 3.2.1(4)(b)) and counting,
so it is proved here
in the generalised form **every model of `S^{ω₁}` has carrier of size at least `ℵ₁`**
(`IsModel.aleph_one_le_mk_carrier`), with the countable case as the corollary
(`IsModel.not_countable_carrier`).

* The **bands** are the Uniformity intervals `[γ, γ + ω)` for non-successor `γ` (`band γ`);
  for distinct non-successors they are pairwise disjoint (`band_pairwise_disjoint`: a
  non-successor above `γ` is at least `γ + ω`, since both are multiples of `ω`).
* The **index set** is the non-successors below `ω₁` (`UniformityIndex`), of size at least `ℵ₁`
  (`aleph_one_le_mk_uniformityIndex`: the block levels `blockLevel ξ = ω + ω·ξ`, `ξ < ω₁`, inject
  into it).
* The **slots** over a realization are the pairs (labelled injective tuple `t`, cell of the type
  realized at `t`) — `SlotData (R.eval t)`, countable per tuple — with value the realized label
  of that cell (`slotLabel`).
* **Uniformity supplies the witnesses**: the empty tuple is an initial segment of some labelled
  tuple `s` (covering), and for each non-successor `γ < ω₁` clause (4)(b) realizes over `s` a
  type with a cell labelled in `[γ, γ + ω)` (`IsModel.exists_slot_mem_band`).

The generic theorem `lift_mk_le_max_aleph0_carrier_of_forall_exists_slot` then gives
`ℵ₁ ≤ #UniformityIndex ≤ max ℵ₀ #M`, i.e. `ℵ₁ ≤ #M`.  No Knight-specific cardinal argument
and no separate infinitude argument is needed; the carrier universe is arbitrary.  (Knight-VC:
`PaperExactWeakMarkerNonexistence.no_countable_core_uniformity_model_at_aleph1_ord`, stated
for countable carriers only.) -/

@[expose] public section

open Cardinal Ordinal

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe u

/-! ### The stage `ω₁` -/



/-! ### Uniformity bands -/


/-! ### The index set: non-successors below `ω₁` -/

/-- The block levels below `ω₁` stay below `ω₁` (`card (ω + ω·ξ) = ℵ₀ + ℵ₀·card ξ < ℵ₁`). -/
theorem blockLevel_lt_ord_aleph_one {ξ : Ordinal.{0}} (hξ : ξ < (aleph 1).ord) :
    blockLevel ξ < (aleph 1).ord := by
  rw [lt_ord] at hξ ⊢
  unfold blockLevel
  rw [card_add, card_mul, card_omega0]
  exact add_lt_of_lt (aleph0_le_aleph 1) aleph0_lt_aleph_one
    (mul_lt_of_lt (aleph0_le_aleph 1) aleph0_lt_aleph_one hξ)

/-! ### Slots: a labelled tuple together with a cell of its realized type -/

section Slot

variable {α : Ordinal.{0}} {n : ℕ}

end Slot

variable {M : Type u}

namespace KnightRealization

variable {α : LimitStage} {R : KnightRealization α M}

end KnightRealization

end VaughtConjecture.Knight
