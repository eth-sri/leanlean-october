/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.DirectedNat
public import VaughtConjecture.JumpClosedCore

@[expose] public section

namespace VaughtConjecture.DirectedFiniteJump

open Filter JumpClosed

universe u v

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  {J : Type v} [Finite J]

omit [IsDirectedOrder I] in
private theorem eventually_approximates_coordinate (f : I → ℕ) (hf : Monotone f) (K : ℕ) :
    ∀ᶠ i in atTop,
      ((⨆ a, (f a : ℕ∞)) ≠ ⊤ → (f i : ℕ∞) = ⨆ a, (f a : ℕ∞)) ∧
      ((⨆ a, (f a : ℕ∞)) = ⊤ → (K : ℕ∞) < f i) := by
  by_cases hr : (⨆ a, (f a : ℕ∞)) = ⊤
  · obtain ⟨a, ha⟩ := lt_iSup_iff.mp (hr ▸ ENat.natCast_lt_top K)
    filter_upwards [eventually_ge_atTop a] with i hai
    exact ⟨by lia,
      fun _ => ha.trans_le (ENat.natCast_le_natCast.mpr (hf hai))⟩
  · obtain ⟨a, ha⟩ := ENat.exists_eq_iSup_of_lt_top (lt_top_iff_ne_top.mpr hr)
    filter_upwards [eventually_ge_atTop a] with i hai
    exact ⟨fun _ => le_antisymm (le_iSup (fun a => (f a : ℕ∞)) i)
      (ha ▸ ENat.natCast_le_natCast.mpr (hf hai)), by lia⟩

/-- Above any base, all finite-coordinate attainments and infinite-coordinate
escapes hold together on one common tail. -/
theorem exists_approximates_iSup_above (f : J → I → ℕ) (hf : ∀ j, Monotone (f j))
    (K : ℕ) (base : I) :
    ∃ i : I, base ≤ i ∧ ∀ a, i ≤ a →
      Approximates K (fun j => (f j a : ℕ∞)) (fun j => ⨆ b, (f j b : ℕ∞)) :=
  DirectedNat.synchronize _ (fun j => eventually_approximates_coordinate (f j) (hf j) K) base

/-- One sufficiently large cutoff reconstructs the completed vector on a
tail. The cutoff bounds every finite completed coordinate simultaneously. -/
theorem exists_eventually_jump_eq_iSup (f : J → I → ℕ) (hf : ∀ j, Monotone (f j))
    (K0 : ℕ) :
    ∃ K : ℕ, K0 ≤ K ∧ ∀ᶠ i in atTop,
      jump K (fun j => (f j i : ℕ∞)) = (fun j => ⨆ a, (f j a : ℕ∞)) := by
  classical
  let := Fintype.ofFinite J
  let r : J → ℕ∞ := fun j => ⨆ a, (f j a : ℕ∞)
  let B : ℕ := Finset.univ.sup fun j => (r j).toNat
  let K : ℕ := max K0 B
  have hK : ∀ j, r j ≠ ⊤ → r j ≤ K := by
    intro j hj
    rw [← ENat.natCast_toNat hj]
    exact ENat.natCast_le_natCast.mpr
      ((Finset.le_sup (f := fun j => (r j).toNat) (Finset.mem_univ j)).trans (le_max_right K0 B))
  obtain ⟨i, _, hi⟩ := exists_approximates_iSup_above f hf K (Classical.arbitrary I)
  exact ⟨K, le_max_left K0 B,
    eventually_atTop.mpr ⟨i, fun a hia => jump_eq_of_approximates (hi a hia) hK⟩⟩

/-- The cutoff is independent of the requested base index; the reconstructing
finite observation can always be chosen above that base. -/
theorem exists_jump_eq_iSup_above (f : J → I → ℕ) (hf : ∀ j, Monotone (f j)) (K0 : ℕ) :
    ∃ K : ℕ, K0 ≤ K ∧ ∀ i0 : I, ∃ i : I, i0 ≤ i ∧
      jump K (fun j => (f j i : ℕ∞)) = (fun j => ⨆ a, (f j a : ℕ∞)) := by
  obtain ⟨K, hK, h⟩ := exists_eventually_jump_eq_iSup f hf K0
  obtain ⟨base, hbase⟩ := eventually_atTop.mp h
  refine ⟨K, hK, fun i0 => ?_⟩
  obtain ⟨i, hi0, hi⟩ := exists_ge_ge i0 base
  tauto

/-- A predicate preserved by every jump above `K0` passes from all finite
observations to the completed vector. No topological closedness is assumed. -/
theorem predicate_iSup_of_jump (f : J → I → ℕ) (hf : ∀ j, Monotone (f j)) (K0 : ℕ)
    (P : (J → ℕ∞) → Prop)
    (hjump : ∀ K : ℕ, K0 ≤ K → ∀ z : J → ℕ∞, P z → P (jump K z))
    (hfinite : ∀ i : I, P (fun j => (f j i : ℕ∞))) :
    P (fun j => ⨆ i, (f j i : ℕ∞)) := by
  obtain ⟨K, hK, h⟩ := exists_jump_eq_iSup_above f hf K0
  obtain ⟨i, _, hi⟩ := h (Classical.arbitrary I)
  rw [← hi]
  solve_by_elim

end VaughtConjecture.DirectedFiniteJump
