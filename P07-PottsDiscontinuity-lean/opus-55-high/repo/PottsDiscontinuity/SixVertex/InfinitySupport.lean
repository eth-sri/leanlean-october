module

public import PottsDiscontinuity.SixVertex.InfinityLimit
public import PottsDiscontinuity.SixVertex.RowTransfer

/-!
# Support of the infinite-anisotropy block

The no-consecutive-up-arrow reduction in Lemma 3.2, including the cyclic seam.
We use the already proved row flux equation rather than an informal interlacing picture.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

section
variable (x : Finset (Fin N))
/-- Up arrows form an independent set of the cyclic row. -/
def NoConsecutiveUp  : Prop := ∀ i ∈ x, nxt i ∉ x

/-- Down arrows preceded by another down arrow, including the seam of the cycle. -/
def defects  : Finset (Fin N) :=
  univ.filter fun i => i ∉ x ∧ prv i ∉ x
end

/-- An interlaced pair admits horizontal arrows satisfying the row ice rule. -/
theorem exists_flux_of_interlaced {x y : Finset (Fin N)} (hi : Interlaced x y) :
    ∃ h : Fin N → Bool, Flux x y h := by
  cases N with
  | zero => exact ⟨fun _ => false, fun i => Fin.elim0 i⟩
  | succ k =>
    rcases (interlaced_iff_validS x y).1 hi with hs | hs
    · exact ⟨hOf x y false, flux_hOf hs⟩
    · exact ⟨hOf x y true, flux_hOf hs⟩


/-- Disjoint interlaced states cannot have adjacent up arrows, even across `N-1 | 0`. -/
theorem noConsecutiveUp_of_interlaced_disjoint {x y : Finset (Fin N)}
    (hi : Interlaced x y) (hd : Disjoint x y) : NoConsecutiveUp x := by
  obtain ⟨h, hf⟩ := exists_flux_of_interlaced hi
  intro i hix hnix
  have h1 := hf i
  have h2 := hf (nxt i)
  have hp : prv (nxt i) = i := by grind
  rw [hp] at h2
  simp only [hix, hnix, (hd.notMem_of_mem_left_finset hix), (hd.notMem_of_mem_left_finset hnix), decide_true, decide_false, toInt,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  omega

section
variable (hn : 0 < n) (x y : State N n)
include hn
/-- Every nonzero matrix entry joins two states with no consecutive up arrows. -/
theorem infinityBlock_support (h : infinityBlock N n x y ≠ 0) : NoConsecutiveUp x.1 ∧ NoConsecutiveUp y.1 := by
  have h1 : infinityBlock N n x y = 1 := by
    grind [infinityBlock]
  obtain ⟨hi, hd⟩ := (infinityBlock_eq_one_iff hn x y).1 h1
  exact ⟨noConsecutiveUp_of_interlaced_disjoint hi hd,
    noConsecutiveUp_of_interlaced_disjoint hi.symm hd.symm⟩

theorem infinityBlock_eq_zero_of_not_noConsecutiveUp (hx : ¬ NoConsecutiveUp x.1) : infinityBlock N n x y = 0 := by
  grind [infinityBlock_support]
end

/-- The range of the limit operator is supported on the independent row states. -/
theorem infinityBlock_mulVec_supported (hn : 0 < n) (v : State N n → ℝ)
    (x : State N n) (hx : ¬ NoConsecutiveUp x.1) :
    (infinityBlock N n *ᵥ v) x = 0 := by
  simp_all [Matrix.mulVec, dotProduct, infinityBlock_eq_zero_of_not_noConsecutiveUp]

/-- Up arrows and their cyclic successors are disjoint. -/
theorem NoConsecutiveUp.disjoint_image {x : Finset (Fin N)} (hx : NoConsecutiveUp x) :
    Disjoint x (x.image nxt) := by
  apply disjoint_left.mpr
  aesop

/-- Defects are precisely the complement of the up arrows and their successors. -/
theorem defects_eq_compl (x : Finset (Fin N)) :
    defects x = (x ∪ x.image nxt)ᶜ := by
  ext i
  have he : i ∈ x.image nxt ↔ prv i ∈ x := by
    grind
  simp_all [defects]

section
variable (x : State N n) (hx : NoConsecutiveUp x.1)
include x hx
/-- There are exactly `N - 2n` defects in a state without consecutive up arrows. -/
theorem card_defects  :
    (defects x.1).card = N - 2 * n := by
  rw [defects_eq_compl, card_compl, card_union_of_disjoint hx.disjoint_image,
    card_image_of_injective _ (finRotate N).injective, x.2, Fintype.card_fin]
  omega

/-- The source's `2r` defect count, with subtraction-free particle-number premises. -/
theorem card_defects_eq_two_mul {r : ℕ} (hN : N = 2 * (n + r)) : (defects x.1).card = 2 * r := by
  grind [card_defects]
end

end PottsDiscontinuity.SixVertex
