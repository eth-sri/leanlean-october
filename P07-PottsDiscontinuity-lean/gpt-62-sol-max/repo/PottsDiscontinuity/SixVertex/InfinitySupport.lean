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

/-- Up arrows form an independent set of the cyclic row. -/
def NoConsecutiveUp (x : Finset (Fin N)) : Prop := ∀ i ∈ x, nxt i ∉ x

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
  have hyi := hd.notMem_of_mem_left_finset hix
  have hyni := hd.notMem_of_mem_left_finset hnix
  have h1 := hf i
  have h2 := hf (nxt i)
  have hp : prv (nxt i) = i := (finRotate N).symm_apply_apply i
  rw [hp] at h2
  simp only [hix, hnix, hyi, hyni, decide_true, decide_false, toInt,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  omega

/-- Every nonzero matrix entry joins two states with no consecutive up arrows. -/
theorem infinityBlock_support (hn : 0 < n) (x y : State N n)
    (h : infinityBlock N n x y ≠ 0) : NoConsecutiveUp x.1 ∧ NoConsecutiveUp y.1 := by
  have h1 : infinityBlock N n x y = 1 := by
    unfold infinityBlock at h ⊢
    split_ifs at * <;> simp_all
  obtain ⟨hi, hd⟩ := (infinityBlock_eq_one_iff hn x y).1 h1
  exact ⟨noConsecutiveUp_of_interlaced_disjoint hi hd,
    noConsecutiveUp_of_interlaced_disjoint hi.symm hd.symm⟩


end PottsDiscontinuity.SixVertex
