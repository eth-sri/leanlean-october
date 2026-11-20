module

public import PottsDiscontinuity.SixVertex.InfinitySupport
public import PottsDiscontinuity.SixVertex.Irreducible

/-!
# Moves on independent row states

Rotation is a genuine positive edge of the limiting matrix. The finite carrier
here is exactly the independent row configurations, with no extra conditions.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- The actual nonzero-support carrier of the infinite-anisotropy block. -/
abbrev IndependentState (N n : ℕ) := {x : State N n // NoConsecutiveUp x.1}

/-- The restriction of the limit matrix to row states with no adjacent up arrows. -/
noncomputable def infinityRestriction (N n : ℕ) :
    Matrix (IndependentState N n) (IndependentState N n) ℝ :=
  (infinityBlock N n).submatrix Subtype.val Subtype.val

/-- Rotate all up arrows one site to the right. -/
def rotateUp (x : Finset (Fin N)) : Finset (Fin N) := x.image nxt

@[simp] theorem mem_rotateUp (x : Finset (Fin N)) (i : Fin N) :
    i ∈ rotateUp x ↔ prv i ∈ x := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    simpa only [prv, nxt, Equiv.symm_apply_apply] using hj
  · intro hi
    exact mem_image.mpr (by grind)

@[simp] theorem card_rotateUp (x : Finset (Fin N)) : (rotateUp x).card = x.card :=
  card_image_of_injective _ (finRotate N).injective

theorem NoConsecutiveUp.rotateUp {x : Finset (Fin N)} (hx : NoConsecutiveUp x) :
    NoConsecutiveUp (rotateUp x) := by
  intro i hi hni
  rw [mem_rotateUp] at hi hni
  exact hx _ hi (by grind)

/-- Rotation of an independent state. -/
def rotateIndependent (x : IndependentState N n) : IndependentState N n :=
  ⟨⟨rotateUp x.1.1, (card_rotateUp _).trans x.1.2⟩, x.2.rotateUp⟩

/-- The converse to the interlacing-to-flux bridge, including the empty cycle. -/
theorem interlaced_of_flux {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) : Interlaced x y := by
  cases N with
  | zero =>
    have hy : y = x := Subsingleton.elim _ _
    rw [hy]
    exact interlaced_refl _
  | succ k =>
    have hs := validS_of_flux hf
    apply (interlaced_iff_validS _ _).mpr
    cases he : h (Fin.last k)
    · grind
    · grind

/-- A row and its one-site rotation interlace, regardless of adjacent up arrows. -/
theorem interlaced_rotateUp (x : Finset (Fin N)) : Interlaced x (rotateUp x) := by
  apply interlaced_of_flux (h := fun i => decide (i ∈ x))
  intro i
  simp

/-- Every independent state has a positive rotation edge. -/
theorem infinityRestriction_rotate (hn : 0 < n) (x : IndependentState N n) :
    infinityRestriction N n x (rotateIndependent x) = 1 := by
  apply (infinityBlock_eq_one_iff hn x.1 _).mpr
  exact ⟨interlaced_rotateUp x.1.1, x.2.disjoint_image⟩

end PottsDiscontinuity.SixVertex
