/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.ProjectiveBox

/-! Primitive integral representatives of rational projective points. -/

namespace CCDN
noncomputable section

section
variable {n : ℕ} (x : ProjectivePoint n)

/-- Every rational projective point is spanned by a nonzero integer vector whose coordinates have
gcd `1`. -/
theorem exists_primitive_projective_rep :
    ∃ (z : IntPoint (n + 1)) (hz : z ≠ 0), Finset.univ.gcd z = 1 ∧
      Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz) = x := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) x.rep
  choose u hu using hb
  have hb0 : b.val ≠ 0 := by simp_all
  have huQ (i : Fin (n + 1)) : (u i : ℚ) = b.val * x.rep i := by simp_all
  have hu0 : u ≠ 0 := by
    intro h
    apply x.rep_nonzero
    funext i
    simp_all
  obtain ⟨z, hz, hprim⟩ := Finset.extract_gcd u
    (show (Finset.univ : Finset (Fin (n + 1))).Nonempty from Finset.univ_nonempty)
  have hzg (i : Fin (n + 1)) : u i = Finset.univ.gcd u * z i :=
    hz i (Finset.mem_univ i)
  refine ⟨z, (by
    intro h
    apply hu0
    funext i
    simp_all), hprim, ?_⟩
  have hgQ : ((Finset.univ.gcd u : ℤ) : ℚ) ≠ 0 := mod_cast (by
    intro h
    apply hu0
    funext i
    simp_all)
  have he : rationalPoint z =
      ((b.val : ℚ) / (Finset.univ.gcd u : ℤ)) • x.rep := by
    funext i
    have hi := huQ i
    rw [hzg i, Int.cast_mul] at hi
    change (z i : ℚ) = (b.val / (Finset.univ.gcd u : ℤ)) * x.rep i
    apply (mul_left_cancel₀ hgQ)
    rw [hi]
    field_simp
  calc
    _ = Projectivization.mk ℚ x.rep x.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      grind
    _ = x := x.mk_rep

/-- A chosen primitive integer representative of the projective point `x`: a nonzero integer
vector with coprime coordinates spanning `x`. -/
def primitiveProjectiveRep : IntPoint (n + 1) :=
  (exists_primitive_projective_rep x).choose

/-- The primitive integer representative of a projective point is nonzero. -/
lemma primitiveProjectiveRep_ne_zero :
    primitiveProjectiveRep x ≠ 0 :=
  (exists_primitive_projective_rep x).choose_spec.choose

/-- The coordinates of the primitive integer representative of a projective point have gcd `1`. -/
lemma primitiveProjectiveRep_gcd :
    Finset.univ.gcd (primitiveProjectiveRep x) = 1 :=
  (exists_primitive_projective_rep x).choose_spec.choose_spec.1

/-- The primitive integer representative of `x` spans `x`. -/
lemma primitiveProjectiveRep_mk :
    Projectivization.mk ℚ (rationalPoint (primitiveProjectiveRep x))
      (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x)) = x :=
  (exists_primitive_projective_rep x).choose_spec.choose_spec.2

end

/-- Distinct projective points have distinct primitive integer representatives. -/
theorem primitiveProjectiveRep_injective {n : ℕ} :
    Function.Injective (primitiveProjectiveRep (n := n)) := by
  intro x y h
  have hQ := congrArg rationalPoint h
  calc
    x = Projectivization.mk ℚ (rationalPoint (primitiveProjectiveRep x))
      (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x)) :=
        (primitiveProjectiveRep_mk x).symm
    _ = Projectivization.mk ℚ (rationalPoint (primitiveProjectiveRep y))
      (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero y)) := by
        congr 1
    _ = y := primitiveProjectiveRep_mk y

variable {n : ℕ} (x : ProjectivePoint n)

theorem primitiveProjectiveRep_height :
    x.mulHeight = ((⨆ i, |primitiveProjectiveRep x i| : ℤ) : ℝ) := by
  have h := projective_height_primitive _ (primitiveProjectiveRep_ne_zero x)
    (primitiveProjectiveRep_gcd x)
  rwa [primitiveProjectiveRep_mk] at h

/-- Every coordinate of the primitive integer representative of `x` has absolute value at most the
multiplicative height of `x`. -/
theorem primitiveProjectiveRep_bound
    (i : Fin (n + 1)) :
    |(primitiveProjectiveRep x i : ℝ)| ≤ x.mulHeight := by
  rw [primitiveProjectiveRep_height, ← Int.cast_abs]
  exact_mod_cast (le_ciSup (Finite.bddAbove_range (fun j => |primitiveProjectiveRep x j|)) i)

