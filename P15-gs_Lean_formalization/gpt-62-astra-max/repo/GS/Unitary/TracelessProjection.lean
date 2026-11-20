module

public import GS.Unitary.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Real-Frobenius projection onto supported traceless skew-Hermitian matrices.
Masks in this module contain every diagonal entry; this is essential for the
trace correction to preserve support. No special-unitary quotient claim is made. -/
noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem trace_skewHermitian_conj {A : CMat n} (hA : IsSkewHermitian A) :
    star A.trace = -A.trace := by
  rw [← Matrix.trace_conjTranspose, hA, Matrix.trace_neg]

theorem tracelessPart_trace (A : CMat n) : (tracelessPart A).trace = 0 := by
  by_cases hn : n=0
  · subst n; simp [Matrix.trace]
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [tracelessPart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      div_mul_cancel₀ _ hc]

theorem tracelessPart_fixed {A : CMat n} (hA : A.trace = 0) : tracelessPart A = A := by
  simp [tracelessPart, hA]

theorem tracelessPart_isSkewHermitian {A : CMat n} (hA : IsSkewHermitian A) :
    IsSkewHermitian (tracelessPart A) := by
  have ht := trace_skewHermitian_conj hA
  change Aᴴ = -A at hA
  simp only [tracelessPart, IsSkewHermitian, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_div₀, star_natCast,
    ht, hA, neg_div, neg_smul]
  abel

def maskedTracelessSkewHermitian (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : CMat n) : CMat n := tracelessPart (maskedSkewHermitian p A)

theorem tracelessPart_hasSupport {p : Fin n → Fin n → Prop}
    (hp : ∀ i, p i i) {A : CMat n} (hA : CHasSupport p A) :
    CHasSupport p (tracelessPart A) := by
  intro i j hij
  have hne : i ≠ j := by intro he; subst j; exact hij (hp i)
  simp [tracelessPart, Matrix.one_apply, hne, hA i j hij]

theorem maskedTracelessSkewHermitian_mem {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A : CMat n) :
    CHasSupport p (maskedTracelessSkewHermitian p A) ∧
    IsSkewHermitian (maskedTracelessSkewHermitian p A) ∧
    (maskedTracelessSkewHermitian p A).trace=0 := by
  exact ⟨tracelessPart_hasSupport hdiag (maskedSkewHermitian_hasSupport _ _),
    tracelessPart_isSkewHermitian (maskedSkewHermitian_isSkewHermitian hp A),
    tracelessPart_trace _⟩

theorem maskedTracelessSkewHermitian_fixed {p : Fin n → Fin n → Prop} [DecidableRel p]
    {A : CMat n} (hs : CHasSupport p A) (hk : IsSkewHermitian A) (ht : A.trace=0) :
    maskedTracelessSkewHermitian p A = A := by
  rw [maskedTracelessSkewHermitian, maskedSkewHermitian_fixed hs hk, tracelessPart_fixed ht]

@[simp] theorem maskedTracelessSkewHermitian_idempotent
    {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (hdiag : ∀ i, p i i) (A : CMat n) :
    maskedTracelessSkewHermitian p (maskedTracelessSkewHermitian p A) =
      maskedTracelessSkewHermitian p A := by
  obtain ⟨hs,hk,ht⟩ := maskedTracelessSkewHermitian_mem hp hdiag A
  exact maskedTracelessSkewHermitian_fixed hs hk ht

end GS.UnitaryGeometry
