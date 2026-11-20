/- Actual related-triple transport to native compact Albert automorphisms.
This file does not assume or prove universal existence of a related triple.
-/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.Obligations
public import Mathlib.Data.Real.Sqrt

@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem octNormSq_add (x y : Octonion) :
    octNormSq (x+y) = octNormSq x+octNormSq y+2*octDot x y := by
  simp [octNormSq, Quaternion.normSq_def', octDot_coordinates]
  ring

theorem octDot_sub_left (x y z : Octonion) :
    octDot (x-y) z = octDot x z-octDot y z := by
  simp [octDot_coordinates]
  ring

theorem octDot_mul_right (x y z : Octonion) :
    octDot (octMul x y) z = octDot x (octMul z (octConj y)) := by
  simp [octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octDot_mul_left (x y z : Octonion) :
    octDot (octMul x y) z = octDot y (octMul (octConj x) z) := by
  simp [octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octDot_ext (x y : Octonion) (h : ∀ z, octDot x z = octDot y z) : x = y := by
  have hz : octNormSq (x-y) = 0 := by
    rw [← octDot_self, octDot_sub_left, h (x-y), sub_self]
  exact sub_eq_zero.mp ((octNormSq_eq_zero (x-y)).mp hz)

structure OctRelatedTriple where
  A : Octonion ≃ₗ[ℝ] Octonion
  B : Octonion ≃ₗ[ℝ] Octonion
  C : Octonion ≃ₗ[ℝ] Octonion
  norm_A : ∀ x, octNormSq (A x) = octNormSq x
  norm_B : ∀ x, octNormSq (B x) = octNormSq x
  norm_C : ∀ x, octNormSq (C x) = octNormSq x
  product : ∀ x y, octMul (A x) (B y) = C (octMul x y)

theorem octDot_of_norm_preserving (A : Octonion ≃ₗ[ℝ] Octonion)
    (hA : ∀ x, octNormSq (A x) = octNormSq x) (x y : Octonion) :
    octDot (A x) (A y) = octDot x y := by
  have h := hA (x+y)
  simp_all [map_add, octNormSq_add, hA]

namespace OctRelatedTriple

theorem dot_A (g : OctRelatedTriple) (x y : Octonion) :
    octDot (g.A x) (g.A y) = octDot x y := octDot_of_norm_preserving g.A g.norm_A x y

theorem dot_B (g : OctRelatedTriple) (x y : Octonion) :
    octDot (g.B x) (g.B y) = octDot x y := octDot_of_norm_preserving g.B g.norm_B x y

theorem dot_C (g : OctRelatedTriple) (x y : Octonion) :
    octDot (g.C x) (g.C y) = octDot x y := octDot_of_norm_preserving g.C g.norm_C x y

theorem cross01 (g : OctRelatedTriple) (v w : Octonion) :
    octMul (g.C v) (octConj (g.B w)) = g.A (octMul v (octConj w)) := by
  apply octDot_ext
  intro t
  obtain ⟨u, rfl⟩ := g.A.surjective t
  simp [octDot_mul_right, octConj_conj, g.product, g.dot_C, g.dot_A]

theorem cross12 (g : OctRelatedTriple) (u v : Octonion) :
    octMul (octConj (g.A u)) (g.C v) = g.B (octMul (octConj u) v) := by
  apply octDot_ext
  intro t
  obtain ⟨w, rfl⟩ := g.B.surjective t
  grind [octDot_mul_left, octConj_conj, octDot_comm (g.C v), g.product, g.dot_C, g.dot_B]

/-- Composition means first h, then g in each slot. -/
def comp (g h : OctRelatedTriple) : OctRelatedTriple where
  A := h.A.trans g.A
  B := h.B.trans g.B
  C := h.C.trans g.C
  norm_A x := (g.norm_A (h.A x)).trans (h.norm_A x)
  norm_B x := (g.norm_B (h.B x)).trans (h.norm_B x)
  norm_C x := (g.norm_C (h.C x)).trans (h.norm_C x)
  product x y := by
    change octMul (g.A (h.A x)) (g.B (h.B y)) = g.C (h.C (octMul x y))
    rw [g.product, h.product]

/-- Fixed diagonal and upper-slot action (01,02,12) ↦ (A,C,B). -/
def albertEquiv (g : OctRelatedTriple) : Albert ≃ₗ[ℝ] Albert where
  toFun x := ⟨x.d0,x.d1,x.d2,g.A x.o01,g.C x.o02,g.B x.o12⟩
  invFun x := ⟨x.d0,x.d1,x.d2,g.A.symm x.o01,g.C.symm x.o02,g.B.symm x.o12⟩
  left_inv x := by apply Albert.ext <;> simp
  right_inv x := by apply Albert.ext <;> simp
  map_add' x y := by apply Albert.ext <;> simp
  map_smul' r x := by apply Albert.ext <;> simp

theorem albertEquiv_jordan (g : OctRelatedTriple) (x y : Albert) :
    g.albertEquiv (jordan x y) = jordan (g.albertEquiv x) (g.albertEquiv y) := by
  apply Albert.ext
  all_goals simp [albertEquiv, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, g.dot_A, g.dot_B, g.dot_C,
    g.cross01, g.cross12, g.product, map_add, map_smul]

/-- Actual native product- and trace-preserving automorphism from a related triple. -/
def compactAutomorphism (g : OctRelatedTriple) : CompactAutomorphism where
  equiv := g.albertEquiv
  map_jordan := g.albertEquiv_jordan
  map_trace _ := rfl

end OctRelatedTriple
end
end Glennie
