/- The native 16-dimensional spin scalar-commutant theorem.
The unknown operator is an arbitrary real-linear map. -/
module

public import AlbertRecognition.FixedFrame.OctonionCommutants

@[expose] public section

namespace AlbertRecognition.FixedFrame
noncomputable section

open Glennie

abbrev Spin := Octonion × Octonion

/-- Native orientation for the fixed-frame spin block. -/
def spinJ (a : Octonion) : Module.End ℝ Spin :=
  ((-octRight (octConj a)).comp (LinearMap.snd ℝ Octonion Octonion)).prod
    ((octRight a).comp (LinearMap.fst ℝ Octonion Octonion))

@[simp] theorem spinJ_apply (a : Octonion) (u v : Octonion) :
    spinJ a (u, v) = (-octMul v (octConj a), octMul u a) := rfl

theorem spinJ_imag_apply (a : Octonion) (ha : octConj a = -a) (u v : Octonion) :
    spinJ a (u, v) = (octMul v a, octMul u a) := by
  apply Prod.ext
  · change -octMul v (octConj a) = octMul v a
    rw [ha]
    change -(octLeft v) (-a) = (octLeft v) a
    rw [map_neg, neg_neg]
  · rfl

def spinP (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.fst ℝ Octonion Octonion).comp
    (F.comp (LinearMap.inl ℝ Octonion Octonion))
def spinQ (F : Module.End ℝ Spin) : Module.End ℝ Octonion :=
  (LinearMap.fst ℝ Octonion Octonion).comp
    (F.comp (LinearMap.inr ℝ Octonion Octonion))
/-- Commuting with J_1 gives precisely [[P,Q],[-Q,P]]. -/
theorem spin_blocks_of_unit (F : Module.End ℝ Spin)
    (hF : F.comp (spinJ (octScalar 1)) = (spinJ (octScalar 1)).comp F)
    (u v : Octonion) :
    F (u, v) = (spinP F u + spinQ F v, -spinQ F u + spinP F v) := by
  have hh (x : Octonion) : F (0, x) = (-(F (x, 0)).2, (F (x, 0)).1) := by
    simpa [spinJ, octRight] using LinearMap.congr_fun hF (x, 0)
  simpa [spinP, spinQ, hh, Prod.add_def] using F.map_add (u, 0) (0, v)

/-- Eight actual native Clifford generators have scalar common commutant.
No self-adjointness, reference invariance or algebra structure is required of F. -/
theorem spin_commutant_scalar (F : Module.End ℝ Spin)
    (hF : ∀ t : Fin 8,
      F.comp (spinJ (octBasis t)) = (spinJ (octBasis t)).comp F) :
    ∃ b : ℝ, F = b • LinearMap.id := by
  have hunit                                                               :=
    hF 0
  have hf := spin_blocks_of_unit F hunit
  have himag (t : Fin 8) (ht : t ≠ 0) (x : Octonion) :
      spinQ F (octMul x (octBasis t)) = -octMul (spinQ F x) (octBasis t) ∧
      spinP F (octMul x (octBasis t)) = octMul (spinP F x) (octBasis t) := by
    have h := LinearMap.congr_fun (hF t) (x, 0)
    simp only [LinearMap.comp_apply] at h
    rw [spinJ_imag_apply _ (octBasis_conj_imag t ht), hf, hf] at h
    simp only [octMul_zero_left, map_zero, zero_add, add_zero, neg_zero] at h
    rw [spinJ_imag_apply _ (octBasis_conj_imag t ht)] at h
    constructor
    · simpa [octMul, sub_eq_add_neg, add_comm] using congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hP : ∀ t : Fin 8, ∀ x : Octonion,
      spinP F (octMul x (octBasis t)) = octMul (spinP F x) (octBasis t) := by
    intro t x
    by_cases ht : t = 0
    · subst t
      simp [octBasis]
    · exact (himag t ht x).2
  have hQ : ∀ t : Fin 8, t ≠ 0 → ∀ x : Octonion,
      spinQ F (octMul x (octBasis t)) = -octMul (spinQ F x) (octBasis t) := by
    intro t ht x
    exact (himag t ht x).1
  obtain ⟨b, hb⟩ := oct_right_commutant_scalar (spinP F) hP
  have hq               := oct_imaginary_right_anticommutant_zero (spinQ F) hQ
  refine ⟨b, ?_⟩
  apply LinearMap.ext
  rintro ⟨u, v⟩
  rw [hf u v, hb, hq]
  simp

end
end AlbertRecognition.FixedFrame
