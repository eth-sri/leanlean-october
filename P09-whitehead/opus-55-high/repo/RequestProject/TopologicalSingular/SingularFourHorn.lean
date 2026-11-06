import RequestProject.TopologicalSingular.SingularSimplicialHelpers
import RequestProject.Tac


bwd

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X]

/-- The missing face of a four-dimensional horn, with its four faces computed.
This is an existence theorem for actual continuous singular tetrahedra. -/
theorem singular_four_horn_missing_one (T0 T2 T3 T4 : Simplex X 3)
    (h02 : face 1 T0 = face 0 T2)
    (h03 : face 2 T0 = face 0 T3)
    (h04 : face 3 T0 = face 0 T4)
    (h23 : face 2 T2 = face 2 T3)
    (h24 : face 3 T2 = face 2 T4)
    (h34 : face 3 T3 = face 3 T4) :
    ∃ W : Simplex X 3,
      face 0 W = face 0 T0 ∧ face 1 W = face 1 T2 ∧
      face 2 W = face 1 T3 ∧ face 3 W = face 1 T4 := by
  let g := ![T0, T0, T2, T3, T4]
  have hg : ∀ j k (hj : j ≠ 1) (hk : j.succAbove k ≠ 1),
      face k (g j) = face (k.predAbove j) (g (j.succAbove k)) := by
    intro j k hj hk
    fin_cases j <;> fin_cases k <;>
      simp_all [g, Fin.succAbove, Fin.predAbove] <;> rfl
  obtain ⟨S, hS⟩ := singular_horn_filler_of_face_compatible 1
    _ hg
  refine ⟨face 1 S, ?_, ?_, ?_, ?_⟩
  · have h := singular_double_face_swap S 1 0
    aesop
  · have h := singular_double_face_swap S 1 1
    aesop
  · have h := singular_double_face_swap S 1 2
    aesop
  · have h := singular_double_face_swap S 1 3
    aesop
