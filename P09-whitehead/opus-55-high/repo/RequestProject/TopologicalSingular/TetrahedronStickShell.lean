/-
The generic codimension-two stick-coordinate lemma below is adapted from
Vilin97/homotopy-groups-lean, c66523531ff172d7f41913d94e56921e790a1b47,
Hurewicz/CubicalShell.lean, Copyright (c) 2026 Vasily Ilin,
released under Apache 2.0. The remaining constructions connect that geometry
to the singular simplex and based-square models in this project.
-/
import RequestProject.TopologicalSingular.StickTriangleComparison
import RequestProject.TopologicalSingular.BasedTetrahedronDisks
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo t
    (ht : t ∈ cubeCodimTwo d) : stickSimplex d t ∈ simplexCodimTwo d := by
  obtain ⟨i, j, hij, hi, hj⟩ := ht
  cases d with
  | zero => exact i.elim0
  | succ m =>
      cases' Fin.exists_succAbove_eq hij.symm with k hk
      let v := i.removeNth t
      have hv : v ∈ Cube.boundary _ := by
        refine ⟨k, ?_⟩
        aesop
      have hrep :=
        (i.insertNth_self_removeNth t).symm
      rw [hrep]
      exact stickSimplex_cubeFace_mem_codimTwo i _ hi v hv

def tetrahedronStickShell (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) : CubicalShell 2 X x where
  map := tau.comp (stickSimplex 3)
  codimTwo z hz := by
    obtain ⟨i, j, hij, hi, hj⟩ := stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo z hz
    exact basedTetrahedron_eq_of_two_zero_coordinates tau hedge _ i j hij hi hj

theorem tetrahedronStickShell_upperFaceLoop (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) (i : Fin 3) :
    (tetrahedronStickShell tau hedge).upperFaceLoop i =
      basedTriangleStickSquare (face i.castSucc tau) (hedge i.castSucc) := by
  apply GenLoop.ext
  intro z
  change tau (stickSimplex 3 (cubeFace i 1 z)) =
    tau (stdSimplex.map (SimplexCategory.δ i.castSucc) (stickSimplex 2 z))
  rw [stickSimplex_cubeFace_one, simplex_face_eq_faceMap]

theorem tetrahedronStickShell_lowerLastFaceLoop (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    (tetrahedronStickShell tau hedge).lowerFaceLoop 2 =
      basedTriangleStickSquare (face 3 tau) (hedge 3) := by
  apply GenLoop.ext
  intro z
  change tau (stickSimplex 3 (cubeFace (Fin.last 2) 0 z)) =
    tau (stdSimplex.map (SimplexCategory.δ 3) (stickSimplex 2 z))
  rw [stickSimplex_cubeFace_last_zero, simplex_face_eq_faceMap]
  rfl

theorem tetrahedronStickShell_lower_constant (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 3) (hi : i ≠ Fin.last 2) :
    (tetrahedronStickShell tau hedge).IsConstantFace i 0 := by
  intro t ht
  have hrep : t = cubeFace i 0 (i.removeNth t) := by
    change t = i.insertNth 0 (i.removeNth t)
    simp_all
  rw [hrep]
  obtain ⟨j, k, hjk, hj, hk⟩ :=
    stickSimplex_cubeFace_zero_mem_codimTwo i hi _
  exact basedTetrahedron_eq_of_two_zero_coordinates tau hedge _ j k hjk hj hk

theorem tetrahedronStickShell_upper_constant (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 3) (hi : face i.castSucc tau = ContinuousMap.const (Domain 2) x) :
    (tetrahedronStickShell tau hedge).IsConstantFace i 1 := by
  intro t ht
  have hrep : t = cubeFace i 1 (i.removeNth t) := by
    change t = i.insertNth 1 (i.removeNth t)
    simp_all
  rw [hrep]
  change tau (stickSimplex 3 (cubeFace i 1 (i.removeNth t))) = x
  rw [stickSimplex_cubeFace_one, ← simplex_face_eq_faceMap]
  exact congrArg (· (stickSimplex 2 (i.removeNth t))) hi

def tetrahedronFacePi2Class (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 4) : Additive (HomotopyGroup (Fin 2) X x) :=
  Additive.ofMul (Quotient.mk _ (basedTriangleSquare (face i tau) (hedge i)))

theorem tetrahedronStickShell_upperFaceClass (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) (i : Fin 3) :
    (tetrahedronStickShell tau hedge).upperFaceClass i =
      tetrahedronFacePi2Class tau hedge i.castSucc := by
  unfold CubicalShell.upperFaceClass tetrahedronFacePi2Class
  rw [tetrahedronStickShell_upperFaceLoop, basedTriangleStickSquare_pi2_eq]

theorem tetrahedronStickShell_lowerLastFaceClass (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    (tetrahedronStickShell tau hedge).lowerFaceClass 2 =
      tetrahedronFacePi2Class tau hedge 3 := by
  unfold CubicalShell.lowerFaceClass tetrahedronFacePi2Class
  rw [tetrahedronStickShell_lowerLastFaceLoop, basedTriangleStickSquare_pi2_eq]

/-- The genuine pi2 multiplication relation for a tetrahedron whose first
face is constant. This is the final-index simplicial multiplication case. -/
theorem tetrahedronStickShell_face_relation (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (hzero : face 0 tau = ContinuousMap.const (Domain 2) x) :
    tetrahedronFacePi2Class tau hedge 1 + tetrahedronFacePi2Class tau hedge 3 =
      tetrahedronFacePi2Class tau hedge 2 := by
  let S := tetrahedronStickShell tau hedge
  have hleading : S.LeadingFacesConstant := by
    intro i
    have hi := i.eq_zero
    subst i
    exact ⟨tetrahedronStickShell_lower_constant tau hedge 0 (by decide),
      tetrahedronStickShell_upper_constant tau hedge 0 hzero⟩
  have h := S.lastTwoFaceClass_relation hleading
  have hlower :=
    S.lowerFaceClass_eq_zero 1 (tetrahedronStickShell_lower_constant tau hedge 1 (by decide))
  simp_all [hlower, add_zero, S, tetrahedronStickShell_upperFaceClass, tetrahedronStickShell_lowerLastFaceClass, show (1 : Fin 3).castSucc = (1) by decide]
