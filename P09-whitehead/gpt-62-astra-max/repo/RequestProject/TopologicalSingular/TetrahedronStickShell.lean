module

/-
The generic codimension-two stick-coordinate lemma below is adapted from
Vilin97/homotopy-groups-lean, c66523531ff172d7f41913d94e56921e790a1b47,
Hurewicz/CubicalShell.lean, Copyright (c) 2026 Vasily Ilin,
released under Apache 2.0. The remaining constructions connect that geometry
to the singular simplex and based-square models in this project.
-/
public import RequestProject.TopologicalSingular.StickTriangleComparison
public import RequestProject.TopologicalSingular.BasedTetrahedronDisks

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo {d : ℕ} (t : Fin d → I)
    (ht : t ∈ cubeCodimTwo d) : stickSimplex d t ∈ simplexCodimTwo d := by
  obtain ⟨i, j, hij, hi, hj⟩ := ht
  cases d with
  | zero => exact Fin.elim0 i
  | succ m =>
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
      have hv : (Fin.removeNth i t) ∈ Cube.boundary _ := by
        refine ⟨k, ?_⟩
        aesop
      rw [(Fin.insertNth_self_removeNth i t).symm]
      apply stickSimplex_cubeFace_mem_codimTwo <;> assumption

variable (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3), face j (face i tau) = ContinuousMap.const (Domain 1) x)

noncomputable def tetrahedronStickShell : CubicalShell 2 X x where
  map := tau.comp (stickSimplex 3)
  codimTwo z hz := by
    obtain ⟨i, j, hij, hi, hj⟩ := stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo z hz
    apply basedTetrahedron_eq_of_two_zero_coordinates <;> assumption

theorem tetrahedronStickShell_upperFaceLoop (i : Fin 3) :
    (tetrahedronStickShell tau hedge).upperFaceLoop i =
      basedTriangleStickSquare _ (hedge i.castSucc) := by
  apply GenLoop.ext
  intro z
  change tau _ =
    tau (stdSimplex.map (SimplexCategory.δ i.castSucc) (stickSimplex 2 z))
  rw [stickSimplex_cubeFace_one, simplex_face_eq_faceMap]

theorem tetrahedronStickShell_lowerLastFaceLoop :
    (tetrahedronStickShell tau hedge).lowerFaceLoop 2 =
      basedTriangleStickSquare _ (hedge 3) := by
  apply GenLoop.ext
  intro z
  change tau (stickSimplex 3 (cubeFace (Fin.last 2) 0 z)) =
    tau (stdSimplex.map (SimplexCategory.δ 3) (stickSimplex 2 z))
  rw [stickSimplex_cubeFace_last_zero, simplex_face_eq_faceMap]
  rfl

variable (i : Fin 3)

theorem tetrahedronStickShell_lower_constant (hi : i ≠ Fin.last 2) :
    (tetrahedronStickShell tau hedge).IsConstantFace i 0 := by
  intro t ht
  have hrep : t = cubeFace i 0 (Fin.removeNth i t) := by
    simp_all
  rw [hrep]
  obtain ⟨j, k, hjk, hj, hk⟩ :=
    stickSimplex_cubeFace_zero_mem_codimTwo i hi _
  apply basedTetrahedron_eq_of_two_zero_coordinates <;> assumption

theorem tetrahedronStickShell_upper_constant (hi : face i.castSucc tau = ContinuousMap.const (Domain 2) x) :
    (tetrahedronStickShell tau hedge).IsConstantFace i 1 := by
  intro t ht
  have hrep : t = cubeFace i 1 (Fin.removeNth i t) := by
    simp_all
  rw [hrep]
  change tau _ = x
  rw [stickSimplex_cubeFace_one, ← simplex_face_eq_faceMap]
  exact congrArg (fun f : Simplex X 2 => f _) hi

noncomputable def tetrahedronFacePi2Class
    (i : Fin 4) : Additive (HomotopyGroup (Fin 2) X x) :=
  Additive.ofMul (Quotient.mk _ (basedTriangleSquare (face i tau) (hedge i)))

theorem tetrahedronStickShell_upperFaceClass (i : Fin 3) :
    (tetrahedronStickShell tau hedge).upperFaceClass i =
      tetrahedronFacePi2Class tau hedge i.castSucc := by
  unfold CubicalShell.upperFaceClass tetrahedronFacePi2Class
  rw [tetrahedronStickShell_upperFaceLoop, basedTriangleStickSquare_pi2_eq]

theorem tetrahedronStickShell_lowerLastFaceClass :
    (tetrahedronStickShell tau hedge).lowerFaceClass 2 =
      tetrahedronFacePi2Class tau hedge 3 := by
  unfold CubicalShell.lowerFaceClass tetrahedronFacePi2Class
  rw [tetrahedronStickShell_lowerLastFaceLoop, basedTriangleStickSquare_pi2_eq]

/-- The genuine pi2 multiplication relation for a tetrahedron whose first
face is constant. This is the final-index simplicial multiplication case. -/
theorem tetrahedronStickShell_face_relation
    (hzero : face 0 tau = ContinuousMap.const (Domain 2) x) :
    tetrahedronFacePi2Class tau hedge 1 + tetrahedronFacePi2Class tau hedge 3 =
      tetrahedronFacePi2Class tau hedge 2 := by
  let S := tetrahedronStickShell tau hedge
  have hleading : S.LeadingFacesConstant := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    exact ⟨tetrahedronStickShell_lower_constant tau hedge 0 (by decide),
      tetrahedronStickShell_upper_constant tau hedge 0 hzero⟩
  have h := S.lastTwoFaceClass_relation hleading
  change S.upperFaceClass 1 + S.lowerFaceClass 2 = S.upperFaceClass 2 + S.lowerFaceClass 1 at h
  rw [(S.lowerFaceClass_eq_zero 1 (tetrahedronStickShell_lower_constant tau hedge 1 (by decide))), add_zero] at h
  simpa only [S, tetrahedronStickShell_upperFaceClass,
    tetrahedronStickShell_lowerLastFaceClass,
    show (1 : Fin 3).castSucc = 1 by decide,
    show (2 : Fin 3).castSucc = 2 by decide] using h

end FiniteChains.TopologicalSingular
