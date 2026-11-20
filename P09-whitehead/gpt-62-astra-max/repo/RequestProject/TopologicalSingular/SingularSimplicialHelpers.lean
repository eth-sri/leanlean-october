module

public import RequestProject.TopologicalSingular.SingularHornFilling
public import RequestProject.TopologicalSingular.SimplexFaceIntersections

@[expose] public section

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

noncomputable def singularDegeneracy (i : Fin (n + 1)) (tau : Simplex X n) :
    Simplex X (n + 1) := (simplices X).σ i tau

@[simp] theorem singular_face_const (i : Fin _) (x : X) :
    face i (ContinuousMap.const _ x) =
      ContinuousMap.const (Domain n) x := rfl

variable (i : Fin (n + 1))

@[simp] theorem singular_degeneracy_const (x : X) :
    singularDegeneracy i (ContinuousMap.const _ x) =
      ContinuousMap.const (Domain _) x := rfl

variable (tau : Simplex X n)

@[simp] theorem singular_face_degeneracy_self :
    face i.castSucc (singularDegeneracy i tau) = tau :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_self) tau

@[simp] theorem singular_face_degeneracy_succ :
    face i.succ (singularDegeneracy i tau) = tau :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_succ) tau

variable (i : Fin (n + 2)) (j : Fin (n + 1))

theorem singular_face_degeneracy_le
    (h : i ≤ j.castSucc) (tau : Simplex X _) :
    face i.castSucc (singularDegeneracy j.succ tau) =
      singularDegeneracy j (face i tau) :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_of_le h) tau

theorem singular_face_degeneracy_gt
    (h : j.castSucc < i) (tau : Simplex X _) :
    face i.succ (singularDegeneracy j.castSucc tau) =
      singularDegeneracy j (face i tau) :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_of_gt h) tau

/-- Algebraic face compatibility suffices for a genuine topological horn filler. -/
theorem singular_horn_filler_of_face_compatible {Y : Type} [TopologicalSpace Y]
    (i : Fin _) (g : ∀ j : Fin _, j ≠ i → Simplex Y _)
    (hg : ∀ (j : Fin _) (k : Fin _)
      (hj : j ≠ i) (hk : j.succAbove k ≠ i),
      face k (g j hj) = face (k.predAbove j) (g _ hk)) :
    ∃ tau : Simplex Y _, ∀ (j : Fin (n + 3)) (hj : j ≠ i),
      face j tau = g j hj := by
  apply singular_horn_filler_exists i g
  intro j k hj hk z w h
  by_cases hjk : j = k
  · subst k
    solve_by_elim [simplex_face_injective]
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
  have hz : z.val a = 0 := by
    rw [← simplex_face_coordinate_succAbove j z a, ha, h]
    exact simplex_face_coordinate_zero k w
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face z a hz
  have hw : w = stdSimplex.map (SimplexCategory.δ (a.predAbove j)) q := by
    apply simplex_face_injective k
    rw [← h, ← hq]
    simpa only [ha] using simplex_double_face_swap j a q
  have he := congrArg (fun t : Simplex Y n => t q) (hg j a hj (by simpa only [ha] using hk))
  grind [face_apply]

end FiniteChains.TopologicalSingular
