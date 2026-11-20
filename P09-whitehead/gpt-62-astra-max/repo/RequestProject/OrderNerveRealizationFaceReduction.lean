module

public import RequestProject.TopologicalSingular.SimplexCoordinates
public import RequestProject.OrderNerveRealizationInterior
public import RequestProject.OrderNerveRealizationNondegenerate

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- A standard-simplex point with a zero coordinate comes from the corresponding face. -/
theorem topologicalSimplex_zero_coordinate_face {n : ℕ}
    (z : SimplexCategory.toTop.obj _) (i : Fin _)
    (hi : z.down.weights i = 0) :
    ∃ w : SimplexCategory.toTop.obj ⦋n⦌, SimplexCategory.toTop.map (SimplexCategory.δ i) w = z := by
  let zold := TopologicalSingular.simplexCoordinates _ z.down
  have hiold : zold.val i = 0 := hi
  let w : stdSimplex ℝ (Fin _) :=
    ⟨fun j => zold.val _, fun j => zold.property.1 _, by
      have hs := zold.property.2
      rw [Fin.sum_univ_succAbove (fun j : Fin _ => zold.val j) i,
        hiold, zero_add] at hs <;> assumption⟩
  refine ⟨ULift.up ((TopologicalSingular.simplexCoordinates n).symm w), ?_⟩
  apply ULift.ext
  apply (TopologicalSingular.simplexCoordinates _).injective
  change TopologicalSingular.simplexCoordinates _
    (Convexity.StdSimplex.map i.succAbove ((TopologicalSingular.simplexCoordinates n).symm w)) = zold
  rw [TopologicalSingular.simplexCoordinates_map, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  funext k
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove w.val) k = zold.val k
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = i
  · simp_all
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [w, Finset.sum_filter]

section

variable (P : Type) [PartialOrder P]

/-- Every point on a nondegenerate simplex belongs to the interior of a
nondegenerate face of no larger dimension. -/
theorem orderNerveRealizationSimplex_interior_representative
    (n : ℕ) (s : (nerve P).nonDegenerate n) (z : SimplexCategory.toTop.obj ⦋n⦌) :
    ∃ (m : ℕ) (_ : m ≤ n) (t : (nerve P).nonDegenerate m)
      (w : SimplexCategory.toTop.obj ⦋m⦌),
      (∀ i, 0 < w.down.weights i) ∧
        orderNerveRealizationSimplex P t.val w = orderNerveRealizationSimplex P s.val z := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, s, z, ?_, rfl⟩ <;> simp_all
  | succ n ih =>
    by_cases hz : ∀ i, 0 < z.down.weights i
    · exact ⟨n + 1, le_rfl, s, z, hz, rfl⟩
    · push_neg at hz
      obtain ⟨i, hi⟩ := hz
      obtain ⟨w, hw⟩ := topologicalSimplex_zero_coordinate_face z i (le_antisymm hi (z.down.weights_nonneg i))
      have ht : (nerve P).map (SimplexCategory.δ i).op s.val ∈
          (nerve P).nonDegenerate n := by
        rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]
        exact ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property).comp Fin.succAbove_right_injective
      obtain ⟨m, hm, t, u, hu, he⟩ := ih ⟨_, ht⟩ w
      have h := congrArg (fun k => k w)
        (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s.val)
      change orderNerveRealizationSimplex P s.val
        (SimplexCategory.toTop.map (SimplexCategory.δ i) w) = _ at h
      grind

/-- Every actual realization point lies in an actual nondegenerate simplex interior. -/
theorem orderNerveRealization_interior_cover
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌),
      (∀ i, 0 < z.down.weights i) ∧ orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  obtain ⟨m, _, t, w, hw, he⟩ := orderNerveRealizationSimplex_interior_representative P n s z
  exact ⟨m, t, w, hw, he.trans hz⟩

end

variable {P : Type} [PartialOrder P] {n : ℕ}

/-- Every boundary point of an actual simplex is represented in one of its finitely
many codimension-one faces. -/
theorem orderNerveRealizationSimplex_boundary_face (s : (nerve P).obj _)
    (z : SimplexCategory.toTop.obj _) (hz : ¬ ∀ i, 0 < z.down.weights i) :
    ∃ (i : Fin _) (w : SimplexCategory.toTop.obj ⦋n⦌),
      orderNerveRealizationSimplex P ((nerve P).map (SimplexCategory.δ i).op s) w =
        orderNerveRealizationSimplex P s z := by
  push_neg at hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨w, hw⟩ := topologicalSimplex_zero_coordinate_face z i (le_antisymm hi (z.down.weights_nonneg i))
  have h := congrArg (fun k => k w)
    (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s)
  simp_all

variable (s : (nerve P).nonDegenerate (n + 1))

/-- Every face of an actual nondegenerate poset-nerve simplex remains nondegenerate. -/
theorem orderNerve_nonDegenerate_face (i : Fin _) :
    (nerve P).map (SimplexCategory.δ i).op s.val ∈ (nerve P).nonDegenerate n := by
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]
  exact ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property).comp
    Fin.succAbove_right_injective

/-- The boundary of every nondegenerate simplex maps into a finite family of
actual lower-dimensional closed simplex images. -/
theorem orderNerveRealizationSimplex_boundary_finite_faces :
    ∃ I : Finset ((nerve P).nonDegenerate n),
      ∀ z : SimplexCategory.toTop.obj _,
        (¬ ∀ i, 0 < z.down.weights i) →
        ∃ t ∈ I, ∃ w : SimplexCategory.toTop.obj ⦋n⦌,
          orderNerveRealizationSimplex P t.val w = orderNerveRealizationSimplex P s.val z := by
  classical
  let face : Fin _ → (nerve P).nonDegenerate n := fun i =>
    ⟨(nerve P).map _ s.val, orderNerve_nonDegenerate_face s i⟩
  refine ⟨Finset.univ.image face, ?_⟩
  intro z hz
  obtain ⟨i, w, hw⟩ := orderNerveRealizationSimplex_boundary_face s.val z hz
  exact ⟨face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, w, hw⟩

end FiniteChains.Comb
