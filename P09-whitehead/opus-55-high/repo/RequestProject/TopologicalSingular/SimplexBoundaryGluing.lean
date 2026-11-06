import RequestProject.TopologicalSingular.SimplexHomotopyExtension
import RequestProject.TopologicalSingular.TriangleSquareGeometry
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_zero i (z : Domain n) :
    (stdSimplex.map (SimplexCategory.δ i) z).val i = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp

def simplexFaceBoundary (i : Fin (n + 2)) : C(Domain n, simplexBoundary (n + 1)) where
  toFun z := ⟨stdSimplex.map (SimplexCategory.δ i) z, ⟨i, simplex_face_coordinate_zero i z⟩⟩
  continuous_toFun := (stdSimplex.continuous_map _).subtype_mk _

def simplexBoundaryPrismCover (n : ℕ) :
    C((Σ _ : Fin (n + 2), I × Domain n), I × simplexBoundary (n + 1)) where
  toFun w := (w.2.1, simplexFaceBoundary w.1 w.2.2)
  continuous_toFun := continuous_sigma fun i =>
    continuous_fst.prodMk ((simplexFaceBoundary i).continuous.comp continuous_snd)

theorem simplexBoundaryPrismCover_surjective n :
    Function.Surjective (simplexBoundaryPrismCover n) := by
  rintro ⟨t, z⟩
  cases' z.property with i hi
  cases' domain_zero_coordinate_face z.val i hi with w hw
  refine ⟨⟨i, t, w⟩, ?_⟩
  apply Prod.ext
  · rfl
  · exact Subtype.ext hw

/-- A coherent family of homotopies on the faces glues continuously over
the entire boundary. The target need not be Hausdorff. -/
theorem simplex_boundary_glue (H : Fin (n + 2) → C(I × Domain n, X))
    (hH : ∀ i j t (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w →
        H i (t, z) = H j (t, w)) :
    ∃ F : C(I × simplexBoundary (n + 1), X),
      ∀ i t z, F (t, simplexFaceBoundary i z) = H i (t, z) := by
  classical
  let q := simplexBoundaryPrismCover n
  have hq : Function.Surjective q := simplexBoundaryPrismCover_surjective n
  cases' hq.hasRightInverse with r hr
  let F := fun w => H (r w).1 (r w).2
  have he : ∀ w : (Σ _ : Fin (n + 2), I × Domain n), F (q w) = H w.1 w.2 := by
    intro w
    have htime := congrArg Prod.fst (hr (q w))
    have hpoint := congrArg (·.2.val) (hr (q w))
    change (r (q w)).2.1 = w.2.1 at htime
    change stdSimplex.map (SimplexCategory.δ (r (q w)).1) (r (q w)).2.2 =
      stdSimplex.map (SimplexCategory.δ w.1) w.2.2 at hpoint
    grind
  have hc : Continuous F := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
    have h : Continuous (fun w : (Σ _ : Fin (n + 2), I × Domain n) => H w.1 w.2) :=
      continuous_sigma (fun i => (H i).continuous)
    simp_all
  exact ⟨⟨F, hc⟩, fun i t z => he ⟨i, t, z⟩⟩

/-- Simultaneously extend prescribed homotopies on all faces of a simplex. -/
theorem simplex_face_homotopy_extension (f : C(Domain (n + 1), X))
    (H : Fin (n + 2) → C(I × Domain n, X))
    (hH : ∀ i j t (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w →
        H i (t, z) = H j (t, w))
    (h0 : ∀ i z, H i (0, z) = face i f z) :
    ∃ g, ∃ F : f.Homotopy g,
      ∀ i t (z : Domain n),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = H i (t, z) := by
  cases' simplex_boundary_glue H hH with B hB
  have hz : ∀ z, B (0, z) = f z := by
    intro z
    cases' z.property with i hi
    cases' domain_zero_coordinate_face z.val i hi with w hw
    have he : simplexFaceBoundary i w = z := Subtype.ext hw
    aesop
  obtain ⟨g, F, hF⟩ := simplex_homotopy_extension f B hz
  refine ⟨g, F, ?_⟩
  intro i t z
  exact (hF t _).trans (hB i t z)
