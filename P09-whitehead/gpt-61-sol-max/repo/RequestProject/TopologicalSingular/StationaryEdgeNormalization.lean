import Mathlib.Tactic

import RequestProject.TopologicalSingular.CoherentEdgeNormalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Choose paths to the basepoint, choosing the constant path at the basepoint. -/
noncomputable def stationaryPath (x a : X) : Path a x := by
  classical
  exact if h : a = x then h.symm ▸ Path.refl x else PathConnectedSpace.somePath a x

variable (x : X)
@[simp] theorem stationaryPath_self  : stationaryPath x x = Path.refl x := by
  simp [stationaryPath]

noncomputable def stationaryVertexPath (x a : X)  :=
  (stationaryPath x a).trans (Path.refl x)

@[simp] theorem stationaryVertexPath_self  (t : I) :
    stationaryVertexPath x x t = x := by simp_all [stationaryVertexPath]

noncomputable def stationaryVertexHomotopy  (tau : Simplex X 0) :
    tau.Homotopy (ContinuousMap.const (Domain 0) x) where
  toFun w := stationaryPath x (tau (stdSimplex.vertex 0)) w.1
  continuous_toFun := (stationaryPath _ _).continuous.comp continuous_fst
  map_zero_left z := by
    rw [Path.source]
    apply congrArg tau
    apply Subtype.ext
    funext i
    have hz := z.property.2
    simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  map_one_left _ := Path.target _

theorem stationaryVertexHomotopy_apply  (tau : Simplex X 0) (t : I) (z : Domain 0) :
    stationaryVertexHomotopy x tau (t, z) = stationaryPath x (tau z) t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      ext <;> simp_all
  change stationaryPath x (tau (stdSimplex.vertex 0)) t = _
  rw [hz]

variable (tau : Simplex X 1)
theorem stationaryEdgeVertexHomotopy_exists   :
    ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = stationaryPath x (tau z) t := by
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    (fun i => (stationaryVertexHomotopy x (face i tau)).toContinuousMap)
    (by
      intro i j t z w h
      dsimp
      simp [stationaryVertexHomotopy_apply]
      exact congrArg (fun a : X => stationaryPath x a t) (congrArg tau h))
    (fun i z => (stationaryVertexHomotopy x (face i tau)).apply_zero z)
  refine ⟨g, F, ?_⟩
  intro t z hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  rw [← hw, hF]
  exact stationaryVertexHomotopy_apply x (face i tau) t w

/-- Coherent edge contractions can be chosen stationary on the constant edge. -/
theorem stationaryEdgeHomotopy_exists   :
    ∃ F : tau.Homotopy (ContinuousMap.const (Domain 1) x),
      (∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = stationaryVertexPath x (tau z) t) ∧
      (tau = ContinuousMap.const (Domain 1) x → ∀ (t : I) (z : Domain 1), F (t, z) = x) := by
  classical
  by_cases htau : tau = ContinuousMap.const (Domain 1) x
  · subst tau
    refine ⟨ContinuousMap.Homotopy.refl _, ?_, ?_⟩
    · simp_all
    · intro _ t z
      rfl
  obtain ⟨g, F, hF⟩ := stationaryEdgeVertexHomotopy_exists x tau
  have hg (i : Fin 2) : g (stdSimplex.vertex i) = x := by
    have h := hF 1 (stdSimplex.vertex i) (simplexOne_vertex_mem_boundary i)
    rw [F.apply_one, Path.target] at h
    exact h
  obtain ⟨G⟩ := singularEdge_nullhomotopic x g (hg 0) (hg 1)
  refine ⟨F.trans G.toHomotopy, ?_, ?_⟩
  · intro t z hz
    rw [ContinuousMap.Homotopy.trans_apply, stationaryVertexPath, Path.trans_apply]
    split_ifs
    · exact hF _ z hz
    · exact G.eq_snd _ hz
  · exact fun h => (htau h).elim

noncomputable def stationaryEdgeHomotopy   :
    tau.Homotopy (ContinuousMap.const (Domain 1) x) :=
  (stationaryEdgeHomotopy_exists x tau).choose

theorem stationaryEdgeHomotopy_boundary   (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    stationaryEdgeHomotopy x tau (t, z) = stationaryVertexPath x (tau z) t :=
  (stationaryEdgeHomotopy_exists x tau).choose_spec.1 t z hz

@[simp] theorem stationaryEdgeHomotopy_constant  (t : I) (z : Domain 1) :
    stationaryEdgeHomotopy x (ContinuousMap.const (Domain 1) x) (t, z) = x :=
  (stationaryEdgeHomotopy_exists x (ContinuousMap.const (Domain 1) x)).choose_spec.2 rfl t z

end FiniteChains.TopologicalSingular
