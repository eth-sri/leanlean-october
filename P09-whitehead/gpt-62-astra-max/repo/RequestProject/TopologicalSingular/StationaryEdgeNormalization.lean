module

public import RequestProject.TopologicalSingular.CoherentEdgeNormalization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Choose paths to the basepoint, choosing the constant path at the basepoint. -/
def stationaryPath (x a : X) : Path a x := by
  classical
  exact if h : a = x then h.symm ▸ Path.refl x else PathConnectedSpace.somePath a x

@[simp] theorem stationaryPath_self (x : X) : stationaryPath x x = Path.refl x := by
  simp [stationaryPath]

def stationaryVertexPath (x a : X) :=
  (stationaryPath x a).trans (Path.refl x)

variable (x : X)

@[simp] theorem stationaryVertexPath_self (t : I) :
    stationaryVertexPath x x t = x := by
  rw [stationaryVertexPath, stationaryPath_self, Path.trans_apply]
  split_ifs <;> rfl

variable (tau : Simplex X 0)

def stationaryVertexHomotopy :
    tau.Homotopy (ContinuousMap.const (Domain 0) x) where
  toFun w := stationaryPath x (tau (stdSimplex.vertex 0)) w.1
  continuous_toFun := (stationaryPath _ _).continuous.comp continuous_fst
  map_zero_left z := by
    rw [Path.source]
    apply congrArg tau
    ext <;> simp
  map_one_left _ := Path.target _

theorem stationaryVertexHomotopy_apply (t : I) (z : Domain 0) :
    stationaryVertexHomotopy x tau (t, z) = stationaryPath x (tau z) t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      apply Subtype.ext
      funext i
      simpa [stdSimplex.vertex, show i = 0 by omega] using z.property.2.symm
  aesop

variable (tau : Simplex X 1)

theorem stationaryEdgeVertexHomotopy_exists :
    ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = stationaryPath x (tau z) t := by
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    _
    (by
      intro i j t z w h
      change stationaryVertexHomotopy x (face i tau) (t, z) =
        stationaryVertexHomotopy x (face j tau) (t, w)
      simp only [stationaryVertexHomotopy_apply, face_apply]
      exact congrArg (fun a : X => stationaryPath x a t) (congrArg tau h))
    (fun i z => (stationaryVertexHomotopy x (face i tau)).apply_zero z)
  refine ⟨g, F, ?_⟩
  intro t z hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  rw [← hw, hF]
  apply stationaryVertexHomotopy_apply

/-- Coherent edge contractions can be chosen stationary on the constant edge. -/
theorem stationaryEdgeHomotopy_exists :
    ∃ F : tau.Homotopy (ContinuousMap.const (Domain 1) x),
      (∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = stationaryVertexPath x (tau z) t) ∧
      (tau = ContinuousMap.const (Domain 1) x → ∀ (t : I) (z : Domain 1), F (t, z) = x) := by
  classical
  by_cases htau : tau = ContinuousMap.const (Domain 1) x
  · subst tau
    refine ⟨ContinuousMap.Homotopy.refl _, ?_, ?_⟩ <;> simp_all
  obtain ⟨g, F, hF⟩ := stationaryEdgeVertexHomotopy_exists x tau
  have hg (i : Fin 2) : g (stdSimplex.vertex i) = x := by
    have h := hF 1 _ (simplexOne_vertex_mem_boundary i)
    simp_all [F.apply_one, Path.target]
  obtain ⟨G⟩ := singularEdge_nullhomotopic x g (hg 0) (hg 1)
  refine ⟨F.trans G.toHomotopy, ?_, ?_⟩
  · intro t z hz
    rw [ContinuousMap.Homotopy.trans_apply, stationaryVertexPath, Path.trans_apply]
    split_ifs
    · solve_by_elim
    · exact G.eq_snd _ hz
  · simp_all

def stationaryEdgeHomotopy :=
  (stationaryEdgeHomotopy_exists x tau).choose

theorem stationaryEdgeHomotopy_boundary (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    stationaryEdgeHomotopy x tau (t, z) = stationaryVertexPath x (tau z) t :=
  (stationaryEdgeHomotopy_exists x tau).choose_spec.1 t z hz

@[simp] theorem stationaryEdgeHomotopy_constant (t : I) (z : Domain 1) :
    stationaryEdgeHomotopy x (ContinuousMap.const (Domain 1) x) (t, z) = x :=
  (stationaryEdgeHomotopy_exists x _).choose_spec.2 rfl t z

end FiniteChains.TopologicalSingular
