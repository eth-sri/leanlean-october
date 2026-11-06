import RequestProject.TopologicalSingular.CoherentEdgeNormalization
import RequestProject.Tac
noncomputable section


bwd

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

@[simp] theorem stationaryVertexPath_self (x : X) t :
    stationaryVertexPath x x t = x := by
  simp [stationaryVertexPath, stationaryPath_self, Path.trans_apply]

def stationaryVertexHomotopy (x : X) (tau : Simplex X 0) :
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

theorem stationaryVertexHomotopy_apply x (tau : Simplex X 0) t z :
    stationaryVertexHomotopy x tau (t, z) = stationaryPath x (tau z) t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      apply Subtype.ext
      funext i
      have hz := z.property.2
      simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  aesop

theorem stationaryEdgeVertexHomotopy_exists x (tau : Simplex X 1) :
    ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ t z, z ∈ simplexBoundary 1 →
        F (t, z) = stationaryPath x (tau z) t := by
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    _
    (by
      intro i j t z w h
      change stationaryVertexHomotopy x (face i tau) (t, z) =
        stationaryVertexHomotopy x (face j tau) (t, w)
      grind [stationaryVertexHomotopy_apply, face_apply])
    (by simp)
  refine ⟨g, F, ?_⟩
  intro t z hz
  cases' hz with i hi
  cases' domain_zero_coordinate_face z i hi with w hw
  rw [← hw, hF]
  exact stationaryVertexHomotopy_apply x _ t w

/-- Coherent edge contractions can be chosen stationary on the constant edge. -/
theorem stationaryEdgeHomotopy_exists x (tau : Simplex X 1) :
    ∃ F : tau.Homotopy (ContinuousMap.const (Domain 1) x),
      (∀ t z, z ∈ simplexBoundary 1 →
        F (t, z) = stationaryVertexPath x (tau z) t) ∧
      (tau = ContinuousMap.const (Domain 1) x → ∀ t z, F (t, z) = x) := by
  classical
  by_cases htau : tau = ContinuousMap.const _ x
  · subst tau
    refine ⟨ContinuousMap.Homotopy.refl _, ?_, ?_⟩
    · simp
    simp
  obtain ⟨g, F, hF⟩ := stationaryEdgeVertexHomotopy_exists x tau
  have hg (i : Fin 2) : g (stdSimplex.vertex i) = x := by
    have h := hF 1 _ (simplexOne_vertex_mem_boundary i)
    simp_all
  cases' singularEdge_nullhomotopic x g (hg 0) (hg 1) with G
  refine ⟨F.trans G.toHomotopy, ?_, ?_⟩
  · intro t z hz
    rw [ContinuousMap.Homotopy.trans_apply, stationaryVertexPath, Path.trans_apply]
    split_ifs
    · tauto
    · exact G.eq_snd _ hz
  simp_all

def stationaryEdgeHomotopy (x : X) (tau : Simplex X 1) :=
  (stationaryEdgeHomotopy_exists x tau).choose

theorem stationaryEdgeHomotopy_boundary x (tau : Simplex X 1) t
    z (hz : z ∈ simplexBoundary 1) :
    stationaryEdgeHomotopy x tau (t, z) = stationaryVertexPath x (tau z) t :=
  (stationaryEdgeHomotopy_exists x tau).choose_spec.1 t z hz

@[simp] theorem stationaryEdgeHomotopy_constant (x : X) t z :
    stationaryEdgeHomotopy x (ContinuousMap.const (Domain 1) x) (t, z) = x :=
  (stationaryEdgeHomotopy_exists x _).choose_spec.2 rfl t z
