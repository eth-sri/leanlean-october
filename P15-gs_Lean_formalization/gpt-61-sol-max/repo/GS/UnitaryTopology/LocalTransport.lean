
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import GS.UnitaryTopology.Nonmanifold
import GS.UnitaryLocalModel.TopologyOuter
import GS.UnitaryManifold.CayleyCharts



/-!
# Transport of the cone obstruction through actual local models

An arbitrary locally Euclidean outer factor can be absorbed into the free
coordinates of the rank-three-row model. Finite tuples of the actual unitary
block groups are locally Euclidean by the existing Cayley charts, with their
inherited matrix topology. The final transfer accepts a proved pointed open
or neighbourhood model; it introduces no nonmanifold hypothesis.
-/
noncomputable section
open GS.NonmanifoldFinal GS.NonmanifoldClosure GS.NonmanifoldObstruction
open GS.UnitaryManifold GS.UnitaryLocalModel
namespace GS.UnitaryTopology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- A pointed open model can be multiplied by any unchanged topological factor. -/
def pointedOpenModel_prodRight {x : X} {y : Y}
    (g : PointedOpenModel X Y x y) (z : Z) :
    PointedOpenModel (X × Z) (Y × Z) (x,z) (y,z) where
  source := g.source ×ˢ Set.univ
  target := g.target ×ˢ Set.univ
  source_open := g.source_open.prod isOpen_univ
  target_open := g.target_open.prod isOpen_univ
  source_point := ⟨g.source_point,Set.mem_univ z⟩
  target_point := ⟨g.target_point,Set.mem_univ z⟩
  chart := (Homeomorph.Set.prod g.source Set.univ).trans
    ((g.chart.prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod g.target Set.univ).symm)
  map_point hx := by
    apply Prod.ext
    · exact g.map_point hx.1
    · rfl

/-- Center a finite-dimensional chart directly in Euclidean coordinates. -/
theorem pointedModel_of_finiteDimensional_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ c.source) :
    ∃ n, Nonempty (PointedOpenModel X (Eucl n) x 0) := by
  let e : E ≃L[ℝ] Eucl (Module.finrank ℝ E) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let p := c.trans (e.toHomeomorph.trans
    (Homeomorph.subRight (e (c x)))).toOpenPartialHomeomorph
  have hp : x ∈ p.source := ⟨hx,Set.mem_univ _⟩
  have hz : p x = 0 := by aesop
  refine ⟨_,⟨{
    source := p.source
    target := p.target
    source_open := p.open_source
    target_open := p.open_target
    source_point := hp
    target_point := hz ▸ p.map_source hp
    chart := p.toHomeomorphSourceTarget
    map_point := fun _ => hz }⟩⟩

/-- The finite product Cayley chart is on the original unitary tuple topology. -/
def blockUTuplePartialChart {ι : Type*} [Finite ι] {n : ℕ}
    {b : Fin n → ℕ} (a : ι → BlockU b) := OpenPartialHomeomorph.pi (fun i => blockPartialChart (a i))

variable (n d : ℕ)

/-- Pack the outer Euclidean coordinates and the unconstrained cone center. -/
def euclideanConeCoordinates := (((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.prodCongr
      (Homeomorph.refl (ConeCoordinates d))).trans
    (Homeomorph.prodAssoc _ _ _).symm).trans
      ((sumCoordinates.trans (Homeomorph.piCongrLeft (Y := fun _ => ℝ) finSumFinEquiv)).prodCongr
        (Homeomorph.refl _))

@[simp] theorem euclideanConeCoordinates_zero  :
    euclideanConeCoordinates n d (0,coneCoordinatesZero d) = (0,rankThreeZero) := by
  exact?





end GS.UnitaryTopology
