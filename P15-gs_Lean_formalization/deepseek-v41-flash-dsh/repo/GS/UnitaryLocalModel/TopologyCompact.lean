module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import GS.CompactFibres
public import GS.ComplexAlgebra
public import GS.Continuation.ExponentialBasics
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.OriginalGImage
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryLocalModel.ChartFibres
public import GS.UnitaryLocalModel.MiddleFibres
public import GS.UnitaryLocalModel.OuterFibres
public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.UnitaryLocalModel.RankCone
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact images in the unitary local model

The middle-matrix parametrization and the real rank-three-row cone have
homeomorphic compact images. Compactness, continuity and the exact fibres are
proved. The only chart assumptions are continuity and injectivity on its
stated domain. This theorem does not assume a same-fibres assertion.

The full-family extension is developed in `TopologyFullImage` and
`TopologyNeighbourhood`, using the actual dephased chart, algebraic phase
normalization, and coverage of every nearby GS matrix.
-/

noncomputable section
open Matrix GS Filter
open scoped BigOperators Topology
namespace GS.UnitaryLocalModel

def localEnergy {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem continuous_localEnergy (d : ℕ) : Continuous (@localEnergy d) := by
  unfold localEnergy
  fun_prop

abbrev LocalParameters (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ) × AxisVector

def localParameterBox (d : ℕ) (r : ℝ) : Set (LocalParameters d) :=
  {p | localEnergy p.1 ≤ r^2 ∧ localEnergy p.2.1 ≤ r^2 ∧ OnSphere p.2.2}

theorem localEnergy_coordinate_bound {d : ℕ} (x : Fin d → ℝ) (r : ℝ)
    (hx : localEnergy x ≤ r^2) (i : Fin d) : |x i| ≤ |r| := by
  have hi : x i ^ 2 ≤ localEnergy x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), sq_abs r, abs_nonneg (x i), abs_nonneg r]

theorem onSphere_coordinate_bound {u : AxisVector} (hu : OnSphere u)
    (i : Fin 3) : |u i| ≤ 1 := by
  have hs : u i ^ 2 ≤ 1 := by
    fin_cases i <;> dsimp [OnSphere] at hu ⊢ <;>
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  nlinarith [sq_abs (u i), abs_nonneg (u i)]

theorem isClosed_localParameterBox (d : ℕ) (r : ℝ) :
    IsClosed (localParameterBox d r) := by
  have hc : IsClosed {p : LocalParameters d | localEnergy p.1 ≤ r^2} :=
    isClosed_le ((continuous_localEnergy d).comp continuous_fst) continuous_const
  have hz : IsClosed {p : LocalParameters d | localEnergy p.2.1 ≤ r^2} :=
    isClosed_le ((continuous_localEnergy d).comp (by fun_prop)) continuous_const
  have hu : IsClosed {p : LocalParameters d | OnSphere p.2.2} := by
    apply isClosed_eq _ continuous_const
    change Continuous (fun p : LocalParameters d =>
      p.2.2 0 ^ 2 + p.2.2 1 ^ 2 + p.2.2 2 ^ 2)
    fun_prop
  exact hc.inter (hz.inter hu)

theorem isCompact_localParameterBox (d : ℕ) (r : ℝ) :
    IsCompact (localParameterBox d r) := by
  let lo : LocalParameters d := (fun _ => -|r|, fun _ => -|r|, fun _ => -1)
  let hi : LocalParameters d := (fun _ => |r|, fun _ => |r|, fun _ => 1)
  apply (show IsCompact (Set.Icc lo hi) from isCompact_Icc).of_isClosed_subset
    (isClosed_localParameterBox d r)
  intro p hp
  have hc := fun i => abs_le.mp (localEnergy_coordinate_bound p.1 r hp.1 i)
  have hz := fun i => abs_le.mp (localEnergy_coordinate_bound p.2.1 r hp.2.1 i)
  have hu := fun i => abs_le.mp (onSphere_coordinate_bound hp.2.2 i)
  exact ⟨⟨fun i => (hc i).1, fun i => (hz i).1, fun i => (hu i).1⟩,
    ⟨fun i => (hc i).2, fun i => (hz i).2, fun i => (hu i).2⟩⟩

abbrev ConeCoordinates (d : ℕ) :=
  (Fin d → ℝ) × {W : Matrix (Fin 3) (Fin d) ℝ // W.rank ≤ 1}

def parameterCone {d : ℕ} (p : LocalParameters d) : ConeCoordinates d :=
  (p.1, ⟨sphereOuter p.2.2 p.2.1, rank_sphereOuter_le_one _ _⟩)

theorem continuous_parameterCone (d : ℕ) : Continuous (@parameterCone d) := by
  have h : Continuous (fun p : LocalParameters d => (p.2.2,p.2.1)) :=
    continuous_snd.snd.prodMk continuous_snd.fst
  exact continuous_fst.prodMk ((continuous_sphereOuter.comp h).subtype_mk _)

def boundedConeCoordinates (d : ℕ) (r : ℝ) : Set (ConeCoordinates d) :=
  {p | localEnergy p.1 ≤ r^2 ∧ frobSq p.2.val ≤ r^2}

theorem parameterCone_image (d : ℕ) (r : ℝ) :
    parameterCone '' localParameterBox d r = boundedConeCoordinates d r := by
  ext p
  constructor
  · rintro ⟨⟨c,z,u⟩,hp,rfl⟩
    refine ⟨hp.1, ?_⟩
    change frobSq (sphereOuter u z) ≤ r^2
    rw [frobSq_sphereOuter hp.2.2]
    exact hp.2.1
  · rintro ⟨hc,hW⟩
    obtain ⟨u,hu,z,hz⟩ := exists_sphereOuter_of_rank_le_one p.2.val p.2.property
    have he : localEnergy z = frobSq p.2.val := by
      rw [← hz, frobSq_sphereOuter hu]
      rfl
    refine ⟨(p.1,z,u), ⟨hc,?_,hu⟩,?_⟩
    · rw [he]
      exact hW
    · change (p.1,⟨sphereOuter u z,rank_sphereOuter_le_one u z⟩) = p
      apply Prod.ext
      · rfl
      · exact Subtype.ext hz

def coneCoordinatesZero (d : ℕ) : ConeCoordinates d :=
  (0,⟨0,by simp⟩)

theorem boundedConeCoordinates_mem_nhds (d : ℕ) {r : ℝ} (hr : 0 < r) :
    boundedConeCoordinates d r ∈ 𝓝 (coneCoordinatesZero d) := by
  have hc : Continuous (fun p : ConeCoordinates d => localEnergy p.1) :=
    (continuous_localEnergy d).comp continuous_fst
  have hW : Continuous (fun p : ConeCoordinates d => frobSq p.2.val) := by
    unfold frobSq frobInner
    have hv : Continuous (fun p : ConeCoordinates d => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro j hj
    exact (((continuous_apply j).comp ((continuous_apply i).comp hv))).mul
      (((continuous_apply j).comp ((continuous_apply i).comp hv)))
  have hco : IsOpen {p : ConeCoordinates d | localEnergy p.1 < r^2} :=
    isOpen_lt hc continuous_const
  have hWo : IsOpen {p : ConeCoordinates d | frobSq p.2.val < r^2} :=
    isOpen_lt hW continuous_const
  apply Filter.mem_of_superset ((hco.inter hWo).mem_nhds ?_) ?_
  · simp [coneCoordinatesZero, localEnergy, frobSq, frobInner, sq_pos_of_pos hr]
  · intro p hp
    exact ⟨hp.1.le,hp.2.le⟩

theorem localEnergy_norm_bound {d : ℕ} (x : Fin d → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hx : localEnergy x ≤ r^2) : ‖x‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using
    localEnergy_coordinate_bound x r hx i

/-- Every open chart domain around zero contains a whole compact parameter box. -/
theorem exists_parameterBox_in_chart {d : ℕ} (U : Set (Fin d → ℝ))
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ localParameterBox d r,
      p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  refine ⟨ε/3,by positivity,?_⟩
  intro p hp
  have hc := localEnergy_norm_bound p.1 (by positivity : 0 ≤ ε/3) hp.1
  have hz := localEnergy_norm_bound p.2.1 (by positivity : 0 ≤ ε/3) hp.2.1
  constructor
  · apply hsub
    change dist (p.1+p.2.1) 0 < ε
    rw [dist_zero_right]
    exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)
  · apply hsub
    change dist (p.1-p.2.1) 0 < ε
    rw [dist_zero_right]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith)

def parameterMiddle {d : ℕ} {κ : Type*}
    (ψ : (Fin d → ℝ) → (κ → ℂ)) (p : LocalParameters d) : κ → CMat 2 :=
  chartMiddle ψ p.1 p.2.1 p.2.2

theorem continuous_parameterMiddle_on_box {d : ℕ} {κ : Type*}
    (ψ : (Fin d → ℝ) → (κ → ℂ)) (U : Set (Fin d → ℝ))
    (hψ : ContinuousOn ψ U) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    Continuous (fun p : localParameterBox d r => parameterMiddle ψ p.val) := by
  have hp : Continuous (fun p : localParameterBox d r => ψ (p.val.1+p.val.2.1)) :=
    hψ.comp_continuous (by fun_prop) (fun p => (hargs p.val p.property).1)
  have hm : Continuous (fun p : localParameterBox d r => ψ (p.val.1-p.val.2.1)) :=
    hψ.comp_continuous (by fun_prop) (fun p => (hargs p.val p.property).2)
  unfold parameterMiddle chartMiddle middleBlock
  apply continuous_pi
  intro j
  exact (((continuous_apply j).comp hp).add ((continuous_apply j).comp hm)).div_const 2 |>.smul
    continuous_const |>.add
      (((((continuous_apply j).comp hp).sub ((continuous_apply j).comp hm)).div_const 2).smul
        (continuous_pauli.comp (by fun_prop)))

end GS.UnitaryLocalModel
