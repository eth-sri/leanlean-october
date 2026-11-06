import Mathlib.Tactic

import GS.UnitaryLocalModel.ChartFibres
import GS.UnitaryLocalModel.RankCone
import GS.CompactFibres
import Mathlib.Topology.Order.Compact
open GS.MatrixBase




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
open scoped Topology
namespace GS.UnitaryLocalModel

variable (x : Fin d → ℝ)

def localEnergy  : ℝ := ∑ i, x i ^ 2

theorem continuous_localEnergy (d : ℕ) : Continuous (@localEnergy d) := by
  unfold localEnergy
  fun_prop

abbrev LocalParameters (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ) × AxisVector

def localParameterBox (d : ℕ) (r : ℝ) : Set (LocalParameters d) :=
  {p | localEnergy p.1 ≤ r^2 ∧ localEnergy p.2.1 ≤ r^2 ∧ OnSphere p.2.2}

theorem localEnergy_coordinate_bound  (r : ℝ)
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
  simp only [localParameterBox, OnSphere, Set.setOf_and]
  repeat' apply IsClosed.inter
  all_goals first
    | exact isClosed_le (by fun_prop [localEnergy]) continuous_const
    | exact isClosed_eq (by fun_prop) continuous_const

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

def parameterCone (p : LocalParameters d) : ConeCoordinates d :=
  (p.1, ⟨sphereOuter p.2.2 p.2.1, rank_sphereOuter_le_one _ _⟩)

theorem continuous_parameterCone (d : ℕ) : Continuous (@parameterCone d) := by
  fun_prop [parameterCone,sphereOuter]

def boundedConeCoordinates (d : ℕ) (r : ℝ) : Set (ConeCoordinates d) :=
  {p | localEnergy p.1 ≤ r^2 ∧ cFrobSq p.2.val ≤ r^2}

theorem parameterCone_image (d : ℕ) (r : ℝ) :
    parameterCone '' localParameterBox d r = boundedConeCoordinates d r := by
  ext p
  constructor
  · rintro ⟨⟨c,z,u⟩,hp,rfl⟩
    refine ⟨hp.1, ?_⟩
    change cFrobSq (sphereOuter u z) ≤ r^2
    rw [frobSq_sphereOuter hp.2.2]
    exact hp.2.1
  · rintro ⟨hc,hW⟩
    obtain ⟨u,hu,z,hz⟩ := exists_sphereOuter_of_rank_le_one p.2.val p.2.property
    have he : localEnergy z = cFrobSq p.2.val := by aesop (add norm [frobSq_sphereOuter])
    refine ⟨(p.1,z,u), ⟨hc,?_,hu⟩,?_⟩
    · aesop
    · aesop

def coneCoordinatesZero (d : ℕ) : ConeCoordinates d :=
  (0,⟨0,by simp⟩)

theorem boundedConeCoordinates_mem_nhds (d : ℕ) {r : ℝ} (hr : 0 < r) :
    boundedConeCoordinates d r ∈ 𝓝 (coneCoordinatesZero d) := by
  have hc : Continuous (fun p : ConeCoordinates d => localEnergy p.1) := by
    fun_prop [localEnergy]
  have hW : Continuous (fun p : ConeCoordinates d => cFrobSq p.2.val) := GS.Extensions.continuous_frobSq.comp (continuous_subtype_val.comp continuous_snd)
  
  exact (hc.continuousAt.eventually_le_const (by simp_all [coneCoordinatesZero,localEnergy])).and
    (hW.continuousAt.eventually_le_const (by simp_all [cFrobInner,cFrobSq,coneCoordinatesZero]))

theorem localEnergy_norm_bound  {r : ℝ}
    (hr : 0 ≤ r) (hx : localEnergy x ≤ r^2) : ‖x‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using
    localEnergy_coordinate_bound x r hx i

/-- Every open chart domain around zero contains a whole compact parameter box. -/
theorem exists_parameterBox_in_chart (U : Set (Fin d → ℝ))
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

def parameterMiddle {κ : Type*}
    (ψ : (Fin d → ℝ) → (κ → ℂ)) (p : LocalParameters d) := chartMiddle ψ p.1 p.2.1 p.2.2

end GS.UnitaryLocalModel
