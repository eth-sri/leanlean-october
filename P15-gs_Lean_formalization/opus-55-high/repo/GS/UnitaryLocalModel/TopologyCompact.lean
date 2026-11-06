module

public import GS.UnitaryLocalModel.ChartFibres
public import GS.UnitaryLocalModel.RankCone
public import GS.CompactFibres
public import Mathlib.Topology.Order.Compact

@[expose] public section


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
open scoped BigOperators Topology
namespace GS.UnitaryLocalModel

def localEnergy {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

section
variable (d : ℕ)
theorem continuous_localEnergy : Continuous (@localEnergy d) := by
  unfold localEnergy
  fun_prop

abbrev LocalParameters := (Fin d → ℝ) × (Fin d → ℝ) × AxisVector

def localParameterBox (r : ℝ) : Set (LocalParameters d) :=
  {p | localEnergy p.1 ≤ r^2 ∧ localEnergy p.2.1 ≤ r^2 ∧ OnSphere p.2.2}

end

theorem localEnergy_coordinate_bound {d : ℕ} (x : Fin d → ℝ) (r : ℝ)
    (hx : localEnergy x ≤ r^2) (i : Fin d) : |x i| ≤ |r| := by
  have hi : x i ^ 2 ≤ localEnergy x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), sq_abs r, abs_nonneg (x i), abs_nonneg r]

theorem isCompact_localParameterBox (d : ℕ) (r : ℝ) :
    IsCompact (localParameterBox d r) := by
  refine (isCompact_Icc (a := ((fun _ => -|r|, fun _ => -|r|, fun _ => -1) : LocalParameters d))
    (b := (fun _ => |r|, fun _ => |r|, fun _ => 1))).of_isClosed_subset
    (show IsClosed {p : LocalParameters d | localEnergy p.1 ≤ r^2 ∧ localEnergy p.2.1 ≤ r^2 ∧
      p.2.2 0 ^ 2 + p.2.2 1 ^ 2 + p.2.2 2 ^ 2 = 1} from
      (isClosed_le ((continuous_localEnergy d).comp continuous_fst) continuous_const).inter
      ((isClosed_le ((continuous_localEnergy d).comp (by fun_prop)) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const))) fun p hp => ?_
  have hc := fun i => abs_le.mp (localEnergy_coordinate_bound p.1 r hp.1 i)
  have hz := fun i => abs_le.mp (localEnergy_coordinate_bound p.2.1 r hp.2.1 i)
  have hu : ∀ i, -1 ≤ p.2.2 i ∧ p.2.2 i ≤ 1 := fun i => by
    have := hp.2.2; unfold OnSphere at this; fin_cases i <;> dsimp <;> constructor <;> nlinarith [sq_nonneg (p.2.2 0), sq_nonneg (p.2.2 1), sq_nonneg (p.2.2 2)]
  exact ⟨⟨fun i => (hc i).1, fun i => (hz i).1, fun i => (hu i).1⟩,
    ⟨fun i => (hc i).2, fun i => (hz i).2, fun i => (hu i).2⟩⟩

abbrev ConeCoordinates (d : ℕ) :=
  (Fin d → ℝ) × {W : Matrix (Fin 3) (Fin d) ℝ // W.rank ≤ 1}

def parameterCone {d : ℕ} (p : LocalParameters d) : ConeCoordinates d :=
  (p.1, ⟨sphereOuter p.2.2 p.2.1, rank_sphereOuter_le_one _ _⟩)

section
variable (d : ℕ)
theorem continuous_parameterCone : Continuous (@parameterCone d) := by
  exact continuous_fst.prodMk ((continuous_sphereOuter.comp (continuous_snd.snd.prodMk continuous_snd.fst)).subtype_mk _)

def boundedConeCoordinates (r : ℝ) : Set (ConeCoordinates d) :=
  {p | localEnergy p.1 ≤ r^2 ∧ frobSq p.2.val ≤ r^2}

theorem parameterCone_image (r : ℝ) :
    parameterCone '' localParameterBox d r = boundedConeCoordinates d r := by
  ext p
  constructor
  · rintro ⟨⟨c,z,u⟩,hp,rfl⟩
    exact ⟨hp.1, (frobSq_sphereOuter hp.2.2 z).trans_le hp.2.1⟩
  · rintro ⟨hc,hW⟩
    obtain ⟨u,hu,z,hz⟩ := exists_sphereOuter_of_rank_le_one p.2.val p.2.property
    have he : localEnergy z = frobSq p.2.val := by
      rw [← hz, frobSq_sphereOuter hu]
      rfl
    refine ⟨(p.1,z,u), ⟨hc,?_,hu⟩,?_⟩
    · grind
    aesop

def coneCoordinatesZero : ConeCoordinates d :=
  (0,⟨0,by simp⟩)

theorem boundedConeCoordinates_mem_nhds {r : ℝ} (hr : 0 < r) :
    boundedConeCoordinates d r ∈ 𝓝 (coneCoordinatesZero d) := by
  refine Filter.mem_of_superset (((isOpen_lt ((continuous_localEnergy d).comp continuous_fst) (continuous_const (y := r^2))).inter
    (isOpen_lt (show Continuous fun p : ConeCoordinates d => frobSq p.2.val by unfold frobSq frobInner; fun_prop)
      (continuous_const (y := r^2)))).mem_nhds ?_) fun p hp => ⟨hp.1.le,hp.2.le⟩
  simp [coneCoordinatesZero, localEnergy, frobSq, frobInner, sq_pos_of_pos hr]

end

section
variable {d : ℕ}
theorem localEnergy_norm_bound (x : Fin d → ℝ) {r : ℝ}
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
  have hc := localEnergy_norm_bound p.1 (by grind) hp.1
  have hz := localEnergy_norm_bound p.2.1 (by grind) hp.2.1
  exact ⟨hsub (by simpa using (norm_add_le _ _).trans_lt (by linarith)),
    hsub (by simpa using (norm_sub_le _ _).trans_lt (by linarith))⟩

end

section
variable {d : ℕ} {κ : Type*} (ψ : (Fin d → ℝ) → (κ → ℂ))
def parameterMiddle (p : LocalParameters d) : κ → CMat 2 :=
  chartMiddle ψ p.1 p.2.1 p.2.2

theorem continuous_parameterMiddle_on_box (U : Set (Fin d → ℝ))
    (hψ : ContinuousOn ψ U) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    Continuous (fun p : localParameterBox d r => parameterMiddle ψ p.val) := by
  have hp : Continuous (fun p : localParameterBox d r => ψ (p.val.1+p.val.2.1)) :=
    hψ.comp_continuous (by fun_prop) (by grind)
  have hm : Continuous (fun p : localParameterBox d r => ψ (p.val.1-p.val.2.1)) :=
    hψ.comp_continuous (by fun_prop) (by grind)
  exact continuous_pi fun j => (((continuous_apply j).comp hp).add ((continuous_apply j).comp hm)).div_const 2 |>.smul
    continuous_const |>.add (((((continuous_apply j).comp hp).sub ((continuous_apply j).comp hm)).div_const 2).smul
        (continuous_pauli.comp (by fun_prop)))

end

end GS.UnitaryLocalModel
