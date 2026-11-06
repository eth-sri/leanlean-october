module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! # C² homogeneous functions and their continuous Bellman images -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The open punctured product plane. -/
def bellmanPuncturedSet : Set (ℝ × ℝ) := {q | q ≠ (0, 0)}

/-- The literal C² homogeneity property used in the source separation argument. -/
def IsBellmanHomogeneous (alpha : ℝ) (phi : (ℝ × ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 phi bellmanPuncturedSet ∧
    ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      phi (bellmanPlaneDilation r q) = r ^ alpha * phi q

variable (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ)

/-- The position directional derivative. -/
def bellmanDx  : ℝ :=
  fderiv ℝ phi q (1, 0)

/-- The velocity directional derivative. -/
def bellmanDv  : ℝ :=
  fderiv ℝ phi q (0, 1)

/-- The second velocity derivative. -/
def bellmanDvv  : ℝ :=
  fderiv ℝ (bellmanDv phi) q (0, 1)

/-- The constant-diffusion operator in the source sign convention. -/
def bellmanOperator (b : ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  q.2 * bellmanDx phi q + b * bellmanDvv phi q

/-- The punctured carrier is open. -/
theorem bellmanPuncturedSet_isOpen : IsOpen bellmanPuncturedSet := isOpen_ne_fun
  continuous_id continuous_const

section
variable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha phi)

include h
/-- C² homogeneity gives a C¹ directional derivative on the punctured plane. -/
theorem IsBellmanHomogeneous.directional_contDiffOn  (e : ℝ × ℝ) :
    ContDiffOn ℝ 1 (fun q => fderiv ℝ phi q e) bellmanPuncturedSet := (h.1.fderiv_of_isOpen bellmanPuncturedSet_isOpen (by norm_num)).clm_apply
    contDiffOn_const

/-- Each first jet is continuous on the source carrier. -/
theorem IsBellmanHomogeneous.dx_continuousOn  :
    ContinuousOn (bellmanDx phi) bellmanPuncturedSet :=
  (h.directional_contDiffOn (1, 0)).continuousOn

/-- The second velocity jet is continuous on the source carrier. -/
theorem IsBellmanHomogeneous.dvv_continuousOn  :
    ContinuousOn (bellmanDvv phi) bellmanPuncturedSet := ((h.directional_contDiffOn (0, 1)).fderiv_of_isOpen
    bellmanPuncturedSet_isOpen (m := 0) (by norm_num)).continuousOn.clm_apply
    continuousOn_const
end


/-- The Bellman expression is continuous on the sphere and coefficient interval. -/
theorem IsBellmanHomogeneous.image_continuous {alpha lam Lam : ℝ}
    {phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha phi) :
    Continuous (fun w : BellmanSphere × BellmanCoefficient lam Lam =>
      bellmanOperator w.2.val phi w.1.val) := by
  let sharedTerm_b1d55ae621 := ((fun w : BellmanSphere × BellmanCoefficient lam Lam => w.1.val))
  have hz : Continuous sharedTerm_b1d55ae621 :=
    continuous_subtype_val.comp continuous_fst
  have hm : MapsTo sharedTerm_b1d55ae621
      univ bellmanPuncturedSet := fun w _ => w.1.ne_zero


  exact ((continuous_snd.comp hz).mul (continuousOn_univ.mp (h.dx_continuousOn.comp hz.continuousOn hm))).add
    ((continuous_subtype_val.comp continuous_snd).mul (continuousOn_univ.mp (h.dvv_continuousOn.comp hz.continuousOn hm)))

/-- The continuous image of one C² homogeneous function. -/
def bellmanImage {alpha : ℝ} (lam Lam : ℝ) (phi : (ℝ × ℝ) → ℝ)
    (h : IsBellmanHomogeneous alpha phi) : C(BellmanSphere × BellmanCoefficient lam Lam, ℝ) :=
  ⟨fun w => bellmanOperator w.2.val phi w.1.val, h.image_continuous⟩

/-- C² homogeneous functions form a genuine linear subspace of ambient functions. -/
def bellmanHomogeneousSpace (alpha : ℝ) : Submodule ℝ ((ℝ × ℝ) → ℝ) where
  carrier := {phi | IsBellmanHomogeneous alpha phi}
  zero_mem' := by
    refine ⟨contDiffOn_const, ?_⟩
    intro r hr q hq
    simp
  add_mem' := by
    intro phi psi hphi hpsi
    refine ⟨hphi.1.add hpsi.1, ?_⟩
    intro r hr q hq
    simp only [Pi.add_apply, hphi.2 r hr q hq, hpsi.2 r hr q hq, mul_add]
  smul_mem' := by
    intro c phi hphi
    refine ⟨contDiffOn_const.smul hphi.1, ?_⟩
    intro r hr q hq
    simp only [Pi.smul_apply, smul_eq_mul, hphi.2 r hr q hq]
    ring

end HypoellipticAleksandrov.KineticAleksandrov
