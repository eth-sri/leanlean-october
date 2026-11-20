module
public import HypoellipticAleksandrov.Parabolic.Transposition.Chain
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Transposing a Hörmander generator on interior tests -/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity MeasureTheory Set Filter KineticAleksandrov.Evolution
open scoped Topology
variable {d k : ℕ} {U : Domain d}

/-- The smooth fields on the interior, with arbitrary values off the domain. -/
def localFields (U : Domain d) : Subalgebra ℝ (TimeVelocity d → ℝ) where
  carrier := {f | ContDiffOn ℝ (⊤ : ℕ∞) f U}
  mul_mem' := ContDiffOn.mul
  add_mem' := ContDiffOn.add
  algebraMap_mem' _ := contDiffOn_const

abbrev Local (U : Domain d) := ↥(localFields U)

def onDomain (U : Domain d) (a : Field d) : Local U := ⟨a.1,a.2.contDiffOn⟩

theorem smooth_local (f : Local U) : ContDiffOn ℝ (⊤ : ℕ∞) f.val U := f.prop

def diff (i : Fin (d+1)) (f : Local U) : Local U :=
  ⟨pd i f.val, ((smooth_local f).fderiv_of_isOpen U.isOpen (by simp)).clm_apply contDiffOn_const⟩

theorem difAt {z : TimeVelocity d} (f : Local U) (hz : z ∈ U) : DifferentiableAt ℝ f.val z :=
  ((smooth_local f).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)

theorem local_apply (f : Local U) (φ : Test U) : weight U f.val φ = ∫ z in U, f.val z * φ z := by
  rw [weight, TestFunction.integralAgainstBilinCLM_eq_integral ((smooth_local f).continuousOn.locallyIntegrableOn U.isOpen.measurableSet)]
  simp [mul_comm]

theorem local_int (f : Local U) (φ : Test U) : IntegrableOn (fun z => f.val z * φ z) U :=
  (integrable_evolution_mul_test (smooth_local f).continuousOn φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset).integrableOn

def pair (φ : Test U) : Local U →ₗ[ℝ] ℝ where
  toFun f := weight U f.val φ
  map_add' f g := by simp only [local_apply]; simpa [add_mul] using integral_add (local_int f φ) (local_int g φ)
  map_smul' r f := by
    simp only [local_apply]; change (∫ z in U, r * f.val z * φ z) = r * _
    simp only [mul_assoc, integral_const_mul]

theorem pair_eq (f : Local U) (φ : Test U) : pair φ f = weight U f.val φ := rfl

theorem move_factor (f : Local U) (a : Field d) (φ : Test U) :
    weight U f.val (times a φ) = weight U (onDomain U a * f).val φ := by
  simp only [local_apply, times_val]; apply setIntegral_congr_fun U.isOpen.measurableSet; intro z _
  change f.val z * (a.val z * φ z) = a.val z * f.val z * φ z; ring

theorem move_diff (i : Fin (d+1)) (f : Local U) (φ : Test U) :
    weight U f.val (part i φ) = -weight U (diff i f).val φ := by
  simp only [local_apply, part_val]
  exact setIntegral_mul_evolution_directional_test (smooth_local f).continuousOn (smooth_local (diff i f)).continuousOn
    (dir i) (fun z hz => (difAt f hz).hasFDerivAt.hasLineDerivAt _) φ.contDiff φ.hasCompactSupport φ.tsupport_subset

theorem eqOn_of_pair {f g : Local U} (h : ∀ φ : Test U, pair φ f = pair φ g) : EqOn f.val g.val U := by
  have hg := smooth_local (f-g)
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ U.isOpen (smooth_local f).continuousOn (smooth_local g).continuousOn
  rw [EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet]
  have hz := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet) (fun v hv hc hs => ?_)
  · filter_upwards [hz] with z hz hu using sub_eq_zero.mp (hz hu)
  · let φ : Test U := ⟨v,hv,hc,hs⟩
    have eq : pair φ (f-g) = 0 := by rw [map_sub, h, sub_self]
    rw [pair_eq, local_apply, setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)] at eq
    · change (∫ z, (f-g).val z * v z) = 0 at eq
      simpa only [smul_eq_mul, mul_comm (v _) _] using eq
    · rw [image_eq_zero_of_notMem_tsupport (f := (φ : TimeVelocity d → ℝ)) (fun hm => hz (hs hm)), mul_zero]

def action (v : Vector d) (f : Local U) : Local U := ∑ j, onDomain U (v j) * diff j f

def generator (X : Fin (k+1) → Vector d) (f : TimeVelocity d → ℝ) (z) :=
  along (X 0) f z + ∑ i : Fin k, along (X i.succ) (along (X i.succ) f) z

def applied (X : Fin (k+1) → Vector d) (f : Local U) : Local U :=
  action (X 0) f + ∑ i : Fin k, action (X i.succ) (action (X i.succ) f)

private theorem val_sum {ι : Type*} [Fintype ι] (v : ι → Local U) : (∑ i, v i).val = ∑ i, (v i).val :=
  map_sum (localFields U).val _ _

theorem action_val (v : Vector d) (f : Local U) : (action v f).val = along v f.val := by
  funext z; simp only [action,val_sum,Finset.sum_apply,along]; rfl

theorem applied_val (X : Fin (k+1) → Vector d) (f : Local U) : (applied X f).val = generator X f.val := by
  funext z; simp only [applied,Subalgebra.coe_add,Pi.add_apply,val_sum,Finset.sum_apply,action_val,generator]

theorem adj_pair (v : Vector d) (f : Local U) (φ : Test U) : weight U f.val (adj v φ) = -weight U (action v f).val φ := by
  simp only [adj,map_sum,move_diff,move_factor,Finset.sum_neg_distrib]
  change _ = -pair φ (∑ j, onDomain U (v j) * diff j f)
  rw [map_sum]; rfl

theorem generator_pair (X : Fin (k+1) → Vector d) (f : Local U) (φ : Test U) :
    weight U f.val (adjoint X φ) = pair φ (applied X f) := by
  simp only [adjoint_apply,map_add,map_neg,map_sum,adj_pair,neg_neg,applied]; rfl

theorem smooth_solution {X : Fin (k+1) → Vector d} (g : Field d)
    (span : KineticAleksandrov.LieAlgebraSpansOn ((unpack d) ⁻¹' (U : Set _)) (fun i => liftField (X i)))
    (u : TimeVelocity d → ℝ) (hu : LocallyIntegrableOn u U volume)
    (h : ∀ φ : Test U, (∫ z in U, u z * adjoint X φ z) = ∫ z in U, g.val z * φ z) :
    ∃ w : Local U, u =ᵐ[volume.restrict U] w.val ∧ EqOn (generator X w.val) g.val U := by
  obtain ⟨w,hw,huw⟩ := smooth_rep X span hu g.prop (fun φ => by
    rw [← adjoint_apply,weight_apply (hu.mono_measure Measure.restrict_le_self),weight_apply (g.prop.continuous.locallyIntegrable.locallyIntegrableOn U),h])
  let f : Local U := ⟨w,hw⟩
  refine ⟨f,huw,applied_val X f ▸ eqOn_of_pair (f := applied X f) (g := onDomain U g) ?_⟩
  intro φ; rw [← generator_pair,local_apply,pair_eq,local_apply]
  change _ = ∫ z in U, g.val z * φ z; rw [← h φ]
  apply integral_congr_ae; filter_upwards [huw] with z e using congrArg (· * _) e.symm

end HypoellipticAleksandrov.Parabolic.Transposition
