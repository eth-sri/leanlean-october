/- Compactness of the actual native automorphism maps.
The maximum theorem does not assert diagonalization; explicit rotations are
needed to show that a maximizing point has vanishing off-diagonal entries. -/
module
public import Glennie.Hilbert
public import Glennie.Automorphism
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Operator.NormedSpace
@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def jordanContinuous : Albert →L[ℝ] Albert →L[ℝ] Albert :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Albert →ₗ[ℝ] Albert) ≃ₗ[ℝ] (Albert →L[ℝ] Albert)).toLinearMap.comp jordanLinear)

@[simp] theorem jordanContinuous_apply (x y : Albert) :
    jordanContinuous x y = jordan x y := rfl

theorem continuous_jordan : Continuous (fun p : Albert × Albert => jordan p.1 p.2) :=
  (jordanContinuous.continuous.comp continuous_fst).clm_apply continuous_snd

section StableNativePairing
set_option backward.isDefEq.respectTransparency false
theorem nativeRealSMulComm : SMulCommClass ℝ ℝ ℝ := inferInstance
theorem nativeRealContinuousAdd : ContinuousAdd ℝ := inferInstance
theorem nativeRealContinuousSMul : ContinuousConstSMul ℝ ℝ := inferInstance
attribute [local instance 20000] nativeRealSMulComm nativeRealContinuousAdd nativeRealContinuousSMul
def nativeInnerLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := inner x
      map_add' y z := inner_add_right x y z
      map_smul' r y := inner_smul_right r x y }
  map_add' x y := by ext z; exact inner_add_left x y z
  map_smul' r x := by ext y; exact inner_smul_left r x y

theorem nativeInnerRight_cont (x : Albert) : Continuous (fun y => inner x y) :=
  (nativeInnerLinear x).continuous_of_finiteDimensional
def nativeInnerRight (x : Albert) : Albert →L[ℝ] ℝ where
  toLinearMap := nativeInnerLinear x
  cont := nativeInnerRight_cont x
theorem nativeInnerRight_add (x y : Albert) :
    nativeInnerRight (x + y) = nativeInnerRight x + nativeInnerRight y :=
  ContinuousLinearMap.ext (fun z => inner_add_left x y z)
theorem nativeInnerRight_smul (r : ℝ) (x : Albert) :
    nativeInnerRight (r • x) = r • nativeInnerRight x :=
  ContinuousLinearMap.ext (fun y => inner_smul_left r x y)
def nativeInnerRightLinear : Albert →ₗ[ℝ] (Albert →L[ℝ] ℝ) where
  toFun := nativeInnerRight
  map_add' := nativeInnerRight_add
  map_smul' := nativeInnerRight_smul
theorem nativeInnerRightLinear_cont : Continuous nativeInnerRightLinear :=
  nativeInnerRightLinear.continuous_of_finiteDimensional
def nativeInnerContinuous : Albert →L[ℝ] Albert →L[ℝ] ℝ where
  toLinearMap := nativeInnerRightLinear
  cont := nativeInnerRightLinear_cont
end StableNativePairing

theorem CompactAutomorphism.norm_map (g : CompactAutomorphism) (x : Albert) :
    ‖g.equiv x‖ = ‖x‖ := by
  have h : ‖g.equiv x‖ ^ 2 = ‖x‖ ^ 2 := by simp only [native_norm_sq, g.inner_map]
  nlinarith [norm_nonneg (g.equiv x), norm_nonneg x]

theorem continuous_native_inner : Continuous (fun p : Albert × Albert => inner p.1 p.2) :=
  (nativeInnerContinuous.continuous.comp continuous_fst).clm_apply continuous_snd

@[fun_prop] theorem continuous_jordan_comp {A : Type*} [TopologicalSpace A] {f g : A → Albert}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => jordan (f x) (g x)) :=
  by simpa only [Function.comp_def] using continuous_jordan.comp (hf.prodMk hg)

@[fun_prop] theorem continuous_inner_comp {A : Type*} [TopologicalSpace A] {f g : A → Albert}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => inner (f x) (g x)) :=
  by simpa only [Function.comp_def] using continuous_native_inner.comp (hf.prodMk hg)

@[fun_prop] theorem continuous_trace_comp {A : Type*} [TopologicalSpace A] {f : A → Albert}
    (hf : Continuous f) : Continuous (fun x => trace (f x)) := by
  simpa only [inner_unit_right] using continuous_inner_comp hf (continuous_const (y := (1 : Albert)))

def diagonalEnergy (x : Albert) : ℝ := x.d0^2 + x.d1^2 + x.d2^2

private theorem continuous_diagonalEnergy : Continuous diagonalEnergy := by
  have hc := Albert.coordinateLinearEquiv.continuous_of_finiteDimensional
  exact ((hc.fst.pow 2).add (hc.snd.fst.pow 2)).add (hc.snd.snd.fst.pow 2)

local notation "End" => Albert →L[ℝ] Albert
local instance : NormedSpace ℝ End := ContinuousLinearMap.toNormedSpace
open Metric

private def automorphismMaps : Set End := {g |
  (∀ x y, g (jordan x y) = jordan (g x) (g y)) ∧ ∀ x, trace (g x) = trace x}

private theorem automorphismMaps_closed : IsClosed automorphismMaps := by
  simp only [automorphismMaps, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (by fun_prop) (by fun_prop)).inter
    (isClosed_iInter fun x => isClosed_eq (by fun_prop) continuous_const)

private theorem norm_eq_of_mem {g : End} (hg : g ∈ automorphismMaps) (x : Albert) : ‖g x‖ = ‖x‖ := by
  have h : ‖g x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [native_norm_sq, native_norm_sq, inner, ← hg.1, hg.2]; rfl
  simpa using (sq_eq_sq_iff_abs_eq_abs _ _).mp h

private theorem automorphismMaps_compact : IsCompact automorphismMaps := by
  let : FiniteDimensional ℝ End := ContinuousLinearMap.finiteDimensional
  let : ProperSpace End := FiniteDimensional.proper ℝ End
  have hball : IsCompact (closedBall (0 : End) 1) := isCompact_closedBall _ _
  refine hball.of_isClosed_subset automorphismMaps_closed fun g hg => ?_
  exact mem_closedBall_zero_iff.mpr (g.opNorm_le_bound zero_le_one (by simp [norm_eq_of_mem hg]))

/-- The norm-bounded closed set of product-and-trace preserving linear maps
contains a diagonal-energy maximizer. Norm preservation makes it bijective. -/
theorem exists_diagonalEnergy_maximum (x : Albert) :
    ∃ g : CompactAutomorphism, ∀ h : CompactAutomorphism,
      diagonalEnergy (h.equiv x) ≤ diagonalEnergy (g.equiv x) := by
  have hc : Continuous (fun g : End => diagonalEnergy (g x)) :=
    continuous_diagonalEnergy.comp (ContinuousLinearMap.apply ℝ Albert x).continuous
  obtain ⟨g, hg, hmax⟩ := automorphismMaps_compact.exists_isMaxOn ⟨1, by
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩⟩ hc.continuousOn
  have hinj : Function.Injective g := (LinearIsometry.mk g.toLinearMap (norm_eq_of_mem hg)).injective
  let e := LinearEquiv.ofBijective g.toLinearMap ⟨hinj, g.toLinearMap.injective_iff_surjective.mp hinj⟩
  refine ⟨⟨e, hg.1, hg.2⟩, fun h => ?_⟩
  exact hmax (show h.equiv.toContinuousLinearEquiv.toContinuousLinearMap ∈ automorphismMaps from
    ⟨h.map_jordan, h.map_trace⟩)

end
end Glennie
