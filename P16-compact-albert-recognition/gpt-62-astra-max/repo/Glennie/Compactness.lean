module
public import Glennie.Hilbert
public import Glennie.Automorphism
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

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

theorem continuous_native_inner : Continuous (fun p : Albert × Albert => inner p.1 p.2) :=
  (nativeInnerContinuous.continuous.comp continuous_fst).clm_apply continuous_snd

/- Maximize a continuous scalar on an automorphism orbit. In the native
operator norm the trace/product preserving isometries form a closed subset
of the compact unit ball. In finite dimension such isometries are onto. -/
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
private def Preserves (J : E →L[ℝ] E →L[ℝ] E) (t : E →L[ℝ] ℝ) (L : E →L[ℝ] E) := (∀ y z : E, L (J y z) = J (L y) (L z)) ∧
    (∀ y, t (L y) = t y) ∧ ∀ y, ‖L y‖ = ‖y‖
private theorem max_linear (J : E →L[ℝ] E →L[ℝ] E) (t : E →L[ℝ] ℝ) (F : E → ℝ) (hf : Continuous F) (x : E) :
    ∃ L, Preserves J t L ∧ ∀ H, Preserves J t H → F (H x) ≤ F (L x) := by
  let C := {L | Preserves J t L}
  have ev (y : E) : Continuous (fun L : E →L[ℝ] E => L y) := continuous_id.clm_apply continuous_const
  have closed : IsClosed C := by
    simp only [C,Preserves,Set.ofPred_and,Set.ofPred_forall]
    exact (isClosed_iInter fun y => isClosed_iInter fun z => isClosed_eq (ev _) ((J.continuous.comp (ev y)).clm_apply (ev z))).inter
      ((isClosed_iInter fun y => isClosed_eq (t.continuous.comp (ev y)) continuous_const).inter
        (isClosed_iInter fun y => isClosed_eq (ev y).norm continuous_const))
  have hc : IsCompact C := (isCompact_closedBall (0:E →L[ℝ] E) 1).of_isClosed_subset closed (by
    intro L h; simpa using L.opNorm_le_bound zero_le_one (fun y => by simp [h.2.2 y]))
  have hi : (ContinuousLinearMap.id ℝ E : E →L[ℝ] E) ∈ C := ⟨fun _ _ => rfl,fun _ => rfl,fun _ => rfl⟩
  obtain ⟨L,hL,hm⟩ := hc.exists_isMaxOn ⟨_,hi⟩ (hf.comp (ev x)).continuousOn
  exact ⟨L,hL,fun _ he => hm he⟩
end

theorem orbit_max (F : Albert → ℝ) (hf : Continuous F) (x : Albert) :
    ∃ g : CompactAutomorphism, ∀ h : CompactAutomorphism, F (h.equiv x) ≤ F (g.equiv x) := by
  obtain ⟨L,hL,hm⟩ := max_linear jordanContinuous traceLinear.toContinuousLinearMap F hf x
  let A : Albert →ₗᵢ[ℝ] Albert := ⟨L.toLinearMap,hL.2.2⟩
  refine ⟨⟨LinearEquiv.ofBijective L.toLinearMap ⟨A.injective, LinearMap.injective_iff_surjective.mp A.injective⟩,
    hL.1,hL.2.1⟩, fun g => ?_⟩
  let H :=  g.equiv.toLinearMap.toContinuousLinearMap
  apply hm H; exact ⟨g.map_jordan,g.map_trace,fun y => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (by change ‖g.equiv y‖^2 = _; rw [native_norm_sq,native_norm_sq,g.inner_map])⟩

end
end Glennie
