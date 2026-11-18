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

abbrev AutomorphismColumns := Fin 27 → Albert

def automorphismBasis : Module.Basis (Fin 27) ℝ Albert :=
  Module.finBasisOfFinrankEq ℝ Albert albert_finrank

def columnMap (v : AutomorphismColumns) : Albert →ₗ[ℝ] Albert :=
  automorphismBasis.constr ℝ v

@[simp] theorem columnMap_basis (v : AutomorphismColumns) (i : Fin 27) :
    columnMap v (automorphismBasis i) = v i :=
  automorphismBasis.constr_basis ℝ v i

@[simp] theorem columnMap_linearImage (f : Albert →ₗ[ℝ] Albert) :
    columnMap (fun i => f (automorphismBasis i)) = f :=
  automorphismBasis.constr_self ℝ f

theorem continuous_columnMap_apply (x : Albert) :
    Continuous (fun v : AutomorphismColumns => columnMap v x) := by
  dsimp only [columnMap]; simp_rw [automorphismBasis.constr_apply_fintype ℝ _ x]
  exact continuous_finsetSum Finset.univ fun i _ =>
    (continuous_const : Continuous fun _ : AutomorphismColumns => automorphismBasis.equivFun x i).smul (continuous_apply i)

def automorphismMaps : Set AutomorphismColumns :=
  {v | columnMap v 1 = 1 ∧
    (∀ x y, columnMap v (jordan x y) = jordan (columnMap v x) (columnMap v y)) ∧
    ∀ x y, inner (columnMap v x) (columnMap v y) = inner x y}

theorem automorphismMaps_compact : IsCompact automorphismMaps := by
  have hev (x : Albert) := continuous_columnMap_apply x
  have hclosed : IsClosed automorphismMaps := by
    rw [show automorphismMaps = {v | columnMap v 1 = 1} ∩
      ((⋂ x, ⋂ y, {v | columnMap v (jordan x y) = jordan (columnMap v x) (columnMap v y)}) ∩
       (⋂ x, ⋂ y, {v | inner (columnMap v x) (columnMap v y) = inner x y})) by ext; simp [automorphismMaps]]
    exact (isClosed_eq (hev 1) (continuous_const : Continuous fun _ : AutomorphismColumns => (1 : Albert))).inter
      ((isClosed_iInter fun x => isClosed_iInter fun y =>
          isClosed_eq (hev _) (by simpa only [Function.comp_def] using continuous_jordan.comp ((hev x).prodMk (hev y)))).inter
        (isClosed_iInter fun x => isClosed_iInter fun y =>
          isClosed_eq (by simpa only [Function.comp_def] using continuous_native_inner.comp ((hev x).prodMk (hev y)))
            (continuous_const : Continuous fun _ : AutomorphismColumns => inner x y)))
  refine (isCompact_pi_infinite fun i => isCompact_closedBall (0 : Albert) ‖automorphismBasis i‖).of_isClosed_subset hclosed
    fun v hv i => ?_
  have h := hv.2.2 (automorphismBasis i) (automorphismBasis i)
  rw [← native_norm_sq, ← native_norm_sq, columnMap_basis] at h
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (by nlinarith [norm_nonneg (v i), norm_nonneg (automorphismBasis i)] : ‖v i‖ ≤ ‖automorphismBasis i‖)

def compactAutomorphismOfMap (v : AutomorphismColumns) (hv : v ∈ automorphismMaps) : CompactAutomorphism := by
  have hinj : Function.Injective (columnMap v) := fun x y hxy =>
    sub_eq_zero.mp ((inner_self_eq_zero _).mp (by simpa only [map_sub, hxy, sub_self, inner_zero_left] using (hv.2.2 (x - y) (x - y)).symm))
  exact ⟨LinearEquiv.ofBijective (columnMap v) ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩, hv.2.1,
    fun x => by simpa only [LinearEquiv.ofBijective_apply, hv.1, inner_unit_right] using hv.2.2 x 1⟩

def diagonalEnergy (x : Albert) : ℝ := x.d0 ^ 2 + x.d1 ^ 2 + x.d2 ^ 2

theorem exists_diagonalEnergy_maximum (x : Albert) :
    ∃ g : CompactAutomorphism, ∀ h : CompactAutomorphism, diagonalEnergy (h.equiv x) ≤ diagonalEnergy (g.equiv x) := by
  have hcd_i (i : Fin 3) : Continuous (fun y : Albert => ![y.d0, y.d1, y.d2] i) :=
    ({ toFun := fun y : Albert => ![y.d0, y.d1, y.d2] i, map_add' := fun _ _ => by fin_cases i <;> rfl,
       map_smul' := fun _ _ => by fin_cases i <;> rfl } : Albert →ₗ[ℝ] ℝ).continuous_of_finiteDimensional
  have hcd : Continuous diagonalEnergy := (((hcd_i 0).pow 2).add ((hcd_i 1).pow 2)).add ((hcd_i 2).pow 2)
  have hc : Continuous (fun v : AutomorphismColumns => diagonalEnergy (columnMap v x)) := by
    simpa only [Function.comp_def] using hcd.comp (continuous_columnMap_apply x)
  have hne : automorphismMaps.Nonempty := ⟨fun i => automorphismBasis i, by
    have hm : columnMap (fun i => automorphismBasis i) = .id := columnMap_linearImage .id
    change columnMap _ 1 = 1 ∧ _; rw [hm]; exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  obtain ⟨v, hv, hmax⟩ := automorphismMaps_compact.exists_isMaxOn hne hc.continuousOn
  refine ⟨compactAutomorphismOfMap v hv, fun h => ?_⟩
  have ha (z : Albert) : columnMap (fun i => h.equiv (automorphismBasis i)) z = h.equiv z := by
    rw [show columnMap (fun i => h.equiv (automorphismBasis i)) = h.equiv.toLinearMap from columnMap_linearImage h.equiv.toLinearMap]; rfl
  have hm : diagonalEnergy (columnMap (fun i => h.equiv (automorphismBasis i)) x) ≤ diagonalEnergy (columnMap v x) :=
    hmax ⟨by simpa only [ha] using h.map_unit, fun a b => by simpa only [ha] using h.map_jordan a b,
      fun a b => by simpa only [ha] using h.inner_map a b⟩
  simpa only [ha, compactAutomorphismOfMap, LinearEquiv.ofBijective_apply] using hm

end
end Glennie
