module

public import DedekindZetaZeroFree.Theta.Periods.CenteredLogarithmicIdealAverages

@[expose] public section

noncomputable section
open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient
open Module NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open scoped Classical
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
namespace DedekindZetaZeroFree.Hecke.Theta.Bridge
variable (F : Type) [Field F] [NumberField F]
private theorem sum_basis (i : InfinitePlace F) :
    (∑ v, completeBasis F i v) = if i = w₀ then (Module.finrank ℚ F : ℝ) else 0 := by
  classical
  by_cases hi : i = w₀
  · subst i
    simp [completeBasis_apply_of_eq, ← Nat.cast_sum, sum_mult_eq]
  · rw [if_neg hi, completeBasis_apply_of_ne F ⟨i, hi⟩]
    rw [sum_expMap_symm_apply (NumberField.Units.coe_ne_zero _),
      NumberField.Units.norm, Rat.cast_one, Real.log_one]
private theorem sum_symm (x : realSpace F) :
    (∑ v, (completeBasis F).equivFun.symm x v) =
      x w₀ * (Module.finrank ℚ F : ℝ) := by
  classical
  simp only [Basis.equivFun_symm_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_basis]
  simp
 section

variable (h : RayCoset.logHyperplane F)

def weighted : realSpace F :=
  fun v => (v.mult : ℝ) * h.val v
private theorem sum_weighted : ∑ v, weighted F h v = 0 := by
  simpa [weighted, RayCoset.logHyperplane, RayCoset.weightedLogSum] using h.property
private theorem coord_zero :
    (completeBasis F).equivFun (weighted F h) w₀ = 0 := by
  have hs := sum_symm F ((completeBasis F).equivFun (weighted F h))
  rw [LinearEquiv.symm_apply_apply, sum_weighted] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')

end
 def coordMap : RayCoset.logHyperplane F →ₗ[ℝ] Theta.Angular F where
  toFun h v := (completeBasis F).equivFun (weighted F h) v
  map_add' h g := by
    have he : weighted F (h+g) = weighted F h + weighted F g := by ext v; simp [weighted, mul_add]
    ext v
    simp only [he, map_add, Pi.add_apply]
  map_smul' r h := by
    have he : weighted F (r • h) = r • weighted F h := by ext v; simp [weighted, mul_left_comm]
    ext v
    simp only [he, map_smul, Pi.smul_apply, RingHom.id_apply]
private theorem lift_coordMap (h : RayCoset.logHyperplane F) :
    Theta.angularLift F (coordMap F h) = (completeBasis F).equivFun (weighted F h) := by
  classical
  ext v
  by_cases hv : v = w₀
  · subst v; simp [Theta.angularLift, coord_zero]
  · simp [Theta.angularLift, hv, coordMap]
 theorem bijective : Function.Bijective (coordMap F) := by
  constructor
  · intro h g he
    have hh := congrArg (Theta.angularLift F) he
    rw [lift_coordMap, lift_coordMap] at hh
    apply Subtype.ext
    ext v
    exact mul_left_cancel₀ mult_coe_ne_zero (congrFun ((completeBasis F).equivFun.injective hh) v)
  · intro u
    let h := fun v => (completeBasis F).equivFun.symm (Theta.angularLift F u) v / (v.mult : ℝ)
    have hm : h ∈ RayCoset.logHyperplane F := by
      have hs := sum_symm F (Theta.angularLift F u)
      rw [show Theta.angularLift F u w₀ = 0 by simp [Theta.angularLift], zero_mul] at hs
      change RayCoset.weightedLogSum F h = 0
      simpa only [RayCoset.weightedLogSum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, h, mul_div_cancel₀ _ mult_coe_ne_zero] using hs
    refine ⟨⟨h, hm⟩, ?_⟩
    have hw : weighted F ⟨h, hm⟩ = (completeBasis F).equivFun.symm (Theta.angularLift F u) := by
      ext v
      simp [weighted, h, mul_div_cancel₀, mult_coe_ne_zero]
    ext v
    change (completeBasis F).equivFun (weighted F ⟨h, hm⟩) v = u v
    rw [hw, LinearEquiv.apply_symm_apply]
    simp [Theta.angularLift, v.property]
 def equiv : RayCoset.logHyperplane F ≃L[ℝ] Theta.Angular F :=
  (LinearEquiv.ofBijective (coordMap F) (bijective F)).toContinuousLinearEquiv
private theorem lift_equiv (h : RayCoset.logHyperplane F) :
    Theta.angularLift F (equiv F h) = (completeBasis F).equivFun (weighted F h) :=
  lift_coordMap F h

variable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t)

include ht in
private theorem theta_eq
    (h : RayCoset.logHyperplane F) :
    centeredLogIdealTheta F I t h = Theta.mixedRadialTheta F I t (equiv F h) := by
  unfold centeredLogIdealTheta Theta.mixedRadialTheta
  rw [dif_pos ht]
  congr 1
  let b := (Real.log t - Real.log (Theta.mixedThetaCovolume F I)) / (Module.finrank ℚ F : ℝ)
  have hr : (completeBasis F).equivFun.symm (Theta.radialLift F b) =
      fun v => b * (v.mult : ℝ) := by
    ext v
    simp only [Basis.equivFun_symm_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Theta.radialLift]
    simp [completeBasis_apply_of_eq]
  have he : (t / Theta.mixedThetaCovolume F I) ^ ((Module.finrank ℚ F : ℝ)⁻¹) = Real.exp b := by
    rw [Real.rpow_def_of_pos (div_pos ht (mixedThetaCovolume_pos F I)), Real.log_div ht.ne' (mixedThetaCovolume_pos F I).ne']
    rfl
  ext v
  change (t / Theta.mixedThetaCovolume F I) ^ ((Module.finrank ℚ F : ℝ)⁻¹) * Real.exp (h.val v) =
    expMapBasis (Theta.angularLift F (equiv F h) + Theta.radialLift F b) v
  rw [expMapBasis_apply, map_add, lift_equiv, LinearEquiv.symm_apply_apply, hr, expMap_apply, Pi.add_apply]
  dsimp [weighted]
  rw [mul_add, inv_mul_cancel_left₀ mult_coe_ne_zero]
  have hv : (v.mult : ℝ)⁻¹ * (b * (v.mult : ℝ)) = b := by field_simp
  rw [hv, Real.exp_add, he, mul_comm]
include ht in
private theorem periodic
    (γ : RayCoset.rayUnitLogLattice F ⊤) (h : RayCoset.logHyperplane F) :
    centeredLogIdealTheta F I t (h + (γ : RayCoset.logHyperplane F)) = centeredLogIdealTheta F I t h := by
  obtain ⟨u, hu⟩ := γ.property
  let e := u.toMul.val
  have he (v : InfinitePlace F) : 0 < v (e : F) := NumberField.Units.pos_at_place e v
  have hs : centeredLogShape F I t (h + γ) =
      fun v => v (algebraMap (𝓞 F) F e) * centeredLogShape F I t h v := by
    ext v
    simp only [centeredLogShape, hu.symm, Submodule.coe_add, Pi.add_apply, RayCoset.logAbs_apply]
    change (t / Theta.mixedThetaCovolume F I) ^ ((Module.finrank ℚ F : ℝ)⁻¹) *
      Real.exp (h.val v + Real.log (v (e : F))) = _
    rw [Real.exp_add, Real.exp_log (he v)]
    ring
  unfold centeredLogIdealTheta
  rw [dif_pos ht, dif_pos ht]
  have hq : ∀ v, v (algebraMap (𝓞 F) F e) * centeredLogShape F I t h v ≠ 0 := by
    intro v
    rw [← congrFun hs v]
    exact ne_of_gt (centeredLogShape_pos F I ht _ v)
  convert Theta.fractionalShapeIdealTheta_unit_invariant F I e (centeredLogShape F I t h)
    (fun v => ne_of_gt (centeredLogShape_pos F I ht h v)) hq using 1
  congr 1
end DedekindZetaZeroFree.Hecke.Theta.Bridge

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

alias logAngularEquiv := Bridge.equiv

theorem centeredLogIdealTheta_eq_mixedRadialTheta
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t)
    (h : RayCoset.logHyperplane F) :
    centeredLogIdealTheta F I t h =
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta F I t
        (logAngularEquiv F h) := Bridge.theta_eq F I t ht h

alias centeredLogIdealTheta_rayUnit_periodic := Bridge.periodic

end DedekindZetaZeroFree.Hecke.Theta

end
