module

public import HypoellipticAleksandrov.Parabolic.Derivatives

/-!
# Parabolic contact-map data

This module defines the affine velocity functions, slope--intercept wedge,
parabolic normal map, and measurable-sign-set candidate used in the smooth
parabolic ABP argument.  Coverage and Jacobian results belong to later modules.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Matrix

section
variable {d : ℕ} (y₀ : PDE.Vec d) (h : ℝ)

include y₀ h in
/-- The affine velocity function with intercept `h`, slope `p`, and center `y₀`. -/
def affineVelocity (p : PDE.Vec d)
    (v : PDE.Vec d) : ℝ :=
  h + PDE.vecDot p (v - y₀)

/-- Evaluation of an affine velocity function. -/
@[simp] theorem affineVelocity_apply
    (p v : PDE.Vec d) :
    affineVelocity y₀ h p v = h + PDE.vecDot p (v - y₀) :=
  rfl

end

/-- The open slope--intercept wedge associated with a height `M`. -/
def slopeInterceptWedge (d : ℕ) (M : ℝ) : Set (TimeVelocity d) :=
  Set.Ioo (M / 2) (3 * M / 4) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) (M / 4)

section
variable {d : ℕ} (u : TimeVelocity d → ℝ) (T : ℝ) (y₀ : PDE.Vec d)

/-- Membership in the slope--intercept wedge. -/
@[simp] theorem mem_slopeInterceptWedge_iff {M h : ℝ} {p : PDE.Vec d} :
    (h, p) ∈ slopeInterceptWedge d M ↔
      M / 2 < h ∧ h < 3 * M / 4 ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4) := by
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hp⟩
    exact ⟨hlower, hupper, hp⟩
  · rintro ⟨hlower, hupper, hp⟩
    exact ⟨⟨hlower, hupper⟩, hp⟩

include u y₀ in
/-- The parabolic normal map built from the velocity gradient of `u`. -/
noncomputable def parabolicNormalMap :
    TimeVelocity d → TimeVelocity d :=
  fun z ↦
    (u z - PDE.vecDot (velocityGradient u z) (z.2 - y₀), velocityGradient u z)

/-- Evaluation of the parabolic normal map. -/
@[simp] theorem parabolicNormalMap_apply (z : TimeVelocity d) :
    parabolicNormalMap u y₀ z =
      (u z - PDE.vecDot (velocityGradient u z) (z.2 - y₀), velocityGradient u z) :=
  rfl

include T y₀ in
/-- The interior sign set on which the parabolic Jacobian has the required sign. -/
def parabolicSignSet (u : TimeVelocity d → ℝ) :
    Set (TimeVelocity d) :=
  {z | z ∈ parabolicInterior T y₀ ∧ 0 < u z ∧
    0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef}

/-- Membership in the parabolic sign set. -/
@[simp] theorem mem_parabolicSignSet_iff {T : ℝ} {y₀ : PDE.Vec d}
    {u : TimeVelocity d → ℝ} {z : TimeVelocity d} :
    z ∈ parabolicSignSet T y₀ u ↔
      z ∈ parabolicInterior T y₀ ∧ 0 < u z ∧
        0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef :=
  Iff.rfl

end

private theorem isClosed_isHermitian (d : ℕ) :
    IsClosed {H : PDE.Mat d | H.IsHermitian} := by
  have hset :
      {H : PDE.Mat d | H.IsHermitian} =
        ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j
      exact h.apply i j
    · intro h
      apply Matrix.IsHermitian.ext
      intro i j
      exact h i j
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)

private theorem isClosed_posSemidef (d : ℕ) :
    IsClosed {H : PDE.Mat d | H.PosSemidef} := by
  have hset :
      {H : PDE.Mat d | H.PosSemidef} =
        {H : PDE.Mat d | H.IsHermitian} ∩
          ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ q ⬝ᵥ (H *ᵥ q)} := by
    ext H
    simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
  rw [hset]
  refine (isClosed_isHermitian d).inter (isClosed_iInter fun q => ?_)
  exact isClosed_le continuous_const (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

variable {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
include hu

/-- A globally `C²` scalar function has continuous time derivative. -/
theorem continuous_timeDerivative : Continuous (timeDerivative u) := by
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

/-- A globally `C²` scalar function has continuous velocity Hessian. -/
theorem continuous_velocityHessian : Continuous (velocityHessian u) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun z : TimeVelocity d ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1))
  fun_prop

/-- The parabolic sign set of a globally `C²` scalar function is measurable. -/
theorem measurableSet_parabolicSignSet (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicSignSet T y₀ u) := by
  have htime := continuous_timeDerivative hu
  have hhess := continuous_velocityHessian hu
  have hpsd :=
    ((isClosed_posSemidef d).preimage hhess.neg).measurableSet
  rw [show parabolicSignSet T y₀ u =
      parabolicInterior T y₀ ∩ {z | 0 < u z} ∩ {z | 0 ≤ timeDerivative u z} ∩
        {z | (-velocityHessian u z).PosSemidef} by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_parabolicSignSet_iff]
    constructor
    · grind
    · grind]
  exact (((measurableSet_parabolicInterior T y₀).inter
    (isOpen_lt continuous_const hu.continuous).measurableSet).inter
      (isClosed_le continuous_const htime).measurableSet).inter hpsd

end HypoellipticAleksandrov.Parabolic
