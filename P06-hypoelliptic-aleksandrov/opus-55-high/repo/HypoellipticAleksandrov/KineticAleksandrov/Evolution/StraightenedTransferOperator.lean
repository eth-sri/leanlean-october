module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedCoefficients
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedTransferCalculus
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData

/-!
# Chain rule: straightened operator versus the viscous transported operator

For a curve `g` and a function `ũ` of the straightened variables `(σ, (Y, z))`, the pullback
`u(σ, y, z) = ũ(σ, (y - g(σ), z))` is a function of the absolute kinetic variables.  The main
result `viscousTransportedOperator_straightenedPullback` is the pointwise identity
`L_ε u (σ, y, z) = (∂σ + a : D² + β · ∇) ũ (σ, (Y, z))` for the straightened block
coefficient `a = diag(B, ε I)` and the drift `β = (-g', b(g + Y))`.  The time derivative of the
pullback produces the term `-g'(σ) · ∇_Y ũ`; the spatial derivatives are the corresponding
blocks of the gradient and the Hessian of `ũ`.  The identity needs joint differentiability of
`ũ` at the point and `C²` regularity of its spatial slice, and nothing else.
-/

@[expose] public section

noncomputable section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter
open scoped Topology ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov

variable {n : ℕ}

/-- The pullback `u(σ, y, z) = ũ(σ, (y - g(σ), z))` of a function of the straightened variables
to the absolute kinetic variables. -/
def straightenedPullback (g : ℝ → PDE.Vec n) (ũ : TimeVelocity (n + n) → ℝ) :
    KineticPoint n → ℝ :=
  fun p => ũ (p.time, spatialPack (p.position - g p.time) p.velocity)

/-- The straightened point `(σ, (y - g(σ), z))` of an absolute kinetic point. -/
def straightenedPoint (g : ℝ → PDE.Vec n) (p : KineticPoint n) : TimeVelocity (n + n) :=
  (p.time, spatialPack (p.position - g p.time) p.velocity)

theorem continuous_spatialPack :
    Continuous (fun q : PDE.Vec n × PDE.Vec n => spatialPack q.1 q.2) :=
  (contDiff_spatialPack (m := 0) contDiff_fst contDiff_snd).continuous

theorem continuous_straightenedPoint {g : ℝ → PDE.Vec n} (hg : Continuous g) :
    Continuous (straightenedPoint g) :=
  continuous_time.prodMk (continuous_spatialPack.comp
    ((continuous_position.sub (hg.comp continuous_time)).prodMk continuous_velocity))

section Blocks

theorem vecDot_spatialPack_right (a b : PDE.Vec n) (w : PDE.Vec (n + n)) :
    PDE.vecDot w (spatialPack a b) = PDE.vecDot (spatialY w) a + PDE.vecDot (spatialZ w) b := by
  rw [vecDot_eq_spatial]
  simp

theorem vecDot_spatialPack_left (a b : PDE.Vec n) (w : PDE.Vec (n + n)) :
    PDE.vecDot (spatialPack a b) w = PDE.vecDot a (spatialY w) + PDE.vecDot b (spatialZ w) := by
  rw [PDE.vecDot_comm, vecDot_spatialPack_right, PDE.vecDot_comm, PDE.vecDot_comm b]

/-- Contraction with the block matrix `diag(A, ε I)` splits along the blocks. -/
theorem matrixContraction_viscousBlockMatrix (A : PDE.Mat n) (ε : ℝ) (H : PDE.Mat (n + n)) :
    matrixContraction (viscousBlockMatrix A ε) H =
      matrixContraction A (fun i j => H (Fin.castAdd n i) (Fin.castAdd n j)) +
        ε * ∑ i : Fin n, H (Fin.natAdd n i) (Fin.natAdd n i) := by
  simp only [matrixContraction, Fin.sum_univ_add, viscousBlockMatrix_castAdd_castAdd,
    viscousBlockMatrix_castAdd_addNat, viscousBlockMatrix_addNat_castAdd, zero_mul, Finset.sum_const_zero, add_zero, Fin.natAdd_eq_addNat]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

end Blocks

section Derivatives

variable {g : ℝ → PDE.Vec n} {ũ : TimeVelocity (n + n) → ℝ} {p : KineticPoint n}

/-- The velocity gradient of the pullback is the transported block of the spatial gradient. -/
theorem kineticVelocityGradient_straightenedPullback
    (h : DifferentiableAt ℝ (fun X => ũ (p.time, X)) (straightenedPoint g p).2) :
    kineticVelocityGradient (straightenedPullback g ũ) p =
      spatialZ (scalarSpatialGradient ũ (straightenedPoint g p)) := by
  have := classicalGradient_comp_block
    (f := fun X => ũ _) (ι := fun z' => spatialPack _ z')
    (hasFDerivAt_pack_right _ p.velocity) h (e := Fin.natAdd n)
    (fun i => embedZCLM_basisVec i)
  exact this

/-- The diffused Hessian of the pullback is the `YY` block of the spatial Hessian. -/
theorem diffusedHessian_straightenedPullback
    (h : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) (i j : Fin n) :
    diffusedHessian (straightenedPullback g ũ) p i j =
      scalarSpatialHessian ũ (straightenedPoint g p) (Fin.castAdd n i) (Fin.castAdd n j) := by
  have := hessian_comp_block
    (f := fun X => ũ _) (ι := fun y' => spatialPack _ p.velocity)
    (fun y' => hasFDerivAt_pack_left _ p.velocity y') (y := p.position) h
    (e := Fin.castAdd n) (fun i => embedYCLM_basisVec i) i j
  exact this

/-- The velocity Hessian of the pullback is the `zz` block of the spatial Hessian. -/
theorem kineticVelocityHessian_straightenedPullback
    (h : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) (i j : Fin n) :
    kineticVelocityHessian (straightenedPullback g ũ) p i j =
      scalarSpatialHessian ũ (straightenedPoint g p) (Fin.natAdd n i) (Fin.natAdd n j) := by
  have := hessian_comp_block
    (f := fun X => ũ _) (ι := fun z' => spatialPack _ z')
    (fun z' => hasFDerivAt_pack_right _ z') (y := p.velocity) h
    (e := Fin.natAdd n) (fun i => embedZCLM_basisVec i) i j
  exact this

/-- The time derivative of the pullback: the straightened time derivative plus the drift
term `-g'(σ) · ∇_Y ũ` produced by the moving frame. -/
theorem kineticTimeDerivative_straightenedPullback
    (hg : DifferentiableAt ℝ g p.time) (hũ : DifferentiableAt ℝ ũ (straightenedPoint g p)) :
    kineticTimeDerivative (straightenedPullback g ũ) p =
      scalarTimeDerivative ũ (straightenedPoint g p) +
        PDE.vecDot (-deriv g p.time)
          (spatialY (scalarSpatialGradient ũ (straightenedPoint g p))) := by
  set X := (straightenedPoint g p).2 with hX
  set L := fderiv ℝ ũ (straightenedPoint g p) with hL
  have hL' : HasFDerivAt ũ L _ := hũ.hasFDerivAt
  -- the curve `r ↦ (r, (y - g r, z))`
  have hcurve1 : HasDerivAt (fun r : ℝ => p.position - g r) (-deriv g p.time) p.time :=
    hg.hasDerivAt.const_sub p.position
  have hcurve2 : HasDerivAt (fun r : ℝ => spatialPack (p.position - g r) p.velocity)
      (spatialPack (-deriv g p.time) 0) p.time := by
    have h : HasDerivAt (fun r : ℝ => embedYCLM n _ + spatialPack 0 p.velocity)
        (embedYCLM n _) p.time :=
      HasDerivAt.add_const _ ((embedYCLM n).hasFDerivAt.comp_hasDerivAt p.time hcurve1)
    have hfun : (fun r : ℝ => spatialPack (p.position - g r) p.velocity) =
        fun r : ℝ => embedYCLM n (p.position - g r) + spatialPack 0 p.velocity := by
      funext r
      rw [embedYCLM_apply, ← spatialPack_add, add_zero, zero_add]
    rw [hfun]
    exact h
  have hcurve : HasDerivAt (fun r : ℝ => (r, spatialPack _ p.velocity))
      (1, spatialPack _ 0) p.time :=
    HasDerivAt.prodMk (hasDerivAt_id p.time) hcurve2
  have hcomp := hL'.comp_hasDerivAt p.time hcurve
  have h1 : kineticTimeDerivative (straightenedPullback g ũ) p =
      L (1, spatialPack (-deriv g p.time) 0) := hcomp.deriv
  -- split the derivative into its time part and its spatial part
  have hsplit : L (1, spatialPack (-deriv g p.time) 0) =
      L (1, 0) + L (0, spatialPack (-deriv g p.time) 0) := by
    rw [← map_add]
    simp
  have htime : L (1, 0) = scalarTimeDerivative ũ (straightenedPoint g p) := by
    have h := hL'.comp_hasDerivAt p.time
      (HasDerivAt.prodMk (hasDerivAt_id p.time) (hasDerivAt_const p.time X))
    exact h.deriv.symm
  have hspace : L (0, spatialPack (-deriv g p.time) 0) =
      PDE.vecDot (-deriv g p.time)
        (spatialY (scalarSpatialGradient ũ (straightenedPoint g p))) := by
    have hslice : HasFDerivAt (fun X' => ũ _) (L.comp (ContinuousLinearMap.inr ℝ ℝ
        (PDE.Vec _))) X :=
      hL'.comp X (hasFDerivAt_prodMk_right p.time X)
    have h2 : fderiv ℝ _ X = L.comp (ContinuousLinearMap.inr ℝ ℝ
        (PDE.Vec _)) := hslice.fderiv
    have h3 := PDE.fderiv_apply_eq_vecDot_classicalGradient (fun X' => ũ (p.time, X')) X
      (spatialPack (-deriv g p.time) 0)
    rw [h2] at h3
    change L (0, spatialPack _ 0) = _ at h3
    rw [h3]
    show PDE.vecDot (scalarSpatialGradient ũ (straightenedPoint g p)) _ = _
    rw [vecDot_spatialPack_right, PDE.vecDot_comm]
    simp [PDE.vecDot]
  rw [h1, hsplit, htime, hspace]

end Derivatives

section Operator

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε : ℝ}
  {g : ℝ → PDE.Vec n} {ũ : TimeVelocity (n + n) → ℝ} {p : KineticPoint n}

/-- The straightened coefficient at the straightened point of `p` is the block matrix of the
original coefficient at `p`. -/
theorem straightenedCoefficient_straightenedPoint (B : FullKineticCoefficient n)
    (g : ℝ → PDE.Vec n) (ε : ℝ) (p : KineticPoint n) :
    straightenedCoefficient B g ε (straightenedPoint g p).1 (straightenedPoint g p).2 =
      viscousBlockMatrix (B p.time p.position p.velocity) ε := by
  simp [straightenedCoefficient, straightenedPoint]

/-- The straightened drift at the straightened point of `p`. -/
theorem straightenedDrift_straightenedPoint (b : PDE.Vec n → PDE.Vec n) (g : ℝ → PDE.Vec n)
    (p : KineticPoint n) :
    straightenedDrift b g (straightenedPoint g p).1 (straightenedPoint g p).2 =
      spatialPack (-deriv g p.time) (b p.position) := by
  simp [straightenedDrift, straightenedPoint]

/-- **Chain-rule transfer of the operator.**  At a point where `ũ` is jointly differentiable and
its spatial slice is `C²`, the viscous transported operator `L_ε` of the pullback
`u(σ, y, z) = ũ(σ, (y - g(σ), z))` equals the straightened scalar operator
`∂σ + diag(B, ε I) : D² + (-g', b(g + Y)) · ∇` of `ũ` at `(σ, (y - g(σ), z))`. -/
theorem viscousTransportedOperator_straightenedPullback
    (hg : DifferentiableAt ℝ g p.time) (hũ : DifferentiableAt ℝ ũ (straightenedPoint g p))
    (hslice : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) :
    viscousTransportedOperator B b ε (straightenedPullback g ũ) p =
      scalarParabolicOperator (straightenedCoefficient B g ε) (straightenedDrift b g) ũ
        (straightenedPoint g p) := by
  have hdiff : DifferentiableAt ℝ (fun X => ũ (p.time, X)) _ :=
    hslice.differentiableAt (by norm_num)
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply,
    scalarParabolicOperator_apply, kineticTimeDerivative_straightenedPullback hg hũ,
    kineticVelocityGradient_straightenedPullback hdiff,
    straightenedCoefficient_straightenedPoint, straightenedDrift_straightenedPoint,
    matrixContraction_viscousBlockMatrix, vecDot_spatialPack_left]
  have hH : (fun i j => scalarSpatialHessian ũ (straightenedPoint g p) (Fin.castAdd n i)
      (Fin.castAdd n j)) = diffusedHessian (straightenedPullback g ũ) p := by
    funext i j
    exact (diffusedHessian_straightenedPullback hslice i j).symm
  have hV : ∑ i, kineticVelocityHessian _ p i i =
      ∑ i : Fin n, scalarSpatialHessian ũ _ _
        _ :=
    Finset.sum_congr rfl fun i _ => kineticVelocityHessian_straightenedPullback hslice i i
  rw [hH, hV]
  simp only [fullKineticCoefficientAt_apply]
  ring

end Operator

section Regularity

variable {g : ℝ → PDE.Vec n} {ũ : TimeVelocity (n + n) → ℝ} {p : KineticPoint n}

/-- Joint differentiability of `ũ` at the straightened point and differentiability of `g` give
differentiability of the time slice of the pullback. -/
theorem differentiableAt_time_straightenedPullback (hg : DifferentiableAt ℝ g p.time)
    (hũ : DifferentiableAt ℝ ũ (straightenedPoint g p)) :
    DifferentiableAt ℝ (fun r => straightenedPullback g ũ ⟨r, p.position, p.velocity⟩) p.time := by
  have hc : DifferentiableAt ℝ (fun r : ℝ => spatialPack (p.position - g r) p.velocity)
      p.time := by
    have h : DifferentiableAt ℝ (fun r : ℝ => embedYCLM n (p.position - g r) +
        spatialPack 0 p.velocity) p.time :=
      ((embedYCLM n).differentiableAt.comp p.time (hg.const_sub p.position)).add_const _
    have hfun : (fun r : ℝ => spatialPack (p.position - g r) p.velocity) =
        fun r : ℝ => embedYCLM n (p.position - g r) + spatialPack 0 p.velocity := by
      funext r
      rw [embedYCLM_apply, ← spatialPack_add, add_zero, zero_add]
    rw [hfun]
    exact h
  exact DifferentiableAt.comp (g := ũ) (f := fun r : ℝ => (r, spatialPack _
    p.velocity)) p.time hũ (differentiableAt_id.prodMk hc)

/-- `C²` regularity of the spatial slice of `ũ` at the straightened point gives `C²` regularity
of the diffused slice of the pullback. -/
theorem contDiffAt_position_straightenedPullback
    (hslice : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) :
    ContDiffAt ℝ 2 (fun y => straightenedPullback g ũ ⟨p.time, y, p.velocity⟩) p.position :=
  ContDiffAt.comp (g := fun X => ũ (p.time, X))
    (f := fun y : PDE.Vec n => spatialPack (y - g p.time) p.velocity) p.position hslice
    (contDiff_spatialPack (contDiff_id.sub contDiff_const) contDiff_const).contDiffAt

/-- `C²` regularity of the spatial slice of `ũ` at the straightened point gives `C²` regularity
of the transported slice of the pullback. -/
theorem contDiffAt_velocity_straightenedPullback
    (hslice : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) :
    ContDiffAt ℝ 2 (fun z => straightenedPullback g ũ ⟨p.time, p.position, z⟩) p.velocity :=
  ContDiffAt.comp (g := fun X => ũ (p.time, X))
    (f := fun z : PDE.Vec n => spatialPack (p.position - g p.time) z) p.velocity hslice
    (contDiff_spatialPack contDiff_const contDiff_id).contDiffAt

/-- The pullback is slice regular wherever `ũ` is jointly differentiable with a `C²` spatial
slice.  This is the regularity hypothesis of the comparison theorems. -/
theorem isSliceRegularAt_straightenedPullback (hg : DifferentiableAt ℝ g p.time)
    (hũ : DifferentiableAt ℝ ũ (straightenedPoint g p))
    (hslice : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) :
    IsSliceRegularAt (straightenedPullback g ũ) p :=
  ⟨differentiableAt_time_straightenedPullback hg hũ,
    contDiffAt_position_straightenedPullback hslice,
    contDiffAt_velocity_straightenedPullback hslice⟩

end Regularity

end HypoellipticAleksandrov.KineticAleksandrov
