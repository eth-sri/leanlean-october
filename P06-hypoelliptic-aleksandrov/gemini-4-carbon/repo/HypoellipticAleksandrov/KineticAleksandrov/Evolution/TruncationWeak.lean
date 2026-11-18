module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution
open Set Filter HypoellipticAleksandrov.Parabolic
open scoped Topology

variable {n : ℕ}

/-- The straightening map on packed evolution coordinates. -/
def truncationPoint (g : ℝ → PDE.Vec n) (x : EvolutionVec n) : TimeVelocity (n + n) :=
  (timeCoord n x, spatialPack (diffusedCoord n x - g (timeCoord n x)) (transportedCoord n x))

/-- The straightening map is smooth when its curve is smooth. -/
theorem contDiff_truncationPoint {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (truncationPoint g) :=
  (timeCoord n).contDiff.prodMk (contDiff_spatialPack
    ((diffusedCoord n).contDiff.sub (hg.comp (timeCoord n).contDiff))
    (transportedCoord n).contDiff)

/-- A packed spatial line straightens to a line in the scalar spatial slice. -/
theorem truncationPoint_spatial_line (g : ℝ → PDE.Vec n) (x w : EvolutionVec n)
    (hw : timeCoord n w = 0) (t : ℝ) :
    truncationPoint g (x + t • w) =
      ((truncationPoint g x).1, (truncationPoint g x).2 +
        t • spatialPack (diffusedCoord n w) (transportedCoord n w)) := by
  unfold truncationPoint
  simp only [map_add, map_smul, hw, smul_zero, add_zero]
  congr 1
  rw [show diffusedCoord n x + t • diffusedCoord n w - g (timeCoord n x) =
    (diffusedCoord n x - g (timeCoord n x)) + t • diffusedCoord n w by abel]
  rw [spatialPack_add, spatialPack_smul]

/-- A scalar C1,2 function pulls back with the expected first spatial line derivative. -/
theorem truncation_hasLineDerivAt_spatial {g : ℝ → PDE.Vec n}
    {u : TimeVelocity (n + n) → ℝ} {U : Set (TimeVelocity (n + n))}
    (hu : IsScalarC12On u U) {x w : EvolutionVec n}
    (hx : truncationPoint g x ∈ U) (hw : timeCoord n w = 0) :
    HasLineDerivAt ℝ (u ∘ truncationPoint g)
      (PDE.vecDot (scalarSpatialGradient u (truncationPoint g x))
        (spatialPack (diffusedCoord n w) (transportedCoord n w))) x w := by
  have h := ((hu.spatialSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (spatialPack (diffusedCoord n w) (transportedCoord n w))
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [Function.comp_def, truncationPoint_spatial_line g x w hw,
    scalarSpatialGradient] using! h

/-- Spatial line derivatives of gradient entries are scalar Hessian entries. -/
theorem truncation_gradient_hasLineDerivAt {g : ℝ → PDE.Vec n}
    {u : TimeVelocity (n + n) → ℝ} {U : Set (TimeVelocity (n + n))}
    (hu : IsScalarC12On u U) {x w : EvolutionVec n}
    (hx : truncationPoint g x ∈ U) (hw : timeCoord n w = 0)
    (i j : Fin (n + n))
    (hdir : spatialPack (diffusedCoord n w) (transportedCoord n w) = PDE.basisVec i) :
    HasLineDerivAt ℝ (fun y => scalarSpatialGradient u (truncationPoint g y) j)
      (scalarSpatialHessian u (truncationPoint g x) i j) x w := by
  have hc2 := hu.spatialSlice_contDiffAt hx
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => u ((truncationPoint g x).1, y)))
      (truncationPoint g x).2 :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (hd.clm_apply (differentiableAt_const (PDE.basisVec j))).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  have he : fderiv ℝ (fun y => fderiv ℝ
      (fun y => u ((truncationPoint g x).1, y)) y (PDE.basisVec j))
      (truncationPoint g x).2 (PDE.basisVec i) =
      scalarSpatialHessian u (truncationPoint g x) i j := by
    have hz : fderiv ℝ (fun _ => PDE.basisVec j)
        (truncationPoint g x).2 = 0 := (hasFDerivAt_const (PDE.basisVec j) _).fderiv
    rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec j))]
    erw [hz]
    simpa using! (scalarSpatialHessian_eq_secondFDeriv hc2 i j).symm
  rw [he] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [truncationPoint_spatial_line g x w hw, hdir,
    scalarSpatialGradient, PDE.classicalGradient] using! h

/-- The time line derivative includes the exact moving-frame correction. -/
theorem truncation_hasLineDerivAt_time {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {u : TimeVelocity (n + n) → ℝ}
    {U : Set (TimeVelocity (n + n))} (hU : IsOpen U) (hu : IsScalarC12On u U)
    {x : EvolutionVec n} (hx : truncationPoint g x ∈ U) :
    HasLineDerivAt ℝ (u ∘ truncationPoint g)
      (scalarTimeDerivative u (truncationPoint g x) +
        PDE.vecDot (-deriv g (timeCoord n x))
          (spatialY (scalarSpatialGradient u (truncationPoint g x)))) x basisT := by
  have hdu := scalarC12_differentiableAt hU hu hx
  have hd :=
    hdu.comp x ((contDiff_truncationPoint hg).differentiable (by simp) x)
  have he : u ∘ truncationPoint g = straightenedPullback g u ∘ evolutionHomeomorph n := rfl
  have h := hd.hasFDerivAt.hasLineDerivAt basisT
  rw [he, ← kineticTimeDerivative_comp (he ▸ hd),
    kineticTimeDerivative_straightenedPullback
      ((hg.differentiable (by simp)) (timeCoord n x)) hdu] at h
  simpa using! h

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped Topology MatrixOrder
open Evolution

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive

/-- The actual classical Dirichlet solution pulls back to a
weak regularized kinetic solution, using its supplied slice C1,2 regularity. -/
theorem weakRegularized_of_straightened_dirichlet
    (a τ r R : ℝ) (haτ : a < τ) (hr : 0 < r) (hR : 0 < R)
    (g : ℝ → PDE.Vec n) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (ε : ℝ) (hε : 0 < ε) (F : BoundedBorel (EvolutionAmbientState n))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    IsKineticWeakRegularizedSolution B b ε
      {p : KineticPoint n | a < p.time ∧ p.time < τ ∧
        spatialPack (p.position - g p.time) p.velocity ∈
          openEllipsoid (straightenedEllipsoidMatrix n r R)}
      (fun p => u (p.time, spatialPack (p.position - g p.time) p.velocity))
      (fun _ => 0) := by
  let D := openEllipsoid (straightenedEllipsoidMatrix n r R)
  let W := scalarParabolicOpenCylinder a τ D
  let Q := truncationPoint g
  let U := Q ⁻¹' W
  let w := u ∘ Q
  let T (x : EvolutionVec n) := scalarTimeDerivative u (Q x) +
    PDE.vecDot (-deriv g (timeCoord n x)) (spatialY (scalarSpatialGradient u (Q x)))
  let V (i : Fin n) (x : EvolutionVec n) :=
    scalarSpatialGradient u (Q x) (Fin.castAdd n i)
  let Z (i : Fin n) (x : EvolutionVec n) :=
    scalarSpatialGradient u (Q x) (Fin.natAdd n i)
  let H (i j : Fin n) (x : EvolutionVec n) :=
    scalarSpatialHessian u (Q x) (Fin.castAdd n i) (Fin.castAdd n j)
  let K (i : Fin n) (x : EvolutionVec n) :=
    scalarSpatialHessian u (Q x) (Fin.natAdd n i) (Fin.natAdd n i)
  have hD : IsOpen D := by
    have he : D = {x : PDE.Vec (n + n) |
        PDE.vecNormSq (spatialY x) / r ^ 2 + PDE.vecNormSq (spatialZ x) / R ^ 2 < 1} := by
      ext x
      exact (straightenedEllipsoid_characterization n r R hr hR).2 x
    rw [he]
    exact isOpen_lt
      (((PDE.continuous_vecNormSq.comp (contDiff_spatialY (m := 0)).continuous).div_const _).add
        ((PDE.continuous_vecNormSq.comp (contDiff_spatialZ (m := 0)).continuous).div_const _))
      continuous_const
  have hW : IsOpen W := isOpen_Ioo.prod hD
  have hQ := contDiff_truncationPoint hg
  have hU : IsOpen U := hW.preimage hQ.continuous
  have huc := hu.2.1
  have hw : ContinuousOn w U := huc.continuousOn.comp hQ.continuous.continuousOn
    (fun x hx => hx)
  have hg0 :=
    huc.continuousOn_scalarSpatialGradient.comp hQ.continuous.continuousOn (fun x hx => hx)
  have hT : ContinuousOn T U := by
    apply (huc.continuousOn_scalarTimeDerivative.comp hQ.continuous.continuousOn (fun x hx => hx)).add
    unfold PDE.vecDot
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp
      (((hg.continuous_deriv (by simp)).comp (timeCoord n).continuous).neg)).continuousOn.mul
      ((continuous_apply (Fin.castAdd n i)).comp_continuousOn hg0)
  have hV : ∀ i, ContinuousOn (V i) U := fun i => (continuous_apply _).comp_continuousOn hg0
  have hZ : ∀ i, ContinuousOn (Z i) U := fun i => (continuous_apply _).comp_continuousOn hg0
  have hentry (i j : Fin (n + n)) :
      ContinuousOn (fun x => scalarSpatialHessian u (Q x) i j) U :=
    (show Continuous (fun A : PDE.Mat (n + n) => A i j) from
      (continuous_apply j).comp (continuous_apply i)).comp_continuousOn (huc.continuousOn_scalarSpatialHessian.comp hQ.continuous.continuousOn (fun x hx => hx))
  have hH : ∀ i j, ContinuousOn (H i j) U := fun i j => hentry _ _
  have hK : ∀ i, ContinuousOn (K i) U := fun i => hentry _ _
  have hdirV (i : Fin n) : spatialPack (diffusedCoord n (basisV i))
      (transportedCoord n (basisV i)) = PDE.basisVec (Fin.castAdd n i) := by
    simpa only [basisV, diffusedCoord_packPoint, transportedCoord_packPoint,
      PDE.basisVec, embedYCLM_apply, embedZCLM_apply] using embedYCLM_basisVec i
  have hdirZ (i : Fin n) : spatialPack (diffusedCoord n (basisZ i))
      (transportedCoord n (basisZ i)) = PDE.basisVec (Fin.natAdd n i) := by
    simpa only [basisZ, diffusedCoord_packPoint, transportedCoord_packPoint,
      PDE.basisVec, embedYCLM_apply, embedZCLM_apply] using embedZCLM_basisVec i
  have hdT : ∀ x ∈ U, HasLineDerivAt ℝ w (T x) x basisT := fun x hx =>
    truncation_hasLineDerivAt_time hg hW huc hx
  have hdV : ∀ i x, x ∈ U → HasLineDerivAt ℝ w (V i x) x (basisV i) := by
    intro i x hx
    have h := truncation_hasLineDerivAt_spatial (w := basisV i) huc hx (by simp [basisV])
    simpa only [hdirV, PDE.vecDot_basisVec_right] using! h
  have hdZ : ∀ i x, x ∈ U → HasLineDerivAt ℝ w (Z i x) x (basisZ i) := by
    intro i x hx
    have h := truncation_hasLineDerivAt_spatial (w := basisZ i) huc hx (by simp [basisZ])
    simpa only [hdirZ, PDE.vecDot_basisVec_right] using! h
  have hdH : ∀ i j x, x ∈ U → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j) := by
    intro i j x hx
    have h := truncation_gradient_hasLineDerivAt huc hx (by simp [basisV])
      (Fin.castAdd n j) (Fin.castAdd n i) (hdirV j)
    have he : scalarSpatialHessian u (Q x) (Fin.castAdd n j) (Fin.castAdd n i) =
        H i j x := congrFun (congrFun (scalarSpatialHessian_isSymm_of_c12 huc hx) (Fin.castAdd n i)) (Fin.castAdd n j)
    rwa [he] at h
  have hdK : ∀ i x, x ∈ U → HasLineDerivAt ℝ (Z i) (K i x) x (basisZ i) :=
    fun i x hx => truncation_gradient_hasLineDerivAt huc hx (by simp [basisZ])
      (Fin.natAdd n i) (Fin.natAdd n i) (hdirZ i)
  have heq : ∀ x ∈ U, T x +
      (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
      (∑ i, b (diffusedCoord n x) i * Z i x) + ε * ∑ i, K i x = 0 := by
    intro x hx
    have h := hu.2.2.1 (Q x) hx
    simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at h
    rw [scalarParabolicOperator_apply] at h
    have ha : straightenedCoefficient B g ε (Q x).1 (Q x).2 =
        viscousBlockMatrix (B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x)) ε := by
      simp [Q, truncationPoint, straightenedCoefficient]
    have hb : straightenedDrift b g (Q x).1 (Q x).2 =
        spatialPack (-deriv g (timeCoord n x)) (b (diffusedCoord n x)) := by
      simp [Q, truncationPoint, straightenedDrift]
    rw [ha, hb, matrixContraction_viscousBlockMatrix, vecDot_spatialPack_left] at h
    dsimp only [T, H, Z, K]
    simp only [matrixContraction, PDE.vecDot, spatialZ, Fin.natAdd_eq_addNat] at h ⊢
    linarith
  apply (isWeakRegularizedSolution_comp_iff B b ε _ _ (fun _ => 0)).mp
  have hUeq : evolutionHomeomorph n ⁻¹'
      {p : KineticPoint n | a < p.time ∧ p.time < τ ∧
        spatialPack (p.position - g p.time) p.velocity ∈ D} = U := by
    ext x
    simp [U, Q, W, D, truncationPoint, mem_scalarParabolicOpenCylinder_iff, time_evolutionHomeomorph, position_evolutionHomeomorph, velocity_evolutionHomeomorph]
  rw [hUeq]
  change IsWeakRegularizedSolution B b ε U w (fun _ => 0)
  refine ⟨hw.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
  rw [integral_regularizedAdjoint_of_jets B b ε hB_smooth hb_smooth
    w T V Z H K hw hT hV hZ hH hK hdT hdV hdZ hdH hdK ψ hψ hc hs]
  have hz : (fun x => (T x +
      (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
      (∑ i, b (diffusedCoord n x) i * Z i x) + ε * ∑ i, K i x) * ψ x) =ᵐ[volume.restrict U]
        fun _ => 0 := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [heq x hx, zero_mul]
  simp [integral_zero]
  exact integral_eq_zero_of_ae hz

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

