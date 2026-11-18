module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import PDEFoundation.Sobolev.ClassicalGradient
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.SpatialBlock
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedCoefficients
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
section
set_option autoImplicit false
open Filter
open scoped Topology ContDiff

section CLM

variable (n : ℕ)

/-- The linear inclusion `y ↦ (y, 0)` of the diffused block. -/
def embedYCLM : PDE.Vec n →L[ℝ] PDE.Vec (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => spatialPack y 0
      map_add' := fun y y' => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
      map_smul' := fun c y => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp }

/-- The linear inclusion `z ↦ (0, z)` of the transported block. -/
def embedZCLM : PDE.Vec n →L[ℝ] PDE.Vec (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => spatialPack 0 z
      map_add' := fun z z' => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
      map_smul' := fun c z => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp }

/-- The linear projection onto the diffused block. -/
def projYCLM : PDE.Vec (n + n) →L[ℝ] PDE.Vec n :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialY
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The linear projection onto the transported block. -/
def projZCLM : PDE.Vec (n + n) →L[ℝ] PDE.Vec n :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialZ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable {n}

@[simp] theorem embedYCLM_apply (y : PDE.Vec n) : embedYCLM n y = spatialPack y 0 :=
  rfl

@[simp] theorem embedZCLM_apply (z : PDE.Vec n) : embedZCLM n z = spatialPack 0 z :=
  rfl

@[simp] theorem projYCLM_apply (x : PDE.Vec (n + n)) : projYCLM n x = spatialY x :=
  rfl

@[simp] theorem projZCLM_apply (x : PDE.Vec (n + n)) : projZCLM n x = spatialZ x :=
  rfl

theorem embedYCLM_basisVec (i : Fin n) :
    embedYCLM n (PDE.basisVec i) = PDE.basisVec (Fin.castAdd n i) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [PDE.basisVec_apply, Fin.ext_iff]
  · simp only [embedYCLM_apply, PDE.basisVec_apply]
    have hne : ¬ j.addNat n = Fin.castAdd n i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_addNat] at this
      omega
    simp [hne]

theorem embedZCLM_basisVec (i : Fin n) :
    embedZCLM n (PDE.basisVec i) = PDE.basisVec (Fin.natAdd n i) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [embedZCLM_apply, spatialPack_castAdd, PDE.basisVec_apply, Pi.zero_apply]
    have hne : ¬ Fin.castAdd n j = i.addNat n := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [hne]
  · simp [PDE.basisVec_apply, Fin.ext_iff]

end CLM

section Slices

variable {n : ℕ}


theorem hasFDerivAt_pack_right (w z : PDE.Vec n) :
    HasFDerivAt (fun z' : PDE.Vec n => spatialPack w z') (embedZCLM n) z := by
  convert (embedZCLM n).hasFDerivAt (x := z) |>.add_const (spatialPack w 0) using 1
  funext z'
  rw [embedZCLM_apply, ← spatialPack_add, add_zero, zero_add]

/-- Gradient of a restriction along an affine block embedding. -/
theorem classicalGradient_comp_block
    {f : PDE.Vec (n + n) → ℝ} {ι : PDE.Vec n → PDE.Vec (n + n)}
    {E : PDE.Vec n →L[ℝ] PDE.Vec (n + n)} {y : PDE.Vec n} (hι : HasFDerivAt ι E y)
    (hf : DifferentiableAt ℝ f (ι y)) {e : Fin n → Fin (n + n)}
    (he : ∀ i, E (PDE.basisVec i) = PDE.basisVec (e i)) :
    PDE.classicalGradient (fun y' => f (ι y')) y =
      fun i => PDE.classicalGradient f (ι y) (e i) := by
  funext i
  simp
  rw [show fderiv ℝ (fun y' => f (ι y')) y = (fderiv ℝ f (ι y)).comp E from (hf.hasFDerivAt.comp y hι).fderiv]
  simp [he]

/-- The gradient of a `C²` function is differentiable. -/
theorem differentiableAt_classicalGradient {m : ℕ} {f : PDE.Vec m → ℝ} {x : PDE.Vec m}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (PDE.classicalGradient f) x := by
  refine differentiableAt_pi.2 fun i => ?_
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero

/-- Hessian of a restriction along an affine block embedding. -/
theorem hessian_comp_block
    {f : PDE.Vec (n + n) → ℝ} {ι : PDE.Vec n → PDE.Vec (n + n)}
    {E : PDE.Vec n →L[ℝ] PDE.Vec (n + n)} {y : PDE.Vec n} (hι : ∀ y', HasFDerivAt ι E y')
    (hf : ContDiffAt ℝ 2 f (ι y)) {e : Fin n → Fin (n + n)}
    (he : ∀ i, E (PDE.basisVec i) = PDE.basisVec (e i)) (i j : Fin n) :
    (fderiv ℝ (fun y' => PDE.classicalGradient (fun w => f (ι w)) y') y (PDE.basisVec i)) j =
      (fderiv ℝ (PDE.classicalGradient f) (ι y) (PDE.basisVec (e i))) (e j) := by
  set P : PDE.Vec (n + n) →L[ℝ] PDE.Vec n :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (φ := fun _ => ℝ) (e j)
    with hP
  have hPapply : ∀ v j, P v j = v (e j) := fun v j => rfl
  have hev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ f (ι y') := by
    exact (hι y).continuousAt.eventually (hf.eventually (by simp)) |>.mono fun y' h => h.differentiableAt (by norm_num)
  have heq : (fun y' => PDE.classicalGradient (fun w => f (ι w)) y') =ᶠ[𝓝 y]
      fun y' => P (PDE.classicalGradient f (ι y')) := by
    filter_upwards [hev] with y' hy'
    rw [classicalGradient_comp_block (hι y') hy' he]
    rfl
  have hcomp :=
    P.hasFDerivAt.comp y (((differentiableAt_classicalGradient hf).hasFDerivAt).comp y (hι y))
  rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
  change P (fderiv ℝ (PDE.classicalGradient f) (ι y) (E (PDE.basisVec i))) j = _
  rw [he i, hPapply]

end Slices

end
section
set_option autoImplicit false
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter
open scoped Topology ContDiff

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
    viscousBlockMatrix_castAdd_addNat, viscousBlockMatrix_addNat_castAdd,
    viscousBlockMatrix_addNat_addNat, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.one_apply, Fin.natAdd_eq_addNat]
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
    (f := fun X => ũ (p.time, X)) (ι := fun z' => spatialPack (p.position - g p.time) z')
    (hasFDerivAt_pack_right (p.position - g p.time) p.velocity) h (e := Fin.natAdd n)
    (fun i => embedZCLM_basisVec i)
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
  have hL' := hũ.hasFDerivAt
  -- the curve `r ↦ (r, (y - g r, z))`
  have hcurve2 : HasDerivAt (fun r => spatialPack (p.position - g r) p.velocity)
      (spatialPack (-deriv g p.time) 0) p.time := by
    have h : HasDerivAt (fun r => embedYCLM n (p.position - g r) + spatialPack 0 p.velocity)
        (embedYCLM n (-deriv g p.time)) p.time :=
      HasDerivAt.add_const _ ((embedYCLM n).hasFDerivAt.comp_hasDerivAt p.time (hg.hasDerivAt.const_sub p.position))
    have hfun : (fun r : ℝ => spatialPack (p.position - g r) p.velocity) =
        fun r : ℝ => embedYCLM n (p.position - g r) + spatialPack 0 p.velocity := by
      funext r
      rw [embedYCLM_apply, ← spatialPack_add, add_zero, zero_add]
    rw [hfun]
    exact h
  have hcomp := hL'.comp_hasDerivAt p.time (HasDerivAt.prodMk (hasDerivAt_id p.time) hcurve2)
  have h1 : kineticTimeDerivative (straightenedPullback g ũ) p =
      L (1, spatialPack (-deriv g p.time) 0) := by
    have : (fun r => straightenedPullback g ũ ⟨r, p.position, p.velocity⟩) =
        ũ ∘ (fun r => (r, spatialPack (p.position - g r) p.velocity)) := rfl
    unfold kineticTimeDerivative
    rw [this]
    exact hcomp.deriv
  -- split the derivative into its time part and its spatial part
  have hsplit : L (1, spatialPack (-deriv g p.time) 0) =
      L (1, 0) + L (0, spatialPack (-deriv g p.time) 0) := by
    rw [← map_add]
    simp
  have htime : L (1, 0) = scalarTimeDerivative ũ (straightenedPoint g p) := by
    exact (hL'.comp_hasDerivAt p.time (HasDerivAt.prodMk (hasDerivAt_id p.time) (hasDerivAt_const p.time X))).deriv.symm
  have hspace : L (0, spatialPack (-deriv g p.time) 0) =
      PDE.vecDot (-deriv g p.time)
        (spatialY (scalarSpatialGradient ũ (straightenedPoint g p))) := by
    have h2 : fderiv ℝ (fun X' => ũ (p.time, X')) X = L.comp (ContinuousLinearMap.inr ℝ ℝ
        (PDE.Vec (n + n))) := (hL'.comp X (hasFDerivAt_prodMk_right p.time X)).fderiv
    have h3 := PDE.fderiv_apply_eq_vecDot_classicalGradient (fun X' => ũ (p.time, X')) X
      (spatialPack (-deriv g p.time) 0)
    rw [h2] at h3
    change L (0, spatialPack (-deriv g p.time) 0) = _ at h3
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
        (straightenedPoint g p)   := by
  have kineticVelocityHessian_straightenedPullback (i : Fin n) (j : Fin n) :
      kineticVelocityHessian (straightenedPullback g ũ) p i j =
      scalarSpatialHessian ũ (straightenedPoint g p) (Fin.natAdd n i) (Fin.natAdd n j) := by
    have := hessian_comp_block
      (f := fun X => ũ (p.time, X)) (ι := fun z' => spatialPack (p.position - g p.time) z')
      (fun z' => hasFDerivAt_pack_right (p.position - g p.time) z') (y := p.velocity) hslice
      (e := Fin.natAdd n) (fun i => embedZCLM_basisVec i) i j
    exact this
  have diffusedHessian_straightenedPullback (i : Fin n) (j : Fin n) :
      diffusedHessian (straightenedPullback g ũ) p i j =
      scalarSpatialHessian ũ (straightenedPoint g p) (Fin.castAdd n i) (Fin.castAdd n j) := by
    have hasFDerivAt_pack_left (c : PDE.Vec n) (z : PDE.Vec n) (y : PDE.Vec n) :
        HasFDerivAt (fun y' => spatialPack (y' - c) z) (embedYCLM n) y := by
      have hslice := (embedYCLM n).hasFDerivAt (x := y) |>.add_const (spatialPack (-c) z)
      convert hslice using 1
      funext y'
      rw [embedYCLM_apply, ← spatialPack_add, sub_eq_add_neg, zero_add]
    have := hessian_comp_block
      (f := fun X => ũ (p.time, X)) (ι := fun y' => spatialPack (y' - g p.time) p.velocity)
      (fun y' => hasFDerivAt_pack_left (g p.time) p.velocity y') (y := p.position) hslice
      (e := Fin.castAdd n) (fun i => embedYCLM_basisVec i) i j
    exact this
  have hdiff : DifferentiableAt ℝ (fun X => ũ (p.time, X)) (straightenedPoint g p).2 :=
    hslice.differentiableAt (by norm_num)
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply,
    scalarParabolicOperator_apply, kineticTimeDerivative_straightenedPullback hg hũ,
    kineticVelocityGradient_straightenedPullback hdiff,
    straightenedCoefficient_straightenedPoint, straightenedDrift_straightenedPoint,
    matrixContraction_viscousBlockMatrix, vecDot_spatialPack_left]
  have hH : (fun i j => scalarSpatialHessian ũ (straightenedPoint g p) (Fin.castAdd n i)
      (Fin.castAdd n j)) = diffusedHessian (straightenedPullback g ũ) p := by
    funext i j
    exact (diffusedHessian_straightenedPullback i j).symm
  have hV : ∑ i, kineticVelocityHessian (straightenedPullback g ũ) p i i =
      ∑ i : Fin n, scalarSpatialHessian ũ (straightenedPoint g p) (Fin.natAdd n i)
        (Fin.natAdd n i) :=
    Finset.sum_congr rfl fun i _ => kineticVelocityHessian_straightenedPullback i i
  rw [hH, hV]
  simp
  ring

end Operator

section Regularity

variable {g : ℝ → PDE.Vec n} {ũ : TimeVelocity (n + n) → ℝ} {p : KineticPoint n}




/-- The pullback is slice regular wherever `ũ` is jointly differentiable with a `C²` spatial
slice.  This is the regularity hypothesis of the comparison theorems. -/
theorem isSliceRegularAt_straightenedPullback (hg : DifferentiableAt ℝ g p.time)
    (hũ : DifferentiableAt ℝ ũ (straightenedPoint g p))
    (hslice : ContDiffAt ℝ 2 (fun X => ũ (p.time, X)) (straightenedPoint g p).2) :
    IsSliceRegularAt (straightenedPullback g ũ) p    := by
  have differentiableAt_time_straightenedPullback (hũ : DifferentiableAt ℝ ũ (straightenedPoint g p)) :
      DifferentiableAt ℝ (fun r => straightenedPullback g ũ ⟨r, p.position, p.velocity⟩) p.time := by
    have hc : DifferentiableAt ℝ (fun r => spatialPack (p.position - g r) p.velocity)
        p.time := by
      have h : DifferentiableAt ℝ (fun r => embedYCLM n (p.position - g r) +
          spatialPack 0 p.velocity) p.time :=
        ((embedYCLM n).differentiableAt.comp p.time (hg.const_sub p.position)).add_const _
      have hfun : (fun r => spatialPack (p.position - g r) p.velocity) =
          fun r => embedYCLM n (p.position - g r) + spatialPack 0 p.velocity := by
        funext r
        rw [embedYCLM_apply, ← spatialPack_add, add_zero, zero_add]
      rw [hfun]
      exact h
    exact DifferentiableAt.comp (g := ũ) (f := fun r => (r, spatialPack (p.position - g r)
      p.velocity)) p.time hũ (differentiableAt_id.prodMk hc)
  exact ⟨differentiableAt_time_straightenedPullback hũ,
    (ContDiffAt.comp (g := fun X => ũ (p.time, X)) (f := fun y => spatialPack (y - g p.time) p.velocity) p.position hslice (contDiff_spatialPack (contDiff_id.sub contDiff_const) contDiff_const).contDiffAt),
    (ContDiffAt.comp (g := fun X => ũ (p.time, X)) (f := fun z => spatialPack (p.position - g p.time) z) p.velocity hslice (contDiff_spatialPack contDiff_const contDiff_id).contDiffAt)⟩

end Regularity

end
set_option autoImplicit false
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology ContDiff

variable {n : ℕ}

/-- Membership of a point in the frontier of the moving domain. -/
theorem mem_frontier_movingDomain_iff {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {σ : ℝ}
    {y : PDE.Vec n} : y ∈ frontier (movingDomain Ω γ σ) ↔ y - γ σ ∈ frontier Ω := by
  have h : movingDomain Ω γ σ = (Homeomorph.subRight (γ σ)) ⁻¹' Ω := by
    rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
    rfl
  rw [h, ← Homeomorph.preimage_frontier]
  rfl



/-- A smooth curve is continuous and piecewise `C¹` (with a single piece). -/
theorem isContinuousPiecewiseC1_of_contDiff {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : IsContinuousPiecewiseC1 g := by
  refine ⟨hg.continuous, fun a b hab => ⟨0, ![a, b], ?_, rfl, rfl, fun i => ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact (hg.contDiffOn (s := Set.Icc _ _)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))

end HypoellipticAleksandrov.KineticAleksandrov

