module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayer
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open MeasureTheory Set Filter HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology


variable {d : ℕ}

/-- The projection `(σ, v, z) ↦ (σ, v)` of packed evolution space onto time and velocity. -/
def evolutionToTimeVelocity (d : ℕ) : EvolutionVec d →L[ℝ] TimeVelocity d :=
  (Evolution.timeCoord d).prod (diffusedCoord d)

@[simp] theorem evolutionToTimeVelocity_apply (x : EvolutionVec d) :
    evolutionToTimeVelocity d x = (Evolution.timeCoord d x, diffusedCoord d x) := rfl

theorem timeCoord_basisT : Evolution.timeCoord d (basisT : EvolutionVec d) = 1 := by
  simp [basisT]

theorem timeCoord_basisV (j : Fin d) :
    Evolution.timeCoord d (basisV j : EvolutionVec d) = 0 := by
  simp [basisV]

theorem timeCoord_basisZ (l : Fin d) :
    Evolution.timeCoord d (basisZ l : EvolutionVec d) = 0 := by
  simp [basisZ]

theorem evolutionToTimeVelocity_basisT :
    evolutionToTimeVelocity d (basisT : EvolutionVec d) = (1, 0) := by
  simp [basisT]

theorem diffusedCoord_basisV (j : Fin d) :
    diffusedCoord d (basisV j : EvolutionVec d) = PDE.basisVec j := by
  simp only [basisV, diffusedCoord_packPoint]
  rfl

theorem evolutionToTimeVelocity_line (x w : EvolutionVec d)
    (hw : Evolution.timeCoord d w = 0) (t : ℝ) :
    evolutionToTimeVelocity d (x + t • w) =
      ((evolutionToTimeVelocity d x).1,
        (evolutionToTimeVelocity d x).2 + t • diffusedCoord d w) := by
  simp only [evolutionToTimeVelocity_apply, map_add, map_smul, hw, Prod.smul_mk, smul_zero,
    Prod.mk_add_mk, add_zero]

/-- The time line derivative of a `z`-independent function. -/
theorem hasLineDerivAt_zIndep_time {w : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hD : IsOpen D) (hw : IsScalarC12On w D) {x : EvolutionVec d}
    (hx : evolutionToTimeVelocity d x ∈ D) :
    HasLineDerivAt ℝ (w ∘ evolutionToTimeVelocity d)
      (scalarTimeDerivative w (evolutionToTimeVelocity d x)) x basisT := by
  simpa only [ContinuousLinearMap.comp_apply, evolutionToTimeVelocity_basisT,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul, map_zero, add_zero] using (((scalarC12_hasFDerivAt hD hw hx).comp x (evolutionToTimeVelocity d).hasFDerivAt).hasLineDerivAt basisT)

/-- Spatial line derivatives of a `z`-independent function. -/
theorem hasLineDerivAt_zIndep_spatial {w : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hw : IsScalarC12On w D) {x v : EvolutionVec d} (hx : evolutionToTimeVelocity d x ∈ D)
    (hv : Evolution.timeCoord d v = 0) :
    HasLineDerivAt ℝ (w ∘ evolutionToTimeVelocity d)
      (PDE.vecDot (scalarSpatialGradient w (evolutionToTimeVelocity d x))
        (diffusedCoord d v)) x v := by
  have h := ((hw.spatialSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (diffusedCoord d v)
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [Function.comp_def, evolutionToTimeVelocity_line x v hv,
    scalarSpatialGradient] using! h

/-- Spatial line derivatives of gradient entries are scalar Hessian entries. -/
theorem hasLineDerivAt_zIndep_gradient {w : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hw : IsScalarC12On w D) {x v : EvolutionVec d} (hx : evolutionToTimeVelocity d x ∈ D)
    (hv : Evolution.timeCoord d v = 0) (i j : Fin d)
    (hdir : diffusedCoord d v = PDE.basisVec i) :
    HasLineDerivAt ℝ (fun y => scalarSpatialGradient w (evolutionToTimeVelocity d y) j)
      (scalarSpatialHessian w (evolutionToTimeVelocity d x) i j) x v := by
  have hc2 := hw.spatialSlice_contDiffAt hx
  have hd :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (hd.clm_apply (differentiableAt_const (PDE.basisVec j))).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  have he : fderiv ℝ (fun y => fderiv ℝ
      (fun y => w ((evolutionToTimeVelocity d x).1, y)) y (PDE.basisVec j))
      (evolutionToTimeVelocity d x).2 (PDE.basisVec i) =
      scalarSpatialHessian w (evolutionToTimeVelocity d x) i j := by
    have hz : fderiv ℝ (fun _ => PDE.basisVec j)
        (evolutionToTimeVelocity d x).2 = 0 := (hasFDerivAt_const (PDE.basisVec j) _).fderiv
    rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec j))]
    erw [hz]
    simpa using! (scalarSpatialHessian_eq_secondFDeriv hc2 i j).symm
  rw [he] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [evolutionToTimeVelocity_line x v hv, hdir,
    scalarSpatialGradient, PDE.classicalGradient] using! h

/-- **Weak form for `z`-independent smooth functions.**  For `w` smooth on the open set `D`
and a smooth compactly supported test `ψ` supported in `π ⁻¹' D`,
`∫ (w ∘ π) Lop^* ψ = ∫ (P₀ w ∘ π) ψ` with `P₀ = ∂_σ + B : D_v²`. -/
theorem integral_transportedAdjoint_zIndep {B' : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B'))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (TimeVelocity d)} (hD : IsOpen D) {w : TimeVelocity d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' D) :
    (∫ x in evolutionToTimeVelocity d ⁻¹' D, w (evolutionToTimeVelocity d x) *
        transportedAdjoint (zIndependentCoefficient B') b ψ x) =
      ∫ x in evolutionToTimeVelocity d ⁻¹' D,
        scalarParabolicOperator B' (fun _ _ => 0) w (evolutionToTimeVelocity d x) * ψ x := by
  have hu :=
    isScalarC12On_of_isOpen_contDiffOn_two hD (hw.of_le (by norm_num))
  set Qp := evolutionToTimeVelocity d with hQp
  have hQc := Qp.continuous
  let T : EvolutionVec d → ℝ := fun x => scalarTimeDerivative w (Qp x)
  let V : Fin d → EvolutionVec d → ℝ := fun i x => scalarSpatialGradient w (Qp x) i
  let Z : Fin d → EvolutionVec d → ℝ := fun _ _ => 0
  let H : Fin d → Fin d → EvolutionVec d → ℝ := fun i j x => scalarSpatialHessian w (Qp x) i j
  let K : Fin d → EvolutionVec d → ℝ := fun _ _ => 0
  have hmaps : Set.MapsTo Qp (Qp ⁻¹' D) D := fun x hx => hx
  have hV : ∀ i, ContinuousOn (V i) (Qp ⁻¹' D) := fun i =>
    (continuous_apply i).comp_continuousOn (hu.continuousOn_scalarSpatialGradient.comp hQc.continuousOn hmaps)
  have hH : ∀ i j, ContinuousOn (H i j) (Qp ⁻¹' D) := fun i j =>
    (show Continuous (fun A : PDE.Mat d => A i j) from
      (continuous_apply j).comp (continuous_apply i)).comp_continuousOn (hu.continuousOn_scalarSpatialHessian.comp hQc.continuousOn hmaps)
  have hdT : ∀ x ∈ Qp ⁻¹' D, HasLineDerivAt ℝ (w ∘ Qp) (T x) x basisT := fun x hx =>
    hasLineDerivAt_zIndep_time hD hu hx
  have hdV : ∀ i x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (w ∘ Qp) (V i x) x (basisV i) := by
    intro i x hx
    have h := hasLineDerivAt_zIndep_spatial hu hx (timeCoord_basisV i)
    rwa [diffusedCoord_basisV, PDE.vecDot_basisVec_right] at h
  have hdZ : ∀ i x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (w ∘ Qp) (Z i x) x (basisZ i) := by
    intro i x hx
    have h := hasLineDerivAt_zIndep_spatial hu hx (timeCoord_basisZ i)
    have hz : diffusedCoord d (basisZ i : EvolutionVec d) = 0 := by
      simp [basisZ]
    rw [hz] at h
    simpa [PDE.vecDot] using h
  have hdH : ∀ i j x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j) := by
    intro i j x hx
    have h := hasLineDerivAt_zIndep_gradient hu hx (timeCoord_basisV j) j i
      (diffusedCoord_basisV j)
    have he : scalarSpatialHessian w (Qp x) j i = H i j x :=
      congrFun (congrFun (scalarSpatialHessian_isSymm_of_c12 hu hx) i) j
    change HasLineDerivAt ℝ (V i) (scalarSpatialHessian w (Qp x) j i) x (basisV j) at h
    rwa [he] at h
  have hdK : ∀ i x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (Z i) (K i x) x (basisZ i) := by
    intro i x _
    exact (hasFDerivAt_const 0 x).hasLineDerivAt _
  have key := integral_regularizedAdjoint_of_jets (U := Qp ⁻¹' D) (zIndependentCoefficient B') b
    0 hB hb (w ∘ Qp) T V Z H K (hu.continuousOn.comp hQc.continuousOn hmaps) (hu.continuousOn_scalarTimeDerivative.comp hQc.continuousOn hmaps) hV (fun _ => continuousOn_const)
    hH (fun _ => continuousOn_const) hdT hdV hdZ hdH hdK ψ hψ hc hs
  have hreg : ∀ x, regularizedAdjoint (zIndependentCoefficient B') b 0 ψ x =
      transportedAdjoint (zIndependentCoefficient B') b ψ x := fun x => by
    simp [regularizedAdjoint]
  simp only [hreg] at key
  refine key.trans ?_
  refine setIntegral_congr_fun (hD.preimage hQc).measurableSet fun x hx => ?_
  congr 1
  simp only [T, H, Z, K, mul_zero, Finset.sum_const_zero, add_zero,
    scalarParabolicOperator_apply, matrixContraction, PDE.vecDot, zIndependentCoefficient_apply]
  simp [hQp]



variable {d : ℕ}

/-- Product rule for a time cutoff. -/
theorem fderiv_cutoff_mul {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {f : EvolutionVec d → ℝ}
    {x : EvolutionVec d} (hf : DifferentiableAt ℝ f x) (v : EvolutionVec d) :
    fderiv ℝ (fun y => χ (Evolution.timeCoord d y) * f y) x v =
      χ (Evolution.timeCoord d x) * fderiv ℝ f x v +
        deriv χ (Evolution.timeCoord d x) * Evolution.timeCoord d v * f x := by
  have hc : HasFDerivAt (fun y => χ (Evolution.timeCoord d y))
      (deriv χ (Evolution.timeCoord d x) • Evolution.timeCoord d) x :=
    (hχ _).hasDerivAt.comp_hasFDerivAt x (Evolution.timeCoord d).hasFDerivAt
  rw [(hc.fun_mul hf.hasFDerivAt).fderiv]
  simp
  ring

/-- The cutoff commutation formula for the transported adjoint. -/
theorem transportedAdjoint_cutoff_mul {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (hB : IsSmoothFullKineticCoefficient B) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : EvolutionVec d) :
    transportedAdjoint B b (fun y => χ (Evolution.timeCoord d y) * ψ y) x =
      χ (Evolution.timeCoord d x) * transportedAdjoint B b ψ x -
        deriv χ (Evolution.timeCoord d x) * ψ x := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE d).contDiff
  have hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) :=
    fun i j => (hA i j).mul hψ
  have hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) := fun i j => contDiff_fderiv_apply (hF i j) _
  have hψd : ∀ y, DifferentiableAt ℝ ψ y := fun y => differentiableAt_of_contDiff hψ y
  unfold transportedAdjoint
  have t3 : ∀ l, fderiv ℝ (fun y => χ (Evolution.timeCoord d y) * ψ y) x (basisZ l) =
      χ (Evolution.timeCoord d x) * fderiv ℝ ψ x (basisZ l) := by
    intro l
    rw [fderiv_cutoff_mul hχd (hψd x), timeCoord_basisZ]
    ring
  have t2 : ∀ i j, fderiv ℝ (fun y => fderiv ℝ (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j *
        (χ (Evolution.timeCoord d w) * ψ w)) y (basisV j)) x (basisV i) =
      χ (Evolution.timeCoord d x) * fderiv ℝ (fun y => fderiv ℝ (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) x (basisV i) := by
    intro i j
    have hin : (fun y => fderiv ℝ (fun w =>
        B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j *
          (χ (Evolution.timeCoord d w) * ψ w)) y (basisV j)) =
        fun y => χ (Evolution.timeCoord d y) * fderiv ℝ (fun w =>
          B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
            (basisV j) := by
      funext y
      have hfun : (fun w =>
          B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j *
            (χ (Evolution.timeCoord d w) * ψ w)) =
          fun w => χ (Evolution.timeCoord d w) * (B (Evolution.timeCoord d w)
            (diffusedCoord d w) (transportedCoord d w) i j * ψ w) := by
        funext w; ring
      rw [hfun, fderiv_cutoff_mul hχd ((hF i j).differentiable (by simp) y), timeCoord_basisV]
      ring
    rw [hin, fderiv_cutoff_mul hχd (((hG i j).differentiable (by simp)) x), timeCoord_basisV]
    ring
  simp only [t2, t3, (fderiv_cutoff_mul (d := d) hχd (hψd x) basisT), timeCoord_basisT]
  simp only [mul_left_comm _ (χ (Evolution.timeCoord d x)), ← Finset.mul_sum]
  ring

/-- The transported adjoint vanishes off the topological support of the test. -/
theorem transportedAdjoint_eq_zero_of_notMem_tsupport {B : FullKineticCoefficient d}
    {b : PDE.Vec d → PDE.Vec d} (ψ : EvolutionVec d → ℝ) {x : EvolutionVec d}
    (hx : x ∉ tsupport ψ) : transportedAdjoint B b ψ x = 0 := by
  have hz : ∀ (φ : EvolutionVec d → ℝ) (v : EvolutionVec d), tsupport φ ⊆ tsupport ψ →
      fderiv ℝ φ x v = 0 := fun φ v hφ =>
    image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v)
      (fun h => hx (hφ (tsupport_evolution_fderiv_apply φ v h)))
  have h1 : fderiv ℝ ψ x basisT = 0 := hz ψ _ subset_rfl
  have h3 : ∀ l, fderiv ℝ ψ x (basisZ l) = 0 := fun l => hz ψ _ subset_rfl
  have h2 : ∀ i j, fderiv ℝ (fun y => fderiv ℝ (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) x (basisV i) = 0 := by
    intro i j
    refine hz _ _ ?_
    intro y hy
    exact tsupport_mul_subset_right (tsupport_evolution_fderiv_apply _ (basisV j) hy)
  unfold transportedAdjoint
  simp only [h1, h2, h3, mul_zero, Finset.sum_const_zero, neg_zero, add_zero, sub_zero]



variable {d : ℕ}

/-- The transported adjoint of a smooth test is smooth. -/
theorem contDiff_transportedAdjoint {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedAdjoint B b ψ) := by
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE d).contDiff
  have hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) :=
    fun i j => (hA i j).mul hψ
  have hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      fderiv ℝ (fun w =>
        B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) := fun i j => contDiff_fderiv_apply (hF i j) _
  unfold transportedAdjoint
  refine (((contDiff_fderiv_apply hψ _).neg).add ?_).sub ?_
  · exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_fderiv_apply (hG i j) _
  · refine ContDiff.sum fun l _ => ?_
    exact ((contDiff_pi.1 hb l).comp (diffusedCoord d).contDiff).mul
      (contDiff_fderiv_apply hψ _)

/-- The transported adjoint of a compactly supported test is compactly supported. -/
theorem hasCompactSupport_transportedAdjoint {B : FullKineticCoefficient d}
    {b : PDE.Vec d → PDE.Vec d} {ψ : EvolutionVec d → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (transportedAdjoint B b ψ) :=
  HasCompactSupport.intro hc fun _ hx => transportedAdjoint_eq_zero_of_notMem_tsupport ψ hx

/-- The cutoff in the source-time variable. -/
def sliceCutoff (r h t : ℝ) : ℝ := layerStep ((r - t) / h)

theorem contDiff_sliceCutoff (r h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sliceCutoff r h) :=
  contDiff_layerStep.comp ((contDiff_const.sub contDiff_id).div_const h)

theorem deriv_sliceCutoff (r h t : ℝ) :
    deriv (sliceCutoff r h) t = -(h⁻¹ * layerKernel ((r - t) / h)) := by
  have h1 : HasDerivAt (fun t => (r - t) / h) (-h⁻¹) t := by
    have := ((hasDerivAt_id t).const_sub r).div_const h
    simpa [div_eq_mul_inv] using this
  have : deriv (sliceCutoff r h) t = layerKernel ((r - t) / h) * -h⁻¹ := ((hasDerivAt_layerStep ((r - t) / h)).comp t h1).deriv
  rw [this]
  ring

/-- Where the cutoff is nonzero, the time is below `r - h`. -/
theorem lt_of_sliceCutoff_ne_zero {r h t : ℝ} (hh : 0 < h) (hne : sliceCutoff r h t ≠ 0) :
    t < r - h := by
  by_contra hlt
  apply hne
  apply layerStep_of_le
  rw [div_le_iff₀ hh]
  linarith [not_lt.1 hlt]

/-- **Cut-off weak identity for one source slice.** -/
theorem slice_cutoff_identity {B' : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B'))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (TimeVelocity d)} (hD : IsOpen D) {V u : TimeVelocity d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, scalarParabolicOperator B' (fun _ _ => 0) V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u) (C : ℝ) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, Evolution.timeCoord d x < r →
      evolutionToTimeVelocity d x ∈ D)
    (h : ℝ) (hh : 0 < h) :
    (∫ x, u (evolutionToTimeVelocity d x) *
        (layerStep ((r - Evolution.timeCoord d x) / h) *
          transportedAdjoint (zIndependentCoefficient B') b ψ x)) +
      ∫ x, u (evolutionToTimeVelocity d x) *
        (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) = 0 := by
  set Qp := evolutionToTimeVelocity d with hQp
  set Ladj := transportedAdjoint (zIndependentCoefficient B') b with hLadj
  have hQc := Qp.continuous
  have hU := hD.preimage hQc
  have hχ := contDiff_sliceCutoff r h
  let φ : EvolutionVec d → ℝ := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp (Evolution.timeCoord d).contDiff).mul hψ
  have hφc : HasCompactSupport φ := hc.mul_left
  have hφsub : tsupport φ ⊆ Qp ⁻¹' D := by
    intro x hx
    have h2 : tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} := by
      apply closure_minimal
      · intro y hy
        exact (lt_of_sliceCutoff_ne_zero hh (left_ne_zero_of_mul hy)).le
      · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const
    exact hψD x (tsupport_mul_subset_right hx) (by have := h2 hx; simp only [mem_ofPred_eq] at this; linarith)
  have key := integral_transportedAdjoint_zIndep hB hb hD hV hφs hφc hφsub
  have hR : (∫ x in Qp ⁻¹' D, scalarParabolicOperator B' (fun _ _ => 0) V (Qp x) * φ x) = 0 := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun _ => 0)]
    · simp
    · intro x hx
      simp only [hVeq _ hx, zero_mul]
  rw [hR] at key
  have hL : (∫ x in Qp ⁻¹' D, V (Qp x) * Ladj φ x) = ∫ x, u (Qp x) * Ladj φ x := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun x => u (Qp x) * Ladj φ x)]
    · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have : x ∉ tsupport φ := fun h' => hx (hφsub h')
      rw [hLadj, transportedAdjoint_eq_zero_of_notMem_tsupport φ this, mul_zero]
    · intro x hx
      simp only [huV _ hx]
  rw [hL] at key
  have hexp : ∀ x, Ladj φ x = sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x +
      h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x := by
    intro x
    simp only [hLadj, φ]
    rw [transportedAdjoint_cutoff_mul hB hχ hψ x, deriv_sliceCutoff]
    ring
  simp_rw [hexp, mul_add] at key
  have hLcs : HasCompactSupport (Ladj ψ) := hasCompactSupport_transportedAdjoint hc
  have hmeasu := hum.comp hQc.measurable
  have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u (Qp x)‖ ≤ C :=
    Eventually.of_forall fun x => by simpa using hub (Qp x)
  have i1 : Integrable (fun x => u (Qp x) * (sliceCutoff r h (Evolution.timeCoord d x) *
      Ladj ψ x)) := by
    have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
      ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul ((contDiff_transportedAdjoint hB hb hψ).continuous)
        ).integrable_of_hasCompactSupport hLcs.mul_left
    exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
  have i2 : Integrable (fun x => u (Qp x) * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h)
      * ψ x)) := by
    have hk : Continuous (fun x =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      (continuous_const.mul (continuous_layerKernel.comp
        ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
    have : Integrable (fun x =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      hk.integrable_of_hasCompactSupport hc.mul_left
    exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
  exact (integral_add i1 i2).symm.trans key

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

