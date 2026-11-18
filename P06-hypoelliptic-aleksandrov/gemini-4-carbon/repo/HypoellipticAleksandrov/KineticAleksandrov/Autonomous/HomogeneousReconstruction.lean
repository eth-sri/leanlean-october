module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionError
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Evolution HypoellipticAleksandrov Parabolic Filter SectionTwo TheoremA
open scoped Topology

/-- The physical finite strip, open at both time endpoints. -/
def reconstructionStrip (H : Interval) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier}

/-- The prescribed exit omits the initial velocity face. -/
def reconstructionExit (H : Interval) (sMinus T : ℝ) : Set Point :=
  {p | p.time = T ∧ p.velocity 0 ∈ Set.Icc H.lo H.hi} ∪
    {p | sMinus < p.time ∧ p.time < T ∧
      (p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi)}


/-- Continuous anisotropic directional jets give the exact transported adjoint identity. -/
theorem integral_transportedAdjoint_of_anisotropic_jets
    {n : ℕ} {U : Set (EvolutionVec n)}
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (u T : EvolutionVec n → ℝ) (V Z : Fin n → EvolutionVec n → ℝ)
    (H : Fin n → Fin n → EvolutionVec n → ℝ)
    (hu : ContinuousOn u U) (hT : ContinuousOn T U)
    (hV : ∀ i, ContinuousOn (V i) U) (hZ : ∀ i, ContinuousOn (Z i) U)
    (hH : ∀ i j, ContinuousOn (H i j) U)
    (hdT : ∀ x ∈ U, HasLineDerivAt ℝ u (T x) x basisT)
    (hdV : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (V i x) x (basisV i))
    (hdZ : ∀ i x, x ∈ U → HasLineDerivAt ℝ u (Z i x) x (basisZ i))
    (hdH : ∀ i j x, x ∈ U → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j))
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * transportedAdjoint B b ψ x) =
      ∫ x in U, (T x +
        (∑ i, ∑ j, B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j * H i j x) +
        (∑ i, b (diffusedCoord n x) i * Z i x)) * ψ x := by
  let A i j (x : EvolutionVec n) :=
    B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j
  let β i (x : EvolutionVec n) := b (diffusedCoord n x) i
  let D (v : EvolutionVec n) (φ : EvolutionVec n → ℝ) (x : EvolutionVec n) :=
    fderiv ℝ φ x v
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (A i j) := fun i j =>
    (hB i j).comp (evolutionProdCLE n).contDiff
  have hβ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (β i) := fun i =>
    (contDiff_pi.mp hb i).comp (diffusedCoord n).contDiff
  have hD : ∀ v φ, ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (D v φ) :=
    fun v φ hφ => (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc : ∀ v φ, HasCompactSupport φ → HasCompactSupport (D v φ) :=
    fun v φ hφ => hφ.fderiv_apply (𝕜 := ℝ) v
  have hDs : ∀ v φ, tsupport (D v φ) ⊆ tsupport φ :=
    fun v φ => tsupport_evolution_fderiv_apply φ v
  have eqT : (∫ x in U, u x * D basisT ψ x) = -∫ x in U, T x * ψ x :=
    setIntegral_mul_evolution_directional_test hu hT basisT hdT hψ hc hs
  have eqH : ∀ i j,
      (∫ x in U, u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) =
        ∫ x in U, (A i j x * H i j x) * ψ x := by
    intro i j
    have h := setIntegral_mul_evolution_second_test hu (hV i) (hH i j)
      (basisV i) (basisV j) (hdV i) (hdH i j) ((hA i j).mul hψ)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
    convert h using 1
    congr 1
    funext x
    ring
  have eqZ : ∀ i, (∫ x in U, u x * (β i x * D (basisZ i) ψ x)) =
      -∫ x in U, (β i x * Z i x) * ψ x := by
    intro i
    have he : D (basisZ i) (fun y => β i y * ψ y) =
        fun x => β i x * D (basisZ i) ψ x := by
      funext x
      dsimp only [D]
      rw [fderiv_fun_mul ((hβ i).differentiable (by simp) x)
        (hψ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      change β i x * fderiv ℝ ψ x (basisZ i) +
        ψ x * fderiv ℝ (fun y => b (diffusedCoord n y) i) x (basisZ i) = _
      rw [fderiv_drift_transported_zero hb, mul_zero, add_zero]

    have h := setIntegral_mul_evolution_directional_test hu (hZ i) (basisZ i)
      (hdZ i) ((hβ i).mul hψ) hc.mul_left (tsupport_mul_subset_right.trans hs)
    change (∫ z in U, u z * D (basisZ i) (fun y => β i y * ψ y) z) = _ at h
    rw [he] at h
    convert h using 1
    congr 2
    funext x
    ring
  have iT : IntegrableOn (fun x => u x * D basisT ψ x) U volume :=
    (integrable_evolution_mul_test hu (hD basisT ψ hψ).continuous
      (hDc basisT ψ hc) ((hDs basisT ψ).trans hs)).integrableOn
  have iH : ∀ i j, IntegrableOn (fun x =>
      u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) U volume := by
    intro i j
    exact (integrable_evolution_mul_test hu
      (hD _ _ (hD _ _ ((hA i j).mul hψ))).continuous
      (hDc _ _ (hDc _ _ hc.mul_left))
      ((hDs _ _).trans ((hDs _ _).trans (tsupport_mul_subset_right.trans hs)))).integrableOn
  have iZ : ∀ i, IntegrableOn (fun x => u x * (β i x * D (basisZ i) ψ x)) U volume :=
    fun i => (integrable_evolution_mul_test hu
      ((hβ i).continuous.mul (hD _ _ hψ).continuous)
      (hDc _ _ hc).mul_left (tsupport_mul_subset_right.trans ((hDs _ _).trans hs))).integrableOn
  have jT : IntegrableOn (fun x => T x * ψ x) U volume :=
    (integrable_evolution_mul_test hT hψ.continuous hc hs).integrableOn
  have jH : ∀ i j, IntegrableOn (fun x => (A i j x * H i j x) * ψ x) U volume :=
    fun i j => (integrable_evolution_mul_test ((hA i j).continuous.continuousOn.mul (hH i j))
      hψ.continuous hc hs).integrableOn
  have jZ : ∀ i, IntegrableOn (fun x => (β i x * Z i x) * ψ x) U volume :=
    fun i => (integrable_evolution_mul_test ((hβ i).continuous.continuousOn.mul (hZ i))
      hψ.continuous hc hs).integrableOn
  have sumInt {ι : Type} [Fintype ι] (f : ι → EvolutionVec n → ℝ)
      (hf : ∀ i, IntegrableOn (f i) U volume) :
      IntegrableOn (fun x => ∑ i, f i x) U volume :=
    integrable_finsetSum _ (fun i _ => hf i)
  change (∫ x in U, u x * (-D basisT ψ x +
    (∑ i, ∑ j, D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
    (∑ i, β i x * D (basisZ i) ψ x))) =
    ∫ x in U, (T x + (∑ i, ∑ j, A i j x * H i j x) +
      (∑ i, β i x * Z i x)) * ψ x
  have hleft : (fun x => u x * (-D basisT ψ x +
      (∑ i, ∑ j, D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
      (∑ i, β i x * D (basisZ i) ψ x))) =
      fun x => -(u x * D basisT ψ x) +
        (∑ i, ∑ j, u x * D (basisV i) (D (basisV j) (fun y => A i j y * ψ y)) x) -
        (∑ i, u x * (β i x * D (basisZ i) ψ x)) := by
    funext x
    simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum]

  rw [hleft]
  erw [integral_sub (iT.neg.add (sumInt _ (fun i => sumInt _ (iH i)))) (sumInt _ iZ),
    integral_add iT.neg (sumInt _ (fun i => sumInt _ (iH i))), integral_neg]
  erw [integral_finsetSum _ (fun i _ => sumInt _ (iH i))]
  simp_rw [integral_finsetSum _ (fun j _ => iH _ j)]
  erw [integral_finsetSum _ (fun i _ => iZ i)]
  simp_rw [eqT, eqH, eqZ]
  simp
  have hright : (fun x => (T x + (∑ i, ∑ j, A i j x * H i j x) +
      (∑ i, β i x * Z i x)) * ψ x) =
      fun x => T x * ψ x + (∑ i, ∑ j, (A i j x * H i j x) * ψ x) +
        (∑ i, (β i x * Z i x) * ψ x) := by
    funext x
    simp only [add_mul, Finset.sum_mul]
  rw [hright]
  erw [integral_add (jT.add (sumInt _ (fun i => sumInt _ (jH i)))) (sumInt _ jZ),
    integral_add jT (sumInt _ (fun i => sumInt _ (jH i)))]
  erw [integral_finsetSum _ (fun i _ => sumInt _ (jH i))]
  simp_rw [integral_finsetSum _ (fun j _ => jH _ j)]
  erw [integral_finsetSum _ (fun i _ => jZ i)]



/-- The reconstruction regularity domain is open. -/
theorem isOpen_reconstructionStrip (H : Interval) (sMinus T : ℝ) :
    IsOpen (reconstructionStrip H sMinus T) :=
  (isOpen_Ioi.preimage continuous_time).inter (isOpen_stripPast H T)

/-- A C112 test has a continuous scalar kinetic operator on its regularity set. -/
theorem continuousOn_forwardScalarOperator {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {D : Set Point} {phi : Point → ℝ} (hphi : IsKineticC112On phi D) :
    ContinuousOn (forwardScalarOperator A.a phi) D := by
  have hx : Continuous (fun p : Point => p.position 0) :=
    (continuous_apply 0).comp continuous_position
  have hv : Continuous (fun p : Point => p.velocity 0) :=
    (continuous_apply 0).comp continuous_velocity
  have hh := (continuous_apply 0).comp_continuousOn
    ((continuous_apply 0).comp_continuousOn hphi.continuousOn_kineticVelocityHessian)
  exact (hphi.continuousOn_kineticTimeDerivative.add (hv.continuousOn.mul ((continuous_apply 0).comp_continuousOn hphi.continuousOn_kineticPositionGradient))).add
    ((A.smooth.continuous.comp (hx.prodMk hv)).continuousOn.mul hh)

/-- The source assumptions supply an actual zero-extended bounded Borel negative operator. -/
theorem exists_bounded_reconstruction_source {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ g : BoundedBorel Point,
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) := by
  classical
  obtain ⟨M, hM⟩ := hb
  let D := reconstructionStrip H sMinus T
  let f := D.piecewise (fun p => -forwardScalarOperator A.a phi p) (fun _ => 0)
  have hm : Measurable f :=
    (continuousOn_forwardScalarOperator A hphi).neg.measurable_piecewise
      continuous_const.continuousOn (isOpen_reconstructionStrip H sMinus T).measurableSet
  have hb' : ∀ p, |f p| ≤ max M 0 := by
    intro p
    by_cases hp : p ∈ D
    · dsimp only [f]
      rw [piecewise_eq_of_mem D _ _ hp, abs_neg]
      exact (hM p hp).2.trans (le_max_left _ _)
    · dsimp only [f]
      rw [piecewise_eq_of_notMem D _ _ hp, abs_zero]
      exact le_max_right _ _
  let g : BoundedBorel Point := ⟨f, hm, ⟨max M 0, le_max_right _ _, hb'⟩⟩
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    change f p = _
    dsimp only [f]
    exact piecewise_eq_of_mem D _ _ hp
  · intro p hp
    change f p = _
    dsimp only [f]
    exact piecewise_eq_of_notMem D _ _ hp


/-- Convert a packed native point to the physical `(time, position, velocity)` point. -/
def reconstructionPhysicalPoint (x : EvolutionVec 1) : Point :=
  ⟨timeCoord 1 x, transportedCoord 1 x, diffusedCoord 1 x⟩

/-- The physical unpacking map is continuous. -/
theorem continuous_reconstructionPhysicalPoint : Continuous reconstructionPhysicalPoint :=
  TheoremA.continuous_sectionTwoPoint 1 |>.comp (evolutionHomeomorph 1).continuous


private theorem physical_velocity_line (x : EvolutionVec 1) (i : Fin 1) (t : ℝ) :
    reconstructionPhysicalPoint (x + t • basisV i) =
      ⟨timeCoord 1 x, transportedCoord 1 x,
        diffusedCoord 1 x + t • PDE.basisVec i⟩ := by
  simp [reconstructionPhysicalPoint, basisV, PDE.basisVec]


/-- The physical time slice supplies the packed time line derivative. -/
theorem reconstruction_time_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) :
    HasLineDerivAt ℝ (phi ∘ reconstructionPhysicalPoint)
      (kineticTimeDerivative phi (reconstructionPhysicalPoint x)) x basisT  := by
  have physical_time_line (x : EvolutionVec 1) (t : ℝ) :
      reconstructionPhysicalPoint (x + t • basisT) =
      ⟨timeCoord 1 x + t, transportedCoord 1 x, diffusedCoord 1 x⟩ := by
    simp [reconstructionPhysicalPoint, basisT]
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_time_line]
  simpa using! (hphi.timeSlice_hasDerivAt hx).comp_of_eq (h := fun t => timeCoord 1 x + t) 0 ((hasDerivAt_id 0).const_add (timeCoord 1 x)) (by simp [reconstructionPhysicalPoint])

/-- The physical velocity slice supplies each packed diffused line derivative. -/
theorem reconstruction_velocity_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) (i : Fin 1) :
    HasLineDerivAt ℝ (phi ∘ reconstructionPhysicalPoint)
      (kineticVelocityGradient phi (reconstructionPhysicalPoint x) i) x (basisV i) := by
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_velocity_line]
  exact ((hphi.velocitySlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt |>.hasLineDerivAt (PDE.basisVec i)

/-- The physical position slice supplies each packed transported line derivative. -/
theorem reconstruction_position_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) (i : Fin 1) :
    HasLineDerivAt ℝ (phi ∘ reconstructionPhysicalPoint)
      (kineticPositionGradient phi (reconstructionPhysicalPoint x) i) x (basisZ i)  := by
  have physical_position_line (x : EvolutionVec 1) (i : Fin 1) (t : ℝ) :
      reconstructionPhysicalPoint (x + t • basisZ i) =
      ⟨timeCoord 1 x, transportedCoord 1 x + t • PDE.basisVec i,
        diffusedCoord 1 x⟩ := by
    simp [reconstructionPhysicalPoint, basisZ, PDE.basisVec]
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_position_line]
  exact ((hphi.positionSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt |>.hasLineDerivAt (PDE.basisVec i)

/-- Differentiating a physical velocity gradient entry gives the actual Hessian entry. -/
theorem reconstruction_hessian_hasLineDerivAt {phi : Point → ℝ} {D : Set Point}
    (hphi : IsKineticC112On phi D) {x : EvolutionVec 1}
    (hx : reconstructionPhysicalPoint x ∈ D) (i j : Fin 1) :
    HasLineDerivAt ℝ
      (fun y => kineticVelocityGradient phi (reconstructionPhysicalPoint y) i)
      (kineticVelocityHessian phi (reconstructionPhysicalPoint x) j i) x (basisV j) := by
  let p := reconstructionPhysicalPoint x
  let f : PDE.Vec 1 → ℝ := fun v => phi ⟨p.time, p.position, v⟩
  have hd :=
    ((hphi.velocitySlice_contDiffAt hx).fderiv_right (m := 1) (by norm_num))
      |>.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (PDE.classicalGradient f) p.velocity := by
    apply differentiableAt_pi.mpr
    intro k
    exact hd.clm_apply (differentiableAt_const (PDE.basisVec k))
  unfold HasLineDerivAt
  simp only [physical_velocity_line]
  exact (hasFDerivAt_pi'.mp hg.hasFDerivAt i).hasLineDerivAt (PDE.basisVec j)


/-- The actual pointwise difference used in homogeneous reconstruction. -/
def stripReconstructionCandidate (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  phi p - stripSourcePotential H K T g p



/-- A physical C112 test satisfies its actual weak equation in packed coordinates. -/
theorem reconstruction_test_isWeakTransportedSolution {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) {D : Set Point} (hD : IsOpen D)
    {phi : Point → ℝ} (hphi : IsKineticC112On phi D) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (reconstructionPhysicalPoint ⁻¹' D) (phi ∘ reconstructionPhysicalPoint)
      (forwardScalarOperator A.a phi ∘ reconstructionPhysicalPoint) := by
  let U := reconstructionPhysicalPoint ⁻¹' D
  have hc {f : Point → ℝ} (hf : ContinuousOn f D) :
      ContinuousOn (f ∘ reconstructionPhysicalPoint) U :=
    hf.comp continuous_reconstructionPhysicalPoint.continuousOn (fun _ hx => hx)
  have hV (i : Fin 1) : ContinuousOn
      (fun x => kineticVelocityGradient phi (reconstructionPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hphi.continuousOn_kineticVelocityGradient)
  have hZ (i : Fin 1) : ContinuousOn
      (fun x => kineticPositionGradient phi (reconstructionPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hphi.continuousOn_kineticPositionGradient)
  have hH (i j : Fin 1) : ContinuousOn
      (fun x => kineticVelocityHessian phi (reconstructionPhysicalPoint x) j i) U :=
    hc ((continuous_apply i).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hphi.continuousOn_kineticVelocityHessian))
  refine ⟨(hc hphi.continuousOn).locallyIntegrableOn (hD.preimage continuous_reconstructionPhysicalPoint).measurableSet, ?_⟩
  intro ψ hψ hcompact hs
  refine (integral_transportedAdjoint_of_anisotropic_jets (evolutionCoefficient A.a) (identityDrift 1) (evolutionCoefficient_smooth A) (identityDrift_smooth 1) (phi ∘ reconstructionPhysicalPoint) (kineticTimeDerivative phi ∘ reconstructionPhysicalPoint) (fun i x => kineticVelocityGradient phi (reconstructionPhysicalPoint x) i) (fun i x => kineticPositionGradient phi (reconstructionPhysicalPoint x) i) (fun i j x => kineticVelocityHessian phi (reconstructionPhysicalPoint x) j i) (hc hphi.continuousOn) (hc hphi.continuousOn_kineticTimeDerivative) hV hZ hH (fun _ hx => reconstruction_time_hasLineDerivAt hphi hx) (fun i _ hx => reconstruction_velocity_hasLineDerivAt hphi hx i) (fun i _ hx => reconstruction_position_hasLineDerivAt hphi hx i) (fun i j _ hx => reconstruction_hessian_hasLineDerivAt hphi hx i j) ψ hψ hcompact hs).trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x
  simp only [Fin.sum_univ_one, evolutionCoefficient, identityDrift,
    Function.comp_def, forwardScalarOperator, reconstructionPhysicalPoint, id_eq]
  ring




/-- The actual bounded-source potential is continuous at every strictly interior strip point.
Only continuity of the source on the open strip is required. -/
theorem reconstruction_source_potential_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (g : BoundedBorel Point)
    (hg : ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T)) :
    ContinuousOn (stripSourcePotential H E.2 T g) (reconstructionStrip H sMinus T)  := by
  intro p hp
  have reconstruction_source_potential_continuousOn_window (sMinus a T R₀ : ℝ) (ha : sMinus < a) (g : BoundedBorel Point) (hg : ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T)) :
      ContinuousOn (stripSourcePotential H E.2 T g)
      {p | a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R₀} := by
    have reconstruction_compact_potential_continuousOn (T : ℝ) {sMinus : ℝ} (f : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ reconstructionSourceDomain H sMinus T) :
        ContinuousOn (fun p => duhamelPotential E.2 T (f ∘ KineticPoint.equivProd 1)
        (sectionTwoPoint p)) (stripPast H T) := by
      have hg := hf
      have hgs : tsupport (f ∘ KineticPoint.equivProd 1) ⊆
          evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
        intro p hp
        have hx := hs ((tsupport_comp_subset_preimage f
          (KineticPoint.homeomorphProd 1).continuous) hp)
        change sMinus < p.time ∧ p.time < T ∧ p.position 0 ∈ H.carrier at hx
        refine ⟨hx.2.1, ?_⟩
        apply PDE.mem_translateSet_iff_sub_mem.mpr
        simpa [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using hx.2.2
      have hcont := reconstruction_compact_duhamel_continuousOn hH hlam hLam A H E hE T
        (f ∘ KineticPoint.equivProd 1) hg (hc.comp_homeomorph (KineticPoint.homeomorphProd 1)) hgs
      apply hcont.comp (continuous_sectionTwoPoint 1).continuousOn
      intro p hp
      refine ⟨hp.1.le, subset_closure ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    classical
    let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
    have hR (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
    obtain ⟨C, hC, hgb⟩ := g.exists_bound
    choose f hf hc hs hclose using fun n => exists_reconstruction_compact_source_approx
      H sMinus a T ha (hr n) (hR n) (hr n)
      (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x))) hg C hC
      (fun x => hgb _)
    have hfc (n : ℕ) : Continuous (f n) := (hf n).continuous
    have hfb (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f n x| ≤ B := by
      obtain ⟨B, hB⟩ := (hfc n).bounded_above_of_compact_support (hc n)
      refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
      have hh : |f n x| ≤ B := by simpa using hB x
      exact hh.trans (le_max_left _ _)
    let G (n : ℕ) : BoundedBorel Point :=
      ⟨fun p => f n (KineticPoint.equivProd 1 (sectionTwoPoint p)),
        (hfc n).measurable.comp
          ((KineticPoint.homeomorphProd 1).continuous.comp
            (continuous_sectionTwoPoint 1)).measurable, by
        obtain ⟨B, hB, hb⟩ := hfb n
        exact ⟨B, hB, fun p => hb _⟩⟩
    let F (n : ℕ) (p : Point) : ℝ :=
      duhamelPotential E.2 T (f n ∘ KineticPoint.equivProd 1) (sectionTwoPoint p)
    have hF (n : ℕ) : ContinuousOn (F n) (stripPast H T) :=
      reconstruction_compact_potential_continuousOn T
        (f n) (hf n) (hc n) (hs n)
    have hFG (n : ℕ) (e : StripPole H (T : WithTop ℝ)) :
        stripPotentialOfKernel H E.2 T (G n) e = F n e.1 := by
      rw [← stripSourcePotential_eq_green H E.2 T (G n) e]
      unfold stripSourcePotential
      congr 1
    let Q := Real.exp ((max |H.lo| |H.hi| + 1) * (T - a)) * (2 * Real.exp R₀)
    let b (n : ℕ) : ℝ := r n * (T - a) + C *
      (Real.exp 1 * (2 * (r n) ^ 2 / lam) + r n + Q * r n)
    have hbd (n : ℕ) (p : Point)
        (hp : a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R₀) :
        |stripSourcePotential H E.2 T g p - F n p| ≤ b n := by
      let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.2.1.1, hp.2.1.2⟩
      have herr := reconstruction_green_potential_error hH hlam hLam A H E hE T a e hp.1
        g (G n) C hC (hr n) (hR n) (hr n).le (fun z hz => by
          have hh := hclose n (KineticPoint.equivProd 1 (sectionTwoPoint z)) hz
          rw [Equiv.symm_apply_apply, sectionTwoPoint_involutive] at hh
          simpa only [G, abs_sub_comm] using hh)
      rw [hFG] at herr
      rw [← stripSourcePotential_eq_green H E.2 T g e] at herr
      have hV : 0 ≤ max |H.lo| |H.hi| + 1 := by
        linarith only [(abs_nonneg H.lo).trans (le_max_left |H.lo| |H.hi|)]
      have hx := abs_le.mp hp.2.2
      have hw : reconstructionSpatialWeight (p.position 0) ≤ 2 * Real.exp R₀ := by
        unfold reconstructionSpatialWeight
        linarith only [(Real.exp_le_exp.mpr hx.2), (Real.exp_le_exp.mpr (neg_le.mp hx.1))]
      have hQ :=
        mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_left hp.1 T) hV)) hw (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          (Real.exp_pos _).le
      apply herr.trans
      change _ ≤ b n
      dsimp only [b]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hp.1 T) (hr n).le
      · apply mul_le_mul_of_nonneg_left _ hC
        apply add_le_add (le_refl _)
        simpa [r, div_eq_mul_inv] using
          div_le_div_of_nonneg_right hQ (hR n).le
    have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hb0 : Tendsto b atTop (𝓝 0) := by
      simpa [b, zero_pow (by decide : 2 ≠ 0)] using
        (hr0.mul_const (T - a)).add
          ((((hr0.pow 2).const_mul 2).div_const lam).const_mul (Real.exp 1) |>.add hr0 |>.add
            (hr0.const_mul Q) |>.const_mul C)
    have hu : TendstoUniformlyOn F (stripSourcePotential H E.2 T g) atTop
        {p | a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R₀} := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      filter_upwards [hb0.eventually (gt_mem_nhds hε)] with n hn
      intro p hp
      simpa only [Real.dist_eq] using (hbd n p hp).trans_lt hn
    exact hu.continuousOn (Eventually.of_forall fun n =>
      (hF n).mono (fun p hp => hp.2.1)).frequently
  let a := (sMinus + p.time) / 2
  let R := |p.position 0| + 1
  have ha : sMinus < a := by dsimp only [a]; linarith only [hp.1]
  have hap : a < p.time := by dsimp only [a]; linarith only [hp.1]
  have hR : |p.position 0| < R := by dsimp only [R]; linarith
  have hpos : Continuous (fun q : Point => |q.position 0|) :=
    ((continuous_apply 0).comp continuous_position).abs
  have hn : {q : Point | a ≤ q.time ∧ q ∈ stripPast H T ∧ |q.position 0| ≤ R} ∈ 𝓝 p := by
    exact Filter.mem_of_superset ((((isOpen_lt continuous_const continuous_time).inter (isOpen_stripPast H T)).inter (isOpen_lt hpos continuous_const)).mem_nhds ⟨⟨hap, hp.2⟩, hR⟩) (fun q hq => ⟨hq.1.1.le, hq.1.2, hq.2.le⟩)
  exact ((reconstruction_source_potential_continuousOn_window sMinus a T R ha g hg).continuousAt hn).continuousWithinAt


/-- The actual negative-operator source is continuous in native product coordinates. -/
theorem reconstruction_source_continuousOn
    {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (g : BoundedBorel Point)
    (hg : ∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) :
    ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T) := by
  have hc :=
    ((continuousOn_forwardScalarOperator A hphi).neg).congr (fun p hp => hg p hp)
  apply hc.comp ((continuous_sectionTwoPoint 1).comp
    (KineticPoint.homeomorphProd 1).symm.continuous).continuousOn
  intro x hx
  exact hx


/-- An actual bounded-source reconstruction has a smooth homogeneous representative with
pointwise equality at every strictly interior source point. -/
theorem exists_reconstruction_smooth_pointwise
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ),
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      EqOn (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      ∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0   := by
  have reconstruction_candidate_eq_smooth (g : BoundedBorel Point) (hg : ∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) (f : EvolutionVec 1 → ℝ) (hf : ContinuousOn f
      (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)) (hae : (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
      =ᵐ[volume.restrict
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f) :
      EqOn (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint) f
      (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) := by
    have hp := reconstruction_source_potential_continuousOn hH hlam hLam A H E hE
      sMinus T g (reconstruction_source_continuousOn A H sMinus T phi hphi g hg)
    have hc : ContinuousOn (stripReconstructionCandidate H E.2 T phi g)
        (reconstructionStrip H sMinus T) := hphi.continuousOn.sub hp
    have hcp := hc.comp continuous_reconstructionPhysicalPoint.continuousOn (fun _ hx => hx)
    exact Measure.eqOn_open_of_ae_eq hae
      ((isOpen_reconstructionStrip H sMinus T).preimage continuous_reconstructionPhysicalPoint)
      hcp hf
  have exists_reconstruction_smooth_ae (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
      ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ),
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
        =ᵐ[volume.restrict
          (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f ∧
      ∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0 := by
    have candidate_weak (g : BoundedBorel Point) (hg : ∀ p ∈ reconstructionStrip H sMinus T,
        g p = -forwardScalarOperator A.a phi p) :
        IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)
        (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
        (fun _ => 0) := by
      have source_congr {U : Set (EvolutionVec 1)} (hU : IsOpen U) {u : EvolutionVec 1 → ℝ} {g : EvolutionVec 1 → ℝ} {f : EvolutionVec 1 → ℝ} (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u g) (hg : EqOn g f U) :
          IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u f := by
        refine ⟨hu.1, ?_⟩
        intro ψ hψ hc hs
        refine (hu.2 ψ hψ hc hs).trans (setIntegral_congr_fun hU.measurableSet ?_)
        intro x hx
        change g x * ψ x = f x * ψ x
        rw [hg hx]
      let U := reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
      have hU : IsOpen U := (isOpen_reconstructionStrip H sMinus T).preimage
        continuous_reconstructionPhysicalPoint
      have htest := reconstruction_test_isWeakTransportedSolution A
        (isOpen_reconstructionStrip H sMinus T) hphi
      have hw := (isWeakTransportedSolution_comp_iff (evolutionCoefficient A.a)
        (identityDrift 1) _ _ _).mpr (stripSourcePotential_weak A H E hE T g)
      have hsub : U ⊆ evolutionHomeomorph 1 ⁻¹'
          evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
        intro x hx
        refine ⟨hx.2.1, ?_⟩
        change diffusedCoord 1 x ∈ movingDomain (intervalDomain H) (fun _ => 0) _
        rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero, intervalDomain,
          PDE.mem_oneDimensionalAxisBox_iff]
        exact hx.2.2
      have hwr := weak_solution_restrict A hsub hw
      have hsource : EqOn
          ((fun p => -nativeStripSource g p) ∘ evolutionHomeomorph 1)
          (forwardScalarOperator A.a phi ∘ reconstructionPhysicalPoint) U := by
        intro x hx
        change -g (reconstructionPhysicalPoint x) = _
        rw [hg _ hx, neg_neg]
        rfl
      have hws := source_congr hU hwr hsource
      exact weak_same_source_sub A htest hws
    obtain ⟨g, hg, hg0⟩ := exists_bounded_reconstruction_source A H sMinus T phi hphi hb
    obtain ⟨f, hf, hae, heq⟩ := homogeneous_weak_smooth_solution hH hlam A
      ((isOpen_reconstructionStrip H sMinus T).preimage continuous_reconstructionPhysicalPoint)
      (candidate_weak g hg)
    exact ⟨g, f, hg, hg0, hf, hae, heq⟩
  obtain ⟨g, f, hg, hg0, hf, hae, heq⟩ :=
    exists_reconstruction_smooth_ae hb
  exact ⟨g, f, hg, hg0, hf,
    reconstruction_candidate_eq_smooth g hg
      f hf.continuousOn hae, heq⟩


/-- The source potential is zero at every invalid open-strip pole. -/
theorem reconstruction_potential_zero_outside (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (p : Point) (hp : p ∉ stripPast H T) :
    stripSourcePotential H K T g p = 0 := by
  by_cases ht : p.time < T
  · apply duhamelPotential_eq_zero_of_not_mem
    change p.velocity ∉ movingDomain (intervalDomain H) (fun _ => 0) p.time
    rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero, intervalDomain,
      PDE.mem_oneDimensionalAxisBox_iff]
    exact fun hv => hp ⟨ht, hv⟩
  · exact duhamelPotential_eq_zero_of_terminal_le K T (nativeStripSource g)
      (sectionTwoPoint p) (le_of_not_gt ht)

/-- The time barrier extends continuously to all ambient points. -/
theorem reconstruction_potential_abs_le_time (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) (p : Point) :
    |stripSourcePotential H K T g p| ≤ C * max (T - p.time) 0 := by
  by_cases hp : p ∈ stripPast H T
  · let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.1, hp.2⟩
    rw [stripSourcePotential_eq_green H K T g e,
      max_eq_left (sub_nonneg.mpr hp.1.le)]
    exact stripPotentialOfKernel_abs_le H K T g e C hC hg
  · rw [reconstruction_potential_zero_outside H K T g p hp, abs_zero]
    exact mul_nonneg hC (le_max_right _ _)




/-- Actual reconstruction is continuous on the interior together with its prescribed exit. -/
theorem reconstruction_candidate_continuousOn_exit
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : Parabolic.IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (g : BoundedBorel Point)
    (hg : ∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) :
    ContinuousOn (stripReconstructionCandidate H E.2 T phi g)
      (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T)   := by
  have reconstruction_potential_continuousAt_face (p : Point) (hp : p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi) :
      ContinuousAt (stripSourcePotential H E.2 T g) p := by
    have reconstruction_potential_abs_le_face (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) (p : Point) :
        |stripSourcePotential H E.2 T g p| ≤
        C * max ((p.velocity 0 - H.lo) * (H.hi - p.velocity 0) / (2 * lam)) 0 := by
      by_cases hp : p ∈ stripPast H T
      · let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.1, hp.2⟩
        have hq : 0 ≤ (p.velocity 0 - H.lo) * (H.hi - p.velocity 0) / (2 * lam) :=
          div_nonneg (mul_nonneg (sub_nonneg.mpr hp.2.1.le) (sub_nonneg.mpr hp.2.2.le))
            (by positivity)
        rw [stripSourcePotential_eq_green H E.2 T g e, max_eq_left hq]
        exact stripPotentialOfRealization_abs_le_quadratic hH hlam hLam A H E hE T e g C hC hg
      · rw [reconstruction_potential_zero_outside H E.2 T g p hp, abs_zero]
        exact mul_nonneg hC (le_max_right _ _)
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    have hv : Continuous (fun q : Point => q.velocity 0) :=
      (continuous_apply 0).comp continuous_velocity
    have hc : Continuous (fun q : Point => C *
        max ((q.velocity 0 - H.lo) * (H.hi - q.velocity 0) / (2 * lam)) 0) :=
      continuous_const.mul
      ((((hv.sub continuous_const).mul (continuous_const.sub hv)).div_const (2 * lam)).max
        continuous_const)
    have hb : Tendsto (fun q : Point => C *
        max ((q.velocity 0 - H.lo) * (H.hi - q.velocity 0) / (2 * lam)) 0)
        (𝓝 p) (𝓝 0) := by
      rcases hp with hp | hp <;>
        simpa [hp, max_self] using!
          (hc.continuousAt (x := p)).tendsto
    have ht := squeeze_zero_norm (f := stripSourcePotential H E.2 T g)
      (fun q => by simpa using
        reconstruction_potential_abs_le_face C hC hg q) hb
    change Tendsto (stripSourcePotential H E.2 T g) (𝓝 p)
      (𝓝 (stripSourcePotential H E.2 T g p))
    have hn : p ∉ stripPast H T := by
      intro h
      rcases hp with hp | hp
      · exact (lt_irrefl _ : ¬H.lo < H.lo) (hp ▸ h.2.1)
      · exact (lt_irrefl _ : ¬H.hi < H.hi) (hp ▸ h.2.2)
    rw [reconstruction_potential_zero_outside H E.2 T g p hn]
    exact ht
  have reconstruction_potential_continuousAt_terminal (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (p : Point) (hp : p.time = T) :
      ContinuousAt (stripSourcePotential H K T g) p := by
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    have hc : Continuous (fun q : Point => C * max (T - q.time) 0) :=
      continuous_const.mul ((continuous_const.sub continuous_time).max continuous_const)
    have hb : Tendsto (fun q : Point => C * max (T - q.time) 0) (𝓝 p) (𝓝 0) := by
      simpa [hp, max_self] using! (hc.continuousAt (x := p)).tendsto
    have ht := squeeze_zero_norm (f := stripSourcePotential H K T g)
      (fun q => by simpa using
        reconstruction_potential_abs_le_time H K T g C hC hg q) hb
    change Tendsto (stripSourcePotential H K T g) (𝓝 p)
      (𝓝 (stripSourcePotential H K T g p))
    rw [reconstruction_potential_zero_outside H K T g p
      (fun h => (by simpa only [hp] using h.1 : T < T).false)]
    exact ht
  apply hc.sub
  apply ContinuousOn.union_continuousAt (isOpen_reconstructionStrip H sMinus T)
    (reconstruction_source_potential_continuousOn hH hlam hLam A H E hE sMinus T g
      (reconstruction_source_continuousOn A H sMinus T phi hphi g hg))
  intro p hp
  rcases hp with ht | hv
  · exact reconstruction_potential_continuousAt_terminal E.2 p ht.1
  · exact reconstruction_potential_continuousAt_face p hv.2.2


/-- The physical scalar operator is the native transported operator after coordinate exchange. -/
theorem reconstruction_scalar_operator_swap (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (u ∘ sectionTwoPoint) p = forwardScalarOperator a u (sectionTwoPoint p) := by
  rw [transportedForwardOperator_apply, forwardScalarOperator]
  simp only [matrixContraction, Fin.sum_univ_one, fullKineticCoefficientAt,
    evolutionCoefficient, PDE.vecDot, identityDrift]
  change kineticTimeDerivative u (sectionTwoPoint p) +
      a (p.velocity 0) (p.position 0) * kineticVelocityHessian u (sectionTwoPoint p) 0 0 +
      p.position 0 * kineticPositionGradient u (sectionTwoPoint p) 0 = _
  dsimp only [sectionTwoPoint]
  ring

/-- The packed operator depends only on the function germ, including its second derivatives. -/
theorem reconstruction_transportedOperator_congr
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1)
    {u f : EvolutionVec 1 → ℝ} {x : EvolutionVec 1} (h : u =ᶠ[𝓝 x] f) :
    transportedOperator B b u x = transportedOperator B b f x := by
  have hd := h.fderiv_eq (𝕜 := ℝ)
  have hh (j : Fin 1) :
      (fun y => fderiv ℝ u y (basisV j)) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ f y (basisV j)) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
  unfold transportedOperator
  rw [hd]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(hh j).fderiv_eq (𝕜 := ℝ)]

/-- A bounded C112 test has an actual smooth homogeneous reconstruction, with the prescribed
exit values and the literal Green integral at every strictly interior pole. -/
theorem strip_bounded_source_reconstruction
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ u : Point → ℝ,
      (∀ e : StripPole H (T : WithTop ℝ), sMinus < e.1.time →
        u e.1 = phi e.1 - ∫ p, -forwardScalarOperator A.a phi p
          ∂stripGreenOfKernel H E.2 T e) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
        (KineticPoint.equivProd 1 '' reconstructionStrip H sMinus T) ∧
      (∀ p ∈ reconstructionStrip H sMinus T, forwardScalarOperator A.a u p = 0) ∧
      ContinuousOn u (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T) ∧
      EqOn u phi (reconstructionExit H sMinus T)  := by
  let K := E.2
  have stripReconstructionCandidate_eqOn_exit (g : BoundedBorel Point) :
      EqOn (stripReconstructionCandidate H K T phi g) phi
      (reconstructionExit H sMinus T) := by
    intro p hp
    have hz : stripSourcePotential H K T g p = 0 := by
      rcases hp with ht | hv
      · exact duhamelPotential_eq_zero_of_terminal_le K T (nativeStripSource g)
          (sectionTwoPoint p) (by change T ≤ p.time; exact ht.1.ge)
      · apply duhamelPotential_eq_zero_of_not_mem K T (nativeStripSource g)
          (sectionTwoPoint p)
        change p.velocity ∉ movingDomain (intervalDomain H) (fun _ => 0) p.time
        rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero]
        rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
        change p.velocity 0 ∉ Set.Ioo H.lo H.hi
        rcases hv.2.2 with hl | hh
        · rw [hl]
          exact fun h => (lt_irrefl H.lo) h.1
        · rw [hh]
          exact fun h => (lt_irrefl H.hi) h.2
    change phi p - stripSourcePotential H K T g p = phi p
    rw [hz, sub_zero]
  obtain ⟨g, f, hg, hg0, hf, heq, hop⟩ :=
    exists_reconstruction_smooth_pointwise hH hlam hLam A H E hE sMinus T phi hphi hb
  let u := stripReconstructionCandidate H E.2 T phi g
  let U := reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
  have hU : IsOpen U := (isOpen_reconstructionStrip H sMinus T).preimage
    continuous_reconstructionPhysicalPoint
  have hus : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ reconstructionPhysicalPoint) U :=
    hf.congr (fun x hx => heq hx)
  have huop : ∀ x ∈ U, transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
      (u ∘ reconstructionPhysicalPoint) x = 0 := by
    intro x hx
    have hh : (u ∘ reconstructionPhysicalPoint) =ᶠ[𝓝 x] f :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => heq hy)
    rw [reconstruction_transportedOperator_congr _ _ hh]
    exact hop x hx
  refine ⟨u, ?_, ?_, ?_,
    reconstruction_candidate_continuousOn_exit hH hlam hLam A H E hE sMinus T phi hphi hc g hg,
    stripReconstructionCandidate_eqOn_exit g⟩
  · intro e he
    have hgAE : g =ᵐ[stripGreenOfKernel H E.2 T e] fun p => -forwardScalarOperator A.a phi p := by
      filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
        reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
      exact hg p ⟨he.trans ht, hp⟩
    change phi e.1 - stripSourcePotential H E.2 T g e.1 = _
    rw [stripSourcePotential_eq_green H E.2 T g e]
    exact congrArg (fun z => phi e.1 - z) (integral_congr_ae hgAE)
  · let c : (ℝ × PDE.Vec 1 × PDE.Vec 1) → EvolutionVec 1 :=
      fun q => (evolutionProdCLE 1).symm (q.1, q.2.2, q.2.1)
    have hcs : ContDiff ℝ (⊤ : ℕ∞) c :=
      (evolutionProdCLE 1).symm.contDiff.comp
        (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))
    have hec : (fun q => reconstructionPhysicalPoint (c q)) =
        (KineticPoint.equivProd 1).symm := by
      funext q
      simp [c, reconstructionPhysicalPoint, KineticPoint.equivProd]
    have hmaps : MapsTo c (KineticPoint.equivProd 1 '' reconstructionStrip H sMinus T) U := by
      rintro q ⟨p, hp, rfl⟩
      change reconstructionPhysicalPoint (c (KineticPoint.equivProd 1 p)) ∈
        reconstructionStrip H sMinus T
      rw [congrFun hec, Equiv.symm_apply_apply]
      exact hp
    have hh := hus.comp hcs.contDiffOn hmaps
    have heqf : (u ∘ reconstructionPhysicalPoint) ∘ c = u ∘ (KineticPoint.equivProd 1).symm := by
      funext q
      change u (reconstructionPhysicalPoint (c q)) = _
      rw [congrFun hec]
      rfl
    rwa [heqf] at hh
  · intro p hp
    let x := (evolutionHomeomorph 1).symm (sectionTwoPoint p)
    have hxp : reconstructionPhysicalPoint x = p := by
      change sectionTwoPoint (evolutionHomeomorph 1 x) = p
      rw [Homeomorph.apply_symm_apply, sectionTwoPoint_involutive]
    have hx : x ∈ U := by
      change reconstructionPhysicalPoint x ∈ reconstructionStrip H sMinus T
      rwa [hxp]
    have hsm : ContDiffAt ℝ 2 ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x :=
      (hus.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
    have hh := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hsm
    change transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
      (u ∘ reconstructionPhysicalPoint) x =
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
          (u ∘ sectionTwoPoint) (evolutionHomeomorph 1 x) at hh
    rw [huop x hx] at hh
    rw [Homeomorph.apply_symm_apply, reconstruction_scalar_operator_swap,
      sectionTwoPoint_involutive] at hh
    exact hh.symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

