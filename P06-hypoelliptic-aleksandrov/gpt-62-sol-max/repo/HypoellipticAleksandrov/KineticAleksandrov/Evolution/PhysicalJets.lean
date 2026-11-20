module

public import HypoellipticAleksandrov.Parabolic.KineticClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry

/-! # Physical C112 jets in packed evolution coordinates

The packed coordinates have order `(time, velocity, position)`. These lemmas use
the physical slice derivatives directly, without imposing second position derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution
open HypoellipticAleksandrov Parabolic SectionTwo MeasureTheory Set
variable {d : ℕ}

/-- Convert a packed native point to the physical `(time, position, velocity)` point. -/
def packedPhysicalPoint (x : EvolutionVec d) : KineticPoint d :=
  ⟨timeCoord d x, transportedCoord d x, diffusedCoord d x⟩

/-- The physical unpacking map is continuous. -/
theorem continuous_packedPhysicalPoint : Continuous (packedPhysicalPoint (d := d)) :=
  TheoremA.continuous_sectionTwoPoint d |>.comp (evolutionHomeomorph d).continuous

private theorem physical_time_line (x : EvolutionVec d) (t : ℝ) :
    packedPhysicalPoint (x + t • basisT) =
      ⟨timeCoord d x + t, transportedCoord d x, diffusedCoord d x⟩ := by
  simp [packedPhysicalPoint, basisT]

section
variable (x : EvolutionVec d) (i : Fin d) (t : ℝ)

private theorem physical_velocity_line :
    packedPhysicalPoint (x + t • basisV i) =
      ⟨timeCoord d x, transportedCoord d x,
        diffusedCoord d x + t • PDE.basisVec i⟩ := by
  simp [packedPhysicalPoint, basisV, PDE.basisVec]

private theorem physical_position_line :
    packedPhysicalPoint (x + t • basisZ i) =
      ⟨timeCoord d x, transportedCoord d x + t • PDE.basisVec i,
        diffusedCoord d x⟩ := by
  simp [packedPhysicalPoint, basisZ, PDE.basisVec]

end

section
variable {phi : KineticPoint d → ℝ} {D : Set (KineticPoint d)} (hphi : IsKineticC112On phi D)
  {x : EvolutionVec d} (hx : packedPhysicalPoint x ∈ D)
include D hphi hx

/-- The physical time slice supplies the packed time line derivative. -/
theorem packed_time_hasLineDerivAt :
    HasLineDerivAt ℝ (phi ∘ packedPhysicalPoint)
      (kineticTimeDerivative phi (packedPhysicalPoint x)) x basisT := by
  have h := (hphi.timeSlice_hasDerivAt hx).comp_of_eq
    (h := fun t : ℝ => timeCoord d x + t) (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).const_add (timeCoord d x))
    (by simp [packedPhysicalPoint])
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_time_line]
  simpa only [Function.comp_def, mul_one, packedPhysicalPoint] using! h

/-- The physical velocity slice supplies each packed diffused line derivative. -/
theorem packed_velocity_hasLineDerivAt (i : Fin d) :
    HasLineDerivAt ℝ (phi ∘ packedPhysicalPoint)
      (kineticVelocityGradient phi (packedPhysicalPoint x) i) x (basisV i) := by
  have h := ((hphi.velocitySlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_velocity_line]
  exact h

/-- The physical position slice supplies each packed transported line derivative. -/
theorem packed_position_hasLineDerivAt (i : Fin d) :
    HasLineDerivAt ℝ (phi ∘ packedPhysicalPoint)
      (kineticPositionGradient phi (packedPhysicalPoint x) i) x (basisZ i) := by
  have h := ((hphi.positionSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt
  simp only [Function.comp_def, physical_position_line]
  exact h

/-- Differentiating a physical velocity gradient entry gives the actual Hessian entry. -/
theorem packed_hessian_hasLineDerivAt (i j : Fin d) :
    HasLineDerivAt ℝ
      (fun y => kineticVelocityGradient phi (packedPhysicalPoint y) i)
      (kineticVelocityHessian phi (packedPhysicalPoint x) j i) x (basisV j) := by
  let p := packedPhysicalPoint x
  let f : PDE.Vec d → ℝ := fun v => phi ⟨p.time, p.position, v⟩
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p.velocity :=
    ((hphi.velocitySlice_contDiffAt hx).fderiv_right (m := 1) (by norm_num))
      |>.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (PDE.classicalGradient f) p.velocity := by
    apply differentiableAt_pi.mpr
    intro k
    exact hd.clm_apply (differentiableAt_const (PDE.basisVec k))
  have h := (hasFDerivAt_pi'.mp hg.hasFDerivAt i).hasLineDerivAt (PDE.basisVec j)
  unfold HasLineDerivAt
  simp only [physical_velocity_line]
  exact h

end

/-- A classical kinetic function satisfies the weak equation of its residual in packed coordinates. -/
theorem packedPhysicalPoint_classical_weak (B : FullKineticCoefficient d)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D) :
    IsWeakTransportedSolution B (identityDrift d) (packedPhysicalPoint ⁻¹' D) (u ∘ packedPhysicalPoint)
      (forwardKineticOperator (fun t x v => B t v x) u ∘ packedPhysicalPoint) := by
  let U := packedPhysicalPoint ⁻¹' D
  have hU : IsOpen U := hD.preimage continuous_packedPhysicalPoint
  have hc {f : KineticPoint d → ℝ} (hf : ContinuousOn f D) :
      ContinuousOn (f ∘ packedPhysicalPoint) U :=
    hf.comp continuous_packedPhysicalPoint.continuousOn (fun _ hx => hx)
  have hV (i : Fin d) : ContinuousOn
      (fun x => kineticVelocityGradient u (packedPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hu.continuousOn_kineticVelocityGradient)
  have hZ (i : Fin d) : ContinuousOn
      (fun x => kineticPositionGradient u (packedPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hu.continuousOn_kineticPositionGradient)
  have hH (i j : Fin d) : ContinuousOn
      (fun x => kineticVelocityHessian u (packedPhysicalPoint x) j i) U :=
    hc ((continuous_apply i).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hu.continuousOn_kineticVelocityHessian))
  refine ⟨(hc hu.continuousOn).locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hcompact hs
  have hi := integral_transportedAdjoint_of_anisotropic_jets
    B (identityDrift d) hB
    (identityDrift_smooth d) (u ∘ packedPhysicalPoint)
    (kineticTimeDerivative u ∘ packedPhysicalPoint)
    (fun i x => kineticVelocityGradient u (packedPhysicalPoint x) i)
    (fun i x => kineticPositionGradient u (packedPhysicalPoint x) i)
    (fun i j x => kineticVelocityHessian u (packedPhysicalPoint x) j i)
    (hc hu.continuousOn) (hc hu.continuousOn_kineticTimeDerivative) hV hZ hH
    (fun _ hx => packed_time_hasLineDerivAt hu hx)
    (fun i _ hx => packed_velocity_hasLineDerivAt hu hx i)
    (fun i _ hx => packed_position_hasLineDerivAt hu hx i)
    (fun i j _ hx => packed_hessian_hasLineDerivAt hu hx i j) ψ hψ hcompact hs
  refine hi.trans (setIntegral_congr_fun hU.measurableSet ?_)
  intro x hx
  have hsum : (∑ i, ∑ j,
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j *
        kineticVelocityHessian u (packedPhysicalPoint x) j i) =
      matrixContraction (B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x))
        (kineticVelocityHessian u (packedPhysicalPoint x)) := by
    rw [matrixContraction, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(hBs (timeCoord d x) (diffusedCoord d x) (transportedCoord d x)).apply i j]
  simp only [identityDrift, Function.comp_apply, id_eq]
  rw [hsum]
  simp only [forwardKineticOperator_apply, packedPhysicalPoint]
  simp only [PDE.vecDot]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
