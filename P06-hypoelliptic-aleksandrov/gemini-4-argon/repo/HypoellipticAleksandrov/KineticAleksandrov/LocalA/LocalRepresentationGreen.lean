module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationBounds
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportTransition

/-! # The local position cutoff defect has zero actual Green integral -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic SectionTwo TheoremA
open scoped Topology

/- A cutoff constant on a position ball has zero transport defect inside that ball. -/
theorem localCutoffTransport_zero_of_one {d } (Z₀ P : KineticPoint d)
    (χ : PDE.Vec d → ℝ) {r }
    (hχ : ∀ x ∈ PDE.euclideanClosedBall 0 r, χ x = 1)
    (hx : relativePosition Z₀ P ∈ PDE.euclideanBall 0 r) :
    localCutoffTransport Z₀ χ P = 0 := by
  have he : χ =ᶠ[𝓝 (relativePosition Z₀ P)] (fun _ => (1 : ℝ)) := by
    filter_upwards [(PDE.isOpen_euclideanBall 0 r).mem_nhds hx] with x hx'
    exact hχ x (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx')
  rw [localCutoffTransport, he.fderiv_eq, fderiv_const_apply, zero_apply]

/- The exact cutoff interior ball contains the reached cone, with a strict margin. -/
theorem local_cone_cutoff_mem {d } (Z₀ P Q : KineticPoint d)
    {R } (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (htlo : P.time ≤ Q.time) (hthi : Q.time ≤ P.time + R ^ 2 / 8)
    (hcone : PDE.vecEuclideanNorm
      (Q.position - P.position - (Q.time - P.time) • Z₀.velocity) ≤
        R * (Q.time - P.time)) :
    relativePosition Z₀ Q ∈ PDE.euclideanBall 0 ((3 / 4 : ℝ) * R ^ 3) := by
  have hmargin := (local_cone_margins Z₀ P Q hR hP htlo hthi hcone).2.2
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
  simp only [sub_zero]
  nlinarith only [hmargin, pow_pos hR 3]

/- The actual killed Green potential vanishes for the cutoff defect outside its cone. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
