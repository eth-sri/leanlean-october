module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity



/-! # Compact geometry for fixed-function coefficient errors -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory

variable {d : ℕ}

/-- A fixed backward kinetic cylinder is contained in an explicit compact set. -/
theorem backwardCylinder_subset_compact  (P₀ : KineticPoint d) (R : ℝ)
    (hR : 0 < R) : ∃ K : Set (KineticPoint d), IsCompact K ∧ backwardCylinder P₀ R ⊆ K := by
  let D := Icc (P₀.time - R ^ 2) P₀.time ×ˢ
    (PDE.euclideanClosedBall (0 : PDE.Vec d) (R ^ 3) ×ˢ
      PDE.euclideanClosedBall P₀.velocity R)
  let f : ℝ × (PDE.Vec d × PDE.Vec d) → KineticPoint d := fun z =>
    ⟨z.1, P₀.position + z.2.1 + (z.1 - P₀.time) • P₀.velocity, z.2.2⟩
  have hD : IsCompact D := isCompact_Icc.prod
    ((PDE.isCompact_euclideanClosedBall 0 (pow_pos hR 3).le).prod
      (PDE.isCompact_euclideanClosedBall P₀.velocity hR.le))
  have hf : Continuous f := KineticPoint.continuous_mk continuous_fst
    ((continuous_const.add continuous_snd.fst).add
      ((continuous_fst.sub continuous_const).smul continuous_const)) continuous_snd.snd
  refine ⟨f '' D, hD.image hf, ?_⟩
  intro P hP
  refine ⟨(P.time, relativePosition P₀ P, P.velocity), ?_, ?_⟩
  · exact ⟨⟨hP.1.le, hP.2.1.le⟩,
      PDE.euclideanBall_subset_euclideanClosedBall 0 (R ^ 3) hP.2.2.2,
      PDE.euclideanBall_subset_euclideanClosedBall P₀.velocity R hP.2.2.1⟩
  · apply KineticPoint.ext <;> dsimp only [f, relativePosition]; abel



/-- The cylinder restriction is a finite measure; no closure or Euclidean normalization changes. -/
theorem backwardCylinder_volume_lt_top  (P₀ : KineticPoint d) (R : ℝ)
    (hR : 0 < R) : volume (backwardCylinder P₀ R) < ⊤ := (Holder.volume_backwardCylinder_lt_top P₀ hR)


end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
