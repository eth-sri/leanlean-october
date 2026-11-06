module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolution
public import PDEFoundation.Calculus.RegularityOrder


/-! # Closure geometry and slice regularity for the boundary functional -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set TheoremA


variable {d : ℕ}

/-- The closure of the nonempty open physical strip is the prescribed closed strip. -/
theorem closure_localStrip  {a T : ℝ} (haT : a < T) (v₀ : PDE.Vec d) (R : ℝ) :
    closure (localStrip a T v₀ R) = localClosedStrip a T v₀ R := by
  let H := KineticPoint.homeomorphProd d
  have heq : localStrip a T v₀ R = H ⁻¹'
      (Ioo a T ×ˢ (univ ×ˢ PDE.euclideanBall v₀ R)) := by
    ext P
    simp only [localStrip, H, mem_preimage, mem_prod, mem_Ioo, mem_univ, true_and]
    change (a < P.time ∧ P.time < T ∧ P.velocity ∈ PDE.euclideanBall v₀ R) ↔
      (a < P.time ∧ P.time < T) ∧ P.velocity ∈ PDE.euclideanBall v₀ R
    tauto
  rw [heq, ← H.preimage_closure, closure_prod_eq, closure_prod_eq,
    closure_Ioo haT.ne, closure_univ]
  ext P
  simp only [localClosedStrip, H, mem_preimage, mem_prod, mem_Icc, mem_univ, true_and]
  change ((a ≤ P.time ∧ P.time ≤ T) ∧
    P.velocity ∈ closure (PDE.euclideanBall v₀ R)) ↔
    (a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R))
  tauto

/-- Physical joint smoothness supplies the swapped slice regularity for comparison. -/
theorem boundary_swapped_slice_regular  {D : Set (KineticPoint d)}
    (hD : IsOpen D) {u : HypoellipticAleksandrov.KineticScalarField d}
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D)) (Q : KineticPoint d) (hQ : sectionTwoPoint Q ∈ D) :
    IsSliceRegularAt (u ∘ sectionTwoPoint) Q := by



  have hs := (hu.contDiffAt (((KineticPoint.homeomorphProd d).isOpenMap D hD).mem_nhds (mem_image_of_mem _ hQ))).of_le
    (by simp : (2 : WithTop ℕ∞) ≤ PDE.smoothOrder)

  change ContDiffAt ℝ 2 (u ∘ (KineticPoint.equivProd d).symm)
    (Q.time, Q.velocity, Q.position) at hs
  have h := hs.comp
    (Q.time, Q.position, Q.velocity) (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)).contDiffAt
  apply IsSliceRegularAt.of_contDiffAt
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
