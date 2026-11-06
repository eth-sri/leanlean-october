module

public import PottsDiscontinuity.Torus.DiamondSeamWinding
public import PottsDiscontinuity.TorusLoops.LoopClusterProjection
public import PottsDiscontinuity.TorusLoops.DualTranslation
public import PottsDiscontinuity.TorusRC.CylinderEvents

/-! The zigzag seam bound, via the homotopic primal and dual ribbon shadows.
The boundary chain's signed intersection with the seam equals the medial loop's
vertical winding. A single open seam edge has only two incident boundary ends. -/

public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}
noncomputable section

/-- The primal ribbon shadow and its medial loop have the same vertical
intersection with the horizontal seam. This is the zigzag cocycle comparison. -/
theorem loopBoundaryCycle_windingY (hN : Even N) (hM : Even M) (hMp : 0 < M)
    (j : Fin M) (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    diamondWindingY A (loopBoundaryCycle hN hM A q).val =
      (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q : ℚ) := by
  apply mul_left_cancel₀ (show (M : ℚ) ≠ 0 by positivity)
  rw [diamondWindingY_mul_period, loopBoundaryCycle_displacement_y,
    loop_vertical_displacement _ _ _ j q]
  simp

section
variable (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
theorem loopVertical_translatedDual (q : Loop hN hM (rcSmoothing A)) :
    loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing (translatedDual A))) j
      (translatedDualLoopEquiv hN hM A q) =
      -loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q := by
  unfold loopVertical
  rw [loopSum_translatedDual]
  have he : (fun d : Dart N M => verticalCross j (dartColumnShift (edgeReverse d))) =
      fun d => -verticalCross j d := by
    funext d
    have hx : verticalCross j (dartColumnShift (edgeReverse d)) =
        verticalCross j (edgeReverse d) := by
      rcases edgeReverse d with ⟨v,p⟩
      cases p <;> rfl
    rw [hx, verticalCross_edgeReverse]
  rw [he]
  simp [loopSum]

/-- Complement and column translation preserve the absolute vertical mass. -/
theorem verticalMass_translatedDual  :
    verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing (translatedDual A))) j =
      verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j := by
  unfold verticalMass
  rw [← (translatedDualLoopEquiv hN hM A).sum_comp]
  simp [loopVertical_translatedDual]
end

section
variable (hN : Even N) (hM : Even M) (hMp : 0 < M) (j : Fin M) (A : RCConfig N M) (i₀ : Fin N) (hi₀ : A (i₀,⟨0,hMp⟩) = true) (honly : ∀ i : Fin N, i ≠ i₀ → A (i,⟨0,hMp⟩) = false)
include hMp i₀ hi₀ honly
/-- If exactly one primal seam edge is open, every loop's vertical winding is
the difference of the two incidence indicators at that edge. -/
theorem loop_winding_of_single_open_seam (q : Loop hN hM (rcSmoothing A)) :
    (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q : ℚ) =
      - (loopBoundaryCycle hN hM A q).val ⟨(i₀,⟨0,hMp⟩),hi₀⟩ := by
  rw [← loopBoundaryCycle_windingY hN hM hMp]
  unfold diamondWindingY
  rw [Finset.sum_eq_single (⟨(i₀,⟨0,hMp⟩),hi₀⟩ : OpenDiamondEdge A)]
  · simp [diamondSeamCrossY]
  · grind [diamondSeamCrossY]
  · simp

/-- One open primal seam edge permits at most two units of absolute vertical
loop winding. Geometric fixed-row crossings are not being counted here. -/
theorem verticalMass_le_two_of_single_open_seam  :
    verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j ≤ 2 := by
  classical
  let q₁ := directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
    (ribbonEndEquiv hN hM ((i₀,⟨0,hMp⟩),true))
  let q₀ := directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
    (ribbonEndEquiv hN hM ((i₀,⟨0,hMp⟩),false))
  have hb (q : Loop hN hM (rcSmoothing A)) :
      ((loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).natAbs : ℚ) ≤
        (if q₁ = q then 1 else 0) + (if q₀ = q then 1 else 0) := by
    rw [Nat.cast_natAbs, Int.cast_abs,
      loop_winding_of_single_open_seam hN hM hMp j A i₀ hi₀ honly q]
    change abs (- ((if q₁ = q then (1 : ℚ) else 0) - (if q₀ = q then 1 else 0))) ≤ _
    grind
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ (univ : Finset (Loop hN hM (rcSmoothing A)))) => hb q)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hs
  exact_mod_cast hs
end

/-- If all but exactly one primal seam edge are open, then U ≤ 1. This is the upper
bound in the implication B ∩ C′ ⇒ U = 1 (`barrier_and_CPrime_imply_U_eq_one`).
The proof counts intersections through the dual shadow of each loop. -/
theorem rcVerticalWinding_le_one_of_seamAllButOneOpen
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (j : Fin M) (A : RCConfig N M)
    (hA : TorusRC.torusRCSeamAllButOneOpen hMp A) :
    rcVerticalWinding hN hM j A ≤ 1 := by
  obtain ⟨i₀,hi₀,hother⟩ := hA
  have hdual : translatedDual A (nxt i₀,⟨0,hMp⟩) = true := by
    simp only [translatedDual, prv, nxt, Equiv.symm_apply_apply, hi₀, Bool.not_false]
  have hdualo : ∀ i : Fin N, i ≠ nxt i₀ →
      translatedDual A (i,⟨0,hMp⟩) = false := by
    intro i hi
    have hip : prv i ≠ i₀ := by
      grind
    change Bool.not (A (prv i,⟨0,hMp⟩)) = false
    simp_all
  have hb := verticalMass_le_two_of_single_open_seam hN hM hMp j
    (translatedDual A) (nxt i₀) hdual hdualo
  rw [verticalMass_translatedDual hN hM j A] at hb
  have he := two_mul_verticalWindingCount hN (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j
  change verticalWindingCount _ _ _ j ≤ 1
  omega

end
end PottsDiscontinuity.TorusTopology
