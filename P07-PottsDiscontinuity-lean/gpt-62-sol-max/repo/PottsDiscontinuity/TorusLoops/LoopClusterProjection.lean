module

public import PottsDiscontinuity.Torus.DiamondClusterProjection
public import PottsDiscontinuity.TorusLoops.HorizontalHomology

/-!
# Projection of a medial boundary loop to its incident primal cluster

The lifted medial displacement equals the displacement of the open-ribbon
traversals, up to an explicit corner coboundary. This supplies a combinatorial
bridge from the fixed winding statistic to actual open clusters.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

/-- The actual primal cluster incident to a canonically oriented loop. -/
def loopPrimalCluster :
    Loop hN hM (rcSmoothing A) →
      (diamondOpenGraph hN hM true A).ConnectedComponent :=
  Quotient.lift (fun d =>
    (diamondOpenGraph hN hM true A).connectedComponentMk (ribbonFace hN hM d))
    (fun _ _ h => SimpleGraph.ConnectedComponent.sound
      (ribbonConnected_reachable hN hM A
        (ribbonConnected_of_boundary_sameCycle hN hM A (by
          rwa [ribbonBoundary_eq_directedStep]))))

@[simp] theorem loopPrimalCluster_loopOf (d : DirectedDart (checkerArrows N M)) :
    loopPrimalCluster hN hM A (directedLoopOf _ _
        (checkerArrows_compatible hN hM (rcSmoothing A)) d) =
      (diamondOpenGraph hN hM true A).connectedComponentMk (ribbonFace hN hM d) := rfl

end

/-- Displacement along the selected axis (`true` for vertical). -/
def axisIncrement (vertical : Bool) : Dart N M → ℤ :=
  if vertical then verticalIncrement else horizontalIncrement

private def primalCornerOffset (vertical : Bool) (d : Dart N M) : ℤ :=
  if d.2 = .west ∨ d.2 = (if vertical then .south else .north) then -1 else 0

/-- Increment of an indexed primal edge oriented from its false end to its true end. -/
def ribbonWeight (vertical : Bool) (v : Fin N × Fin M) : ℤ :=
  if vertical || checker v then -1 else 1

private def arrivingRibbon (vertical : Bool) (A : RCConfig N M) (d : Dart N M) : ℤ :=
  if A d.1 then (if ribbonEndSide d.2 then 1 else -1) * ribbonWeight vertical d.1 else 0

private theorem increment_ribbon (hN : Even N) (hM : Even M)
    (vertical : Bool) (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    axisIncrement vertical d.val =
      arrivingRibbon vertical A (stepPerm (rcSmoothing A) d.val) + primalCornerOffset vertical d.val -
        primalCornerOffset vertical (stepPerm (rcSmoothing A) d.val) := by
  rcases d with ⟨⟨⟨i, j⟩, p⟩, hd⟩
  rw [dartOut_checker_at hN hM] at hd
  have hx₁ := checker_prv_x hN i j
  have hx₂ := checker_nxt_x hN i j
  have hy₁ := checker_prv_y hM i j
  have hy₂ := checker_nxt_y hM i j
  cases ha : A (edgeReverse ((i, j), p)).1 <;> cases p <;>
    cases hc : checker (i, j) <;> cases vertical <;>
    simp_all [axisIncrement, horizontalIncrement, verticalIncrement, arrivingRibbon,
      primalCornerOffset, ribbonWeight, stepPerm_apply, strandReverse, rcSmoothing,
      edgeReverse, ribbonEndSide, pairedPort]

private theorem loopSum_add (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f g : Dart N M → ℤ) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => f d + g d) q =
      loopSum ω s h f q + loopSum ω s h g q := by
  classical
  unfold loopSum
  rw [Finset.sum_add_distrib]

private theorem loop_arrivingRibbon (hN : Even N) (hM : Even M) (vertical : Bool)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (axisIncrement vertical) q =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (arrivingRibbon vertical A) q := by
  let s := stepPerm (rcSmoothing A)
  let R := arrivingRibbon vertical A
  let C : Dart N M → ℤ := primalCornerOffset vertical
  have he : loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (axisIncrement vertical) q =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (fun d => R (s d) + C d - C (s d)) q := by
    classical
    unfold loopSum
    exact Finset.sum_congr rfl (fun d _ => increment_ribbon hN hM vertical A d)
  dsimp only [s] at he
  rw [he, loopSum_sub, loopSum_add, loopSum_step, loopSum_step]
  change _ + _ - _ = loopSum _ _ _ R q
  omega

/-- Characteristic function of a specified medial loop on the ribbon boundaries. -/
noncomputable def loopBoundaryFunction (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    RibbonBoundaryComponent hN hM A → ℚ := by
  classical
  refine Quotient.lift (fun d => if directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) d = q then 1 else 0) ?_
  intro d e h
  grind only [directedLoopOf, Quotient.sound, ribbonBoundary_eq_directedStep]

open scoped Classical in
@[simp] theorem loopBoundaryFunction_corner (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A))
    (d : DirectedDart (checkerArrows N M)) :
    loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d) =
      if directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) d = q
      then 1 else 0 := rfl

/-- A loop's boundary chain, supported on the actual open indexed edges. -/
noncomputable def loopBoundaryCycle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    diamondCycleSpace hN hM A :=
  ⟨ribbonFaceBoundary hN hM A (loopBoundaryFunction hN hM A q),
    ribbonFaceBoundary_mem_cycleSpace hN hM A _⟩

@[simp] private theorem arrivingRibbon_end (vertical : Bool) (A : RCConfig N M)
    (v : Fin N × Fin M) (b : Bool) :
    arrivingRibbon vertical A (ribbonEnd v b) =
      if A v then (if b then 1 else -1) * ribbonWeight vertical v else 0 := by
  cases hc : checker v <;> cases b <;> simp [arrivingRibbon, ribbonEnd, ribbonEndSide, hc]

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

private theorem sum_arrivingRibbon (vertical : Bool)
    (f : DirectedDart (checkerArrows N M) → ℚ) :
    (∑ e : OpenDiamondEdge A, (ribbonWeight vertical e.val : ℚ) *
      (f (ribbonEndEquiv hN hM (e.val, true)) - f (ribbonEndEquiv hN hM (e.val, false)))) =
      ∑ d : DirectedDart (checkerArrows N M), f d * (arrivingRibbon vertical A d.val : ℚ) := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun v => A v = true) (by intro v; simp)
    (fun v => (ribbonWeight vertical v : ℚ) *
      (f (ribbonEndEquiv hN hM (v, true)) - f (ribbonEndEquiv hN hM (v, false)))),
    Finset.sum_filter, ← (ribbonEndEquiv hN hM).sum_comp]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v <;> simp [ha] <;> ring

private theorem sum_loopBoundaryFunction (q : Loop hN hM (rcSmoothing A)) (g : Dart N M → ℤ) :
    (∑ d : DirectedDart (checkerArrows N M),
      loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d) * (g d.val : ℚ)) =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) g q : ℚ) := by
  classical
  unfold loopSum
  rw [Int.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  simp

/-- The projected primal chain has the same displacement as the medial loop. -/
theorem loopBoundaryCycle_displacement (vertical : Bool) (q : Loop hN hM (rcSmoothing A)) :
    (∑ e : OpenDiamondEdge A, (ribbonWeight vertical e.val : ℚ) *
      (loopBoundaryCycle hN hM A q).val e) =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (axisIncrement vertical) q : ℚ) := by
  rw [loop_arrivingRibbon hN hM vertical A]
  exact (sum_arrivingRibbon hN hM A vertical
    (fun d => loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d))).trans
      (sum_loopBoundaryFunction hN hM A q (arrivingRibbon vertical A))

theorem loopBoundaryCycle_displacement_x (q : Loop hN hM (rcSmoothing A)) :
    diamondHorizontalDisplacement A (loopBoundaryCycle hN hM A q).val =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) horizontalIncrement q : ℚ) := by
  simpa [diamondHorizontalDisplacement, axisIncrement, ribbonWeight] using
      loopBoundaryCycle_displacement hN hM A false q

theorem loopBoundaryCycle_displacement_y (q : Loop hN hM (rcSmoothing A)) :
    diamondVerticalDisplacement A (loopBoundaryCycle hN hM A q).val =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) verticalIncrement q : ℚ) := by
  simpa [diamondVerticalDisplacement, axisIncrement, ribbonWeight] using
      loopBoundaryCycle_displacement hN hM A true q

theorem loopPrimalCluster_end
    (e : OpenDiamondEdge A) (b : Bool) :
    loopPrimalCluster hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (e.val, b))) = diamondEdgeCluster hN hM A e :=
  ribbonCornerCluster_end hN hM A e b

/-- A medial boundary loop projects entirely into its incident actual primal cluster. -/
theorem loopBoundaryCycle_supported (q : Loop hN hM (rcSmoothing A)) :
    SupportedOnDiamondCluster hN hM A (loopPrimalCluster hN hM A q)
      (loopBoundaryCycle hN hM A q) := by
  classical
  intro e he
  have hn (b : Bool) : directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (e.val, b)) ≠ q := by
    intro hq
    apply he
    rw [← loopPrimalCluster_end hN hM A e b, hq]
  change loopBoundaryFunction hN hM A q
      (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, true))) -
    loopBoundaryFunction hN hM A q
      (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, false))) = 0
  simp_all

end

end PottsDiscontinuity.TorusLoops
