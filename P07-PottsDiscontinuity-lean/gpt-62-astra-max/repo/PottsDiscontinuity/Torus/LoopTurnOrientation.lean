module

public import PottsDiscontinuity.Torus.LoopReorientation
public import PottsDiscontinuity.Torus.LoopTurning
public import PottsDiscontinuity.Torus.LoopHomology

/-! # Discrete loop turning under reversal of orientation -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The turn at the other port of the same smoothed strand has opposite sign. -/
theorem strandTurn_pairedPort (s : Bool) (p : Port) :
    strandTurn s (pairedPort s p) = -strandTurn s p := by
  cases s <;> cases p <;> rfl

variable (ω : ArrowConfig N M) (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M) (d : Dart N M)

/-- Reversing an edge and then taking the next smoothed step reverses the local turn. -/
theorem strandTurn_edgeReverse_eq_neg_step :
    strandTurn (s (edgeReverse d).1) (edgeReverse d).2 =
      -strandTurn (s (stepPerm s d).1) (stepPerm s d).2 := by
  simp [stepPerm_apply, strandReverse, strandTurn_pairedPort]

/-- Reindexing by one orbit step shows that the turn sum on the reversed loop is negative. -/
theorem loopSum_edgeReverse_turn
    (h : CompatibleConfig ω s) (q : DirectedLoop h) :
    loopSum (fun d => strandTurn (s (edgeReverse d).1) (edgeReverse d).2) q =
      -loopTurn q := by
  classical
  have hsum :
      loopSum (fun d => strandTurn (s (edgeReverse d).1) (edgeReverse d).2) q =
        -loopSum (fun d => strandTurn (s (stepPerm s d).1) (stepPerm s d).2) q := by
    unfold loopSum
    simp only [Finset.sum_filter]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hq : directedLoopOf h d = q
    · simp [hq, strandTurn_edgeReverse_eq_neg_step]
    · grind
  calc
    _ = -loopSum (fun d => strandTurn (s (stepPerm s d).1)
        (stepPerm s d).2) q := hsum
    _ = -loopSum (fun d => strandTurn (s d.1) d.2) q := by
      congr 1
      exact loopSum_step (fun d => strandTurn (s d.1) d.2) q

private theorem arrowDart_eq_dart_if_direction :
    arrowDart ω (dartEdge d) = if dartOut ω d then d else edgeReverse d := by
  by_cases hd : dartOut ω d = true
  · simpa [hd] using arrowDart_dartEdge ⟨d, hd⟩
  · have hdF := Bool.eq_false_iff.mpr hd
    have hr : dartOut ω (edgeReverse d) = true := by
      simp [dartOut_edgeReverse, hdF]
    have h := arrowDart_dartEdge ⟨edgeReverse d, hr⟩
    simpa [hdF] using h

/-- A compatible arrow orientation preserves a loop turn, while reversing that loop negates it. -/
theorem loopTurn_reorient
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s)
    (q : DirectedLoop h₀) :
    loopTurn (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ h₁ q then loopTurn q
      else -loopTurn q := by
  classical
  unfold loopTurn
  rw [loopSum_reorient_edges]
  let b := loopOrientation ω₀ s h₀ h₁ q
  have hpoint (d : DirectedDart ω₀)
      (hd : directedLoopOf h₀ d = q) :
      strandTurn (s (arrowDart ω₁ (dartEdge d.val)).1)
          (arrowDart ω₁ (dartEdge d.val)).2 =
        if b then strandTurn (s d.val.1) d.val.2
        else strandTurn (s (edgeReverse d.val).1) (edgeReverse d.val).2 := by
    have horient : dartOut ω₁ d.val = b := by
      rw [← loopOrientation_apply ω₀ s h₀ ω₁ h₁ d, hd]
    rw [arrowDart_eq_dart_if_direction ω₁ d.val, horient]
    grind
  have hsum :
      loopSum
          (fun d => strandTurn (s (arrowDart ω₁ (dartEdge d)).1)
            (arrowDart ω₁ (dartEdge d)).2) q =
        loopSum
          (fun d => if b then strandTurn (s d.1) d.2
            else strandTurn (s (edgeReverse d).1) (edgeReverse d).2) q := by
    apply Finset.sum_congr rfl
    grind
  rw [hsum]
  by_cases hb : b
  · grind
  · simp [hb, b, loopTurn, loopSum_edgeReverse_turn]

end PottsDiscontinuity.Torus
