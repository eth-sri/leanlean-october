module

public import PottsDiscontinuity.Torus.LoopReorientation
public import PottsDiscontinuity.Torus.LoopTurning
public import PottsDiscontinuity.Torus.LoopHomology

/-! # Discrete loop turning under reversal of orientation -/

public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The turn at the other port of the same smoothed strand has opposite sign. -/
theorem strandTurn_pairedPort (s : Bool) (p : Port) :
    strandTurn s (pairedPort s p) = -strandTurn s p := by
  cases s <;> cases p <;> rfl

/-- Reversing an edge and then taking the next smoothed step reverses the local turn. -/
theorem strandTurn_edgeReverse_eq_neg_step (s : Smoothing N M) (d : Dart N M) :
    strandTurn (s (edgeReverse d).1) (edgeReverse d).2 =
      -strandTurn (s (stepPerm s d).1) (stepPerm s d).2 := by
  rw [stepPerm_apply, strandReverse]
  grind [strandTurn, edgeReverse, pairedPort, strandTurn_pairedPort]

section
variable (ω : ArrowConfig N M)
/-- Reindexing by one orbit step shows that the turn sum on the reversed loop is negative. -/
theorem loopSum_edgeReverse_turn (s : Smoothing N M)
    (h : CompatibleConfig ω s) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => strandTurn (s (edgeReverse d).1) (edgeReverse d).2) q =
      -loopTurn ω s h q := by
  have hsum :
      loopSum ω s h (fun d => strandTurn (s (edgeReverse d).1) (edgeReverse d).2) q =
        -loopSum ω s h (fun d => strandTurn (s (stepPerm s d).1) (stepPerm s d).2) q := by
    unfold loopSum
    rw [← Finset.sum_neg_distrib]
    grind [directedLoopOf, strandTurn_edgeReverse_eq_neg_step]
  calc
    _ = -loopSum ω s h (fun d => strandTurn (s (stepPerm s d).1)
        (stepPerm s d).2) q := hsum
    _ = -loopSum ω s h (fun d => strandTurn (s d.1) d.2) q := by
      congr 1
      exact loopSum_step ω s h (fun d => strandTurn (s d.1) d.2) q

theorem arrowDart_eq_dart_if_direction (d : Dart N M) :
    arrowDart ω (dartEdge d) = if dartOut ω d then d else edgeReverse d := by
  by_cases hd : dartOut ω d = true
  · simpa [hd] using arrowDart_dartEdge ω ⟨d, hd⟩
  · have hr : dartOut ω (edgeReverse d) = true := by
      simp_all
    have h := arrowDart_dartEdge ω ⟨edgeReverse d, hr⟩
    simp_all
end

/-- A compatible arrow orientation preserves a loop turn, while reversing that loop negates it. -/
theorem loopTurn_reorient (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M)
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s)
    (q : DirectedLoop ω₀ s h₀) :
    loopTurn ω₁ s h₁ (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ ω₁ h₁ q then loopTurn ω₀ s h₀ q
      else -loopTurn ω₀ s h₀ q := by
  unfold loopTurn
  rw [loopSum_reorient_edges]
  let b := loopOrientation ω₀ s h₀ ω₁ h₁ q
  have hpoint (d : DirectedDart ω₀)
      (hd : directedLoopOf ω₀ s h₀ d = q) :
      strandTurn (s (arrowDart ω₁ (dartEdge d.val)).1)
          (arrowDart ω₁ (dartEdge d.val)).2 =
        if b then strandTurn (s d.val.1) d.val.2
        else strandTurn (s (edgeReverse d.val).1) (edgeReverse d.val).2 := by
    have horient : dartOut ω₁ d.val = b := by
      aesop
    rw [arrowDart_eq_dart_if_direction ω₁ d.val, horient]
    grind
  have hsum :
      loopSum ω₀ s h₀
          (fun d => strandTurn (s (arrowDart ω₁ (dartEdge d)).1)
            (arrowDart ω₁ (dartEdge d)).2) q =
        loopSum ω₀ s h₀
          (fun d => if b then strandTurn (s d.1) d.2
            else strandTurn (s (edgeReverse d).1) (edgeReverse d).2) q := by
    apply Finset.sum_congr rfl
    grind
  rw [hsum]
  by_cases hb : b
  · grind
  · simp [hb, b, loopTurn, loopSum_edgeReverse_turn]

end PottsDiscontinuity.Torus
