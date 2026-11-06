module
public import Mathlib

public import PottsDiscontinuity.Torus.DiamondSeamWinding
public import PottsDiscontinuity.TorusLoops.WindingClusterCount

/-!
# Rectangle cuts and crossings from conserved winding

Removing the indexed edge rows and columns at the coordinate seams produces the
finite rectangle graph. A conserved chain whose transverse-seam coefficients
vanish cannot have nonzero longitudinal winding unless its open cluster contains
a left-to-right crossing component.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The primal graph after deleting both coordinate seam edge sets. -/
def rectangleOpenGraph (hN : Even N) (hM : Even M) (A : RCConfig N M)  :=
  SimpleGraph.fromEdgeSet {p | ∃ v, A v = true ∧ v.1.val ≠ 0 ∧ v.2.val ≠ 0 ∧
    p = Sym2.mk (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)}

section

variable (hN : Even N)
include hN

private theorem prv_ne_self_of_even_pos  (hNp : 0 < N) (i : Fin N) :
    prv i ≠ i := by
  intro h
  
  
  by_cases hz : i.val = 0
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNp.ne'
    simp_all
  · have hi := prv_val_of_pos i (Nat.pos_of_ne_zero hz)
    omega

section

variable (hM : Even M)


private theorem endpoint_x_ne   (hNp : 0 < N)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.1 ≠
      (faceEndpoint hN hM true v true).val.1 := by
  have hfalse : (faceEndpoint hN hM true v false).val.1 =
      if checker v then v.1 else prv v.1 := by
    grind [faceEndpoint, faceEndpointRaw]
  have htrue : (faceEndpoint hN hM true v true).val.1 =
      if checker v then prv v.1 else v.1 := by
    grind [faceEndpoint, faceEndpointRaw]
  rw [hfalse, htrue]
  cases hc : checker v
  · exact prv_ne_self_of_even_pos hN hNp v.1
  · exact (prv_ne_self_of_even_pos hN hNp v.1).symm

private theorem endpoint_x_false  
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.1 =
      if checker v then v.1 else prv v.1 := by
  grind [faceEndpoint, faceEndpointRaw]

private theorem endpoint_x_true  
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.1 =
      if checker v then prv v.1 else v.1 := by
  grind [faceEndpoint, faceEndpointRaw]

section

variable (hNp : 0 < N)
include hNp

private theorem endpoint_x_seam   
    (v : Fin N × Fin M) (hv : v.1.val = 0) :
    if checker v then
      (faceEndpoint hN hM true v false).val.1.val = 0 ∧
        (faceEndpoint hN hM true v true).val.1.val + 1 = N
    else
      (faceEndpoint hN hM true v false).val.1.val + 1 = N ∧
        (faceEndpoint hN hM true v true).val.1.val = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNp.ne'
  have hv' : v.1 = 0 := by
                          simp_all
  
  rw [endpoint_x_false, endpoint_x_true, hv']
  cases checker v <;> simp

section

variable (A : RCConfig N M) (e : OpenDiamondEdge A) (hx : e.val.1.val ≠ 0) (hy : e.val.2.val ≠ 0)
include A e hx hy

theorem rectangleOpenGraph_edge_adj   
     :
    (rectangleOpenGraph hN hM A).Adj (faceEndpoint hN hM true e.val false)
      (faceEndpoint hN hM true e.val true) := by
  
  refine ⟨?_, ?_⟩
  · aesop
  · intro he
    exact endpoint_x_ne hN hM hNp e.val
      (congrArg (fun u  => u.val.1) he)

theorem rectangleOpenGraph_reachable_edge  
      :
    (rectangleOpenGraph hN hM A).Reachable (faceEndpoint hN hM true e.val false)
      (faceEndpoint hN hM true e.val true) :=
  by
    solve_by_elim [_root_.SimpleGraph.Adj.reachable, _root_.PottsDiscontinuity.TorusLoops.rectangleOpenGraph_edge_adj]

end

end

end

end

/-- A cut component reaches the right side when it contains a right-boundary vertex. -/
def rectangleReachesRight (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (u : FaceVertex N M true) : Prop :=
  ∃ v, v.val.1.val + 1 = N ∧ (rectangleOpenGraph hN hM A).Reachable u v

private theorem rectangleReachesRight_congr (hN : Even N) (hM : Even M)
    (A : RCConfig N M) {u v : FaceVertex N M true}
    (h : (rectangleOpenGraph hN hM A).Reachable u v) :
    rectangleReachesRight hN hM A u ↔ rectangleReachesRight hN hM A v := by
  constructor
  · rintro ⟨w, hw, huw⟩
    exact ⟨w, hw, h.symm.trans huw⟩
  · rintro ⟨w, hw, hvw⟩
    exact ⟨w, hw, h.trans hvw⟩

/-- An original primal cluster contains a left-to-right component of the cut rectangle. -/
def hasRectangleCrossingX (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)  :=
  ∃ u v : FaceVertex N M true, u.val.1.val = 0 ∧ v.val.1.val + 1 = N ∧
    (diamondOpenGraph hN hM true A).connectedComponentMk u = c ∧
      (rectangleOpenGraph hN hM A).Reachable u v

noncomputable def rectanglePotential (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (u : FaceVertex N M true) : ℚ :=
  by
    classical
    exact if rectangleReachesRight hN hM A u then -1 else 0

section

variable (hN : Even N) (hM : Even M)
include hN hM

private theorem rectanglePotential_eq_zero_of_left 
    (A : RCConfig N M) (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (hnc : ¬ hasRectangleCrossingX hN hM A c) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0)
    (hcu : (diamondOpenGraph hN hM true A).connectedComponentMk u = c) :
    rectanglePotential hN hM A u = 0 := by
  grind +locals

private theorem rectanglePotential_eq_neg_one_of_right 
    (A : RCConfig N M) (u : FaceVertex N M true) (hu : u.val.1.val + 1 = N) :
    rectanglePotential hN hM A u = -1 := by
  
  unfold rectanglePotential
  have hr : rectangleReachesRight hN hM A u :=
    ⟨u, hu, SimpleGraph.Reachable.refl _⟩
  simp [hr]

/-- A supported conserved flow with nonzero horizontal displacement forces a
left-to-right crossing in its actual primal cluster, provided the chain uses no
edges on the transverse seam. -/
theorem supportedCycle_nonzero_horizontal_hasRectangleCrossingX
     (hNp : 0 < N) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (f : diamondCycleSpace hN hM A)
    (hsupport : SupportedOnDiamondCluster hN hM A c f)
    (hclean : ∀ e : OpenDiamondEdge A, e.val.2.val = 0 → f.val e = 0)
    (hdisp : diamondHorizontalDisplacement A f.val ≠ 0) :
    hasRectangleCrossingX hN hM A c := by
  
  by_contra hnc
  let g  := rectanglePotential hN hM A
  have hpair := diamondBoundary_pairing hN hM A g f.val
  rw [f.property] at hpair
  
  have hsum :  ∑ e, diamondCoboundary hN hM A g e * f.val e  =
      diamondWindingX A f.val := by
    
    apply Finset.sum_congr rfl
    intro e _
    by_cases hy : e.val.2.val = 0
    · 
      simp [ hclean e hy ]
    · by_cases hf : f.val e = 0
      · simp [hf]
      · have hcluster : diamondEdgeCluster hN hM A e = c := by
          by_contra hc
          exact hf (hsupport e hc)
        by_cases hx : e.val.1.val = 0
        · have hseam := endpoint_x_seam hN hM hNp e.val hx
          have hsame : (diamondOpenGraph hN hM true A).connectedComponentMk
              (faceEndpoint hN hM true e.val false) =
            (diamondOpenGraph hN hM true A).connectedComponentMk
              (faceEndpoint hN hM true e.val true) := by
            exact SimpleGraph.ConnectedComponent.sound
              (diamond_endpoints_reachable hN hM A e.val e.property)
          
          cases hc : checker e.val
          · simp only [hc] at hseam
            obtain ⟨hfalseRight, htrueLeft⟩ := hseam
            
            
            
            simp [g, diamondSeamCrossX, hx, hc,  rectanglePotential_eq_neg_one_of_right hN hM A
                                                   (faceEndpoint hN hM true e.val false) hfalseRight ,  rectanglePotential_eq_zero_of_left hN hM A c hnc
                                                          (faceEndpoint hN hM true e.val true) htrueLeft (hsame.symm.trans hcluster) ]
          · simp only [hc] at hseam
            obtain ⟨hfalseLeft, htrueRight⟩ := hseam
            
            
            
            simp [g, diamondSeamCrossX, hx, hc,  rectanglePotential_eq_zero_of_left hN hM A c hnc
                                                   (faceEndpoint hN hM true e.val false) hfalseLeft hcluster ,  rectanglePotential_eq_neg_one_of_right hN hM A
                                                          (faceEndpoint hN hM true e.val true) htrueRight ]
        · have hreach := rectangleOpenGraph_reachable_edge hN hM hNp A e hx hy
          have hpot : rectanglePotential hN hM A
              (faceEndpoint hN hM true e.val false) =
              rectanglePotential hN hM A (faceEndpoint hN hM true e.val true) := by
            grind [rectanglePotential, rectangleReachesRight_congr]
          
          simp [g, diamondSeamCrossX, hx, hpot]
  have hwind : diamondWindingX A f.val = 0 := by
    simp_all
  apply hdisp
  rw [← diamondWindingX_mul_period hN hM A f, hwind]
  simp

end

/-- Loops with nonzero horizontal displacement. -/
noncomputable def horizontalWindingLoopSet (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.univ.filter fun q => loopDisplacementX hN hM A q ≠ 0

/-- Loops with nonzero vertical displacement. -/
noncomputable def verticalWindingLoopSet (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.univ.filter fun q => loopDisplacementY hN hM A q ≠ 0

/-- Horizontal-winding loops whose projected chains avoid the horizontal cut. -/
noncomputable def cleanHorizontalWindingLoops (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact horizontalWindingLoopSet hN hM A |>.filter fun q =>
    ∀ e : OpenDiamondEdge A, e.val.2.val = 0 →
      (loopBoundaryCycle hN hM A q).val e = 0

/-- The loop attached to one of the two ribbon ends at the horizontal seam. -/
noncomputable def horizontalSeamEndLoop (hN : Even N) (hM : Even M)
    (hMp : 0 < M) (A : RCConfig N M) (x : Fin N) (b : Bool) :
    Loop hN hM (rcSmoothing A) :=
  directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
    (ribbonEndEquiv hN hM ((x, ⟨0, hMp⟩), b))

/-- All loop classes incident to the two ends of indexed edges on row zero. -/
noncomputable def horizontalSeamEndLoops (hN : Even N) (hM : Even M)
    (hMp : 0 < M) (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.univ.image fun x : Fin N × Bool =>
    horizontalSeamEndLoop hN hM hMp A x.1 x.2

private theorem horizontalSeamEndLoops_card_le (hN : Even N) (hM : Even M)
    (hMp : 0 < M) (A : RCConfig N M) :
    (horizontalSeamEndLoops hN hM hMp A).card ≤ 2 * N := by
  classical
  calc
    _ ≤ (Finset.univ ).card := Finset.card_image_le
    _ = 2 * N := by simp [Nat.mul_comm]

noncomputable def badHorizontalWindingLoopSet (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact (horizontalWindingLoopSet hN hM A).filter
     fun q => q ∉ cleanHorizontalWindingLoops hN hM A 

private theorem badHorizontalWindingLoops_subset_seamEnds
    (hN : Even N) (hM : Even M) (hMp : 0 < M)
    (A : RCConfig N M) :
    badHorizontalWindingLoopSet hN hM A ⊆
      horizontalSeamEndLoops hN hM hMp A := by
  classical
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hnot := hq'.2
  simp only [cleanHorizontalWindingLoops, Finset.mem_filter] at hnot
  push Not at hnot
  obtain ⟨e, heRow, heCoeff⟩ := hnot hq'.1
  have hCoeff' : (if directedLoopOf _ _ (checkerArrows_compatible hN hM
        (rcSmoothing A)) (ribbonEndEquiv hN hM (e.val, true)) = q then (1 : ℚ) else 0) -
      (if directedLoopOf _ _ (checkerArrows_compatible hN hM
        (rcSmoothing A)) (ribbonEndEquiv hN hM (e.val, false)) = q then 1 else 0) ≠ 0 := heCoeff
  
  have heVal :  (e.val.1, ⟨0, hMp⟩)  = e.val :=
    by
      bound
  by_cases htrue : directedLoopOf _ _ (checkerArrows_compatible hN hM
      (rcSmoothing A)) (ribbonEndEquiv hN hM (e.val, true)) = q
  · 
    refine Finset.mem_image.mpr ⟨(e.val.1, true), Finset.mem_univ _, ?_⟩
    
    rw [← htrue, ← heVal]
    rfl
  · have hfalse : directedLoopOf _ _ (checkerArrows_compatible hN hM
        (rcSmoothing A)) (ribbonEndEquiv hN hM (e.val, false)) = q := by
      simp_all
    refine Finset.mem_image.mpr ⟨(e.val.1, false), Finset.mem_univ _, ?_⟩
    
    rw [← hfalse, ← heVal]
    rfl

/-- Each clean horizontal winding loop yields a crossing cluster in the cut rectangle. -/
theorem cleanHorizontalLoop_cluster_crosses (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hq : q ∈ cleanHorizontalWindingLoops hN hM A) :
    hasRectangleCrossingX hN hM A (loopPrimalCluster hN hM A q) := by
  
  
  
  exact supportedCycle_nonzero_horizontal_hasRectangleCrossingX hN hM hNp A
    (loopPrimalCluster hN hM A q) (loopBoundaryCycle hN hM A q)
    (loopBoundaryCycle_supported hN hM A q)
     (Finset.mem_filter.mp hq).2  (by
      simpa [loopDisplacementX, loopBoundaryCycle_displacement_x] using  (Finset.mem_filter.mp  (Finset.mem_filter.mp hq).1 ).2 )

/-- The distinct rectangle-crossing primal clusters supplied by clean winding loops. -/
noncomputable def horizontalCrossingPrimalClusters (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Finset (diamondOpenGraph hN hM true A).ConnectedComponent := by
  classical
  exact (cleanHorizontalWindingLoops hN hM A).image (loopPrimalCluster hN hM A)

noncomputable def verticalSeamLoops (hN : Even N) (hM : Even M)
    (j : Fin M) (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact (verticalCutDarts (checkerArrows N M) j).image
    (directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A)))

section

variable (hN : Even N) (hM : Even M)
include hN hM

private theorem verticalWindingLoopSet_card_le 
    (j : Fin M) (A : RCConfig N M) :
    (verticalWindingLoopSet hN hM A).card ≤ N := by
  classical
  have hsub : verticalWindingLoopSet hN hM A ⊆ verticalSeamLoops hN hM j A := by
    intro q hq
    have hv : loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 := by
      intro hz
      
      exact (Finset.mem_filter.mp hq).2 (by
                                           unfold loopDisplacementY
                                           rw [loop_vertical_displacement (checkerArrows N M) (rcSmoothing A)
                                             (checkerArrows_compatible hN hM (rcSmoothing A)) j q]
                                           simp [hz])
    
    obtain ⟨d, hdq, hdv⟩ := exists_dart_of_loopSum_ne_zero
      (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) (verticalCross j) q  hv 
    exact Finset.mem_image.mpr ⟨d, by simp [verticalCutDarts, hdv], hdq⟩
  calc
    _ ≤ (verticalSeamLoops hN hM j A).card := Finset.card_le_card hsub
    _ ≤ (verticalCutDarts (checkerArrows N M) j).card := Finset.card_image_le
    _ ≤ N := verticalCutDarts_card_le _ _

section

variable (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
include hNp hMp

private theorem cleanHorizontalWindingLoops_card_le_two_crossingClusters
      :
    (cleanHorizontalWindingLoops hN hM A).card ≤
      2 * (horizontalCrossingPrimalClusters hN hM A).card := by
  classical
  
  have hcleanSub : cleanHorizontalWindingLoops hN hM A ⊆
      windingLoopSet hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A := by
    intro q hq
    rw [mem_windingLoopSet_iff_displacement hN hM _ _ A q]
    exact Or.inl (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  
  calc
    (cleanHorizontalWindingLoops hN hM A).card =
        ∑ c ∈ horizontalCrossingPrimalClusters hN hM A,
          ((cleanHorizontalWindingLoops hN hM A).filter
            fun q => loopPrimalCluster hN hM A q = c).card :=  Finset.card_eq_sum_card_fiberwise
                                                                 (s := cleanHorizontalWindingLoops hN hM A)
                                                                 (t := horizontalCrossingPrimalClusters hN hM A)
                                                                 (f := loopPrimalCluster hN hM A)
                                                                  fun q hq => Finset.mem_image_of_mem _ hq  
    _ ≤ ∑ _c ∈ horizontalCrossingPrimalClusters hN hM A, 2 := by
      apply Finset.sum_le_sum
      intro c hc
      apply le_trans (Finset.card_le_card ?_)
        (windingLoops_per_primalCluster_le_two hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A c)
      grind
    _ = 2 * (horizontalCrossingPrimalClusters hN hM A).card := by
      simp [Nat.mul_comm]

/-- Corrected loop-to-crossing-cluster count. The coefficient `2` records the
possible two essential loops incident to one primal cluster; the additive
`3N` consists of the vertical-winding bound `N` and the at-most `2N` loops
whose projected chains meet the chosen horizontal seam. -/
theorem windingLoopCount_le_threeN_add_two_mul_rectangleCrossings
      :
    windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A ≤
      3 * N + 2 * (horizontalCrossingPrimalClusters hN hM A).card := by
  classical
  let xset := horizontalWindingLoopSet hN hM A
  let yset := verticalWindingLoopSet hN hM A
  let clean := cleanHorizontalWindingLoops hN hM A
  let bad := badHorizontalWindingLoopSet hN hM A
  have hsubset : windingLoopSet hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A ⊆ xset ∪ yset := by
    intro q hq
    rw [mem_windingLoopSet_iff_displacement hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A q] at hq
    simp only [xset, yset, horizontalWindingLoopSet, verticalWindingLoopSet,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact hq
  have hcleanSubset : clean ⊆ xset := fun q hq => (Finset.mem_filter.mp hq).1
  have hcleanEq : xset.filter (fun q => q ∈ clean) = clean := by
    simp_all
  have hbadEq : xset.filter (fun q => q ∉ clean) = bad := rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := xset) (p := fun q => q ∈ clean)
  rw [hcleanEq, hbadEq] at hsplit
  have hbad : bad.card ≤ 2 * N := Trans.trans (card_le_card (badHorizontalWindingLoops_subset_seamEnds hN hM hMp A))
                                    (horizontalSeamEndLoops_card_le hN hM hMp A)
  have hy : yset.card ≤ N := by
                               solve_by_elim [_root_.PottsDiscontinuity.TorusLoops.verticalWindingLoopSet_card_le]
  
  
  calc
    windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A =
        (windingLoopSet hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A).card := rfl
    _ ≤ (xset ∪ yset).card := (Finset.card_le_card hsubset)
    _ ≤ xset.card + yset.card :=  Finset.card_union_le xset yset 
    _ ≤ clean.card + bad.card + N := by  omega
    _ ≤ clean.card + 2 * N + N := by omega
    _ ≤ 2 * (horizontalCrossingPrimalClusters hN hM A).card + 3 * N := by
      grind [cleanHorizontalWindingLoops_card_le_two_crossingClusters]
    _ = 3 * N + 2 * (horizontalCrossingPrimalClusters hN hM A).card := by omega

end

end

end PottsDiscontinuity.TorusLoops
