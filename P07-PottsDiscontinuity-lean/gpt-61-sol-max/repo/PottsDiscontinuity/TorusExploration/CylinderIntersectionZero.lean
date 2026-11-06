module
public import Mathlib

public import PottsDiscontinuity.TorusExploration.CylinderIntersection

/-! A seam-band return has zero algebraic intersection with every cycle
avoiding the explored crossing cluster in the cylinder interior. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus Finset
open PottsDiscontinuity.SixVertex
variable {N M : ℕ}

/-- The explicit vertex correction supported on the cylinder's bottom row. -/
def bottomSeamPotential (f : OpenDiamondEdge (openRCConfig N M) → ℚ)
    (v : FaceVertex N M true)  :=
  if v.val.2.val=0 then fullFlowAt f v.val else 0

lemma full_eastFlow_eq_bottomPotential
    (f : OpenDiamondEdge (openRCConfig N M) → ℚ) (v : FaceVertex N M true)
    (hf : ∀ p : Port, (faceCorner v.val p).1.2.val ≠ 0 →
      fullFlowAt f (faceCorner v.val p).1=0) :
    fullFlowAt f v.val=bottomSeamPotential f v := by
  by_cases hy : v.val.2.val=0
  · simp [bottomSeamPotential,hy]
  · 
    simpa [bottomSeamPotential,hy,faceCorner] using  hf .east hy 

section

variable (hN : Even N) (hM : Even M)
include hN hM

lemma full_northFlow_eq_neg_bottomPotential 
    (f : diamondCycleSpace hN hM (openRCConfig N M)) (v : FaceVertex N M true)
    (hf : ∀ p : Port, (faceCorner v.val p).1.2.val ≠ 0 →
      fullFlowAt f.val (faceCorner v.val p).1=0)
    (hnxt : (nxt v.val.2).val ≠ 0) :
    -fullFlowAt f.val (nxt v.val.1,v.val.2)=bottomSeamPotential f.val v := by
  by_cases hy : v.val.2.val=0
  · have hw := hf .west hnxt
    have hs := hf .south hnxt
    have hc := sum_ribbonHalfFlow_corners hN hM (openRCConfig N M) f v
    rw [sum_port] at hc
    simp only [full_halfFlow_corner] at hc
    change fullFlowAt f.val (nxt v.val.1,nxt v.val.2)=0 at hw
    change fullFlowAt f.val (v.val.1,nxt v.val.2)=0 at hs
    
    simp only [bottomSeamPotential,hy,ite_true]
    linarith
  · have hh := hf .north hy
    simp only [faceCorner] at hh
    simp only [bottomSeamPotential,hy,ite_false,hh,neg_zero]

lemma full_intersectionCoefficient_eq_bottomCoboundary
    
    (f : diamondCycleSpace hN hM (openRCConfig N M))
    (e : OpenDiamondEdge (openRCConfig N M)) (he : e.val.2.val ≠ 0)
    (hf : ∀ b : Bool, ∀ p : Port,
      (faceCorner (faceEndpoint hN hM true e.val b).val p).1.2.val ≠ 0 →
      fullFlowAt f.val (faceCorner (faceEndpoint hN hM true e.val b).val p).1=0) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) f e =
      diamondCoboundary hN hM (openRCConfig N M) (bottomSeamPotential f.val) e := by
  have hyf : (faceEndpoint hN hM true e.val false).val.2.val ≠ 0 := by
    grind [faceEndpoint, faceEndpointRaw]
  have hyt : nxt (faceEndpoint hN hM true e.val true).val.2=e.val.2 := by
    cases hc : checker e.val <;>
      simp only [faceEndpoint, faceEndpointRaw, hc, Bool.false_eq_true, ite_true, ite_false, Equiv.apply_symm_apply]
  
  have hx := full_eastFlow_eq_bottomPotential f.val
    (faceEndpoint hN hM true e.val true) (hf true)
  rw [full_intersectionCoefficient_eq_below,diamondCoboundary_apply]
  simp only [bottomSeamPotential,hyf,ite_false,sub_zero]
  cases hc : checker e.val
  · grind [bottomSeamPotential, faceEndpoint, faceEndpointRaw]
  · simpa only [bottomSeamPotential, hc, ite_true, neg_one_mul, faceEndpoint, faceEndpointRaw, Equiv.apply_symm_apply] using  full_northFlow_eq_neg_bottomPotential hN hM f
                                                                                     (faceEndpoint hN hM true e.val true) (hf true) (by simpa only [hyt] using he) 

/-- A conserved cylinder cycle outside the nonseam support of f has zero
intersection with f, even if the seam return touches boundary vertices. -/
theorem cylinder_exterior_intersection_zero
    
    (f g : diamondCycleSpace hN hM (openRCConfig N M))
    (hg : ∀ e : OpenDiamondEdge (openRCConfig N M), g.val e ≠ 0 →
      e.val.2.val ≠ 0 ∧ ∀ b : Bool, ∀ p : Port,
        (faceCorner (faceEndpoint hN hM true e.val b).val p).1.2.val ≠ 0 →
        fullFlowAt f.val (faceCorner (faceEndpoint hN hM true e.val b).val p).1=0) :
    ribbonIntersection hN hM (openRCConfig N M) f g=0 := by
  have heq : ribbonIntersection hN hM (openRCConfig N M) f g =
      ∑ e, diamondCoboundary hN hM (openRCConfig N M) (bottomSeamPotential f.val) e*g.val e := by
    apply Finset.sum_congr rfl
    intro e he
    by_cases hz : g.val e=0
    · simp [hz]
    · grind [full_intersectionCoefficient_eq_bottomCoboundary]
  rw [heq]
  have hp := diamondBoundary_pairing hN hM (openRCConfig N M) (bottomSeamPotential f.val) g.val
  rw [g.property] at hp
  simpa only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] using hp.symm

end

end PottsDiscontinuity.TorusExploration
