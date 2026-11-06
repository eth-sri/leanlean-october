module
public import Mathlib

public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.Torus.RibbonConnectivity
public import PottsDiscontinuity.Torus.RibbonFullBoundary

/-!
# Connectivity of the fully open primal diamond torus

Diagonal steps generate the black checkerboard faces. A descent in the ordinary
coordinate sum gives an explicit finite connectivity proof, including period two.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- One southwest diagonal move between primal face vertices. -/
def faceDownLeft (hN : Even N) (hM : Even M) (v : FaceVertex N M true) :
    FaceVertex N M true :=
  ⟨(prv v.val.1, prv v.val.2), by
    rw [checker_prv_x hN, checker_prv_y hM, Bool.not_not, v.property]⟩

/-- One southeast diagonal move between primal face vertices. -/
def faceDownRight (hN : Even N) (hM : Even M) (v : FaceVertex N M true) :
    FaceVertex N M true :=
  ⟨(nxt v.val.1, prv v.val.2), by
    rw [checker_nxt_x hN, checker_prv_y hM, Bool.not_not, v.property]⟩

/-- One northwest diagonal move between primal face vertices. -/
def faceUpLeft (hN : Even N) (hM : Even M) (v : FaceVertex N M true) :
    FaceVertex N M true :=
  ⟨(prv v.val.1, nxt v.val.2), by
    rw [checker_prv_x hN, checker_nxt_y hM, Bool.not_not, v.property]⟩

section

variable (hN : Even N) (hM : Even M) (v : FaceVertex N M true)


theorem full_reachable_downLeft  :
    (diamondOpenGraph hN hM true (openRCConfig N M)).Reachable v (faceDownLeft hN hM v) := by
  
  simpa only [faceEndpoint, faceEndpointRaw, v.property, Bool.false_eq_true, ite_true, ite_false,
    faceDownLeft] using  diamond_endpoints_reachable hN hM (openRCConfig N M) v.val rfl 

theorem full_reachable_downRight  :
    (diamondOpenGraph hN hM true (openRCConfig N M)).Reachable v (faceDownRight hN hM v) := by
  
  simpa only [faceEndpoint, faceEndpointRaw, checker_nxt_x hN, v.property, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, Equiv.symm_apply_apply, faceDownRight] using  diamond_endpoints_reachable hN hM (openRCConfig N M) (nxt v.val.1, v.val.2) rfl 

theorem full_reachable_upLeft  :
    (diamondOpenGraph hN hM true (openRCConfig N M)).Reachable v (faceUpLeft hN hM v) := by
  have he := full_reachable_downRight hN hM (faceUpLeft hN hM v)
  have hv : faceDownRight hN hM (faceUpLeft hN hM v) = v := by
    grind +locals
  rw [hv] at he
  exact he.symm

end

/-- The face at the coordinate origin, when the torus has positive periods. -/
def originFace (hNp : 0 < N) (hMp : 0 < M) : FaceVertex N M true :=
  ⟨(⟨0, hNp⟩, ⟨0, hMp⟩), rfl⟩

section

variable (hN : Even N) (hM : Even M)


theorem full_reachable_origin  (hNp : 0 < N) (hMp : 0 < M)
    (v : FaceVertex N M true) :
    (diamondOpenGraph hN hM true (openRCConfig N M)).Reachable v (originFace hNp hMp) := by
  have hall : ∀ n , ∀ v , v.val.1.val + v.val.2.val = n →
      (diamondOpenGraph hN hM true (openRCConfig N M)).Reachable v (originFace hNp hMp) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn
      have hp  := of_decide_eq_true v.property
      by_cases hx : v.val.1.val = 0
      · by_cases hy : v.val.2.val = 0
        · have hv : v = originFace hNp hMp := by
                                                bound
          rw [hv]
        · 
          let w := faceDownRight hN hM (faceDownLeft hN hM v)
          
          have hy₁ := prv_val_of_pos v.val.2 (by omega)
          have hy₂ := prv_val_of_pos (prv v.val.2) (by omega)
          
          exact ((full_reachable_downLeft hN hM v).trans
            (full_reachable_downRight hN hM (faceDownLeft hN hM v))).trans
              (ih _ (by
                       grind +locals) w rfl)
      · by_cases hy : v.val.2.val = 0
        · 
          let w := faceUpLeft hN hM (faceDownLeft hN hM v)
          
          have hx₁ := prv_val_of_pos v.val.1 (by omega)
          have hx₂ := prv_val_of_pos (prv v.val.1) (by omega)
          
          exact ((full_reachable_downLeft hN hM v).trans
            (full_reachable_upLeft hN hM (faceDownLeft hN hM v))).trans
              (ih _ (by
                       grind +locals) w rfl)
        · let w := faceDownLeft hN hM v
          have hx₁ := prv_val_of_pos v.val.1 (by omega)
          have hy₁ := prv_val_of_pos v.val.2 (by omega)
          
          exact (full_reachable_downLeft hN hM v).trans (ih _ (by
                                                                 change (prv v.val.1).val + (prv v.val.2).val < n
                                                                 omega) w rfl)
  exact hall _ v rfl

/-- The fully open primal graph is preconnected for every pair of even periods. -/
theorem diamondOpenGraph_open_preconnected  :
    (diamondOpenGraph hN hM true (openRCConfig N M)).Preconnected := by
  intro v w
  have hNp  := Fin.pos v.val.1
  have hMp  := Fin.pos v.val.2
  exact (full_reachable_origin hN hM hNp hMp v).trans
    (full_reachable_origin hN hM hNp hMp w).symm

theorem clusterCount_open  (hNp : 0 < N) (hMp : 0 < M) :
    clusterCount hN hM true (openRCConfig N M) = 1 := by
  let G := diamondOpenGraph hN hM true (openRCConfig N M)
  let : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (originFace hNp hMp)⟩
  let : Subsingleton G.ConnectedComponent :=
    (diamondOpenGraph_open_preconnected hN hM).subsingleton_connectedComponent
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

end

end PottsDiscontinuity.Torus
