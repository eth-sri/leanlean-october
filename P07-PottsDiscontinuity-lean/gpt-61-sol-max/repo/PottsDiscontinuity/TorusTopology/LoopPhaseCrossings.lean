module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PhaseCrossings
public import PottsDiscontinuity.TorusTopology.PositiveLoops
public import PottsDiscontinuity.TorusTopology.WindingPhase

/-! A loop of positive vertical winding b gives b distinct crossing clusters
in the seam-closed cylinder, all within its original incident primal cluster. -/

@[expose] public section


namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC TorusLoops
variable {N M : ℕ}
noncomputable section

/-- All phases of one positive-winding loop yield distinct actual cylinder
clusters. This is the multiplicity step in the proof that `U ≥ r` gives `r` distinct
bottom-to-top clusters after the seam row is closed (`hUr_proved`). -/
theorem cylinder_crossings_of_positive_vertical_loop
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (j : Fin M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hq : 0 < loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q) :
    ∃ x : Fin  (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat  →
        FaceVertex N M true,
      (∀ i, (x i).val.2.val=0 ∧
        (diamondOpenGraph hN hM true A).connectedComponentMk (x i)=loopPrimalCluster hN hM A q ∧
        cylinderReachesTop hN hM A (x i)) ∧
      ∀ i k, i ≠ k → ¬ (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable (x i) (x k) := by
  
  let b := (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat
  have hb : 0 < b := by  omega
  
  
  let c := loopPrimalCluster hN hM A q
  
  obtain ⟨g,hg⟩ := exists_winding_phase_of_integral_divisor hN hM A c b (by
                                                                           intro f hs hint
                                                                           obtain ⟨z,hz⟩ := incident_vertical_winding_divides_integral_cycle hN hM
                                                                             ⟨0,width_pos_of_loop hN hM A q⟩ j A q hq.ne' f hs hint
                                                                           grind)
  
  have hex (i : Fin b)  :=
    exists_cylinder_crossing_at_each_phase hN hM hMp A hb c g hg
      (loopBoundaryCycle hN hM A q) (loopBoundaryCycle_supported hN hM A q) (by
                                                                               rw [loopBoundaryCycle_windingY hN hM hMp j A q]
                                                                               exact_mod_cast (Int.toNat_of_nonneg hq.le).symm) i.val
  choose x hx using hex
  refine ⟨x,fun i => ⟨(hx i).1,(hx i).2.1,(hx i).2.2.2⟩,?_⟩
  intro i k hik hr
  
  
  have hv := congrArg ZMod.val ((hx i).2.2.1.symm.trans ((winding_phase_eq_of_cylinder_reachable hN hM A c g hg (hx i).2.1 hr).trans (hx k).2.2.1))
  have hi  := i.isLt
  have hk  := k.isLt
  simp only [ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hk] at hv
  exact hik (Fin.ext hv)

end
end PottsDiscontinuity.TorusTopology
