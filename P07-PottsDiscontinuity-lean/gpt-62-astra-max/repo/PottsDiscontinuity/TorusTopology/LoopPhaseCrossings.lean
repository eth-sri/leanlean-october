module

public import PottsDiscontinuity.TorusTopology.PhaseCrossings
public import PottsDiscontinuity.TorusTopology.PositiveLoops
public import PottsDiscontinuity.TorusTopology.WindingPhase

/-! A loop of positive vertical winding b gives b distinct crossing clusters
in the seam-closed cylinder, all within its original incident primal cluster. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC TorusLoops
variable {N M : ℕ}
noncomputable section

/-- All phases of one positive-winding loop yield distinct actual cylinder
clusters. This is the multiplicity step in the proof that `U ≥ r` gives `r` distinct
bottom-to-top clusters after the seam row is closed (`hUr_proved`). -/
theorem cylinder_crossings_of_positive_vertical_loop
    (hN : Even N) (hM : Even M) (hMp : 0 < M) {j : Fin M} (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hq : 0 < loopVertical j q) :
    ∃ x : Fin ((loopVertical j q).toNat) →
        FaceVertex N M true,
      (∀ i, (x i).val.2.val=0 ∧
        (diamondOpenGraph hN hM true A).connectedComponentMk (x i)=loopPrimalCluster q ∧
        cylinderReachesTop hN hM A (x i)) ∧
      ∀ i k, i ≠ k → ¬ (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable (x i) (x k) := by
  classical
  let b := (loopVertical j q).toNat
  have hb : 0 < b := by omega
  have hbcast :=
    Int.toNat_of_nonneg hq.le
  let c := loopPrimalCluster q
  have hdiv : ∀ f : diamondCycleSpace hN hM A,
      SupportedOnDiamondCluster c f →
      (∀ e : OpenDiamondEdge A, ∃ z : ℤ, f.val e=z) →
      ∃ z : ℤ, diamondWindingY f.val=(((b : ℤ)*z : ℤ) : ℚ) := by
    intro f hs hint
    obtain ⟨z,hz⟩ := incident_vertical_winding_divides_integral_cycle hN hM
      ⟨0,width_pos_of_loop hN hM A q⟩ j A q hq.ne' f hs hint
    grind
  obtain ⟨g,hg⟩ := exists_winding_phase_of_integral_divisor hN hM A c b hdiv
  have hw : diamondWindingY (loopBoundaryCycle q).val=(b : ℚ) := by
    rw [loopBoundaryCycle_windingY hN hM hMp j A q]
    exact_mod_cast hbcast.symm
  have hex (i : Fin b) :=
    exists_cylinder_crossing_at_each_phase hN hM hMp A hb c g hg (loopBoundaryCycle_supported hN hM A q) hw (i.val : ZMod b)
  choose x hx using hex
  refine ⟨x,fun i => ⟨(hx i).1,(hx i).2.1,(hx i).2.2.2⟩,?_⟩
  intro i k hik hr
  have he := winding_phase_eq_of_cylinder_reachable hN hM A c g hg (hx i).2.1 hr
  have hlabel :=
    (hx i).2.2.1.symm.trans (he.trans (hx k).2.2.1)
  have hv := congrArg ZMod.val hlabel
  have hi := i.isLt
  have hk := k.isLt
  simp only [ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hk] at hv
  exact hik (Fin.ext hv)

end
end PottsDiscontinuity.TorusTopology
