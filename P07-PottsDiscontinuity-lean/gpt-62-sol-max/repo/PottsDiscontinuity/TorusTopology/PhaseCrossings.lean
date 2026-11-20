module

public import PottsDiscontinuity.TorusTopology.CylinderCrossing
public import PottsDiscontinuity.TorusTopology.LiftedPotentials
public import PottsDiscontinuity.TorusTopology.PhaseFlux

/-! Each nonzero modular phase flux forces a genuine bottom-to-top cylinder
component. Distinct phases cannot belong to the same seam-closed cluster. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC
variable {N M b : ℕ}
noncomputable section

section

variable (hN : Even N) (hM : Even M)

/-- The seam-closed cylinder is a subgraph of the original primal graph. -/
theorem seamClosed_graph_le (A : RCConfig N M) :
    diamondOpenGraph hN hM true (torusRCSeamClosed A) ≤ diamondOpenGraph hN hM true A := by
  intro u v huv
  rw [diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at huv ⊢
  obtain ⟨⟨e,he,hep⟩,hne⟩ := huv
  have hy : e.2.val ≠ 0 := by intro hy; simp [torusRCSeamClosed,hy] at he
  have hAe : A e=true := by simpa [torusRCSeamClosed, hy] using he
  exact ⟨⟨e,hAe,hep⟩,hne⟩

/-- A winding phase is constant along an actual seam-closed component. -/
theorem winding_phase_eq_of_cylinder_reachable (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : IsWindingPhase hN hM A c g)
    {u v : FaceVertex N M true}
    (hu : (diamondOpenGraph hN hM true A).connectedComponentMk u=c)
    (hr : (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable u v) : g u=g v := by
  have hadj {w z : FaceVertex N M true}
      (hw : (diamondOpenGraph hN hM true A).connectedComponentMk w=c)
      (h : (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Adj w z) : g w=g z := by
    rw [diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at h
    obtain ⟨⟨e,he,hep⟩,_⟩ := h
    have hy : e.2.val ≠ 0 := by intro hy; simp [torusRCSeamClosed,hy] at he
    have hAe : A e=true := by simpa [torusRCSeamClosed, hy] using he
    rcases Sym2.eq_iff.1 hep with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have hv := hg ⟨e,hAe⟩ hw
      simp only [hy,ite_false] at hv
      exact (sub_eq_zero.1 hv).symm
    · have hc :=
        (SimpleGraph.ConnectedComponent.sound (diamond_endpoints_reachable hN hM A e hAe)).trans hw
      have hv := hg ⟨e,hAe⟩ hc
      simp only [hy,ite_false] at hv
      exact sub_eq_zero.1 hv
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => rfl
  | @tail w z hr hwz ih =>
    have hreach :=
      ((SimpleGraph.reachable_iff_reflTransGen u w).2 hr).mono (seamClosed_graph_le hN hM A)
    have hw :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hu
    exact ih.trans (hadj hw hwz)

/-- Every phase of a chain with winding b has a bottom-to-top cylinder cluster
inside its original primal component. -/
theorem exists_cylinder_crossing_at_each_phase (hMp : 0 < M) (A : RCConfig N M) (hb : 0 < b)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : IsWindingPhase hN hM A c g)
    (f : diamondCycleSpace hN hM A) (hs : SupportedOnDiamondCluster hN hM A c f)
    (hw : diamondWindingY A f.val = (b : ℚ)) (k : ZMod b) :
    ∃ u : FaceVertex N M true, u.val.2.val=0 ∧
      (diamondOpenGraph hN hM true A).connectedComponentMk u=c ∧
        g u=k ∧ cylinderReachesTop hN hM A u := by
  classical
  by_contra hn
  let X := cylinderReachesTop hN hM A
  have hX (e : OpenDiamondEdge A) (hy : e.val.2.val ≠ 0) :
      X (faceEndpoint hN hM true e.val true) ↔ X (faceEndpoint hN hM true e.val false) := by
    have hr := diamond_endpoints_reachable hN hM (torusRCSeamClosed A) e.val
      (by simp [torusRCSeamClosed, hy, e.property])
    constructor
    · rintro ⟨v, hv, hvr⟩; exact ⟨v, hv, hr.trans hvr⟩
    · rintro ⟨v, hv, hvr⟩; exact ⟨v, hv, hr.symm.trans hvr⟩
  have htop (e : OpenDiamondEdge A) (he : e.val.2.val = 0) : X (faceEndpoint hN hM true e.val true) := by
    refine ⟨_, ?_, SimpleGraph.Reachable.refl _⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hMp.ne'
    have hprev : (faceEndpoint hN hM true e.val true).val.2 = prv e.val.2 := by
      cases hcheck : checker e.val <;> simp [faceEndpoint, faceEndpointRaw, hcheck]
    rw [hprev, show e.val.2 = 0 from Fin.ext he, prv_zero]
    rfl
  have hflux := phaseFlux_conservation hN hM A c g hg f hs X hX k
  have hzero : phaseFluxOn hN hM A g k X false f.val = 0 := by
    unfold phaseFluxOn
    refine sum_eq_zero fun e he => hs e (fun hc => hn ?_)
    obtain ⟨⟨hy, hk⟩, hreach⟩ := (mem_filter.mp he).2
    exact ⟨_, by simpa [faceEndpoint_false_y] using hy, hc, hk, hreach⟩
  have hfull : phaseFluxOn hN hM A g (k + 1) X true f.val = phaseFlux hN hM A g (k + 1) f.val := by
    unfold phaseFluxOn phaseFlux
    apply sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp only [mem_filter, mem_univ, true_and, and_true]
    exact and_iff_left_of_imp (fun h => htop e h.1)
  rw [hzero, hfull, phaseFlux_eq_neg_one hN hM A hb c g hg f hs hw] at hflux
  norm_num at hflux

end

end
end PottsDiscontinuity.TorusTopology
