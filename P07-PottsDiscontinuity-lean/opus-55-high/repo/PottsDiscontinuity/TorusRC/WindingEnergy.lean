module

public import PottsDiscontinuity.TorusRC.IndexedOpening
public import PottsDiscontinuity.TorusRC.WindingClosure

/-! # Finite-energy completion of the source's primal winding event -/

public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

def seamOtherEdges (hMp : 0 < M) (i₀ : Fin N) : Finset (Fin N × Fin M) :=
  (Finset.univ.erase i₀).image (fun i => (i,(⟨0,hMp⟩ : Fin M)))

theorem seamOtherEdges_card_le (hMp : 0 < M) (i₀ : Fin N) :
    (seamOtherEdges hMp i₀).card ≤ N :=
  Finset.card_image_le.trans (Finset.card_erase_le.trans_eq (by simp))

theorem boundedChain_mono (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i : Fin (3*n+1)) (hi : Even (i.val : ℤ)) (k : ℕ)
    {A B : RCConfig N M} (hAB : A ≤ B)
    (hA : A ∈ boundedRectangleChain hNp hMp n i hi k) :
    B ∈ boundedRectangleChain hNp hMp n i hi k := by
  obtain ⟨w,hw⟩ := hA
  let F : liftedStripGraph hNp hMp A 0 (3*(n:ℤ)) →g
      liftedStripGraph hNp hMp B 0 (3*(n:ℤ)) :=
    ⟨id,fun h => liftedStripGraph_mono hNp hMp 0 (3*(n:ℤ)) hAB h⟩
  refine ⟨w.map F,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨z',hz',heq⟩ := List.mem_map.mp hz
  subst z
  exact hw z' hz'

/-- Complete a bounded chain with its terminal zigzag, and close every seam
edge except the chosen one. Both costs are finite-energy costs on actual
indexed edges. The slightly enlarged strip leaves room for the zigzag. -/
theorem primalWinding_probability_ge_boundedChain (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (i : Fin (3*n+1)) (hi : Even (i.val : ℤ))
    (k : ℕ) (hheight : 2*n*k < M) :
    ((1 - (rcCriticalParameter q).val) ^ N *
      fkOpenEnergy (torusRCBridgeParameters q) ^ (M - 2*n*k)) *
      torusRCProbability hN hM q (boundedRectangleChain hNp hMp n i hi k) ≤
      torusRCProbability hN hM q (primalWindingSingleSeam hNp hMp hM (3*n+1)) := by
  let T := terminalZigzagEdges hNp hMp i.val (2*n*k)
  let i₀ := periodicCoordinate hNp ((i.val : ℤ)+1)
  let S := seamOtherEdges hMp i₀
  let E := boundedRectangleChain hNp hMp n i hi k
  let U : Set (RCConfig N M) := {A | ∀ e ∈ T, A e = true}
  have hstable : ∀ e ∈ S, ∀ A : RCConfig N M,
      A ∈ E ∩ U ↔ toggleEdge A e ∈ E ∩ U := by
    intro e he A
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    have hchain := boundedRectangleChain_toggle_seam hNp hMp n i hi k hheight
      (j,⟨0,hMp⟩) rfl A
    have haway (f : Fin N × Fin M) (hf : f ∈ T) :
        toggleEdge A (j,⟨0,hMp⟩) f = A f := by
      apply toggleEdge_away
      have hc := terminalZigzagEdges_column hNp hMp i.val (2*n*k) f hf
      grind
    constructor
    · rintro ⟨hc,hu⟩
      refine ⟨hchain.mp hc,?_⟩
      intro f hf
      rw [haway f hf]
      tauto
    · rintro ⟨hc,hu⟩
      refine ⟨hchain.mpr hc,?_⟩
      intro f hf
      have h := hu f hf
      rw [haway f hf] at h
      omega
  have hclose := TorusLoops.torusRCProbability_close_finite_set hN hM q S (E ∩ U) hstable
  have hopen := torusRCProbability_allOpen_inter_ge hN hM hN4 hM4 q T E (fun {_ _} hAB hA => boundedChain_mono hNp hMp n i hi k hAB hA)
  rw [Set.inter_comm U E] at hopen
  have hsub : ((E ∩ U) ∩ {A | ∀ e ∈ S, A e = false}) ⊆
      primalWindingSingleSeam hNp hMp hM (3*n+1) := by
    rintro A ⟨⟨hc,hu⟩,hcl⟩
    apply boundedChain_terminal_implies_winding hNp hMp hM n i hi k hheight A hc hu
    intro j hj
    exact hcl (j,⟨0,hMp⟩) (Finset.mem_image.mpr
      ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩,rfl⟩)
  have hc0 : 0 ≤ 1 - (rcCriticalParameter q).val := by grind
  have hc1 : 1 - (rcCriticalParameter q).val ≤ 1 := by
    grind
  have ho0 := (fkOpenEnergy_pos (torusRCBridgeParameters q)).le
  have hfac := mul_le_mul
    (pow_le_pow_of_le_one hc0 hc1 (seamOtherEdges_card_le hMp i₀))
    (pow_le_pow_of_le_one ho0 (fkOpenEnergy_le_one (torusRCBridgeParameters q)) (terminalZigzagEdges_card_le hNp hMp i.val (2*n*k)))
    (pow_nonneg ho0 _) (pow_nonneg hc0 S.card)
  calc
    _ ≤ ((1-(rcCriticalParameter q).val)^S.card *
        fkOpenEnergy (torusRCBridgeParameters q)^T.card) * torusRCProbability hN hM q E :=
      mul_le_mul_of_nonneg_right hfac (torusRCProbability_nonneg hN hM q E)
    _ = (1-(rcCriticalParameter q).val)^S.card *
        (fkOpenEnergy (torusRCBridgeParameters q)^T.card * torusRCProbability hN hM q E) := by ring
    _ ≤ (1-(rcCriticalParameter q).val)^S.card * torusRCProbability hN hM q (E ∩ U) :=
      mul_le_mul_of_nonneg_left hopen (pow_nonneg hc0 _)
    _ ≤ torusRCProbability hN hM q (primalWindingSingleSeam hNp hMp hM (3*n+1)) :=
      hclose.trans (torusRCProbability_mono hN hM q hsub)

end PottsDiscontinuity.TorusRC
