module

public import proofs.HordijkSteelThreshold.WordEndBalls

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordBallEdgeAnchors (L N : ℕ) (s : List Bool) (r : ℕ) :=
  (wordBasicEdges L N).filter (fun e => e.1.val ∈ endWordBall r s)

noncomputable def wordMoleculeContourEnvelope (L N : ℕ) (s : List Bool) (b : ℕ) :=
  (wordBallEdgeAnchors L N s (64 * b)).biUnion (fun e => wordAnchoredContours L N e b)

def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

theorem wordMoleculeContourEnvelope_card (L N : ℕ) (s : List Bool) (b : ℕ) (hb : 0 < b) :
    (wordMoleculeContourEnvelope L N s b).card ≤ molecularContourConstant ^ b := by
  have hball : (wordBallEdgeAnchors L N s (64 * b)).card ≤ 2 * 7 ^ (64 * b) := by
    have hc : (wordBallEdgeAnchors L N s (64 * b)).card ≤
        ((endWordBall (64 * b) s) ×ˢ (Finset.univ : Finset Bool)).card :=
      Finset.card_le_card_of_injOn (fun e : WordBasicEdge L N => (e.1.val, e.2))
        (fun e he => Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2, Finset.mem_univ _⟩)
        fun ⟨⟨_, _⟩, _⟩ _ ⟨⟨_, _⟩, _⟩ _ h => by cases h; rfl
    have := endWordBall_card (64 * b) s
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc; omega
  have hraw : (wordMoleculeContourEnvelope L N s b).card ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) :=
    Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 81 ^ (b - 1))
      fun e _ => wordAnchoredContours_card L N e b).trans
      (by simp only [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hball))
  refine hraw.trans ((Nat.mul_le_mul (Nat.mul_le_mul_right _
    (by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 2) hb))
    (pow_le_pow_right₀ (by decide) (Nat.sub_le b 1))).trans_eq ?_)
  simp only [molecularContourConstant, mul_pow, pow_mul]

theorem wordBond_mem_molecule_envelope {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (hn : (wordGraphCut f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    wordGraphCut f ∈ wordMoleculeContourEnvelope L N s (wordGraphCut f).card := by
  obtain ⟨e, he⟩ := hn
  obtain ⟨p, hp⟩ := wordBond_molecular_anchor_radius f hmin e he c hminor s hs
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr
    ⟨(Finset.filter_subset _ _ : wordGraphCut f ⊆ wordBasicEdges L N) he, endWord_walk_mem_ball p _ hp⟩,
    wordBond_mem_anchored f hmin e he⟩

end HordijkSteelThreshold
