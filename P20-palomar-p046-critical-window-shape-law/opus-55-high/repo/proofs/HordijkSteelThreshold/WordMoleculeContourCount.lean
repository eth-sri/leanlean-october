module

public import proofs.HordijkSteelThreshold.WordEndBalls

@[expose] public section

namespace HordijkSteelThreshold
open Classical

variable (L N : ℕ) (s : List Bool)

section
variable (r : ℕ)

noncomputable def wordBallEdgeAnchors   :=
  (wordBasicEdges L N).filter $ fun e => e.1.val ∈ endWordBall r s

theorem wordBallEdgeAnchors_card   :
    (wordBallEdgeAnchors L N s r).card ≤ 2 * 7 ^ r := by
  have := Finset.card_le_card_of_injOn (fun e : WordBasicEdge L N => (e.1.val, e.2))
    (s := wordBallEdgeAnchors L N s r) (t := endWordBall r s ×ˢ Finset.univ)
    (fun e he => by simp_all [wordBallEdgeAnchors]) fun e _ d _ h =>
      Prod.ext (Subtype.ext $ congrArg Prod.fst h) (congrArg Prod.snd h :)
  simp at this
  linarith [endWordBall_card r s]

end

variable (b : ℕ)

/-- A finite envelope for all size-b contours whose smaller side contains molecule s. -/
noncomputable def wordMoleculeContourEnvelope   :=
  (wordBallEdgeAnchors L N s $ 64 * b).biUnion $ fun e => wordAnchoredContours L N e b

def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

/-- Uniform per-molecule exponential contour count with an explicit safe constant. -/
theorem wordMoleculeContourEnvelope_card   (hb : 0 < b) :
    (wordMoleculeContourEnvelope L N s b).card ≤ molecularContourConstant ^ b :=
  calc _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := Finset.card_biUnion_le.trans
        ((Finset.sum_le_card_nsmul _ _ _ fun e _ => wordAnchoredContours_card L N e b).trans
          (by simpa using wordBallEdgeAnchors_card L N s $ 64 * b))
    _ ≤ 2 ^ b * 7 ^ (64 * b) * 81 ^ b := by gcongr <;> grind
    _ = _ := by simp only [molecularContourConstant, mul_pow, pow_mul]

end HordijkSteelThreshold
