module

public import proofs.HordijkSteelThreshold.PositiveLowerPhase
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

/-- Finite quantitative consumer for near-full static mass, with every
parameter comparison and nonfood threshold explicit. -/
theorem canonical_raf_ge_near_full_static (n m : ℕ) (lambda : ℝ) (hm : 0 < m)
    (q : I) (hk : 6 < (m-1)*(Fintype.card (Molecule n)/m))
    (hq : q ≤ fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) ((m-1)*(Fintype.card (Molecule n)/m))).card) :
    staticReactionMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
        uniformCatalysisMeasure n lambda (HasRAFEvent n) := by
  let k := (m-1)*(Fintype.card (Molecule n)/m)
  rw [canonical_raf_measure_eq_ambient]
  refine ((measure_mono (t := {ω | k ≤ (temporaryReactionClosure 2 (staticOpenReactions ω)).card}) fun ω hω => ?_).trans
    (static_increasing_event_mono n hq (fun S => k ≤ (temporaryReactionClosure 2 S).card)
      fun S T hST hS => hS.trans (Finset.card_le_card (temporaryReactionClosure_mono hST)))).trans
    ((source_mass_ge_iid_static lambda (temporaryReactionClosure 2) (fun _ _ h => temporaryReactionClosure_mono h)
      k (Fintype.card (Reaction n))).trans (measure_mono fun ω hω => source_terminal_hasRAF ω (hk.trans_le hω)))
  have := Nat.mul_le_mul_left (m-1) (Nat.div_mul_le_self (Fintype.card (Molecule n)) m)
  change (m-1)*Fintype.card (Molecule n) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card at hω
  dsimp [k]; nlinarith

end HordijkSteelThreshold
