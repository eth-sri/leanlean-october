module

public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.RunningTimes.Sec3.Theorem19.Layout
public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Light.Sec3

/-- Exact Triangle in `O(n^a)` steps of the word RAM for every `a > 3 - δ`, from the explicit
bound `K κ n^{3-δ} (log n)^e` from some size on. -/
theorem exactTriangle_of_explicitFrom {δ : ℝ} {e : ℕ} (h : ExplicitFrom lightModel δ e) {a : ℝ}
    (ha : 3 - δ < a) : SolvedInTime EndStatement.ExactTriangle a 0 := by
  obtain ⟨_, _, T, hT, hb⟩ := h
  exact FromClaims.solvedInTime_of_claim realized_exactTriangle fun κ hκ =>
    ⟨T, hT, (hb.along hκ (c := 1) fun _ _ => by simp).upperBigOPow ha⟩

end ImprovedExponents
