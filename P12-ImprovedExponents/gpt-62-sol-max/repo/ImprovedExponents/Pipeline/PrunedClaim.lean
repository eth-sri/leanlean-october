module

public import ImprovedExponents.Pipeline.Ratios

public import ImprovedExponents.Pipeline.Fits
public import ImprovedExponents.Pipeline.RegimeRS
public import ImprovedExponents.Cost8P.Offline
public import ImprovedExponents.PrunedProgram.Wrapper.Program

@[expose] public section

/-! Verification of the pruned thin-product solver, including its regime test. -/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4 Real

/-- **The thin product with pruned encodings and the regime test `D^r ≤ N^s`**, at the ratios
`c = a/b` and `θ = p/q` with `A'(c) < (r/s) ln 4`: every exponent `γ < γX(c, θ)`, for
`ε < R'_c(γ)` and `ε ≤ s/r`. -/
-- adapted from ImprovedExponents/Pipeline/Claims.lean (thinClaimRS_gammaX)
theorem thinClaimP_gammaX (G : RatParams) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrs : basePruned G.realC < ((r : ℝ) / s) * log 4) {γ ε : ℝ}
    (hγ0 : 0 < γ) (hγ : γ < gammaX G.realC G.realTheta)
    (hε : ε < RcP G.realC γ) (hεrs : ε ≤ (s : ℝ) / r) :
    ThinClaim lightModel ε γ (qOf G.realTheta) := by
  obtain ⟨m₁, h₁⟩ := offlineWithinP cShared30 G hγ0 hγ hε
  obtain ⟨m₂, h₂⟩ := exists_fitsRS G hr hs hrs
  let m := max (max m₁ m₂) 1
  have hm₀ : 1 ≤ m := le_max_right _ _
  obtain ⟨hoff, hauxO, hall⟩ := offline32PRoutine_programP (G.withThreshold m hm₀) r s
  exact thinClaimRS_of_offlineWithinT (O := offline32PRoutine _ r s) hr
    (h₂ _ hm₀ (by dsimp [m]; omega)) ⟨_, rfl⟩ hall hoff hauxO hεrs
    (h₁ _ hm₀ (by dsimp [m]; omega))

end ImprovedExponents
