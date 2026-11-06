module

public import NearlyMinimax.PolynomialGaussian
public import NearlyMinimax.DegreeBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# The finite scalar bias bound for the actual upper allocation

This module composes the explicit candidate width, terminal dyadic flooring,
coordinate-degree subtraction, Gaussian absorption and uniform lattice sum.
Unlike the abstract allocation lemma, the final theorem has no level-range,
degree, summand, or bias-sum hypotheses. Its hypotheses concern only the fixed
positive allocation constants and the two scalar coefficient identities.
This is a scalar allocation theorem, not a statistical risk theorem.
-/

𝚷
𝚪

𝚨

𝗇 𝔈 allocationLevelPosition δ a C H x j
/-- The exact degree `m_j=floor(beta Q_S(z_j))-q` at the explicit level position. -/
def actualApproximationDegree (δ a C H β x : ℝ) (j q : ℕ) : ℕ :=
  allocatedApproximationDegree β 𝚑₂ 𝔈 q

𝗇 𝔄 terminalAllocationLevel δ a C H γ x
𝗇 𝔅 actualApproximationDegree δ a C H β x j q
𝗇 𝔇 (r + 𝙖) * Real.log S
𝗃 𝔊 Real.exp $ δ * ἀ
𝗇 𝔉 𝔊 j
𝗃 𝔍 ἀ + 1
/-- `eq:U12-sum` for the actual floored scalar allocation, for all sufficiently large sample sizes. -/
theorem eventually_actual_allocation_bias_sum (r q : ℕ) δ a C H γ β θ τ
    (hδ : 𝙮₂) (ha : 𝙆) (hH : 𝚉) (hβ : 0 < β) (hθ : 0 < θ) (hτ : 0 < τ)
    (hθβ : τ * β = θ) (hθγ : θ * γ = 𝗥₂ + 𝙖) :
    ∃ B , 𝘶₁ ∧ ∀ᶠ x : ℝ in atTop,
       ∑ j ∈ Finset.range 𝔍 𝔄,
        𝔉 ^ (-θ) * 𝔍 𝔅 ^ r *
           Real.exp (-τ) ^ 𝔅 ≤
        B * 𝔊 𝔄 ^ (-θ) := by
  refine ⟨allocationBiasSumConstant r q β θ τ δ,
    allocationBiasSumConstant_pos r q hβ.le hθ hδ, ?_⟩
  filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually $ eventually_ge_atTop 1 ,
    eventually_terminal_cell_log_nonneg ha hH C γ,
    eventually_width_degree_threshold ha hβ C q] with x hS hLT hdegree
  let J := 𝔄
  let S := 𝚑₂
  let ell := Real.log $ H * S
  let T := δ * J - Real.log x
  let u₀ := -Real.log x + ell - S / 2
  let Kstar := 𝔊 J
  have hu := (roundedTerminalDepth_bounds hδ hLT).2
  change T ≤ S - ell - γ * Real.log S at hu
  have hreserve : 𝔇 ≤ θ * (S - ell - T) := by
    have he : θ * γ * Real.log S = 𝔇 := by rw [hθγ]
    nlinarith
  have hqS : q ≤ β * S / 4 := by
    linarith
  have hz j : u₀ + j * δ + S / 2 = 𝔈 := by
    unfold allocationLevelPosition
    ring
  have hbound := floored_raw_allocation_bias_sum_bound (Finset.range 𝔍 J) r q
    u₀ δ β θ τ S ell T Kstar (fun j => 𝔉)
    hδ hβ.le hθ hτ hS hθβ (Real.exp_pos _) (fun j hj => Real.exp_pos _) (by
      intro j hj
      rw [Real.log_exp, Real.log_exp]
      ring) hreserve $ by
      intro j hj
      exact profile_coordinate_order_admissible q hβ.le  𝖡₄  hqS
  simp_rw [hz] at hbound
  simpa [actualApproximationDegree, J, Kstar] using hbound
