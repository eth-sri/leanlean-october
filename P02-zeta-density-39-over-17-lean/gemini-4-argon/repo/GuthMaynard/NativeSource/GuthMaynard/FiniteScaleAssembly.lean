module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalLargeValues
public import GuthMaynard.NativeSource.GuthMaynard.FiniteDensityExponents

@[expose] public section

namespace GuthMaynard.NativeMoment

/-!
# Finite scale and exponent assembly for the classical endpoints

This module isolates the exact real-arithmetic content of ANTEDB
Corollaries 11.8--11.10.  It does not assert the still-open finite
zero-density-from-large-values reduction.  Instead it packages the concrete
MHH exponent, the bounded two-or-three-fold subdivision choice, the endpoint
windows, and the exceptional zeta-polynomial alternatives which that
reduction will consume.
-/

/-- The exponent supplied by the finite Montgomery--Halász--Huxley estimate
after writing `T = N^τ` and `V = N^σ`, before epsilon losses. -/
def classicalMHHExponent (σ τ : ℝ) : ℝ :=
  max (2 - 2 * σ) (min (τ + 1 - 2 * σ) (τ + 4 - 6 * σ))

/-- The subdivision envelope obtained from a Montgomery range ending at
`τ₀ + σ - 1`. -/
def corollary1110Envelope (σ τ₀ τ : ℝ) : ℝ :=
  max (2 - 2 * σ) (3 - 3 * σ + τ - τ₀)

/-- The bounded power choice used in Corollary 11.8: every scale in the
raised window is returned to the basic window by dividing its exponent by
either two or three. -/
theorem exists_two_or_three_scale_reduction
    {τ₀ τ : ℝ} (hτLower : 4 * τ₀ / 3 ≤ τ)
    (hτUpper : τ ≤ 8 * τ₀ / 3) :
    (2 * τ₀ / 3 ≤ τ / 2 ∧ τ / 2 ≤ τ₀) ∨
      (2 * τ₀ / 3 ≤ τ / 3 ∧ τ / 3 ≤ τ₀) := by
  by_cases hτ : τ ≤ 2 * τ₀
  · left
    constructor <;> nlinarith
  · right
    constructor <;> nlinarith

/-- The second-moment branch gives the Montgomery exponent throughout
`τ ≤ 1`. -/
theorem classicalMHHExponent_le_montgomery_of_tau_le_one
    {σ τ : ℝ} (hτ : τ ≤ 1) :
    classicalMHHExponent σ τ ≤ 2 - 2 * σ := by
  rw [classicalMHHExponent, max_le_iff]
  constructor
  · exact le_rfl
  · exact (min_le_left _ _).trans (by linarith)

/-- Exact finite arithmetic behind Corollary 11.10.  Subdivision of a
Montgomery range controls the entire basic window by the target line. -/
theorem corollary1110Envelope_le_target
    {σ τ₀ τ : ℝ} (hσ : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hBase : 3 - 3 * σ ≤ τ₀)
    (hτLower : 2 * τ₀ / 3 ≤ τ) (hτUpper : τ ≤ τ₀) :
    corollary1110Envelope σ τ₀ τ ≤
      (3 - 3 * σ) * τ / τ₀ := by
  rw [corollary1110Envelope, max_le_iff]
  have hOneMinus : 0 ≤ 1 - σ := by linarith
  have hTargetFirst : 2 - 2 * σ ≤ (3 - 3 * σ) * τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]
    nlinarith
  have hTargetSecond :
      3 - 3 * σ + τ - τ₀ ≤ (3 - 3 * σ) * τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]
    nlinarith
  exact ⟨hTargetFirst, hTargetSecond⟩

structure EndpointScaleCertificate (σ τ₀ : ℝ) : Prop where
  tau0_pos : 0 < τ₀
  density_base_le_tau0 : 3 - 3 * σ ≤ τ₀
  mhh_window : ∀ τ : ℝ, 0 ≤ τ → τ ≤ τ₀ + σ - 1 →
    classicalMHHExponent σ τ ≤ 2 - 2 * σ
  subdivision_window : ∀ τ : ℝ,
    2 * τ₀ / 3 ≤ τ → τ ≤ τ₀ →
      corollary1110Envelope σ τ₀ τ ≤ (3 - 3 * σ) * τ / τ₀
  raised_scale_window : ∀ τ : ℝ,
    4 * τ₀ / 3 ≤ τ → τ ≤ 8 * τ₀ / 3 →
      (2 * τ₀ / 3 ≤ τ / 2 ∧ τ / 2 ≤ τ₀) ∨
        (2 * τ₀ / 3 ≤ τ / 3 ∧ τ / 3 ≤ τ₀)
  tau0_le_ingham : τ₀ ≤ 2 - σ
  tau0_ge_short : 11 / 10 ≤ τ₀

theorem ingham_endpoint_scale_certificate
    {σ : ℝ} (_hσLower : 1 / 2 < σ) (hσUpper : σ ≤ 9 / 13) :
    EndpointScaleCertificate σ (2 - σ) := by
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, le_rfl, by linarith⟩
  · intro τ _hτNonneg hτ
    exact classicalMHHExponent_le_montgomery_of_tau_le_one (by linarith)
  · intro τ hτLower hτUpper
    exact corollary1110Envelope_le_target (by linarith) (by linarith)
      (by linarith) hτLower hτUpper
  · intro τ hτLower hτUpper
    exact exists_two_or_three_scale_reduction hτLower hτUpper

