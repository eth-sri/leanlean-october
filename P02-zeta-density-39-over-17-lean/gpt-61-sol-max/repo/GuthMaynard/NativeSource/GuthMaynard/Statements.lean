module
public import GuthMaynard.NativeSource.GuthMaynard.Asymptotics
public import GuthMaynard.NativeSource.GuthMaynard.Separated
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial

@[expose] public section

open Complex Finset

namespace GuthMaynard.NativeMoment

/--
Theorem 1.1 (Large values estimate).
Suppose $b_n$ is a sequence of complex numbers with $|b_n| \le 1$, and $W$ is a sequence of
$1$-separated points in $[0, T]$ such that $|D_N(t)| \ge V$ for all $t \in W$.
Then $|W| \lessapprox N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4}$.

We formulate $T^{o(1)}$ explicitly with $\varepsilon$.  This is the project's
internal open-dyadic-support interface: it asks for a global coefficient bound
because that is convenient for downstream consumers.  The literal published
Theorem 1.1 contract (closed sum, support-only coefficient bound, and positive
phase) and its native proof are in `GuthMaynard.NativeMomentBase.PublicationContract`.
-/
def GuthMaynardLargeValues : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∃ (C T₀ : ℝ), 0 < C ∧ 1 ≤ T₀ ∧
    ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → T₀ ≤ T → 0 < V →
      (∀ n, ‖b n‖ ≤ 1) →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N:ℝ)^2 * V^(-2:ℝ) + (N:ℝ)^(18/5:ℝ) * V^(-4:ℝ) + T * (N:ℝ)^(12/5:ℝ) * V^(-4:ℝ))

/-- The equivalent negative-sign form consumed by the project's detector
polynomials. Its proof is coefficient conjugation, not an additional analytic
assumption. -/
def GuthMaynardLargeValuesNeg : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∃ (C T₀ : ℝ), 0 < C ∧ 1 ≤ T₀ ∧
    ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      0 < N → T₀ ≤ T → 0 < V →
      (∀ n, ‖b n‖ ≤ 1) →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖dirichletPoly N b t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N:ℝ)^2 * V^(-2:ℝ) + (N:ℝ)^(18/5:ℝ) * V^(-4:ℝ) + T * (N:ℝ)^(12/5:ℝ) * V^(-4:ℝ))

theorem guthMaynardLargeValues_neg
    (hLargeValues : GuthMaynardLargeValues) : GuthMaynardLargeValuesNeg := by
  intro ε hε
  obtain ⟨C, T₀, hC, hT₀, hLarge⟩ := hLargeValues ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N V T b W hN hT hV hb hSeparated hInterval hValues
  apply hLarge N V T (conjugateCoeffs b) W hN hT hV
  · intro n
    rw [norm_conjugateCoeffs]
    exact hb n
  · exact hSeparated
  · exact hInterval
  · intro t ht
    rw [norm_sourceDirichletPoly_conjugateCoeffs]
    exact hValues t ht


