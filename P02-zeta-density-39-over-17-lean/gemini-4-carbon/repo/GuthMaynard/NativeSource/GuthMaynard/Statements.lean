module
public import GuthMaynard.NativeSource.GuthMaynard.Separated
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial

@[expose] public section

open Complex Finset

namespace GuthMaynard.NativeMoment

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
    (hLargeValues : GuthMaynardLargeValues) : GuthMaynardLargeValuesNeg :=
  fun ε hε =>
    let ⟨C, T₀, hC, hT₀, hLarge⟩ := hLargeValues ε hε
    ⟨C, T₀, hC, hT₀, fun N V T b W hN hT hV hb hSeparated hInterval hValues =>
      hLarge N V T (conjugateCoeffs b) W hN hT hV
        (fun n => by rw [norm_conjugateCoeffs]; exact hb n)
        hSeparated hInterval
        (fun t ht => by rw [norm_sourceDirichletPoly_conjugateCoeffs]; exact hValues t ht)⟩

end GuthMaynard.NativeMoment
