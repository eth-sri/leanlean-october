module

public import ThreeSumApsp.TimeClaims.Sec3.Theorem19
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.RealParameters

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

def ThinClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ ε →
      T N D w u ≤ C * (preBound31 γ N D + (w : ℝ) * queryBound31 q D)

def LopClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), M.lopDetect Td ∧
    ∀ n D w : ℕ, 1 ≤ n → 1 ≤ D → (D : ℝ) ≤ (n : ℝ) ^ ε →
      Td n D w ≤ C * (preBound31 γ n D + (w : ℝ) * queryBound31 q D)

def HostBound (M : DetTimeModel) (MM : ℕ → ℝ) (D g Dc : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ 4 * (n : ℝ) * (g n : ℝ) *
            (T n (Dc n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
          C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

def ExplicitFrom (M : DetTimeModel) (δ : ℝ) (e : ℕ) : Prop :=
  ∃ (n₀ : ℕ) (K : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧
    ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))

theorem one_le_queryBound31 {D₀ : ℕ} {q : ℝ} (hD : 1 ≤ D₀) (hq : 0 ≤ q) :
    1 ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hDR hq) (by linarith [Real.log_nonneg hDR])

end ImprovedExponents
