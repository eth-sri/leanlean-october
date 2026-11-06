module
public import GuthMaynard.NativeSource.GuthMaynard.FiniteDensityTransfer
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalPowering
import WeylPort.Analytic.RealLaplace

public section

open Complex Finset Set

namespace GuthMaynard.NativeMoment

/-- One factorization constant works simultaneously for every positive power
`k ≤ B`.  This finite-uniform form is required when the power is selected
from a `T`-dependent logarithmic scale inside an epsilon-power proof. -/
theorem powered_unit_block_large_values_bound_bounded_uniform
    (B : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k N : ℕ) (a : ℕ → ℂ) (sigma H L : ℝ) (W : Finset ℝ),
        0 < k → k ≤ B → 0 < N → 0 ≤ sigma → 1 ≤ H → 0 < L →
        (∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          L ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(sigma + I * t))‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let V := ((((N ^ k : ℕ) : ℝ) ^ sigma * L ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k a sigma C eta) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / V ^ 2 +
                H * min ((Q : ℝ) / V ^ 2)
                  ((Q : ℝ) ^ 4 / V ^ 6)) := by
  have hEach : ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) (a : ℕ → ℂ),
        (∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) →
        ∀ m : ℕ, 0 < m →
          ‖finitePowCoeff N k a m‖ ≤ c * (m : ℝ) ^ eta :=
    fun k => finitePowCoeff_bound_uniform k eta heta
  choose c hc hCoeff using hEach
  let C : ℝ := 1 + ∑ k ∈ Finset.range (B + 1), c k
  have hC : 0 < C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ k ∈ Finset.range (B + 1), c k := by
      exact Finset.sum_nonneg fun k _ => (hc k).le
    linarith
  have hCOne : 1 ≤ C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ k ∈ Finset.range (B + 1), c k :=
      Finset.sum_nonneg fun k _ => (hc k).le
    linarith
  have hcC : ∀ {k : ℕ}, k ≤ B → c k ≤ C := by
    intro k hkB
    have hkMem : k ∈ Finset.range (B + 1) := Finset.mem_range.mpr (by omega)
    have hsingle : c k ≤ ∑ j ∈ Finset.range (B + 1), c j :=
      Finset.single_le_sum (fun j _ => (hc j).le) hkMem
    dsimp only [C]
    linarith
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  pm_505 C hCOne K hK
  intro k N a sigma H L W hk hkB hN hsigma hH hL ha hSep hBase hLarge
  have hCoeffC : ∀ m : ℕ, 0 < m →
      ‖finitePowCoeff N k a m‖ ≤ C * (m : ℝ) ^ eta := by
    intro m hm
    exact (hCoeff k N a ha m hm).trans
      (mul_le_mul_of_nonneg_right (hcC hkB) (Real.rpow_nonneg (by positivity) _))
  have hDenom : 0 < C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta := by
    pm_964 hUpper N hN
    pm_8779 hC
  obtain ⟨r, hr, W', hWsub, hCard, hLarge'⟩ :=
    extract_normalized_finite_powered_block N k a sigma C eta L W
      hN hk hL.le hDenom hLarge
  pm_6009
  let V := ((((N ^ k : ℕ) : ℝ) ^ sigma * L ^ k /
      (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ eta)) / k)
  have hQ : 0 < Q := mul_pos (pow_pos (by omega) r) (pow_pos hN k)
  pm_4838
  have hWideMem : ∀ m ∈ dyadicInterval Q,
      m ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
    pm_4840 Finset.Ioc
    · have hrlt : r < k := Finset.mem_range.mp hr
      pm_4934 hrOne r k
      have hpow : 2 ^ (r + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hrOne
      pm_4839 hQtwice
  have hNorm : ∀ m ∈ dyadicInterval Q,
      ‖normalizedFinitePoweredCoeffs N k a sigma C eta m‖ ≤ 1 := by
    intro m hm
    have hmWide := hWideMem m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one N k m a sigma C eta
      hN hsigma hC heta hmWide (hCoeffC m (by
        have hmData := Finset.mem_Ioc.mp hmWide
        omega))
  pm_5008 hWsub H
  have hMHH' := hMHH Q H V W'
    (normalizedFinitePoweredCoeffs N k a sigma C eta)
    hQ hH hV hNorm hSep' hBase' (by
      intro t ht
      simpa only [Q, V] using hLarge' t ht)
  pm_505 r hr W' hWsub
  dsimp only
  exact ⟨hCard, hSep', hBase', by simpa only [Q, V] using hLarge',
    by simpa only [Q, V] using hMHH'⟩

/-- Bounded-power uniform form for the actual sharp zeta--Möbius detector.
All constants precede the `T`-dependent power selected by the endpoint scale
reduction. -/
theorem actual_typeII_powered_mhh_bounded_uniform_native
    (B : ℕ) (η₀ η : ℝ) (hη₀ : 0 < η₀) (hη : 0 < η) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k A X N : ℕ) (σ H L : ℝ) (W : Finset ℝ),
        0 < k → k ≤ B → 0 < N → 0 ≤ σ → 1 ≤ H → 0 < L →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          L ≤ ‖dirichletPoly N (sharpMollifiedLineCoeff A X σ) t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let D := C₀ * (2 * N : ℝ) ^ η₀ * (N : ℝ) ^ (-σ)
          let Q := 2 ^ r * N ^ k
          let V := (((L / D) ^ k /
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', V ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀)
                0 C η) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / V ^ 2 +
                H * min ((Q : ℝ) / V ^ 2)
                  ((Q : ℝ) ^ 4 / V ^ 6)) := by
  pm_98 Craw hCraw hCoeffRaw sharpMollifiedCoeff_bound η₀ hη₀
  let C₀ : ℝ := max 1 Craw
  pm_4884 hC₀One C₀
  have hCrawC₀ : Craw ≤ C₀ := le_max_right _ _
  have hC₀ : 0 < C₀ := zero_lt_one.trans_le hC₀One
  have hCoeff : ∀ (A X n : ℕ), 0 < n →
      ‖sharpMollifiedCoeff A X n‖ ≤ C₀ * (n : ℝ) ^ η₀ := by
    intro A X n hn
    exact (hCoeffRaw A X n hn).trans
      (mul_le_mul_of_nonneg_right hCrawC₀ (Real.rpow_nonneg (by positivity) _))
  pm_351 C hC K hK hPowered powered_unit_block_large_values_bound_bounded_uniform B η hη
  refine ⟨C₀, hC₀One, C, hC, K, hK, ?_⟩
  intro k A X N σ H L W hk hkB hN hσ hH hL hSep hBase hLarge
  pm_4841 η₀
  let a : ℕ → ℂ := normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀
  pm_116 hD D
  have ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one
      A X N n σ η₀ C₀ hN hσ hη₀.le hC₀
        (fun m hm => hCoeff A X m hm) hn
  have hSeries : ∀ t ∈ W,
      L / D ≤ ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(0 + I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            a n * (n : ℂ) ^ (-(0 + I * t)) =
          dirichletPoly N a t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      simp only [zero_add]
      congr 2
      ring
    rw [hEq]
    change L / D ≤
      ‖dirichletPoly N
        (normalizedSharpMollifiedLineCoeff A X N σ η₀ C₀) t‖
    rw [dirichletPoly_normalizedSharpMollifiedLineCoeff,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (hLarge t ht) hD.le
  obtain ⟨r, hr, W', hW', hCard, hSep', hBase', hLarge', hBound⟩ :=
    hPowered k N a 0 H (L / D) W hk hkB hN (by norm_num) hH
      (div_pos hL hD) ha hSep hBase hSeries
  pm_505 r hr W' hW'
  simpa only [D, a, Real.rpow_zero, one_mul] using
    And.intro hCard (And.intro hSep' (And.intro hBase'
      (And.intro hLarge' hBound)))

end GuthMaynard.NativeMoment
