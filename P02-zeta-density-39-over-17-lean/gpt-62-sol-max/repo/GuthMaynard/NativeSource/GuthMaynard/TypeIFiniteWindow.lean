module
public import GuthMaynard.NativeSource.GuthMaynard.FiniteScaleAssembly
public import GuthMaynard.NativeSource.GuthMaynard.TypeIFiniteEstimates
public import GuthMaynard.NativeSource.GuthMaynard.FiniteDensityEndpoint

@[expose] public section

open Finset Set

namespace GuthMaynard.NativeMoment

/-- The height exponent of `T` relative to a positive finite block `N`.
This is the convention used by `classicalMHHExponent`: `T = N ^ τ`. -/
noncomputable def typeILogarithmicScale (T : ℝ) (N : ℕ) : ℝ :=
  Real.logb N T

/-- Exact conversion from the logarithmic scale back to the physical
height. -/
theorem rpow_typeILogarithmicScale_eq
    {T : ℝ} {N : ℕ} (hT : 0 < T) (hN : 1 < N) :
    (N : ℝ) ^ typeILogarithmicScale T N = T := by
  exact Real.rpow_logb (by exact_mod_cast (show 0 < N by omega))
    (by exact_mod_cast hN.ne') hT

/-- The source normalization for a Type-I block of length `N`.  Multiplying
the coefficients `n⁻σ` by `N^σ` makes them uniformly bounded by one on
`(N,2N]`, while preserving coefficients independent of the ordinate. -/
noncomputable def normalizedClassicalTypeICoeff
    (C N : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (((N : ℝ) ^ σ : ℝ) : ℂ) * classicalZetaLongLineCoeff C σ n

/-- The normalized Type-I coefficients are genuinely unit bounded on the
dyadic block.  This is the normalization needed for the MHH exponent
`classicalMHHExponent σ τ`; applying MHH directly to `n⁻σ` at the unscaled
threshold loses the decisive factor `N^(2σ)`. -/
theorem norm_normalizedClassicalTypeICoeff_le_one
    (C N : ℕ) (σ : ℝ) (hN : 0 < N) (hσ : 0 ≤ σ) :
    ∀ n ∈ dyadicInterval N, ‖normalizedClassicalTypeICoeff C N σ n‖ ≤ 1 := by
  intro n hn
  have hnData := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
  unfold normalizedClassicalTypeICoeff classicalZetaLongLineCoeff
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
      Complex.norm_natCast_cpow_of_pos hnPos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by exact_mod_cast hnPos.le),
      ← div_eq_mul_inv, ← Real.div_rpow (Nat.cast_nonneg N)
        (by exact_mod_cast hnPos.le)]
    apply Real.rpow_le_one
    · positivity
    · exact (div_le_one (by exact_mod_cast hnPos)).2 (by exact_mod_cast hnData.1.le)
    · exact hσ
  · simp

/-- Normalizing the coefficients scales the whole finite Dirichlet
polynomial by the positive real factor `N^σ`. -/
theorem dirichletPoly_normalizedClassicalTypeICoeff
    (C N : ℕ) (σ t : ℝ) :
    dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t =
      (((N : ℝ) ^ σ : ℝ) : ℂ) *
        dirichletPoly N (classicalZetaLongLineCoeff C σ) t := by
  unfold dirichletPoly normalizedClassicalTypeICoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A large value of the actual sharp Type-I polynomial becomes a large
value at threshold `N^σ V` after source normalization. -/
theorem normalizedClassicalTypeICoeff_large
    (C N : ℕ) (σ t V : ℝ) (hN : 0 < N) (hLarge :
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    (N : ℝ) ^ σ * V ≤
      ‖dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t‖ := by
  rw [dirichletPoly_normalizedClassicalTypeICoeff, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact mul_le_mul_of_nonneg_left hLarge
    (Real.rpow_nonneg (by exact_mod_cast hN.le) _)

/-!
# Finite Type-I window resolution

The production dichotomy returns an actual sharp finite Dirichlet block,
not an unbounded Poisson series.  Its coefficients are independent of the
ordinate.  The source MHH exponent nevertheless requires the additional
normalization by `N^σ`; merely observing that `n⁻σ` is bounded by one gives a
strictly weaker estimate.  This module proves that normalization, the
epsilon-absorbed direct route, exact powered extraction, the weighted Weyl
route, and the endpoint package.  It stops before the later
multiplicity-weighted branch-to-slab reduction.
-/

/-- Unrestricted MHH applied after the indispensable `N^σ` source
normalization.  The conclusion retains the harmonic factor, but its
threshold is the correctly normalized `N^σ V`; this is the form consumed
by the endpoint branch-to-slab theorem. -/
theorem actual_typeI_normalized_dichotomy_witness_mhh_native :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C N : ℕ) (σ δ T V : ℝ) (W : Finset ℝ),
        0 ≤ σ → 0 < N → 2 ≤ T → 0 < V →
        T ^ δ ≤ T / 2 → IsSeparated 1 W →
        (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        (W.card : ℝ) ≤
          K * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / ((N : ℝ) ^ σ * V) ^ 2 +
              (3 * T) * min
                ((N : ℝ) / ((N : ℝ) ^ σ * V) ^ 2)
                ((N : ℝ) ^ 4 / ((N : ℝ) ^ σ * V) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨K, hK, ?_⟩
  intro C N σ δ T V W hσ hN hT hV hShift hSep hInterval hLarge
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    rw [Set.mem_Icc]
    have htRange := hInterval t ht
    constructor
    · calc
        (0 : ℝ) ≤ T / 2 := by linarith
        _ ≤ T - T ^ δ := by linarith
        _ ≤ t := htRange.1
    · calc
        t ≤ 2 * T + T ^ δ := htRange.2
        _ ≤ 3 * T := by linarith
  have hThreshold : 0 < (N : ℝ) ^ σ * V := by positivity
  exact hMHH N (3 * T) ((N : ℝ) ^ σ * V) W
    (normalizedClassicalTypeICoeff C N σ) hN (by linarith) hThreshold
    (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
    hSep hBase (fun t ht =>
      normalizedClassicalTypeICoeff_large C N σ t V hN (hLarge t ht))

/-- Bounded-power uniform form of the actual Type-I powered route. -/
theorem powered_actual_typeI_block_large_values_bound_bounded_uniform
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 1 ≤ D ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k C N : ℕ) (σ H V : ℝ) (W : Finset ℝ),
        0 < k → k ≤ B → 0 < N → 0 ≤ σ → 1 ≤ H → 0 < V →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let L := (((N : ℝ) ^ σ * V) ^ k /
              (D * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', L ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedClassicalTypeICoeff C N σ) 0 D η) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / L ^ 2 +
                H * min ((Q : ℝ) / L ^ 2)
                  ((Q : ℝ) ^ 4 / L ^ 6)) := by
  obtain ⟨D, hD, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B η hη
  refine ⟨D, hD, K, hK, ?_⟩
  intro k C N σ H V W hk hkB hN hσ hH hV hSep hBase hLarge
  have hLargeNormalized : ∀ t ∈ W,
      (N : ℝ) ^ σ * V ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N),
          normalizedClassicalTypeICoeff C N σ n *
            (n : ℂ) ^ (-(0 + Complex.I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            normalizedClassicalTypeICoeff C N σ n *
              (n : ℂ) ^ (-(0 + Complex.I * t)) =
          dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      ring
    rw [hEq]
    exact normalizedClassicalTypeICoeff_large C N σ t V hN (hLarge t ht)
  obtain ⟨r, hr, W', hW', hCard, hSep', hBase', hLarge', hBound⟩ :=
    hPowered k N (normalizedClassicalTypeICoeff C N σ) 0 H
      ((N : ℝ) ^ σ * V) W hk hkB hN (by norm_num) hH (by positivity)
      (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
      hSep hBase hLargeNormalized
  refine ⟨r, hr, W', hW', hCard, hSep', hBase', ?_, ?_⟩
  · simpa only [Real.rpow_zero, one_mul] using hLarge'
  · simpa only [Real.rpow_zero, one_mul] using hBound

end GuthMaynard.NativeMoment
