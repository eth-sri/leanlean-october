module

public import AnalyticESC.Main.LocalDimension

@[expose] public section

/-!
# Dimension theory: vocabulary and cited results

The vocabulary of Section 1.2.1 and of the natural measure of the polynomial example
in Section 1.2.2: entropy, Lyapunov exponent, self-conformal measures, the equality in (1.6),
the potential `s log|f'_{ω₀}(π(σω))|` and its Gibbs measures.

The three results cited from the literature are recorded as propositions, which the theorems of
the library take as hypotheses. `Challenge.lean` states them identically, as hypotheses of the
audited theorems that use them.

* `BowenGibbsStatement`: R. Bowen, *Equilibrium states and the ergodic theory of Anosov
  diffeomorphisms*, Lecture Notes in Mathematics 470, Springer, 1975, Theorem 1.4, for the
  one-sided full shift.
* `RapaportMeasureStatement`: A. Rapaport, *Dimension of self-conformal measures associated to an
  exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, with the exact
  dimensionality of self-conformal measures of D.-J. Feng and H. Hu, *Dimension theory of iterated
  function systems*, Comm. Pure Appl. Math. 62 (2009).
* `RapaportSetStatement`: the same paper of Rapaport, Corollary 1.3.

Rapaport's statements are for real maps of `I = [0,1]`; `realComp` is the composition of real
maps and `RapaportHyp` collects his hypotheses.
-/

namespace Challenge

open Set Metric
open MeasureTheory Filter Topology

/-- Division with a proof that the denominator is nonzero. -/
noncomputable def divide (a b : ℝ) (_hb : b ≠ 0) : ℝ := a / b

/-- The scales `0 < r < 1`, on which `log r` is nonzero. -/
abbrev Scale := {r : ℝ // 0 < r ∧ r < 1}

/-- Scales tending to zero from above. -/
def scaleZero : Filter Scale := comap Subtype.val (𝓝[>] (0 : ℝ))

/-- The logarithmic ratio at a scale in `(0,1)`. -/
noncomputable def logRatio (a : ℝ) (r : Scale) : ℝ :=
  divide (Real.log a) (Real.log r) (Real.log_neg r.2.1 r.2.2).ne

variable {N : ℕ}

/-- The sum `∑_{w ∈ Σ_n} (sup_{x ∈ I} |f_w'(x)|)^t`. -/
noncomputable def pressureSum (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, (⨆ x : I, ‖deriv (comp f (List.ofFn w)) x‖) ^ t

/-- The normalized logarithmic pressure sum, at positive word length `n + 1`. -/
noncomputable def pressureRatio (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  divide (Real.log (pressureSum f t (n + 1))) ((n + 1 : ℕ) : ℝ)
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))

/-- The entropy `H(p) = -∑_i p_i log p_i` of a probability vector. -/
noncomputable def entropy (p : Fin N → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- `p` is a positive probability vector. -/
def IsProbVec (p : Fin N → ℝ) : Prop := (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1. -/
noncomputable def lyapunov (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : ℝ :=
  -∑ i, p i * ∫ x, Real.log |deriv (fun y : ℝ => (f i y).re) x| ∂μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2). -/
def IsSelfConformal (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Iᶜ = 0 ∧
    μ = ∑ i, ENNReal.ofReal (p i) • μ.map (fun x : ℝ => (f i x).re)

/-- The potential `φ_s(ω) = s log|f'_{ω₀}(π(σω))|` on `Σ = (Fin N)^ℕ`. -/
noncomputable def potential (f : Fin N → ℂ → ℂ) (s : ℝ) (ω : ℕ → Fin N) : ℝ :=
  s * Real.log ‖deriv (f (ω 0)) (natProj f fun i => ω (i + 1))‖

/-- `ν` is a Gibbs measure for the potential `φ` on `Σ = (Fin N)^ℕ` in Bowen's sense: there are
`c₁, c₂ > 0` and `P` with `c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + ∑_{k<m} φ(σ^k x)) ≤ c₂` for every
`x ∈ Σ` and `m ≥ 0`, where `σ` is the left shift. -/
def IsGibbsMeasure (φ : (ℕ → Fin N) → ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∃ P : ℝ, ∀ (x : ℕ → Fin N) (m : ℕ),
    c₁ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k))) ≤
        ν.real {y | ∀ i < m, y i = x i} ∧
      ν.real {y | ∀ i < m, y i = x i} ≤
        c₂ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k)))

/-- `φ_u = φ_{u₁} ∘ ⋯ ∘ φ_{uₙ}` for real maps and a finite word `u`, with `φ_∅ = id`. -/
def realComp (φ : Fin N → ℝ → ℝ) (u : List (Fin N)) : ℝ → ℝ :=
  u.foldr (fun i g => φ i ∘ g) id

/-- The hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3. -/
structure RapaportHyp (φ : Fin N → ℝ → ℝ) : Prop where
  mapsTo : ∀ i, MapsTo (φ i) I I
  analytic : ∀ i, AnalyticOnNhd ℝ (φ i) I
  deriv_pos : ∀ i, ∀ x ∈ I, 0 < |deriv (φ i) x|
  deriv_lt_one : ∀ i, ∀ x ∈ I, |deriv (φ i) x| < 1
  no_common_fixed_point : ¬ ∃ x ∈ I, ∀ i, φ i x = x
  exp_separated : ∃ c > 0, ∃ᶠ n in atTop, ∀ u v : Fin n → Fin N, u ≠ v →
    c ^ n ≤ ⨆ x : I, |realComp φ (List.ofFn u) x - realComp φ (List.ofFn v) x|

/-- Bowen's Theorem 1.4 for the one-sided full shift on `N ≥ 1` symbols. -/
def BowenGibbsStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (φ : (ℕ → Fin N) → ℝ) {b α : ℝ}, 0 < b → 0 < α → α < 1 →
    (∀ (k : ℕ) (x y : ℕ → Fin N), (∀ i < k, x i = y i) → |φ x - φ y| ≤ b * α ^ k) →
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure φ ν

/-- Rapaport's Theorem 1.2, with the exact dimensionality of Feng and Hu. -/
def RapaportMeasureStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ p : Fin N → ℝ, (∀ i, 0 < p i) → ∑ i, p i = 1 →
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ Iᶜ = 0 →
      μ = ∑ i, ENNReal.ofReal (p i) • μ.map (φ i) →
      ∀ hχ : (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) ≠ 0,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (-∑ i, p i * Real.log (p i))
          (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) hχ)))

/-- Rapaport's Corollary 1.3. -/
def RapaportSetStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ K : Set ℝ, K.Nonempty → IsCompact K → K ⊆ I → K = ⋃ i, φ i '' K →
    ∀ s : ℝ, Tendsto (fun n : ℕ => divide (Real.log (∑ u : Fin (n + 1) → Fin N,
        (⨆ x : I, |deriv (realComp φ (List.ofFn u)) x|) ^ s)) ((n + 1 : ℕ) : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) atTop (𝓝 0) →
      dimH K = ENNReal.ofReal (min 1 s)

end Challenge

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory Challenge
export Challenge (divide Scale scaleZero logRatio entropy IsProbVec IsGibbsMeasure realComp
  RapaportHyp BowenGibbsStatement RapaportMeasureStatement RapaportSetStatement)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1. -/
noncomputable abbrev lyapunov (p : Fin N → ℝ) (μ : Measure ℝ) : ℝ := Challenge.lyapunov Φ.f p μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2). -/
abbrev IsSelfConformal (p : Fin N → ℝ) (μ : Measure ℝ) : Prop := Challenge.IsSelfConformal Φ.f p μ

/-- Equality in (1.6). -/
def DimEquality : Prop :=
  (∃ s : ℝ, (∀ t, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s) ∧
      dimH Φ.attractor = ENNReal.ofReal (min 1 s)) ∧
    ∀ p : Fin N → ℝ, IsProbVec p → ∀ μ : Measure ℝ, Φ.IsSelfConformal p μ →
      ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
        (𝓝 (min 1 (entropy p / Φ.lyapunov p μ)))

/-- The potential `φ_s(ω) = s log|f'_{ω₀}(π(σω))|` on `Σ`, where `σ` is the left shift. -/
noncomputable abbrev potential (s : ℝ) (ω : ℕ → Fin N) : ℝ := Challenge.potential Φ.f s ω

end IFS

/-- Restricting to scales in `(0,1)` does not change the filter at zero from above. -/
theorem scaleZero_map : map (fun r : Scale => (r : ℝ)) scaleZero = 𝓝[>] (0 : ℝ) :=
  map_comap_of_mem (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun r hr => ⟨⟨r, hr⟩, rfl⟩)

theorem scale_tendsto_iff (g : ℝ → ℝ) (l : Filter ℝ) :
    Tendsto (fun r : Scale => g r) scaleZero l ↔ Tendsto g (𝓝[>] 0) l := by
  rw [← scaleZero_map, tendsto_map'_iff]; rfl

theorem scale_liminf (g : ℝ → ℝ) :
    liminf (fun r : Scale => g r) scaleZero = liminf g (𝓝[>] 0) := by
  rw [← scaleZero_map]; rfl

theorem positive_length_tendsto_iff (g : ℕ → ℝ) :
    Tendsto (fun n : ℕ => divide (g (n + 1)) ((n + 1 : ℕ) : ℝ)
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) atTop (𝓝 0) ↔
    Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) := by
  simpa only [divide] using
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => g n / (n : ℝ)) (l := 𝓝 0) 1)

end AnalyticESC
