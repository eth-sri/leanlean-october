module

public import AnalyticESC.Main.LocalDimension
set_option hygiene false
local notation "𝖁" => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
local notation "𝖀" => p i
local notation "𝖋" => φ i


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

namespace AnalyticESC
variable (g : ℝ → ℝ)


open Set Metric Filter Topology MeasureTheory

/-- Division with a proof that the denominator is nonzero. -/
noncomputable def divide (a b : ℝ) (_hb : b ≠ 0) : ℝ := a / b

/-- The scales `0 < r < 1`, on which `log r` is nonzero. -/
abbrev Scale := {r : ℝ // 0 < r ∧ r < 1}

/-- Scales tending to zero from above. -/
def scaleZero : Filter Scale := comap Subtype.val (𝓝[>] (0 : ℝ))

/-- The logarithmic ratio at a scale in `(0,1)`. -/
noncomputable def logRatio (a : ℝ) (r : Scale) : ℝ :=
  divide (Real.log a) (Real.log r) (Real.log_neg r.2.1 r.2.2).ne

/-! ### Rapaport's setting: real analytic IFSs on `I` -/

/-- `φ_u = φ_{u₁} ∘ ⋯ ∘ φ_{uₙ}` for real maps and a finite word `u`, with `φ_∅ = id`. -/
def realComp (φ : Fin N → ℝ → ℝ) (u : 𝔚 N) : ℝ → ℝ :=
  u.foldr (fun i g => φ i ∘ g) id

/-- The hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3: `φ_i(I) ⊆ I`, each `φ_i` is real
analytic on a neighbourhood of each point of `I`, `0 < |φ_i'(x)| < 1` for `x ∈ I`, the maps have no
common fixed point in `I`, and the system is exponentially separated: there is `c > 0` such that
for infinitely many `n`, `sup_{x ∈ I} |φ_u(x) - φ_v(x)| ≥ c^n` for all distinct `u, v` of length
`n`. -/
structure RapaportHyp (φ : Fin N → ℝ → ℝ) : Prop where
  mapsTo : ∀ i, MapsTo 𝖋 I I
  analytic : ∀ i, AnalyticOnNhd ℝ 𝖋 I
  deriv_pos : ∀ i, Ɐ 0 < |deriv 𝖋 x|
  deriv_lt_one : ∀ i, Ɐ |deriv 𝖋 x| < 1
  no_common_fixed_point : ¬ ∃ x ∈ I, ∀ i, φ i x = x
  exp_separated : ∃ c > 0, ∃ᶠ n in atTop, ∀ u v : Fin n → Fin N, u ≠ v →
    c ^ n ≤ ⨆ x : I, |realComp φ (List.ofFn u) x - realComp φ (List.ofFn v) x|

/-- Rapaport's Theorem 1.2, with the exact dimensionality of Feng and Hu: for a positive
probability vector `p`, the self-conformal measure `μ = ∑_i p_i φ_i μ` on `I` satisfies
`lim_{δ → 0} log μ(B(x,δ)) / log δ = min{1, H(p)/χ}` for `μ`-almost every `x`, where
`H(p) = -∑ p_i log p_i` and `χ = -∑ p_i ∫ log|φ_i'| dμ`. -/
def RapaportMeasureStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ p : Fin N → ℝ, (∀ i, 0 < p i) → ∑ i, p i = 1 →
    ∀ μ, IsProbabilityMeasure μ → μ Iᶜ = 0 →
      μ = ∑ i, ENNReal.ofReal 𝖀 • μ.map 𝖋 →
      ∀ hχ,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (-∑ i, p i * Real.log 𝖀)
          (-∑ i, p i * ∫ y, Real.log |deriv 𝖋 y| ∂μ) hχ)))

/-- Rapaport's Corollary 1.3: the attractor `K`, the nonempty compact set `K ⊆ I` with
`K = ⋃_i φ_i(K)`, has Hausdorff dimension `min{1, s(Φ)}`, where `s(Φ)` is the zero of the pressure
`P(t) = lim_n (1/n) log ∑_{u ∈ Σ_n} (sup_{x ∈ I} |φ_u'(x)|)^t`. -/
def RapaportSetStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ K : Set ℝ, K.Nonempty → IsCompact K → K ⊆ I → K = ⋃ i, φ i '' K →
    ∀ s, Tendsto (fun n => divide (Real.log (∑ u : Fin (n + 1) → Fin N,
        (⨆ x : I, |deriv (realComp φ (List.ofFn u)) x|) ^ s)) ((n + 1 : ℕ) : ℝ)
        𝖁) atTop (𝓝 0) →
      dimH K = ENNReal.ofReal (min 1 s)

/-! ### Gibbs measures -/

/-- `ν` is a Gibbs measure for the potential `φ` on `Σ = (Fin N)^ℕ` in Bowen's sense: there are
`c₁, c₂ > 0` and `P` with `c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + ∑_{k<m} φ(σ^k x)) ≤ c₂` for every
`x ∈ Σ` and `m ≥ 0`, where `σ` is the left shift. -/
def IsGibbsMeasure (φ : 𝔖 N → ℝ) (ν : Measure 𝔖 N) : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∃ P, ∀ (x : 𝔖 N) (m : ℕ),
    c₁ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k))) ≤
        ν.real {y | ∀ i < m, y i = x i} ∧
      ν.real {y | ∀ i < m, y i = x i} ≤
        c₂ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k)))

/-- Bowen's Theorem 1.4 for the one-sided full shift on `N ≥ 1` symbols: a potential `φ` with
`sup{|φ(x) - φ(y)| : x_i = y_i for i < k} ≤ b α^k` for all `k`, where `b > 0` and `0 < α < 1`, has a
Gibbs measure. Bowen states the theorem for two-sided mixing subshifts of finite type; a potential
of the coordinates `i ≥ 0` has the same variations, and the image of the two-sided Gibbs measure
under `x ↦ (x_i)_{i ≥ 0}` has the same cylinder measures. -/
def BowenGibbsStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (φ : 𝔖 N → ℝ) {b α : ℝ}, 0 < b → 0 < α → α < 1 →
    (∀ (k : ℕ) (x y : 𝔖 N), (∀ i < k, x i = y i) → |φ x - φ y| ≤ b * α ^ k) →
    ∃ ν, IsProbabilityMeasure ν ∧ IsGibbsMeasure φ ν

/-! ### Entropy, Lyapunov exponent and self-conformal measures -/

/-- The entropy `H(p) = -∑_i p_i log p_i` of a probability vector. -/
noncomputable def entropy (p : Fin N → ℝ) : ℝ := -∑ i, p i * Real.log 𝖀

/-- `p` is a positive probability vector. -/
def IsProbVec (p : Fin N → ℝ) : Prop := (∀ i, 0 < p i) ∧ ∑ i, p i = 1

namespace IFS

variable (Φ : IFS N ε) (p : Fin N → ℝ)

/-- The real map `x ↦ f_i(x)` of the system. -/
def realMap (i : Fin N) (x : ℝ) : ℝ := (Φ.f i x).re

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1, for the measure
`μ`. -/
noncomputable def lyapunov (μ : Measure ℝ) : ℝ :=
  -∑ i, p i * ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2): a Borel probability measure on `I`
with `μ = ∑_i p_i μ ∘ f_i⁻¹`. -/
def IsSelfConformal (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Iᶜ = 0 ∧ μ = ∑ i, ENNReal.ofReal 𝖀 • μ.map (Φ.realMap i)

/-- Equality in (1.6): the pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` has a unique zero
`s(Φ)`, the attractor has Hausdorff dimension `min{1, s(Φ)}`, and for every positive probability
vector `p` the self-conformal measure `μ_p` has local dimension `min{1, H(p)/χ}` at `μ_p`-almost
every point. -/
def DimEquality : Prop :=
  (∃ s, Φ.PressureZero s ∧
      dimH Φ.attractor = ENNReal.ofReal (min 1 s)) ∧
    ∀ p, IsProbVec p → ∀ μ, Φ.IsSelfConformal p μ →
      ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
        (𝓝 (min 1 (entropy p / Φ.lyapunov p μ)))

/-- The potential `φ_s(ω) = s log|f'_{ω₀}(π(σω))|` on `Σ`, where `σ` is the left shift. -/
noncomputable def potential (s : ℝ) (ω : 𝔖 N) : ℝ :=
  s * Real.log ‖deriv (Φ.f (ω 0)) (Φ.natProj fun i => ω (i + 1))‖

end IFS

/-- Restricting to scales in `(0,1)` does not change the filter at zero from above. -/
theorem scaleZero_map : map (fun r : Scale => (r : ℝ)) scaleZero = 𝓝[>] 0 := by
  apply map_comap_of_mem
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one)] with r hr
  simp_all

theorem scale_tendsto_iff l :
    Tendsto (fun r : Scale => g r) scaleZero l ↔ Tendsto g (𝓝[>] 0) l := by
  rw [← scaleZero_map, tendsto_map'_iff]
  rfl

theorem scale_liminf :
    liminf (fun r : Scale => g r) scaleZero = liminf g (𝓝[>] 0) := by
  rw [← scaleZero_map]
  rfl

theorem positive_length_tendsto_iff (g : ℕ → ℝ) :
    Tendsto (fun n => divide (g (n + 1)) ((n + 1 : ℕ) : ℝ)
      𝖁) atTop (𝓝 0) ↔
    Tendsto (fun n => g n / n) atTop (𝓝 0) := by
  simpa only [divide] using
    (tendsto_add_atTop_iff_nat (f := fun n => g n / n) 1)

end AnalyticESC
