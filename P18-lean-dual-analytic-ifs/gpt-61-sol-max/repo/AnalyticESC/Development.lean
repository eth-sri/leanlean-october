module
public import Mathlib
@[expose] public section
noncomputable section
set_option backward.proofsInPublic true
open Set Metric Filter Topology MeasureTheory Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AnalyticESC

/-- Holomorphic extensions and their real restrictions. -/
abbrev CMap := ℂ → ℂ
abbrev RMap := ℝ → ℝ
/-- Infinite addresses and finite blocks over an `N`-letter alphabet. -/
abbrev FWord (N : ℕ) := List (Fin N)
abbrev Address (N : ℕ) := ℕ → Fin N
abbrev Block (N n : ℕ) := Fin n → Fin N
abbrev WordPair (N n : ℕ) := Block N n × Block N n

end AnalyticESC

namespace Challenge


/-- The unit interval `I = [0,1]`. -/
abbrev I : Set ℝ := Icc 0 1

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := {z | ∃ x ∈ I, ‖z - (x : ℂ)‖ < δ}

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (nbhd (2 * ε))
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0
  re_mem_I : ∀ x ∈ I, (f x).re ∈ I
  mapsTo : ∀ z ∈ closure (nbhd ε), f z ∈ nbhd ε
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1

variable {N : ℕ}

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (f : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℂ → ℂ := w.foldr (fun i g => f i ∘ g) id

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
def supDist (f : Fin N → ℂ → ℂ) (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖comp f i x - comp f j x‖

/-- The strong exponential separation condition (Definition 1.2): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n` and all `n`. -/
def SESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- Nonvanishing of the derivatives at every finite orbit of a point of `I`. -/
def NonzeroDerivatives (f : Fin N → ℂ → ℂ) : Prop :=
  ∀ (i : Fin N) (w : List (Fin N)) (x : I), deriv (f i) (comp f w x) ≠ 0

/-- The distortion `f''/f'`. -/
def nonlin (g : ℂ → ℂ) (z : ℂ) (_h : deriv g z ≠ 0) : ℂ :=
  deriv (deriv g) z / deriv g z

/-- The dual natural projection `H_w` of (1.4) for a finite word `w`. The term with index `n`
(from `0`) is `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where `v` is the prefix of the first `n`
letters, `i` the next letter and `f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}`. -/
def dualProjFin (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : List (Fin N)) (x : I) : ℂ :=
  ∑ n : Fin w.length,
    nonlin (f (w.get n)) (comp f (w.take n).reverse x) (hd (w.get n) (w.take n).reverse x) *
      deriv (comp f (w.take n).reverse) x

/-- The dual natural projection `H_w` of (1.4) for an infinite word `w`. -/
def dualProjInf (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : ℕ → Fin N) (x : I) : ℂ :=
  ∑' n, nonlin (f (w n)) (comp f (List.ofFn fun k : Fin n => w k).reverse x)
    (hd (w n) (List.ofFn fun k : Fin n => w k).reverse x) *
      deriv (comp f (List.ofFn fun k : Fin n => w k).reverse) x

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
def cmax (ε : ℝ) (f : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (f i) z‖

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
def beta (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f) : ℝ :=
  ⨆ (x : I) (i : Fin N), ‖nonlin (f i) x (hd i [] x)‖

/-- The maps `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` of the example in
Section 1.2.2. -/
def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
def natProj (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) : ℝ :=
  Filter.limUnder Filter.atTop fun n => (comp f (List.ofFn fun k : Fin n => w k) 0).re

/-- The attractor `Λ = π(Σ)`. -/
def attractor (f : Fin N → ℂ → ℂ) : Set ℝ := range (natProj f)

/-- `g` is an analytic, invertible map on `[0,1]` (Definition 1.9): analytic on a neighbourhood
of each point of `[0,1]` and injective on `[0,1]`. -/
def IsAnalyticCoord (g : ℝ → ℝ) : Prop := AnalyticOnNhd ℝ g I ∧ InjOn g I

/-- The maps `F_j` of `[0,1]` are conjugated to a self-similar IFS (Definition 1.9): for an
analytic invertible `g`, `g ∘ F_j ∘ g⁻¹` is the similarity `y ↦ λ_j y + t_j` with
`λ_j ∈ (-1,1) \ {0}`, that is, `g(F_j(x)) = λ_j g(x) + t_j` on `[0,1]`. -/
def ConjSelfSimilar {M : ℕ} (F : Fin M → ℝ → ℝ) : Prop :=
  ∃ g, IsAnalyticCoord g ∧ ∃ lam t : Fin M → ℝ, ∀ j,
    lam j ≠ 0 ∧ |lam j| < 1 ∧ ∀ x ∈ I, g (F j x) = lam j * g x + t j

/-- The infinite word `w w w ⋯` for a nonempty finite word `w`. -/
def periodic {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) : ℕ → Fin N :=
  fun n => w ⟨n % m, Nat.mod_lt n hm⟩

/-- The `𝒞²` distance: the maximum over maps of the sum of the uniform distances
between their values, first derivatives and second derivatives on `[0,1]` (Section 1.1). -/
def d2 (f g : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ i,
    ((⨆ x : I, ‖f i x - g i x‖) + ⨆ x : I, ‖deriv (f i) x - deriv (g i) x‖) +
      ⨆ x : I, ‖deriv (deriv (f i)) x - deriv (deriv (g i)) x‖

/-- The space `𝔖_N` of Section 1.1: IFSs whose maps lie in `S^ω_ε(I)` for some `ε > 0`, which may
depend on the system. -/
def InUnionClass (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

section
/-- Division with a proof that the denominator is nonzero. -/
def divide (a b : ℝ) (_hb : b ≠ 0) : ℝ := a / b

/-- The scales `0 < r < 1`, on which `log r` is nonzero. -/
abbrev Scale := {r : ℝ // 0 < r ∧ r < 1}

/-- Scales tending to zero from above. -/
def scaleZero : Filter Scale := comap Subtype.val (𝓝[>] (0 : ℝ))

/-- The logarithmic ratio at a scale in `(0,1)`. -/
def logRatio (a : ℝ) (r : Scale) : ℝ :=
  divide (Real.log a) (Real.log r) (Real.log_neg r.2.1 r.2.2).ne

/-! ### Dimension theory (Sections 1.2.1 and 1.2.2) -/

/-- The exponential separation condition (ESC): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n`, for infinitely many
`n`. -/
def ESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- The sum `∑_{w ∈ Σ_n} (sup_{x ∈ I} |f_w'(x)|)^t`. The pressure is
`P(t) = lim_n log(pressureSum f t n) / n`; its zero is `s(Φ)` (Section 1.2.1). -/
def pressureSum (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, (⨆ x : I, ‖deriv (comp f (List.ofFn w)) x‖) ^ t

/-- The normalized logarithmic pressure sum, at positive word length `n + 1`. -/
def pressureRatio (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  divide (Real.log (pressureSum f t (n + 1))) ((n + 1 : ℕ) : ℝ)
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))

/-- The entropy `H(p) = -∑_i p_i log p_i` of a probability vector. -/
def entropy (p : Fin N → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- `p` is a positive probability vector. -/
def IsProbVec (p : Fin N → ℝ) : Prop := (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1, for the measure
`μ`, with the derivatives of the real maps `x ↦ f_i(x)`. -/
def lyapunov (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : ℝ :=
  -∑ i, p i * ∫ x, Real.log |deriv (fun y : ℝ => (f i y).re) x| ∂μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2): a Borel probability measure on
`[0,1]` with `μ = ∑_i p_i μ ∘ f_i⁻¹`. -/
def IsSelfConformal (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Iᶜ = 0 ∧ μ = ∑ i, ENNReal.ofReal (p i) • μ.map fun x : ℝ => (f i x).re

/-- Equality in (1.6): the pressure has a unique zero `s(Φ)`, the attractor has Hausdorff
dimension `min{1, s(Φ)}`, and for every positive probability vector `p` the self-conformal measure
`μ_p` has local dimension `min{1, H(p)/χ}` at `μ_p`-almost every point. -/
def DimEquality (f : Fin N → ℂ → ℂ) : Prop :=
  (∃ s : ℝ, (∀ t, Tendsto (pressureRatio f t) atTop (𝓝 0) ↔ t = s) ∧
      dimH (attractor f) = ENNReal.ofReal (min 1 s)) ∧
    ∀ p : Fin N → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal f p μ →
      ∀ hχ : lyapunov f p μ ≠ 0,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (entropy p) (lyapunov f p μ) hχ)))

/-- The potential `φ_s(ω) = s log|f'_{ω₀}(π(σω))|` on `Σ = (Fin N)^ℕ`, where `σ` is the left
shift. -/
def potential (f : Fin N → ℂ → ℂ) (s : ℝ) (ω : ℕ → Fin N) : ℝ :=
  s * Real.log ‖deriv (f (ω 0)) (natProj f fun i => ω (i + 1))‖

/-- `ν` is a Gibbs measure for the potential `φ` on `Σ = (Fin N)^ℕ` in Bowen's sense: there are
`c₁, c₂ > 0` and `P` with `c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + ∑_{k<m} φ(σ^k x)) ≤ c₂` for every
`x ∈ Σ` and `m ≥ 0`, where `σ` is the left shift. -/
def IsGibbsMeasure (φ : (ℕ → Fin N) → ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ c₁ > 0,
    ∃ c₂ > 0,
      ∃ P : ℝ,
        ∀ (x : ℕ → Fin N) (m : ℕ),
          c₁ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ fun i => x (i + k)) ≤ ν.real {y | ∀ i < m, y i = x i} ∧
            ν.real {y | ∀ i < m, y i = x i} ≤ c₂ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ fun i => x (i + k))

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2, where
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`. -/
def lqDim (μ : Measure ℝ) (q : ℝ) (hq : q - 1 ≠ 0) : ℝ :=
  divide (liminf (fun r : Scale =>
    logRatio (∑' k : ℤ, μ.real (Ico (k * (r : ℝ)) ((k + 1) * (r : ℝ))) ^ q) r)
    scaleZero) (q - 1) hq

/-! ### Cited results

The results that the paper cites are stated as in their sources and are explicit hypotheses of
the theorems that use them. Rapaport's results are stated, as in his paper, for real maps `φ_i`
of `I = [0,1]`. -/

/-- `φ_u = φ_{u₁} ∘ ⋯ ∘ φ_{uₙ}` for real maps and a finite word `u`, with `φ_∅ = id`. -/
def realComp (φ : Fin N → ℝ → ℝ) (u : List (Fin N)) : ℝ → ℝ := u.foldr (fun i g => φ i ∘ g) id

/-- The hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3: `φ_i(I) ⊆ I`, each `φ_i` is real
analytic on a neighbourhood of each point of `I`, `0 < |φ_i'(x)| < 1` for `x ∈ I`, the maps have no
common fixed point in `I`, and the system is exponentially separated: there is `c > 0` such that
for infinitely many `n`, `sup_{x ∈ I} |φ_u(x) - φ_v(x)| ≥ c^n` for all distinct `u, v` of length
`n`. -/
structure RapaportHyp (φ : Fin N → ℝ → ℝ) : Prop where
  mapsTo : ∀ i, MapsTo (φ i) I I
  analytic : ∀ i, AnalyticOnNhd ℝ (φ i) I
  deriv_pos : ∀ i, ∀ x ∈ I, 0 < |deriv (φ i) x|
  deriv_lt_one : ∀ i, ∀ x ∈ I, |deriv (φ i) x| < 1
  no_common_fixed_point : ¬ ∃ x ∈ I, ∀ i, φ i x = x
  exp_separated : ∃ c > 0, ∃ᶠ n in atTop, ∀ u v : Fin n → Fin N, u ≠ v →
    c ^ n ≤ ⨆ x : I, |realComp φ (List.ofFn u) x - realComp φ (List.ofFn v) x|

/-- **Cited result.** R. Bowen, *Equilibrium states and the ergodic theory of Anosov
diffeomorphisms*, Lecture Notes in Mathematics 470, Springer, 1975, Theorem 1.4, for the one-sided
full shift on `N ≥ 1` symbols: a potential `φ` with
`sup{|φ(x) - φ(y)| : x_i = y_i for i < k} ≤ b α^k` for all `k`, where `b > 0` and `0 < α < 1`, has a
Gibbs measure. Bowen states the theorem for two-sided mixing subshifts of finite type; a potential
of the coordinates `i ≥ 0` has the same variations, and the image of the two-sided Gibbs measure
under `x ↦ (x_i)_{i ≥ 0}` has the same cylinder measures. -/
def BowenGibbsStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (φ : (ℕ → Fin N) → ℝ) {b α : ℝ}, 0 < b → 0 < α → α < 1 →
    (∀ (k : ℕ) (x y : ℕ → Fin N), (∀ i < k, x i = y i) → |φ x - φ y| ≤ b * α ^ k) →
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure φ ν

/-- **Cited result.** A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, together with the exact
dimensionality of self-conformal measures, D.-J. Feng and H. Hu, *Dimension theory of iterated
function systems*, Comm. Pure Appl. Math. 62 (2009): under `RapaportHyp`, for a positive
probability vector `p`, the self-conformal measure `μ = ∑_i p_i φ_i μ` on `I` satisfies
`lim_{δ → 0} log μ(B(x,δ)) / log δ = min{1, H(p)/χ}` for `μ`-almost every `x`, where
`H(p) = -∑ p_i log p_i` and `χ = -∑ p_i ∫ log|φ_i'| dμ`. -/
def RapaportMeasureStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ),
    RapaportHyp φ →
      ∀ p : Fin N → ℝ,
        (∀ i, 0 < p i) →
          ∑ i, p i = 1 →
            ∀ μ : Measure ℝ,
              IsProbabilityMeasure μ →
                μ Iᶜ = 0 →
                  μ = ∑ i, ENNReal.ofReal (p i) • μ.map (φ i) →
                    ∀ hχ : -∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ ≠ 0,
                      ∀ᵐ x ∂μ,
                        Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
                          (𝓝
                            (min 1
                              (divide (-∑ i, p i * Real.log (p i)) (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) hχ)))

/-- **Cited result.** A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Corollary 1.3: under `RapaportHyp`,
the attractor `K`, the nonempty compact set `K ⊆ I` with `K = ⋃_i φ_i(K)`, has Hausdorff dimension
`min{1, s(Φ)}`, where `s(Φ)` is the zero of the pressure
`P(t) = lim_n (1/n) log ∑_{u ∈ Σ_n} (sup_{x ∈ I} |φ_u'(x)|)^t`. -/
def RapaportSetStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ K : Set ℝ, K.Nonempty → IsCompact K → K ⊆ I → K = ⋃ i, φ i '' K →
    ∀ s : ℝ, Tendsto (fun n : ℕ => divide (Real.log (∑ u : Fin (n + 1) → Fin N,
        (⨆ x : I, |deriv (realComp φ (List.ofFn u)) x|) ^ s)) ((n + 1 : ℕ) : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) atTop (𝓝 0) →
      dimH K = ENNReal.ofReal (min 1 s)

end
end Challenge

namespace AnalyticESC
open Challenge

/-! ## AnalyticESC.Estimates -/

/-! Compositional norm bounds, used by `bound` in the analytic estimates. -/

attribute [bound] norm_add_le_of_le norm_mul_le_of_le norm_sub_le_of_le

/-- A finite family of continuous maps is uniformly bounded on a compact set. -/
lemma uniform_norm_bound  [TopologicalSpace X] [Fintype α] [NormedAddCommGroup E]
     (hS : IsCompact S) {F : α → X → E} (hF : ∀ a, ContinuousOn (F a) S) :
    ∃ M ≥ 0, ∀ a, ∀ x ∈ S, ‖F a x‖ ≤ M := by
  obtain ⟨M,hM0,hM⟩ := (hS.image_of_continuousOn (continuousOn_pi.2 hF)).isBounded.exists_pos_norm_le
  exact ⟨M, hM0.le, fun a x hx =>
    (norm_le_pi_norm (fun a => F a x) a).trans (hM _ (mem_image_of_mem _ hx))⟩

lemma norm_div_sub_div_le {a b f g : ℂ} (hf : f ≠ 0) (hg : g ≠ 0) (h1 : ‖a - b‖ ≤ E) (h2 : ‖f - g‖ ≤ E)
    (hM : ‖a / f‖ ≤ M) : ‖a / f - b / g‖ ≤ (1 + M) * E / ‖g‖ :=
  by
  have key : a / f - b / g = (a - b - a / f * (f - g)) / g := by field_simp; ring
  rw [key, norm_div]
  calc
    _ ≤ (E + M * E) / ‖g‖ := by bound
    _ = _ := by ring

lemma bounded_le_of_le_add_mul  {u : X → ℝ} 
    (hb : BddAbove (range u)) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ x, ∃ y, u x ≤ A + c * u y) : ∀ x, u x ≤ A / (1-c) := by
  intro x
  have  : sSup (range u) ≤ A + c * sSup (range u) := by
    apply csSup_le ⟨_, mem_range_self x⟩
    rintro _ ⟨z,rfl⟩
    obtain ⟨y,hy⟩ := h z
    exact hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left (le_csSup hb (mem_range_self y)) hc0) _)
  exact (le_csSup hb (mem_range_self x)).trans ((le_div_iff₀ (by linarith)).2 (by nlinarith))

/-! ## AnalyticESC.Defs -/

/-!
# Definitions

The vocabulary of B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation of
analytic self-conformal sets on the real line*.

Maps are given by their holomorphic extension `f : ℂ → ℂ`. Statements about `[0,1]` evaluate at
real points `(x : ℂ)`, `x ∈ I`; there `f`, `f'` and `f''` are real, and the complex derivatives
agree with the derivatives of the real restriction. Finite words are lists, read from the left:
`f_{i₁ ⋯ iₙ} = f_{i₁} ∘ ⋯ ∘ f_{iₙ}`.
-/


/-- Notation for the closed complex neighbourhood and the second derivative. -/
scoped notation:max "closedNbhd" ε:max => closure (nbhd ε)
scoped notation:max "D²" f:max => deriv (deriv f)

/-- Real restrictions of the holomorphic extensions. -/
scoped notation:max "realRestrict" f:max => (fun x : ℝ => Complex.re (f x))

/-- The first `n` letters of an address, regarded as a finite word. -/
scoped notation:max "prefix" n:max w:max => List.ofFn (fun k : Fin n => w k)

/-- Drop the first `n` symbols of an address. -/
scoped notation:max "shift" n:max w:max => (fun k : ℕ => w (k + n))

/-- An analytic IFS `Φ = (f_i)_{i ∈ Fin N}` in `𝔖_N`, for a fixed `ε > 0`. -/
structure IFS (N : ℕ) (ε : ℝ) where
  /-- The maps of the system. -/
  f : Fin N → CMap
  ε_pos : 0 < ε
  inClass : ∀ i, InClass ε (f i)

variable {N : ℕ} {ε ε' : ℝ} (Φ : IFS N ε)

/-- A finite or infinite word over the alphabet `Fin N`, an element of `Σ_* ∪ Σ`. -/
inductive Word (N : ℕ) where
  | fin (w : FWord N)
  | inf (w : Address N)

namespace Word

/-- The length `|w| ∈ ℕ ∪ {∞}`. -/
def length : Word N → ℕ∞
  | fin w => w.length
  | inf _ => ⊤

/-- The letter in position `n` (counted from `0`), if `n < |w|`. -/
def get? : Word N → ℕ → Option (Fin N)
  | fin w, n => w[n]?
  | inf w, n => some (w n)

/-- The prefix of the first `n` letters (the whole word if `|w| ≤ n`). -/
def take : Word N → ℕ → FWord N
  | fin w, n => w.take n
  | inf w, n => prefix n w

/-- The word `a w` obtained by placing the finite word `a` in front of `w`. -/
def prepend (a : FWord N) : Word N → Word N
  | fin w => fin (a ++ w)
  | inf w => inf fun n => if h : n < a.length then a[n] else w (n - a.length)

end Word

namespace IFS

/-- The real restriction of a map of the system. -/
def realMap i :=
  realRestrict(Φ.f i)

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
abbrev comp := Challenge.comp Φ.f

/-- The strong exponential separation condition (SESC, Definition 1.2). -/
abbrev SESC :=
  Challenge.SESC Φ.f

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
abbrev natProj := Challenge.natProj Φ.f

/-- The attractor `Λ = π(Σ)`. -/
abbrev attractor :=
  Challenge.attractor Φ.f

/-- Compositions along distinct finite words differ somewhere on `[0,1]`: `f_i ≢ f_j` on `[0,1]`
for all distinct `i, j ∈ Σ_*` (the hypothesis of Lemma 4.1). -/
def NoCoincidence :=
  ∀ i j : FWord N, i ≠ j → ∃ x ∈ I, Φ.comp i x ≠ Φ.comp j x

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
abbrev cmax := Challenge.cmax ε Φ.f

/-- The distortion `f_i''/f_i'`. -/
def nonlin i z :=
  D²(Φ.f i) z / deriv (Φ.f i) z

/-- The term with index `n` (from `0`) of the series (1.4) for `H_w`: with `v` the first `n`
letters of `w` and `i` the next one, `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where
`f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}` is the composition in reverse order. Zero if `|w| ≤ n`. -/
def dualTerm (w : Word N) n z :=
  match w.get? n with
  | none => 0
  | some i => Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z

/-- The dual natural projection `H_w` of (1.4), for finite and infinite words. -/
def dualProj w z :=
  ∑' n, Φ.dualTerm w n z

/-- The dual operator `(F_i h)(z) = f_i'(z) · h(f_i(z)) + (f_i''/f_i')(z)` of (2.1). -/
def dualOp i (h : CMap) z :=
  deriv (Φ.f i) z * h (Φ.f i z) + Φ.nonlin i z

/-- `F_w = F_{w₁} ∘ ⋯ ∘ F_{w_k}` for a finite word `w`. -/
def dualComp (w : FWord N) :=
  w.foldr (fun i G => Φ.dualOp i ∘ G) id

/-- `Φ` is sub-conjugated to a self-similar IFS: for distinct words `i, j` of the same length,
the pair `(f_i, f_j)` is conjugated to a self-similar IFS. -/
def SubConjSelfSimilar :=
  ∃ (m : ℕ) (i j : Block N m),
    i ≠ j ∧ ConjSelfSimilar ![realRestrict(Φ.comp (List.ofFn i)), realRestrict(Φ.comp (List.ofFn j))]

/-- Coding form of the strong separation condition for the dual: the first-letter
branches consist of distinct analytic functions. -/
def DualSSC :=
  0 < N ∧ ∀ i j : Address N, i 0 ≠ j 0 → ∃ x ∈ I, Φ.dualProj (.inf i) x ≠ Φ.dualProj (.inf j) x

/-- `conv((F_i k)(x), (F_i K)(x))` for a finite word `i` and constants `k`, `K`. -/
def dualCylAt (k K : ℝ) i (x : ℝ) :=
  uIcc (Φ.dualComp i (fun _ => k) x).re (Φ.dualComp i (fun _ => K) x).re

/-- The cylinders `F_i(k,K)` and `F_j(k,K)` are disjoint in the sense of (2.2). -/
def DualCylDisjoint (k K) (i j) :=
  ∃ x ∈ I, Disjoint (Φ.dualCylAt k K i x) (Φ.dualCylAt k K j x)

/-- The orbit `𝒪_i(x) = (x, f_{i₁}(x), f_{i₂ i₁}(x), …, f_{i_{|i|} ⋯ i₁}(x))` of Section 4.1, as
a list of real points. -/
def orbit (i : FWord N) (x : ℝ) :=
  (List.range (i.length + 1)).map fun l => (Φ.comp (i.take l).reverse x).re

end IFS

/-- The `𝒞²` distance on `I` between two maps (Section 1.1), with derivatives at real points. -/
def d2Map (f g : CMap) :=
  ((⨆ x : I, ‖f x - g x‖) + ⨆ x : I, ‖deriv f x - deriv g x‖) + ⨆ x : I, ‖D²f x - D²g x‖

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` on `𝔖_N`. The two systems may lie in
`𝔖_N(ε)` for different `ε`. -/
def d2 (Φ : IFS N ε) (Ψ : IFS N ε') :=
  ⨆ i, d2Map (Φ.f i) (Ψ.f i)

/-! ## AnalyticESC.Basic -/


/-!
# Basic properties

The neighbourhoods `B_δ`, consequences of the conditions (A)–(C) defining the class, the
constants `c_min` and `c_max`, compositions along finite words, and the passage between complex
derivatives and derivatives of real restrictions.
-/

/-- Maps that agree on `[0,1]` and are differentiable at `x ∈ [0,1]` have the same derivative
at `x`. -/
def hasDerivAt_unique_of_eqOn_I {u v : RMap} (hx : x ∈ I) (hu : HasDerivAt u a x) (hv : HasDerivAt v b x)
    huv :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt (hv.hasDerivWithinAt.congr huv (huv x hx))

/-! ## The neighbourhoods `B_δ` -/

/-- The norm-based and metric descriptions of the same neighbourhood. -/
theorem nbhd_eq_thickening δ : nbhd δ = thickening δ ((↑) '' I) :=
  by
  ext z
  simp [nbhd, mem_thickening_iff, dist_eq_norm]

/-- The image of `I` in `ℂ` is compact. -/
theorem isCompact_image_I : IsCompact (((↑) : ℝ → ℂ) '' I) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem isOpen_nbhd δ : IsOpen (nbhd δ) := by rw [nbhd_eq_thickening]; exact isOpen_thickening

theorem convex_nbhd δ : Convex ℝ (nbhd δ) := by rw [nbhd_eq_thickening]; exact ((convex_Icc 0 1).linear_image Complex.ofRealCLM.toLinearMap).thickening δ

def isPreconnected_nbhd δ :=
  (convex_nbhd δ).isPreconnected

theorem isCompact_closure_nbhd δ : IsCompact closedNbhd δ :=
  by
  rw [nbhd_eq_thickening]
  exact isCompact_image_I.isBounded.thickening.isCompact_closure

theorem ofReal_mem_nbhd  (hδ : 0 < δ)  (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  by rw [nbhd_eq_thickening]; exact self_subset_thickening hδ _ (mem_image_of_mem _ hx)

theorem ofReal_mem_closure  (hδ : 0 < δ)  (hx : x ∈ I) :
    (x : ℂ) ∈ closedNbhd δ :=
  subset_closure (ofReal_mem_nbhd hδ hx)

theorem ball_subset_nbhd  (hx : x ∈ I) : ball (x : ℂ) δ ⊆ nbhd δ :=
  by rw [nbhd_eq_thickening]; exact ball_subset_thickening (mem_image_of_mem _ hx) δ

theorem nbhd_mono  (h : δ ≤ δ') : nbhd δ ⊆ nbhd δ' := by simp only [nbhd_eq_thickening]; exact thickening_mono h _

theorem nbhd_of_nonpos  (h : δ ≤ 0) : nbhd δ = ∅ := by rw [nbhd_eq_thickening]; exact thickening_of_nonpos h _

theorem zero_mem_closure_nbhd (hδ : 0 < δ) : 0 ∈ closedNbhd δ :=
  ofReal_mem_closure hδ unitInterval.zero_mem

theorem closure_nbhd_subset  (h : δ < δ') : closedNbhd δ ⊆ nbhd δ' := by
  rcases le_or_gt δ' 0 with h' | h'
  · simp [nbhd_of_nonpos (h.le.trans h')]
  simp  [nbhd_eq_thickening]
  solve_by_elim [Metric.closure_thickening_subset_cthickening, LE.le.trans, Metric.cthickening_subset_thickening']

/-! ## Real restrictions -/

theorem iteratedDeriv_ofReal (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0)
    k {x : ℝ} (hx : (x : ℂ) ∈ U) : iteratedDeriv k g x = (iteratedDeriv k (realRestrict g) x : ℝ) := by
  induction k generalizing x with
  | zero => exact Complex.ext rfl (hreal x hx)
  | succ k
    ih =>
    have heq := by filter_upwards [(hU.preimage Complex.continuous_ofReal).mem_nhds hx] with t ht using ih ht
    simp [iteratedDeriv_eq_iterate] at heq
    simpa [iteratedDeriv_succ, iteratedDeriv_eq_iterate] using
      ((hg.analyticOnNhd hU).iterated_deriv k _ hx).differentiableAt.hasDerivAt.comp_ofReal.unique
        (((hg.analyticOnNhd hU _ hx).re_ofReal.iterated_deriv
                k).differentiableAt.hasDerivAt.ofReal_comp.congr_of_eventuallyEq
          heq)

theorem _root_.Challenge.InClass.analytic_real (hf : InClass ε f) (hε : 0 < ε) :
    AnalyticOnNhd ℝ (realRestrict f) I := fun x hx =>
  (hf.differentiableOn.analyticOnNhd (isOpen_nbhd _) _
    (ofReal_mem_nbhd (by positivity) hx)).re_ofReal

/-- A holomorphic map real on real points has real derivatives there. -/
theorem im_deriv_eq_zero {g : CMap}  (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    (deriv g x).im = 0 := by
  simpa using congrArg Complex.im (iteratedDeriv_ofReal hU hg hreal 1 hx)

/-- A bound on the logarithmic derivative gives a Lipschitz bound for `log ‖g‖` on `I`. -/
def abs_log_norm_sub_le {g : CMap} (hg : ∀ x ∈ I, DifferentiableAt ℂ g x) (hreal : ∀ x ∈ I, (g x).im = 0)
    (hne : ∀ x ∈ I, g x ≠ 0) (hL : ∀ x ∈ I, ‖deriv g x / g x‖ ≤ L) (hx : x ∈ I) (hy : y ∈ I) :=
  by
  let F (t : ℝ) := Real.log (g t).re
  have he : ∀ t ∈ I, Real.log ‖g t‖ = F t := by grind [Complex.abs_re_eq_norm, Real.log_abs]
  have hd : ∀ t ∈ I, HasDerivWithinAt F ((deriv g t).re / (g t).re) I t :=
    by
    intro t ht
    exact ((hg t ht).hasDerivAt.real_of_complex.log fun h => hne t ht (Complex.ext h (hreal t ht))).hasDerivWithinAt
  simpa [← he x hx, ← he y hy] using
    (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (by
        intro t ht
        rw [Real.norm_eq_abs, abs_div, Complex.abs_re_eq_norm.2 (hreal t ht)]
        refine (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)).trans ?_
        simpa [] using hL t ht)
      hy hx

namespace IFS

def mem_closure (hx : x ∈ I) :=
  ofReal_mem_closure Φ.ε_pos hx

/-! ## Single maps -/

theorem nbhd_subset_two : nbhd ε ⊆ nbhd (2 * ε) := by
  grind [AnalyticESC.nbhd_of_nonpos, AnalyticESC.nbhd_mono]

theorem closure_nbhd_subset_two : closedNbhd ε ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact closure_nbhd_subset (by linarith)

def differentiableOn_f i :=
  (Φ.inClass i).differentiableOn

def analyticAt_f i (hz : z ∈ closedNbhd ε) :=
  (Φ.differentiableOn_f i).analyticAt ((isOpen_nbhd _).mem_nhds (closure_nbhd_subset_two hz))

theorem continuous_iteratedDeriv_on_I i k : Continuous fun x : I => iteratedDeriv k (Φ.f i) x :=
  by
  rw [iteratedDeriv_eq_iterate]
  exact
    continuous_iff_continuousAt.2 fun x =>
      ((Φ.analyticAt_f i (Φ.mem_closure x.2)).iterated_deriv k).continuousAt.comp (f := fun x : I => (x : ℂ))
        (by fun_prop)

theorem mapsTo_f i : MapsTo (Φ.f i) (nbhd ε) (nbhd ε) :=
  fun _ hz => (Φ.inClass i).mapsTo _ (subset_closure hz)

def im_f_ofReal i {t} ht :=
  (Φ.inClass i).im_eq_zero t ht

def continuousOn_norm_deriv_f i :=
  (((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).continuousOn.mono closure_nbhd_subset_two).norm

theorem cmax_nonneg : 0 ≤ Φ.cmax :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cmax_lt_one : Φ.cmax < 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [cmax, Challenge.cmax]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [cmax, Challenge.cmax, Finite.ciSup_lt_iff]
  intro i
  rw [iSup, ← image_eq_range fun z : ℂ => ‖deriv (Φ.f i) z‖]
  exact
    ((isCompact_closure_nbhd ε).sSup_lt_iff_of_continuous ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩
          (Φ.continuousOn_norm_deriv_f i) 1).2
      (Φ.inClass i).norm_deriv_lt_one

theorem norm_deriv_le_cmax i (hz : z ∈ closedNbhd ε) : ‖deriv (Φ.f i) z‖ ≤ Φ.cmax :=
  calc
    ‖deriv (Φ.f i) z‖ ≤ ⨆ z : closedNbhd ε, ‖deriv (Φ.f i) z‖ :=
      le_ciSup
        (by
          rw [← image_eq_range fun z => ‖deriv (Φ.f i) z‖]
          exact (isCompact_closure_nbhd ε).bddAbove_image (Φ.continuousOn_norm_deriv_f i))
        (⟨z, hz⟩ : closedNbhd ε)
    _ ≤ Φ.cmax := le_ciSup (f := fun i => ⨆ z : closedNbhd ε, ‖deriv (Φ.f i) z‖) (finite_range _).bddAbove i

/-- A uniform positive lower derivative bound. -/
theorem exists_deriv_lower_bound : ∃ c > 0, ∀ i, ∀ z ∈ closedNbhd ε, c ≤ ‖deriv (Φ.f i) z‖ :=
  by
  obtain ⟨M, hM0, hM⟩ :=
    uniform_norm_bound (isCompact_closure_nbhd ε) (F := fun i z => (deriv (Φ.f i) z)⁻¹) fun i z hz =>
      ((Φ.analyticAt_f i hz).deriv.inv ((Φ.inClass i).deriv_ne_zero z hz)).continuousAt.continuousWithinAt
  refine ⟨(M + 1)⁻¹, by positivity, fun i z hz => ?_⟩
  rw [inv_le_comm₀ (by positivity) (norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero z hz))]
  simpa using (hM i z hz).trans (le_add_of_nonneg_right zero_le_one)

def cmin :=
  Φ.exists_deriv_lower_bound.choose

theorem cmin_pos : 0 < Φ.cmin := Φ.exists_deriv_lower_bound.choose_spec.1

theorem cmin_le_norm_deriv i  (hz : z ∈ closedNbhd ε) :
    Φ.cmin ≤ ‖deriv (Φ.f i) z‖ := Φ.exists_deriv_lower_bound.choose_spec.2 i z hz

def cmin_le_cmax hN :=
  (Φ.cmin_le_norm_deriv ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos)).trans
    (Φ.norm_deriv_le_cmax ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos))

/-- `f_i''/f_i'` is holomorphic on an open set containing `cl B_ε`. -/
def analyticAt_nonlin i (hz : z ∈ closedNbhd ε) :=
  (Φ.analyticAt_f i hz).deriv.deriv.div (Φ.analyticAt_f i hz).deriv ((Φ.inClass i).deriv_ne_zero z hz)

theorem exists_nonlin_bound : ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ closedNbhd ε, ‖Φ.nonlin i z‖ ≤ M :=
  uniform_norm_bound (isCompact_closure_nbhd ε) fun i z hz => (Φ.analyticAt_nonlin i hz).continuousAt.continuousWithinAt

def im_deriv_f_ofReal i {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) :=
  im_deriv_eq_zero (isOpen_nbhd _) (Φ.differentiableOn_f i) (fun _ => Φ.im_f_ofReal i) ht

theorem im_nonlin_ofReal i {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.nonlin i t).im = 0 := by
  have  := nbhd_subset_two ht
  grind [@AnalyticESC.IFS.differentiableOn_f, DifferentiableOn.deriv, AnalyticESC.isOpen_nbhd, AnalyticESC.im_deriv_eq_zero, @AnalyticESC.IFS.im_deriv_f_ofReal, AnalyticESC.IFS.nonlin, Complex.div_im]

/-! ## Compositions along finite words -/

@[simp] theorem comp_nil : Φ.comp [] = id := rfl

@[simp] theorem comp_cons i w : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w :=
  rfl

theorem comp_append (u v ) : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u <;> aesop

theorem mapsTo_comp w : MapsTo (Φ.comp w) (nbhd ε) (nbhd ε) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih =>  exact (Φ.mapsTo_f i).comp ih

theorem mapsTo_comp_closure w : MapsTo (Φ.comp w) closedNbhd ε closedNbhd ε := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => exact fun z hz => subset_closure ((Φ.inClass i).mapsTo _ (ih hz))

theorem analyticAt_comp w  (hz : z ∈ closedNbhd ε) : AnalyticAt ℂ (Φ.comp w) z := by
  induction w with
  | nil => exact analyticAt_id
  | cons i w ih => exact (Φ.analyticAt_f i (Φ.mapsTo_comp_closure w hz)).comp ih

def differentiableAt_comp w (hz : z ∈ closedNbhd ε) :=
  (Φ.analyticAt_comp w hz).differentiableAt

theorem differentiableOn_comp w : DifferentiableOn ℂ (Φ.comp w) (nbhd ε) :=
  fun _ hz => (Φ.differentiableAt_comp w (subset_closure hz)).differentiableWithinAt

/-- `f_w` is holomorphic on an open set containing `cl B_ε`. -/

theorem deriv_comp_cons i w  (hz : z ∈ closedNbhd ε) :
    deriv (Φ.comp (i :: w)) z = deriv (Φ.f i) (Φ.comp w z) * deriv (Φ.comp w) z := deriv_comp z (AnalyticAt.differentiableAt (analyticAt_f Φ i (mapsTo_comp_closure Φ w hz)))
    (Φ.differentiableAt_comp w hz)

theorem deriv_comp_append (u v )  (hz : z ∈ closedNbhd ε) :
    deriv (Φ.comp (u ++ v)) z = deriv (Φ.comp u) (Φ.comp v z) * deriv (Φ.comp v) z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem norm_deriv_comp_le w  (hz : z ∈ closedNbhd ε) :
    ‖deriv (Φ.comp w) z‖ ≤ Φ.cmax ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.norm_deriv_le_cmax i (Φ.mapsTo_comp_closure w hz)) ih (norm_nonneg _)
      Φ.cmax_nonneg

theorem cmin_pow_le_norm_deriv_comp w  (hz : z ∈ closedNbhd ε) :
    Φ.cmin ^ w.length ≤ ‖deriv (Φ.comp w) z‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.cmin_le_norm_deriv i (Φ.mapsTo_comp_closure w hz)) ih
      (pow_nonneg Φ.cmin_pos.le _) (norm_nonneg _)

def deriv_comp_ne_zero w (hz : z ∈ closedNbhd ε) :=
  norm_pos_iff.1 ((pow_pos Φ.cmin_pos _).trans_le (Φ.cmin_pow_le_norm_deriv_comp w hz))

def abs_re_comp_sub_le_mul w (hx : x ∈ I) (hy : y ∈ I) :=
  by
  have h :=
    (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le (fun _ hx => Φ.differentiableAt_comp w (subset_closure hx))
      (fun _ hx => Φ.norm_deriv_comp_le w (subset_closure hx)) (ofReal_mem_nbhd Φ.ε_pos hy) (ofReal_mem_nbhd Φ.ε_pos hx)
  rw [← Complex.ofReal_sub, Complex.norm_real] at h
  exact (Complex.abs_re_le_norm _).trans h

theorem abs_re_comp_sub_le v  (hy : y ∈ I) (hy' : y' ∈ I) :
    |(Φ.comp v y).re - (Φ.comp v y').re| ≤ Φ.cmax ^ v.length := (Φ.abs_re_comp_sub_le_mul v hy hy').trans (by
    simpa using mul_le_mul_of_nonneg_left (show |y-y'| ≤ 1 by grind)
      (pow_nonneg Φ.cmax_nonneg v.length))

theorem im_comp_ofReal w {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (Φ.comp w t).im = 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have h1 : Φ.comp w t = (Φ.comp w t).re := Complex.ext rfl ih
    rw [comp_cons, Function.comp_apply, h1]
    exact Φ.im_f_ofReal i (nbhd_subset_two (h1 ▸ Φ.mapsTo_comp w ht))

theorem comp_ofReal w (hx : x ∈ I) : Φ.comp w x = (Φ.comp w x).re :=
  Complex.ext rfl (Φ.im_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hx))

theorem re_comp_mem_I w  (hx : x ∈ I) : (Φ.comp w x).re ∈ I := by
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply, Φ.comp_ofReal w hx]
    grind [AnalyticESC.IFS.inClass, Challenge.InClass.re_mem_I]

/-- Compositions map real points of `I` into the closed unit disc. -/
theorem norm_comp_ofReal_le_one w  (hx : x ∈ I) :
    ‖Φ.comp w x‖ ≤ 1 := by
  grind [AnalyticESC.IFS.comp_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_le, AnalyticESC.IFS.re_comp_mem_I]

def im_deriv_comp_ofReal w {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :=
  im_deriv_eq_zero (isOpen_nbhd ε) (Φ.differentiableOn_comp w) (fun _ => Φ.im_comp_ofReal w) ht

/-- The real restriction of a composition is injective on `I`. -/
theorem injOn_re_comp w : InjOn (realRestrict(Φ.comp w)) I :=
  by
  have hd t (ht : t ∈ I) := (Φ.differentiableAt_comp w (Φ.mem_closure ht)).hasDerivAt.real_of_complex
  have hne t (ht : t ∈ I) h0 :=
    Φ.deriv_comp_ne_zero w (Φ.mem_closure ht) (Complex.ext h0 (Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos ht)))
  norm_num at hne
  intro a ha b hb heq
  wlog hab : a < b generalizing a b
  · grind
  have hsub := Icc_subset_Icc ha.1 hb.2
  obtain ⟨⟩ :=
    exists_hasDerivAt_eq_zero hab (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt) heq fun t ht =>
      hd t (hsub (Ioo_subset_Icc_self ht))
  grind

/-- The image `f_w(I)` is an interval of length between `c_min^{|w|}` and `c_max^{|w|}`. -/
theorem exists_image_comp_eq_Icc w :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 1 ∧ Φ.cmin ^ w.length ≤ q - p ∧ realRestrict(Φ.comp w) '' I = Icc p q :=
  by
  set h := realRestrict(Φ.comp w)
  have hderiv (x : ℝ) (hx : x ∈ I) := (Φ.differentiableAt_comp w (Φ.mem_closure hx)).hasDerivAt.real_of_complex
  have hcont : ContinuousOn h I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have himage := hcont.image_Icc zero_le_one
  set p := sInf (h '' I)
  set q := sSup (h '' I)
  have h0 := himage ▸ mem_image_of_mem h unitInterval.zero_mem
  have h1 := himage ▸ mem_image_of_mem h unitInterval.one_mem
  have hpq := h0.1.trans h0.2
  have hsub : Icc p q ⊆ I := himage ▸ image_subset_iff.2 fun x => Φ.re_comp_mem_I w
  refine ⟨p, q, (hsub ⟨le_rfl, hpq⟩).1, hpq, (hsub ⟨hpq, le_rfl⟩).2, ?_, himage⟩
  · -- lower bound via the mean value theorem on `[0,1]`
    
    obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope h (fun x => (deriv (Φ.comp w) x).re) zero_lt_one hcont fun x hx =>
        hderiv x (Ioo_subset_Icc_self hx)
    have hcI := Ioo_subset_Icc_self hc
    have hl := Φ.cmin_pow_le_norm_deriv_comp w (Φ.mem_closure hcI)
    rw [← Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hcI)), hslope, sub_zero,
      div_one] at hl
    exact hl.trans (abs_sub_le_of_le_of_le h1.1 h1.2 h0.1 h0.2)

end IFS

/-! ## AnalyticESC.Analysis -/


/-!
# Real-variable and identity-theorem lemmas

Lemma 3.1 (closeness of two functions gives closeness of their derivatives), its iterate, the
identity theorem on `B_ε` in the forms used in the paper, and the elementary bound (4.3).
-/

/-- An interior Cauchy estimate, requiring no boundary continuity. -/
def norm_iteratedDeriv_le_on_I (hε : 0 < ε) {g : CMap} (hg : DifferentiableOn ℂ g (nbhd ε))
    (hM : ∀ z ∈ closedNbhd ε, ‖g z‖ ≤ M) k (hx : x ∈ I) :=
  by
  have hs : closedBall (x : ℂ) (ε / 2) ⊆ nbhd ε := (closedBall_subset_ball (by linarith)).trans (ball_subset_nbhd hx)
  exact
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (half_pos hε) (hg.diffContOnCl_ball hs) fun z hz =>
      hM z (subset_closure (hs (sphere_subset_closedBall hz)))

/-! ## Lemma 3.1 and its iterate -/

/-! ## The identity theorem on `B_ε` -/

/-- The inclusion `ℝ → ℂ` maps punctured neighbourhoods into punctured neighbourhoods. -/
private theorem tendsto_ofReal_nhdsNE c :
    Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] c) (𝓝[≠] c) := Complex.continuous_ofReal.continuousAt.continuousWithinAt.tendsto_nhdsWithin (by simp [MapsTo])

/-- Identity theorem: maps holomorphic on `B_ε` that agree on a nondegenerate interval of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_eqOn_Icc  (hε : 0 < ε) {g h : CMap}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) 
    (hab : a < b) (hI : Icc a b ⊆ I) (heq : ∀ x ∈ Icc a b, g x = h x) : EqOn g h (nbhd ε) := by
  have hU := isOpen_nbhd ε
  have hc : (((a + b) / 2 : ℝ) : ℂ) ∈ nbhd ε :=
    ofReal_mem_nbhd hε (hI ⟨by linarith, by linarith⟩)
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hh.analyticOnNhd hU)
    (isPreconnected_nbhd ε) hc ?_
  apply (tendsto_ofReal_nhdsNE _).frequently
  exact (eventually_nhdsWithin_of_eventually_nhds
    (Icc_mem_nhds (by linarith) (by linarith))).frequently.mono fun x => heq x

/-- A map holomorphic on `B_ε`, not identically zero on `I`, has finitely many zeros in `I`. -/
theorem finite_zeros  (hε : 0 < ε) {g : CMap} (hg : DifferentiableOn ℂ g (nbhd ε))
    (hne : ∃ x ∈ I, g x ≠ 0) : {x : ℝ | x ∈ I ∧ g x = 0}.Finite := by
  by_contra hinf
  -- Infinitely many zeros in the compact `I` accumulate at some `c ∈ I`.
  obtain ⟨c, hcI, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc fun x hx => hx.1
  
  have  :=
    (hg.analyticOnNhd (isOpen_nbhd ε)).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_nbhd ε) (ofReal_mem_nbhd hε hcI) (by
        grind [accPt_iff_frequently_nhdsNE, AnalyticESC.tendsto_ofReal_nhdsNE, Filter.Tendsto.frequently, Filter.Frequently.mono]
      )
  obtain ⟨x, hx, hgx⟩ := hne
  solve_by_elim [AnalyticESC.ofReal_mem_nbhd]

/-! ## The bound (4.3) -/

/-! ## AnalyticESC.Analysis.Primitive -/


open scoped Interval
/-! Real integration supplies global primitives; local complex primitives prove analyticity. -/

def realPrimitive (f : RMap) (p x ) := ∫ t in p..x, f t

lemma hasDerivAt_realPrimitive  (hU : IsOpen U) (hUc : Convex ℝ U)
     (hf : ContinuousOn f U)  (hp : p ∈ U) (hx : x ∈ U) :
    HasDerivAt (realPrimitive f p) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (hf.mono (hUc.ordConnected.uIcc_subset hp hx)).intervalIntegrable
    (hf.stronglyMeasurableAtFilter hU x hx) (hf.continuousAt (hU.mem_nhds hx))

lemma local_primitive_extension (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {φ : RMap}
    (hφ : ∀ t : ℝ, (t : ℂ) ∈ U → HasDerivAt (fun t => (φ t : ℂ)) (f t) t) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0,
      ball (x : ℂ) r ⊆ U ∧
        ∃ g : CMap, DifferentiableOn ℂ g (ball x r) ∧ ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → g t = φ t :=
  by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨g, hgx, hg⟩ := (hf.mono hsub).isExactOn_ball.with_val_at x (φ x)
  have hm {t : ℝ} : t ∈ ball x r ↔ (t : ℂ) ∈ ball (x : ℂ) r := by simp [dist_eq_norm, ← Complex.ofReal_sub]
  have hgd t (ht : t ∈ ball x r) := (hg t (hm.1 ht)).comp_ofReal
  have hpd t (ht : t ∈ ball x r) := hφ t (hsub (hm.1 ht))
  exact
    ⟨r, hr, hsub, g, fun t ht => (hg t ht).differentiableAt.differentiableWithinAt, fun t ht =>
      (isOpen_ball.eqOn_of_deriv_eq (convex_ball x r).isPreconnected
          (fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt)
          (fun t ht => (hpd t ht).differentiableAt.differentiableWithinAt)
          (fun t ht => (hgd t ht).deriv.trans (hpd t ht).deriv.symm) (mem_ball_self hr) hgx)
        (hm.2 ht)⟩

/-! ## AnalyticESC.Words -/

/-!
# Words

Finite and infinite words: prefixes, prepending, the longest common prefix `|i ∧ j|`,
convergence of words by prefixes and the compactness of `Σ_* ∪ Σ`, and the decomposition of two
distinct words of equal length at their last difference.
-/

namespace Word

attribute [simp] length.eq_1 length.eq_2 take.eq_1 take.eq_2 get?.eq_1 get?.eq_2

/-- The letters of a prefix. -/
private theorem getElem?_take_word (w : Word N) (n k ) :
    (w.take n)[k]? = if k < n then w.get? k else none := by
  cases w <;> aesop

/-- Two prefixes of length `n` agree if and only if the first `n` letters agree. -/
theorem take_eq_take_iff {v w : Word N}  :
    v.take n = w.take n ↔ ∀ k < n, v.get? k = w.get? k := by
  simp only [List.ext_getElem?_iff, getElem?_take_word]
  grind

/-- A word is determined by its letters. -/
theorem ext_get? {v w : Word N} (h : ∀ n, v.get? n = w.get? n) : v = w := by
  cases v <;> cases w <;>
    first
    | exact congrArg fin (List.ext_getElem? h)
    | (congr 1; funext n; exact Option.some.inj (h n))
    | (have := h ‹List (Fin N)›.length; simpa [get?] using this)

theorem get?_prepend a (w : Word N) n :
    (w.prepend a).get? n = if n < a.length then a[n]? else w.get? (n - a.length) := by
  cases w with
  | fin w => simp [prepend, List.getElem?_append]
  | inf w =>
    grind [AnalyticESC.Word.prepend, AnalyticESC.Word.get?.eq_2]

theorem get?_prepend_add a (w : Word N) n :
    (w.prepend a).get? (n + a.length) = w.get? n := by
  simp [get?_prepend]

theorem take_prepend_of_le a (w : Word N)  (hn : n ≤ a.length) :
    (w.prepend a).take n = a.take n := by
  refine List.ext_getElem? fun k => ?_
  grind [AnalyticESC.Word.getElem?_take_word, AnalyticESC.Word.get?_prepend]

theorem take_prepend_add a (w : Word N) n :
    (w.prepend a).take (n + a.length) = a ++ w.take n := by
  refine List.ext_getElem? fun k => ?_
  grind [AnalyticESC.Word.getElem?_take_word, AnalyticESC.Word.get?_prepend]

/-- Sharing the complete first `n` letters. -/
def AgreePrefix (i j : Word N) n :=
  i.take n = j.take n ∧ (i.take n).length = n

/-- A letter in position `n` ensures that the first `n` letters exist. -/
theorem length_take_of_get?_eq_some {w : Word N}  
    (h : w.get? n = some i) : (w.take n).length = n := by
  cases w <;> grind [take, get?, List.length_take]

 theorem eq_prepend_take (w : Word N) n : ∃ w' : Word N, w = w'.prepend (w.take n) := by
  cases w with
  | fin w => exact ⟨.fin (w.drop n), congrArg fin (by norm_num)⟩
  | inf w =>
    refine ⟨.inf shift n w, ext_get? fun k => ?_⟩
    simp [prepend]
    grind

 theorem exists_eq_prepend   (h : AgreePrefix i j n) :
    ∃ (a : FWord N) (i' j' : Word N), a.length = n ∧ i = i'.prepend a ∧ j = j'.prepend a := by
  obtain ⟨i', hi⟩ := eq_prepend_take i n
  obtain ⟨j', hj⟩ := eq_prepend_take j n
  exact ⟨i.take n,i',j',h.2,hi,by rwa [← h.1] at hj⟩

/-- Complete a finite word with repetitions of one fixed letter. -/
def extend (w : FWord N) i := fun n => if h : n < w.length then w[n] else i

/-! ## Convergence of words -/

/-- `w k → w₀` letter by letter: every prefix of `w₀` is eventually the prefix of `w k`. -/
def TendstoPrefix (w : ℕ → Word N) (w₀ : Word N) :=
  ∀ n, ∀ᶠ k in atTop, (w k).take n = w₀.take n

/-- Compactness for finite words whose lengths diverge, by padding them with any letter. -/
theorem exists_subseq_tendstoPrefix (w : ℕ → FWord N) (h : Tendsto (fun k => (w k).length) atTop atTop) (i : Fin N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Address N, TendstoPrefix (fun k => fin (w (φ k))) (.inf v) :=
  by
  let f k := extend (w k) i
  obtain ⟨v, φ, hφ, hv⟩ := CompactSpace.tendsto_subseq f
  have hc : ∀ n, ∀ᶠ k in atTop, f (φ k) n = v n := by simpa [tendsto_pi_nhds] using hv
  refine ⟨φ, hφ, v, fun n => ?_⟩
  filter_upwards [(h.comp hφ.tendsto_atTop).eventually_ge_atTop n, eventually_all.2 fun m : Fin n => hc m] with k hk he
  apply take_eq_take_iff.2
  intro m hm
  have hml : m < (w (φ k)).length := hm.trans_le hk
  simpa [f, extend, hml] using he ⟨m, hm⟩

end Word

/-- Two distinct words of equal length split at their last difference: `i = a u`, `j = b u` with
`|a| = |b| ≥ 1` and different last letters of `a` and `b`. -/
theorem List.exists_decomp_of_ne {i j} (hlen : i.length = j.length) (hne : i ≠ j) :
    ∃ a b u : FWord N, i = a ++ u ∧ j = b ++ u ∧ a.length = b.length ∧ 0 < a.length ∧ a.getLast? ≠ b.getLast? := by
  induction i using _root_.List.reverseRecOn generalizing j with
  | nil =>
    have := _root_.List.eq_nil_of_length_eq_zero hlen.symm
    exact absurd this.symm hne
  | append_singleton i x
    ih =>
    have hj : j ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨j', y, rfl⟩ : ∃ j' y, j = j' ++ [y] :=
      ⟨j.dropLast, j.getLast hj, (_root_.List.dropLast_append_getLast hj).symm⟩
    simp at hlen
    by_cases hxy : x = y
    · subst hxy
      have : i ≠ j' := by solve_by_elim
      grind
    · exact ⟨i ++ [x], j' ++ [y], [], by simp, by simp, by simp [hlen], by simp [hxy]⟩

/-! ## AnalyticESC.Dual.Projection -/

/-!
# The dual natural projection

Convergence and holomorphy of the series (1.4) defining `H_w`, its uniform bounds, the cocycle
identity for prepended words, the formula (2.7) `H_{v^←} = f_v''/f_v'` for finite words, and
Lemma 2.5, analyticity and Hölder continuity: `H_w ∈ C^ω_ε([0,1])` and Hölder dependence on the word.
-/

namespace IFS

/-! ## The terms of the series -/

theorem dualTerm_of_get?_eq_none   (h : w.get? n = none) z :
    Φ.dualTerm w n z = 0 := by
  simp [dualTerm, h]

theorem dualTerm_of_get?_eq_some    (h : w.get? n = some i)
    z :
    Φ.dualTerm w n z =
      Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z := by
  simp [dualTerm, h]

/-- The terms of (1.4) decay geometrically on `cl B_ε`, uniformly in the word. -/
theorem exists_dualTerm_bound : ∃ C, 0 ≤ C ∧ ∀ w n, ∀ z ∈ closedNbhd ε,
    ‖Φ.dualTerm w n z‖ ≤ C * Φ.cmax ^ n := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_nonlin_bound
  refine ⟨C, hC0, fun w n z hz => ?_⟩
  cases h : w.get? n with
  | none =>
    grind [AnalyticESC.IFS.dualTerm_of_get?_eq_none, norm_zero, mul_nonneg, pow_nonneg, AnalyticESC.IFS.cmax_nonneg]
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have  := hC i _ (Φ.mapsTo_comp_closure (w.take n).reverse hz)
    grind [AnalyticESC.IFS.norm_deriv_comp_le,  AnalyticESC.Word.length_take_of_get?_eq_some, mul_le_mul]

theorem summable_dualTerm w  (hz : z ∈ closedNbhd ε) :
    Summable fun n => Φ.dualTerm w n z := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    fun n => hC w n z hz

@[simp] theorem dualProj_nil : Φ.dualProj (.fin []) = 0 := by
  funext z
  simp [dualProj, dualTerm]

/-- For a finite word, `H_a` is the finite sum of its `|a|` terms. -/
theorem dualProj_fin_eq_sum a z :
    Φ.dualProj (.fin a) z = ∑ n ∈ Finset.range a.length, Φ.dualTerm (.fin a) n z := by
  refine tsum_eq_sum fun n hn => Φ.dualTerm_of_get?_eq_none ?_ z
  aesop

theorem dualProj_singleton i z : Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  simp_all [AnalyticESC.IFS.dualProj_fin_eq_sum, AnalyticESC.IFS.dualTerm]

/-! ## Bounds -/

/-- The uniform bound `‖H_w‖ ≤ M` on `cl B_ε`. -/
theorem exists_norm_dualProj_le :
    ∃ M, 0 ≤ M ∧ ∀ w : Word N, ∀ z ∈ closedNbhd ε, ‖Φ.dualProj w z‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_dualTerm_bound
  refine ⟨C * (1 - Φ.cmax)⁻¹,
    mul_nonneg hC0 (inv_nonneg.2 (sub_nonneg.2 Φ.cmax_lt_one.le)), fun w z hz => ?_⟩
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C) fun n => hC w n z hz

/-- Boundedness of dual-projection differences on the unit interval. -/
theorem bddAbove_dualProj_sub (u v ) :
    BddAbove (range fun x : I => ‖Φ.dualProj u x - Φ.dualProj v x‖) := by
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  refine ⟨M + M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := Φ.mem_closure x.2
  exact (norm_sub_le _ _).trans (add_le_add (hM u x hx) (hM v x hx))

/-! ## Holomorphy and realness -/

theorem differentiableOn_dualProj w : DifferentiableOn ℂ (Φ.dualProj w) (nbhd ε) := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    (fun n z hz => by
      have hz' := subset_closure hz
      cases h : w.get? n with
      | none => rw [funext (Φ.dualTerm_of_get?_eq_none h)]; fun_prop
      | some i =>
        rw [funext (Φ.dualTerm_of_get?_eq_some h)]
        exact (((Φ.analyticAt_nonlin i (Φ.mapsTo_comp_closure _ hz')).comp
          (Φ.analyticAt_comp _ hz')).mul (Φ.analyticAt_comp _ hz').deriv).differentiableAt.differentiableWithinAt) (isOpen_nbhd ε)
    fun n z hz => hC w n z (subset_closure hz)

theorem im_dualProj_ofReal w {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (Φ.dualProj w t).im = 0 :=
  by
  rw [dualProj, Complex.im_tsum (Φ.summable_dualTerm w (subset_closure ht))]
  have H n : (Φ.dualTerm w n t).im = 0 := by
    cases h : w.get? n with
    | none => simp [Φ.dualTerm_of_get?_eq_none h]
    | some i =>
      rw [Φ.dualTerm_of_get?_eq_some h]
      have h1 : Φ.comp (w.take n).reverse t = (Φ.comp (w.take n).reverse t).re := by
        solve_by_elim [Complex.ext, AnalyticESC.IFS.im_comp_ofReal]
      have := h1 ▸ Φ.mapsTo_comp _ ht
      grind [AnalyticESC.IFS.im_nonlin_ofReal, Complex.mul_im, @AnalyticESC.IFS.im_deriv_comp_ofReal]
  simp [H]

/-! ## The cocycle identity and (2.7) -/

/-- The cocycle identity: `H_{a w}(z) = H_a(z) + f_{a^←}'(z) · H_w(f_{a^←}(z))`, where
`f_{a^←} = f_{a_{|a|}} ∘ ⋯ ∘ f_{a_1}`. -/
theorem dualProj_prepend a w (hz : z ∈ closedNbhd ε) :
    Φ.dualProj (w.prepend a) z =
      Φ.dualProj (.fin a) z + deriv (Φ.comp a.reverse) z * Φ.dualProj w (Φ.comp a.reverse z) :=
  by
  rw [dualProj_fin_eq_sum]
  unfold dualProj
  rw [← (Φ.summable_dualTerm (w.prepend a) hz).sum_add_tsum_nat_add a.length, ← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    simp [dualTerm, Word.get?_prepend, hn', Word.take_prepend_of_le a w hn'.le, ]
  · refine tsum_congr fun m => ?_
    have hg := Word.get?_prepend_add a w m
    cases h : w.get? m with
    | none => grind [AnalyticESC.IFS.dualTerm_of_get?_eq_none]
    | some
      i =>
      rw [Φ.dualTerm_of_get?_eq_some (hg.trans h), Φ.dualTerm_of_get?_eq_some h, Word.take_prepend_add a w m,
        List.reverse_append, Φ.deriv_comp_append _ _ hz, Φ.comp_append, Function.comp_apply]
      ring

/-- (2.7): `H_{v^←} = f_v''/f_v'` for a finite word `v`. -/
theorem dualProj_fin_reverse v  (hz : z ∈ closedNbhd ε) :
    Φ.dualProj (.fin v.reverse) z = D² (Φ.comp v) z / deriv (Φ.comp v) z := by
  induction v with
  | nil => simp
  | cons i v ih =>
    have hfin : (Word.fin [i]).prepend v.reverse = Word.fin (i :: v).reverse := by
      rw [List.reverse_cons]; rfl
    have h2 := iteratedDeriv_comp_two
      (Φ.analyticAt_f i (Φ.mapsTo_comp_closure v hz)).contDiffAt
      (Φ.analyticAt_comp v hz).contDiffAt
    simp  [iteratedDeriv_succ, iteratedDeriv_zero] at h2
    rw [← comp_cons] at h2
    rw [← hfin, Φ.dualProj_prepend _ _ hz, dualProj_singleton,  Φ.deriv_comp_cons i v hz, nonlin]
    have   :=
      (Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure v hz)
    grind

/-! ## Lemma 2.5 -/

/-- Uniform bound for `H_w` on `cl B_ε` and the bound `2M c_max^m` for words sharing a prefix of
length `m`. -/
theorem exists_dualProj_bounds :
    ∃ M, 0 ≤ M ∧ (∀ w : Word N, ∀ z ∈ closedNbhd ε, ‖Φ.dualProj w z‖ ≤ M) ∧
      ∀ (i j ) m, Word.AgreePrefix i j m →
        ∀ z ∈ closedNbhd ε, ‖Φ.dualProj i z - Φ.dualProj j z‖ ≤ 2 * M * Φ.cmax ^ m := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  refine ⟨M, hM0, hM, fun i j m hm z hz => ?_⟩
  obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
  rw [Φ.dualProj_prepend a i' hz, Φ.dualProj_prepend a j' hz, add_sub_add_left_eq_sub,
    ← mul_sub]
  have hz' := Φ.mapsTo_comp_closure a.reverse hz
  have h1 := Φ.norm_deriv_comp_le a.reverse hz
  rw [List.length_reverse] at h1
  calc _ ≤ Φ.cmax ^ m * (M + M) := by
        bound [Φ.cmax_nonneg, hM i' _ hz', hM j' _ hz']
    _ = 2 * M * Φ.cmax ^ m := by ring

end IFS

/-! ## AnalyticESC.Conjugation.Koenigs -/

/-! The single-map cocycle and a real analytic solution of its linearising ODE. -/

/-- The function `Ĥ_f(z) = ∑_{k ≥ 0} (f''/f')(f^k(z)) · (f^k)'(z)` of (5.1). -/
def hatH (f : CMap) z :=
  ∑' k, D²f (f^[k] z) / deriv f (f^[k] z) * deriv f^[k] z

/-- The system consisting of the single map `f`. -/
private def koenigsIFS   (hε : 0 < ε) (hf : InClass ε f) : IFS 1 ε :=
  ⟨fun _ => f, hε, fun _ => hf⟩

section

variable {f : CMap} (hε : 0 < ε) (hf : InClass ε f)

include hε hf

/-! ## Iterates of a single map -/

private theorem koenigsIFS_comp n : (koenigsIFS hε hf).comp (List.replicate n 0) = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    grind [AnalyticESC.IFS.comp_cons, Function.iterate_succ', AnalyticESC.koenigsIFS]

private theorem hatH_eq_dualProj :
    hatH f = (koenigsIFS hε hf).dualProj (.inf fun _ => 0) := by
  funext z
  refine tsum_congr fun k => ?_
  rw [(koenigsIFS hε hf).dualTerm_of_get?_eq_some (Word.get?.eq_2 k _)]
  simp only [Word.take, List.ofFn_const, List.reverse_replicate, koenigsIFS_comp hε hf]
  rfl

theorem differentiableOn_hatH : DifferentiableOn ℂ (hatH f) (nbhd ε) := by
  rw [hatH_eq_dualProj hε hf]
  grind [AnalyticESC.IFS.differentiableOn_dualProj]

theorem im_hatH_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (hatH f t).im = 0 := by
  rw [hatH_eq_dualProj hε hf]
  grind [AnalyticESC.IFS.im_dualProj_ofReal]

theorem hatH_eq_add  (hz : z ∈ nbhd ε) :
    hatH f z = D² f z / deriv f z + deriv f z * hatH f (f z) := by
  have hw : (Word.inf fun _ : ℕ => (0 : Fin 1)).prepend [0] = .inf fun _ => 0 := by
    grind [AnalyticESC.Word.prepend]
  have h := (koenigsIFS hε hf).dualProj_prepend [0] (.inf fun _ => 0) (subset_closure hz)
  rw [hw, IFS.dualProj_singleton] at h
  rw [hatH_eq_dualProj hε hf, h]
  rfl

end

lemma exists_real_ode_coord (hε : 0 < ε) (hf : InClass ε f) :
    ∃ φ, IsAnalyticCoord φ ∧ (∀ x ∈ I, 0 < deriv φ x) ∧ ∀ x ∈ I, D² φ x = (hatH f x).re * deriv φ x :=
  by
  let V : Set ℝ := {t | (t : ℂ) ∈ nbhd ε}
  have hV : IsOpen V := (isOpen_nbhd ε).preimage Complex.continuous_ofReal
  have hVc : Convex ℝ V := (convex_nbhd ε).linear_preimage Complex.ofRealCLM.toLinearMap
  have h0 : 0 ∈ V := ofReal_mem_nbhd hε unitInterval.zero_mem
  have hmem {x : ℝ} (hx : x ∈ I) : x ∈ V := ofReal_mem_nbhd hε hx
  have hH := differentiableOn_hatH hε hf
  let u := realPrimitive (realRestrict(hatH f)) 0
  have hu t (ht : t ∈ V) : HasDerivAt u (hatH f t).re t :=
    hasDerivAt_realPrimitive hV hVc
      (Complex.continuous_re.comp_continuousOn
        (hH.continuousOn.comp Complex.continuous_ofReal.continuousOn fun _ ht => ht))
      h0 ht
  let G := fun t => Real.exp (u t)
  have hG t (ht : t ∈ V) : HasDerivAt G (G t * (hatH f t).re) t := (hu t ht).exp
  let K := realPrimitive G 0
  have hK t (ht : t ∈ V) : HasDerivAt K (G t) t :=
    hasDerivAt_realPrimitive hV hVc (fun t ht => (hG t ht).continuousAt.continuousWithinAt) h0 ht
  have hKa : AnalyticOnNhd ℝ K I := by
    intro x hx
    obtain ⟨r, hr, hsub, g, hg, hgu⟩ :=
      local_primitive_extension (isOpen_nbhd ε) hH
        (fun t ht => by
          convert (hu t ht).ofReal_comp using 1
          exact Complex.ext (by simp) (by simp [im_hatH_ofReal hε hf ht]))
        (hmem hx)
    obtain ⟨s, hs, _, k, hk, hkK⟩ :=
      local_primitive_extension isOpen_ball hg.cexp
        (fun t ht => by simpa [hgu t ht, ← Complex.ofReal_exp] using (hK t (hsub ht)).ofReal_comp) (mem_ball_self hr)
    apply (hk.analyticOnNhd isOpen_ball _ (mem_ball_self hs)).re_ofReal.congr
    filter_upwards [(isOpen_ball.preimage Complex.continuous_ofReal).mem_nhds (mem_ball_self hs)] with t ht
    simpa [] using congrArg Complex.re (hkK t ht)
  have hpos x (hx : x ∈ I) : 0 < deriv K x := by rw [(hK x (hmem hx)).deriv]; exact Real.exp_pos _
  refine
    ⟨K,
      ⟨hKa,
        (strictMonoOn_of_deriv_pos (convex_Icc 0 1) hKa.continuousOn fun x hx => hpos x (interior_subset hx)).injOn⟩,
      hpos, ?_⟩
  intro x hx
  rw [(Filter.eventuallyEq_of_mem (hV.mem_nhds (hmem hx)) fun t ht => (hK t ht).deriv).deriv_eq, (hG x (hmem hx)).deriv,
    (hK x (hmem hx)).deriv]
  ring

/-! ## AnalyticESC.Dual.Attractor -/

/-! # Coding and separation of the dual IFS -/

namespace Word

/-- An infinite word is its prefix of length `n` followed by its `n`-fold shift. -/
theorem inf_eq_prepend_ofFn (w : Address N) n : inf w = (inf shift n w).prepend prefix n w :=
  by
  congr 1
  grind

end Word
namespace IFS

/-- The cocycle identity for a single letter. -/
theorem dualProj_prepend_singleton i w 
    (hz : z ∈ closedNbhd ε) :
    Φ.dualProj (w.prepend [i]) z = deriv (Φ.f i) z * Φ.dualProj w (Φ.f i z) + Φ.nonlin i z := by
  simp_all [AnalyticESC.IFS.dualProj_prepend, AnalyticESC.IFS.dualProj_singleton, add_comm]

theorem dualProj_eq_of_cocycle (hG : ContinuousOn G I)
    (h : ∀ k, ∀ x ∈ I, G x = deriv (Φ.f k) x * G (Φ.f k x).re + Φ.nonlin k x) :
    ∀ w : Address N, ∀ x ∈ I, Φ.dualProj (.inf w) x = G x :=
  by
  let u (p : Address N × I) := ‖Φ.dualProj (.inf p.1) p.2 - G p.2‖
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨B, -, hB⟩ := Φ.exists_norm_dualProj_le
  have hs : ∀ p, ∃ q, u p ≤ 0 + Φ.cmax * u q := by
    rintro ⟨w, x⟩
    refine ⟨(shift 1w, ⟨_, (Φ.inClass (w 0)).re_mem_I x x.2⟩), ?_⟩
    have hx := Φ.mem_closure x.2
    have hp := Word.inf_eq_prepend_ofFn w 1
    simp at hp
    dsimp [u]
    rw [hp, Φ.dualProj_prepend_singleton _ _ hx, h (w 0) x x.2, add_sub_add_right_eq_sub, ← mul_sub, norm_mul, zero_add,
      show Φ.f (w 0) x = (Φ.f (w 0) x).re from Φ.comp_ofReal [w 0] x.2]
    exact mul_le_mul_of_nonneg_right (Φ.norm_deriv_le_cmax _ hx) (norm_nonneg _)
  intro w x hx
  simpa [u, sub_eq_zero] using
    bounded_le_of_le_add_mul
      (by
        refine ⟨B + M, ?_⟩
        rintro _ ⟨⟨w, x⟩, rfl⟩
        exact (norm_sub_le _ _).trans (add_le_add (hB _ _ (Φ.mem_closure x.2)) (hM x x.2)))
      Φ.cmax_nonneg Φ.cmax_lt_one hs (w, ⟨x, hx⟩)

/-- `F_w h = f_{w^←}' · (h ∘ f_{w^←}) + H_w` on `B_ε` (Section 2.1). -/
theorem dualComp_apply w h  (hz : z ∈ nbhd ε) :
    Φ.dualComp w h z =
      deriv (Φ.comp w.reverse) z * h (Φ.comp w.reverse z) + Φ.dualProj (.fin w) z := by
  induction w generalizing z with
  | nil => simp [dualComp]
  | cons i w ih =>
    have hcl  := subset_closure hz
    change Φ.dualOp i (Φ.dualComp w h) z = _
    rw [dualOp, ih (Φ.mapsTo_f i hz), List.reverse_cons, Φ.deriv_comp_append _ _ hcl,
      Φ.comp_append]
    erw [Φ.dualProj_prepend_singleton i (.fin w) hcl]
    simp  [ ]
    ring

/-- At each real point, dual projections vary continuously with the coding word. -/
lemma continuous_dualProj_word (hx : x ∈ I) : Continuous fun w : Address N => Φ.dualProj (.inf w) x :=
  by
  obtain ⟨M, -, -, hM⟩ := Φ.exists_dualProj_bounds
  rw [continuous_iff_continuousAt]
  intro w
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).const_mul (2 * M)
  simp [] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  filter_upwards [eventually_all.2 fun k : Fin m =>
      (continuous_apply (k : ℕ)).continuousAt.eventually (mem_nhds_discrete.2 (mem_singleton (w k)))] with
    v hv
  rw [dist_eq_norm]
  exact
    (hM _ _ m ⟨Word.take_eq_take_iff.2 fun k hk => by exact congrArg some (hv ⟨k, hk⟩), by simp⟩ x
          (Φ.mem_closure hx)).trans_lt
      hm

/-- Compactness turns pointwise separation of first-letter branches into a uniform gap. -/
theorem dualSSC_iff_exists_delta (hN : 0 < N) :
    Φ.DualSSC ↔ ∃ δ > 0, ∀ i j : Address N, i 0 ≠ j 0 → δ < ⨆ x : I, ‖Φ.dualProj (.inf i) x - Φ.dualProj (.inf j) x‖ :=
  by
  simp only [DualSSC, hN, true_and]
  let D : Address N × Address N → ℝ := fun p => ⨆ x : I, ‖Φ.dualProj (.inf p.1) x - Φ.dualProj (.inf p.2) x‖
  have hbdd := fun p : Address N × Address N => Φ.bddAbove_dualProj_sub (.inf p.1) (.inf p.2)
  constructor
  · intro h
    let S : Set (Address N × Address N) := {p | p.1 0 ≠ p.2 0}
    have hpos : ∀ p ∈ S, 0 < D p := by
      rintro ⟨i, j⟩ hp
      obtain ⟨x, hxI, hne⟩ := h i j hp
      exact (norm_pos_iff.2 (sub_ne_zero.2 hne)).trans_le (le_ciSup (hbdd (i, j)) ⟨x, hxI⟩)
    have hcont : LowerSemicontinuous D := by
      apply lowerSemicontinuous_ciSup hbdd
      intro x
      exact
        (((Φ.continuous_dualProj_word x.2).comp continuous_fst).sub
            ((Φ.continuous_dualProj_word x.2).comp continuous_snd)).norm.lowerSemicontinuous
    rcases S.eq_empty_or_nonempty with hE | hne
    · refine ⟨1, one_pos, fun i j hij => ?_⟩
      have : (i, j) ∈ S := hij
      grind
    · obtain ⟨p₀, hp₀, hmin⟩ :=
        LowerSemicontinuousOn.exists_isMinOn hne
          (IsClosed.preimage (f := fun p : Address N × Address N => (p.1 0, p.2 0)) (by fun_prop)
              (isClosed_discrete {q : Fin N × Fin N | q.1 ≠ q.2})).isCompact
          (hcont.lowerSemicontinuousOn S)
      refine ⟨D p₀ / 2, half_pos (hpos p₀ hp₀), fun i j hij => ?_⟩
      calc
        D p₀ / 2 < D p₀ := half_lt_self (hpos p₀ hp₀)
        _ ≤ D (i, j) := by solve_by_elim
  · rintro ⟨δ, hδ, h⟩ i j hij
    obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (hδ.trans (h i j hij))
    exact ⟨x, x.2, sub_ne_zero.1 (norm_pos_iff.1 hx)⟩

/-- Equal compositions with different last letters violate dual separation. -/
theorem not_dualSSC_of_comp_eq (hlen : a.length = b.length) (hlast : a.getLast? ≠ b.getLast?)
    (h : ∀ x ∈ I, Φ.comp a x = Φ.comp b x) : ¬Φ.DualSSC :=
  by
  rintro ⟨hN, hsep⟩
  let i₀ : Fin N := ⟨0, hN⟩
  have hEq :=
    eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b) zero_lt_one subset_rfl h
  have hF : ∀ x ∈ I, Φ.dualProj (.inf (Word.extend a.reverse i₀)) x = Φ.dualProj (.inf (Word.extend b.reverse i₀)) x :=
    by
    intro x hx
    have hz := ofReal_mem_nbhd Φ.ε_pos hx
    have hz' := subset_closure hz
    change
      Φ.dualProj ((Word.inf fun _ => i₀).prepend a.reverse) x = Φ.dualProj ((Word.inf fun _ => i₀).prepend b.reverse) x
    rw [Φ.dualProj_prepend _ _ hz', Φ.dualProj_prepend _ _ hz', List.reverse_reverse, List.reverse_reverse,
      Φ.dualProj_fin_reverse _ hz', Φ.dualProj_fin_reverse _ hz', hEq hz, hEq.deriv (isOpen_nbhd ε) hz,
      (hEq.deriv (isOpen_nbhd ε)).deriv (isOpen_nbhd ε) hz]
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', i, rfl⟩
  · grind
  rcases List.eq_nil_or_concat' b with rfl | ⟨b', j, rfl⟩
  · simp at hlen
  have hij : i ≠ j := fun hij => hlast (by simp [hij])
  have he : Word.extend (a' ++ [i]).reverse i₀ 0 ≠ Word.extend (b' ++ [j]).reverse i₀ 0 := by
    simpa [Word.extend] using hij
  obtain ⟨x, hx, hne⟩ := hsep _ _ he
  exact hne (hF x hx)

end IFS

/-! ## AnalyticESC.Generic.Class -/

/-!
# The classes `S^ω_ε(I)` and `S^ω(I)`

The inclusion `f(cl B_ε) ⊆ B_ε` in condition (B) of the class `S^ω_ε(I)` follows from the other
conditions. Hence the classes `S^ω_ε(I)` decrease as `ε` increases, and their union `S^ω(I)` is
described by conditions on `[0,1]`.
-/

/-- Every point of `cl B_ε` lies within distance `ε` of a point of `I`. -/
theorem exists_mem_I_norm_sub_le  (hε : 0 ≤ ε)  (hz : z ∈ closedNbhd ε) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  rw [nbhd_eq_thickening] at hz
  have hz' := closure_thickening_subset_cthickening ε _ hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall hε] at hz'
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
  grind [mem_closedBall_iff_norm]

/-- A map complex analytic on `B_{2ε}`, real at the real points of `B_{2ε}`, with
`f(I) ⊆ I` and `0 < |f'| < 1` on `cl B_ε`, lies in `S^ω_ε(I)`. -/
theorem _root_.Challenge.InClass.of_deriv (hε : 0 < ε) (hd : DifferentiableOn ℂ f (nbhd (2 * ε)))
    (him : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0) (hI : ∀ x ∈ I, (f x).re ∈ I)
    (hne : ∀ z ∈ closedNbhd ε, deriv f z ≠ 0) (hlt : ∀ z ∈ closedNbhd ε, ‖deriv f z‖ < 1) : InClass ε f :=
  by
  refine ⟨hd, him, hI, ?_, hne, hlt⟩
  have hsub : closedNbhd ε ⊆ nbhd (2 * ε) := closure_nbhd_subset (by linarith)
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_closure_nbhd ε).exists_isMaxOn ⟨0, zero_mem_closure_nbhd hε⟩
      ((hd.deriv (isOpen_nbhd _)).continuousOn.mono hsub).norm
  intro z hz
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hε.le hz
  have hxcl := ofReal_mem_closure hε hx
  have hfx : f x = (f x).re := Complex.ext rfl (by bound)
  refine ball_subset_nbhd (hI x hx) (mem_ball_iff_norm.2 ?_)
  rw [← hfx]
  calc
    ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ :=
      (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
        (fun y hy => hd.differentiableAt ((isOpen_nbhd _).mem_nhds (hsub hy))) (fun y hy => hmax hy) hxcl hz
    _ ≤ ‖deriv f w‖ * ε := (mul_le_mul_of_nonneg_left hzx (norm_nonneg _))
    _ < 1 * ε := (mul_lt_mul_of_pos_right (hlt w hw) hε)
    _ = ε := one_mul ε

/-- Nesting of the classes: `S^ω_ε(I) ⊆ S^ω_{ε'}(I)` for `0 < ε' ≤ ε`. -/
theorem _root_.Challenge.InClass.mono   (h : InClass ε f) (hε' : 0 < ε') (hle : ε' ≤ ε) :
    InClass ε' f := by
  have  : nbhd (2 * ε') ⊆ nbhd (2 * ε) := nbhd_mono (by linarith)
  have   := closure_mono (nbhd_mono hle)
  grind [Challenge.InClass.of_deriv, Challenge.InClass.differentiableOn, DifferentiableOn.mono, Challenge.InClass.im_eq_zero, Challenge.InClass.re_mem_I, Challenge.InClass.deriv_ne_zero, Challenge.InClass.norm_deriv_lt_one]

/-! ## AnalyticESC.Conjugation.Composite -/

/-!
# Compositions and periodic words

Compositions `f_w` along nonempty words lie in the class for a smaller `ε`; their functions
`Ĥ_{f_w}` of (5.1) are dual natural projections of periodic words; and if the dual natural
projections of the constant words agree, then all dual natural projections agree (the remark
after Theorem 1.12).
-/

namespace Word

/-- A periodic word is its period followed by itself. -/
private theorem composite_inf_periodic_eq_prepend  hm (v : Block N m) :
    inf (periodic hm v) = (inf (periodic hm v)).prepend (List.ofFn v) := by
  congr 1
  funext n
  simp
  split_ifs with hn
  · simp [periodic, Nat.mod_eq_of_lt hn]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
    simp [periodic]

end Word

/-- `List.ofFn (w ∘ Fin.rev) = (List.ofFn w)^←`. -/
private theorem composite_ofFn_comp_rev   (w : Fin m → α) :
    List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  grind

namespace IFS

/-- Compositions along nonempty words lie in the class for some `ε' > 0`. -/
theorem inClass_comp (hw : w ≠ []) : InClass (ε / 4) (Φ.comp w) :=
  by
  have := Φ.ε_pos
  have hsub : nbhd (2 * (ε / 4)) ⊆ nbhd ε := nbhd_mono (by linarith)
  have hcl : closedNbhd(ε / 4) ⊆ closedNbhd ε := closure_mono (nbhd_mono (by linarith))
  exact
    Challenge.InClass.of_deriv (by positivity) ((Φ.differentiableOn_comp w).mono hsub)
      (fun x hx => Φ.im_comp_ofReal w (hsub hx)) (fun x => Φ.re_comp_mem_I w)
      (fun z hz => Φ.deriv_comp_ne_zero w (hcl hz)) fun z hz =>
      (Φ.norm_deriv_comp_le w (hcl hz)).trans_lt
        (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne')

/-- `Ĥ_{f_w} = H_{(w^←)^∞}` on `[0,1]`, where `w^←` is the reversed word. -/
theorem hatH_comp_eq_dualProj (hm : 0 < m) w :
    ∀ x ∈ I, hatH (Φ.comp (List.ofFn w)) x = Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) x :=
  by
  let f := Φ.comp (List.ofFn w)
  let A := Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev)))
  have hε : 0 < ε / 4 := by linarith [Φ.ε_pos]
  have hf : InClass (ε / 4) f := Φ.inClass_comp (by simpa using hm.ne')
  have hreal {y : ℝ} hy : f y = (f y).re := Φ.comp_ofReal _ hy
  have hB y (hy : y ∈ I) := by
    have hz := Φ.mem_closure hy
    have h := Φ.dualProj_prepend (List.ofFn (w ∘ Fin.rev)) (.inf (periodic hm (w ∘ Fin.rev))) hz
    rw [← Word.composite_inf_periodic_eq_prepend, composite_ofFn_comp_rev, Φ.dualProj_fin_reverse _ hz,
      List.reverse_reverse] at h
    exact h
  intro x hx
  simpa [← hatH_eq_dualProj hε hf] using
    ((koenigsIFS hε hf).dualProj_eq_of_cocycle
        ((Φ.differentiableOn_dualProj _).continuousOn.comp Complex.continuous_ofReal.continuousOn fun _ =>
          ofReal_mem_nbhd Φ.ε_pos)
        fun _ y hy => by
        change A y = deriv f y * A (f y).re + D² f y / deriv f y
        rw [← hreal hy]
        exact (hB y hy).trans (add_comm _ _))
      (fun _ => 0) x hx

end IFS

/-! ## AnalyticESC.Conjugation.Characterisation -/


/-!
# Single-map conjugation

Individual-map linearisation for Theorem 1.12 and the single-map ODE tools used in its proof.
The equivalences, including the two-map subsystem argument for part (b), are proved in
`Conjugation.PeriodicPoints`.
-/

/-- A function with zero derivative within `[0,1]` at every point of `[0,1]` is constant there. -/
def eq_of_hasDerivWithinAt_zero_I {u : RMap} (hu : ∀ x ∈ I, HasDerivWithinAt u 0 I x) (hx : x ∈ I)
    (hy : y ∈ I) := by
  simpa [sub_eq_zero] using (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hu (by simp) hy hx

/-! ## Single maps of the class -/

section
variable {f : CMap}

/-- At points of `[0,1]`, the derivative of a map of the class is real, nonzero and of modulus
less than one. -/
theorem re_deriv_ne_zero_abs_lt_one (hε : 0 < ε) (hf : InClass ε f) 
    (hx : x ∈ I) : (deriv f x).re ≠ 0 ∧ |(deriv f x).re| < 1 := by
  have hcl  := ofReal_mem_closure hε hx
  
  exact ⟨fun h => hf.deriv_ne_zero _ hcl (Complex.ext h (im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn
    hf.im_eq_zero (ofReal_mem_nbhd (by linarith) hx)
  )),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

/-- A solution of `φ'' = Re Ĥ_f φ'` on `[0,1]` conjugates `f` to an affine contraction. -/
theorem char_exists_conj_of_ode (hε : 0 < ε) (hf : InClass ε f) (hφ : AnalyticOnNhd ℝ φ I)
    (hode : ∀ x ∈ I, D² φ x = (hatH f x).re * deriv φ x) :
    ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, φ (f x).re = lam * φ x + t :=
  by
  let F := realRestrict f
  have hFa := hf.analytic_real hε
  have hr k x (hx : x ∈ I) :=
    iteratedDeriv_ofReal (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero k (ofReal_mem_nbhd (by positivity) hx)
  have hr0 x hx := hr 0 x hx
  have hr1 x hx := hr 1 x hx
  have hr2 x hx := hr 2 x hx
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hr0 hr1 hr2
  obtain ⟨p, hp, hfix⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hFa.continuousOn zero_le_one hf.re_mem_I
  let G := φ ∘ F
  have hGa := fun x hx => (hφ (F x) (hf.re_mem_I x hx)).comp (hFa x hx)
  have hG1 x hx :=
    ((hφ (F x) (hf.re_mem_I x hx)).differentiableAt.hasDerivAt.comp x (hFa x hx).differentiableAt.hasDerivAt).deriv
  have hGode : ∀ x ∈ I, D² G x = (hatH f x).re * deriv G x :=
    by
    intro x hx
    have hG2 := iteratedDeriv_comp_two (hφ (F x) (hf.re_mem_I x hx)).contDiffAt (hFa x hx).contDiffAt
    simp [iteratedDeriv_succ] at hG2
    have hmem := ofReal_mem_nbhd hε hx
    have hH : hatH f x * deriv f x = deriv f x * deriv f x * hatH f (f x) + D² f x :=
      by
      rw [hatH_eq_add hε hf hmem]
      field_simp [hf.deriv_ne_zero _ (subset_closure hmem)]
      ring
    rw [hr0 x hx, hr1 x hx, hr2 x hx] at hH
    have hR := congrArg Complex.re hH
    simp at hR
    rw [hode _ (hf.re_mem_I x hx)] at hG2
    rw [hG1 x hx]
    linear_combination hG2 - deriv φ (f x).re * hR
  obtain ⟨g, hg, hg', hgo⟩ := exists_real_ode_coord hε hf
  refine
    ⟨(deriv f p).re, φ p * (1 - (deriv f p).re), (re_deriv_ne_zero_abs_lt_one hε hf hp).1,
      (re_deriv_ne_zero_abs_lt_one hε hf hp).2, fun x hx => ?_⟩
  have hdp := congrArg Complex.re (hr1 p hp)
  change (f p).re = p at hfix
  have h0 := hG1 p hp
  dsimp [F] at h0 hdp
  rw [hfix] at h0
  have hinit : deriv G p = (deriv f p).re * deriv φ p :=
    by
    rw [h0, hdp]
    ring
  have hr : ∀ x ∈ I, HasDerivWithinAt (fun t => (deriv G t - (deriv f p).re * deriv φ t) / deriv g t) 0 I x :=
    by
    intro x hx
    convert
      (((hGa x hx).deriv.differentiableAt.hasDerivAt.sub
              ((hφ x hx).deriv.differentiableAt.hasDerivAt.const_mul (deriv f p).re)).div
          (hg.1 x hx).deriv.differentiableAt.hasDerivAt (hg' x hx).ne').hasDerivWithinAt using
      1
    rw [hGode x hx, hode x hx, hgo x hx]
    dsimp [Pi.sub_apply]
    ring
  have H :=
    eq_of_hasDerivWithinAt_zero_I
      (by
        intro x hx
        convert
          ((hGa x hx).differentiableAt.hasDerivAt.sub
              ((hφ x hx).differentiableAt.hasDerivAt.const_mul (deriv f p).re)).hasDerivWithinAt using
          1
        have h := eq_of_hasDerivWithinAt_zero_I hr hx hp
        simp [hinit, sub_self, zero_div, div_eq_zero_iff] at h
        exact (h.resolve_right (hg' x hx).ne').symm)
      hx hp
  dsimp [G, F] at H
  rw [hfix] at H
  nlinarith [H]

end
/-! ## AnalyticESC.Separation -/

/-!
# Separation conditions

The natural projection and the Challenge.attractor, the equivalence in Definition 1.2 between the failure
of the SESC and weak super-exponential condensation, the implication SESC ⇒ Challenge.ESC, and the
consequence of having no exact overlaps used in Lemma 4.1.
-/

namespace IFS

theorem tendsto_natProj w : Tendsto (fun n => (Φ.comp (prefix n w) 0).re) atTop (𝓝 (Φ.natProj w)) :=
  by
  have hu : ∀ n, dist (Φ.comp (prefix n w) 0).re (Φ.comp (prefix(n + 1)w) 0).re ≤ 1 * Φ.cmax ^ n :=
    by
    intro n
    have hsplit : prefix(n + 1)w = prefix n w ++ [w n] :=
      by
      rw [List.ofFn_succ']
      simp
    rw [hsplit, Φ.comp_append]
    have h := Φ.abs_re_comp_sub_le (prefix n w) unitInterval.zero_mem (Φ.re_comp_mem_I [w n] unitInterval.zero_mem)
    rw [← Φ.comp_ofReal [w n] unitInterval.zero_mem] at h
    simpa [Real.dist_eq, ] using h
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric Φ.cmax 1 Φ.cmax_lt_one hu)
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem attractor_subset_I : Φ.attractor ⊆ I := by
  rintro _ ⟨w, rfl⟩
  exact isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj w)
    (Eventually.of_forall fun n => Φ.re_comp_mem_I _ unitInterval.zero_mem)

theorem natProj_eq_comp_prefix ω k : Φ.natProj ω = (Φ.comp (prefix k ω) (Φ.natProj shift k ω)).re :=
  by
  set v := shift k ω
  set a := prefix k ω
  have hlist : ∀ n, prefix(n + k)ω = a ++ prefix n v := fun n =>
    List.ext_getElem (by simp [a, Nat.add_comm]) fun l h1 h2 => by grind
  have hc : ContinuousAt (realRestrict(Φ.comp a)) (Φ.natProj v) :=
    Complex.continuous_re.continuousAt.comp
      ((Φ.differentiableAt_comp a (Φ.mem_closure (Φ.attractor_subset_I ⟨v, rfl⟩))).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat k).2 (Φ.tendsto_natProj ω)) ?_
  refine (hc.tendsto.comp (Φ.tendsto_natProj v)).congr fun n => ?_
  rw [Function.comp_apply, hlist n, Φ.comp_append, Function.comp_apply, ← Complex.ofReal_zero, ←
    Φ.comp_ofReal _ unitInterval.zero_mem]

theorem continuous_natProj : Continuous Φ.natProj :=
  by
  refine
    TendstoUniformly.continuous (F := fun n ω => (Φ.comp (prefix n ω) 0).re) (p := atTop) ?_
      (Frequently.of_forall fun n => ?_)
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).eventually
        (gt_mem_nhds hδ)] with
      n hn ω
    have hπ : Φ.natProj shift n ω ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have h := Φ.abs_re_comp_sub_le (prefix n ω) hπ unitInterval.zero_mem
    rw [List.length_ofFn, ← Φ.natProj_eq_comp_prefix] at h
    exact h.trans_lt hn
  fun_prop

/-- `π(ω) = f_{ω₀}(π(σω))`, where `σ` is the left shift. -/
theorem natProj_eq_realMap ω : Φ.natProj ω = Φ.realMap (ω 0) (Φ.natProj shift 1ω) :=
  by
  rw [Φ.natProj_eq_comp_prefix ω 1]
  simp [realMap]

/-- The remark after Theorem 1.6: the attractor is a singleton exactly when the maps have a
common fixed point in `I`. -/
theorem exists_attractor_eq_singleton_iff (hN : 0 < N) : (∃ x, Φ.attractor = { x }) ↔ ∃ x ∈ I, ∀ i, Φ.realMap i x = x :=
  by
  constructor
  · rintro ⟨x, hx⟩
    have hp ω := mem_singleton_iff.1 (hx ▸ show Φ.natProj ω ∈ Φ.attractor from ⟨ω, rfl⟩)
    refine ⟨x, Φ.attractor_subset_I (hx ▸ mem_singleton x), fun i => ?_⟩
    simpa [hp] using (Φ.natProj_eq_realMap fun _ => i).symm
  · rintro ⟨p, hp, hfix⟩
    have : ∀ i, Φ.f i p = p := fun i =>
      Complex.ext (hfix i) (Φ.im_f_ofReal i (nbhd_subset_two (ofReal_mem_nbhd Φ.ε_pos hp)))
    have hc : ∀ w, Φ.comp w p = p := by
      intro w
      induction w <;> aesop
    have hπ : ∀ ω, Φ.natProj ω = p := by
      intro ω
      exact
        sub_eq_zero.1
          (abs_nonpos_iff.1
            (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one)
              (by
                intro n
                have hπ : Φ.natProj shift n ω ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
                have h := Φ.abs_re_comp_sub_le (prefix n ω) hπ hp
                rwa [List.length_ofFn, hc, ← Φ.natProj_eq_comp_prefix] at h)))
    refine ⟨p, ?_⟩
    ext x
    constructor
    · rintro ⟨ω, rfl⟩
      exact hπ ω
    · rintro rfl
      exact ⟨fun _ => ⟨0, hN⟩, hπ _⟩

theorem norm_le_supDist (i j )  (hx : x ∈ I) :
    ‖Φ.comp i x - Φ.comp j x‖ ≤ Challenge.supDist Φ.f i j :=
  le_ciSup (f := fun x : I => ‖Φ.comp i x - Φ.comp j x‖)
    ⟨2, by
      rintro _ ⟨x, rfl⟩
      grind [norm_sub_le, IFS.norm_comp_ofReal_le_one]⟩ ⟨x, hx⟩

theorem esc_of_sesc (h : Φ.SESC) : Challenge.ESC Φ.f := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, Frequently.of_forall h⟩

end IFS

/-! ## AnalyticESC.Conjugation.PeriodicPoints -/

/-!
# Theorem 1.12 (a) along periodic points

The paper's proof of Theorem 1.12 (a). Let `g` be analytic and injective on `[0,1]` with
`g ∘ f_k = λ_k g + t_k` there for every letter `k`, so that `g ∘ f_w = λ_w g + t_w` for every
finite word `w`.

1. Differentiating gives `g'(f_k(x)) f_k'(x) = λ_k g'(x)`, so every `f_k` maps the zero set of
   `g'` in `[0,1]` into itself. This set is closed and `π(i) = lim f_{i₁ ⋯ iₙ}(x)` for every
   `x ∈ [0,1]`, so it contains the attractor once it is nonempty. A non-singleton attractor is
   infinite, and the identity theorem would give `g' ≡ 0`, against injectivity. Hence `g' ≠ 0`
   on `[0,1]`.
2. At the fixed point `p` of `f_w`, `f_w'(p) = λ_w`, and differentiating twice with (2.7) gives
   `g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`.
3. For `i, j ∈ Σ` let `kₙ = i₁ ⋯ iₙ jₙ ⋯ j₁`. The fixed point `p_{kₙ}` lies in
   `f_{i₁ ⋯ iₙ}([0,1])`, so `p_{kₙ} → π(i)`; `f_{kₙ}'(p_{kₙ}) → 0`; and
   `H_{j₁ ⋯ jₙ iₙ ⋯ i₁}(p_{kₙ}) → H_j(π(i))` by `exists_dualProj_bounds`, used to prove Lemma 2.5, uniformly on
   `cl B_ε` and holds for a finite and an infinite word with a common prefix, and the continuity
   of `H_j`. As `g''/g'` is continuous at `π(i)`, `g''/g' = H_j` on the attractor for every `j`,
   and the identity theorem gives `H_j = H_k` on `[0,1]`.

The converse follows the paper as well: `H = H_{k^∞} = Ĥ_{f_k}` for every letter `k`, Lemma 5.1
gives an invertible `g` with `g'' = H g'`, and the second part of Lemma 5.1 conjugates each `f_k`
to `y ↦ f_k'(p_k) y + g(p_k)(1 - f_k'(p_k))`. `theorem_1_12` states Theorem 1.12 (a) and (b) for
systems whose attractor is not a singleton.
-/

/-! ## Analytic maps on `[0,1]` -/

namespace IFS

/-! ## The first step: `g'` has no zero -/

/-! ## The second step: periodic points -/

/-! ## The third step: the limit along periodic points -/

/-- Theorem 1.12 (a), third step of the proof: if `Φ` is conjugated to a self-similar IFS and its
attractor is not a singleton, then all dual natural projections agree on `[0,1]`. -/
private theorem periodic_hatH_f_eq_dualProj_const k :
    ∀ x ∈ I, hatH (Φ.f k) x = Φ.dualProj (.inf fun _ => k) x := by
  simpa +unfoldPartialApp [periodic] using Φ.hatH_comp_eq_dualProj one_pos ![k]

theorem dualProj_eq_of_conjSelfSimilar (hnd : ¬∃ x, Φ.attractor = { x }) (h : ConjSelfSimilar Φ.realMap) :
    ∀ i j : Address N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x :=
  by
  intro i j
  obtain ⟨g, hg, lam, t, hconj⟩ := h
  have hg' : ∀ x ∈ I, deriv g x ≠ 0 := by
    obtain ⟨hga, hinj⟩ := hg
    intro z hz hgz
    set Z :=
      I ∩
        deriv g ⁻¹'
          {0}
            -- `g'(f_k(x)) f_k'(x) = λ_k g'(x)` and `f_k' ≠ 0`, so every `f_k` maps `Z` into itself
            
    have hinv : ∀ k, MapsTo (Φ.realMap k) Z Z := by
      rintro k x ⟨hx, hx0⟩
      have hFx := (Φ.inClass k).re_mem_I x hx
      have hid :=
        hasDerivAt_unique_of_eqOn_I hx
          ((hga _ hFx).differentiableAt.hasDerivAt.comp x
            (AnalyticAt.differentiableAt (analyticAt_f Φ k (mem_closure Φ hx))).hasDerivAt.real_of_complex)
          (((hga x hx).differentiableAt.hasDerivAt.const_mul (lam k)).add_const (t k)) (hconj k).2.2
      refine ⟨hFx, ?_⟩
      rw [hx0, mul_zero] at hid
      exact (mul_eq_zero.1 hid).resolve_right (re_deriv_ne_zero_abs_lt_one Φ.ε_pos (Φ.inClass k) hx).1
    have hzZ : z ∈ Z := ⟨hz, hgz⟩
    have hInf : Z.Infinite := by
      intro hfin
      have hsub : Z.Subsingleton := by
        let k := i 0
        let := hfin.fintype
        have hs := ((hfin.injOn_iff_bijOn_of_mapsTo (hinv k)).1 ((Φ.injOn_re_comp [k]).mono inter_subset_left)).surjOn
        have h :=
          bounded_le_of_le_add_mul (u := fun p : Z × Z => |p.1 - p.2|) (A := 0) (Set.finite_range _).bddAbove
            Φ.cmax_nonneg Φ.cmax_lt_one
            (by
              rintro ⟨x, y⟩
              obtain ⟨a, ha, hax⟩ := hs x.2
              obtain ⟨b, hb, hby⟩ := hs y.2
              simp only [realMap] at hax hby
              exact
                ⟨(⟨a, ha⟩, ⟨b, hb⟩), by
                  simpa [hax, hby] using Φ.abs_re_comp_sub_le_mul [k] (inter_subset_left ha) (inter_subset_left hb)⟩)
        intro x hx y hy
        simpa [sub_eq_zero] using h (⟨x, hx⟩, ⟨y, hy⟩)
      exact hnd ((Φ.exists_attractor_eq_singleton_iff (i 0).pos).2 ⟨z, hz, fun k => hsub (hinv k hzZ) hzZ⟩)
    obtain ⟨c, hc, hacc⟩ := hInf.exists_accPt_of_subset_isCompact isCompact_Icc inter_subset_left
    have hzero :=
      hga.deriv.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Icc hc
        ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2)
    exact
      one_ne_zero
        (hinj unitInterval.one_mem unitInterval.zero_mem
          (eq_of_hasDerivWithinAt_zero_I
            (fun x hx => by simpa [hzero hx] using (hga x hx).differentiableAt.hasDerivAt.hasDerivWithinAt)
            unitInterval.one_mem unitInterval.zero_mem))
  let G x := (D² g x / deriv g x : ℝ)
  have hc : ∀ k, ∀ x ∈ I, G x = deriv (Φ.f k) x * G (Φ.f k x).re + Φ.nonlin k x :=
    by
    intro k
    have hf := Φ.inClass k
    let F := realRestrict(Φ.f k)
    have hFa := hf.analytic_real Φ.ε_pos
    have hr k x (hx : x ∈ I) :=
      iteratedDeriv_ofReal (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero k
        (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hx)
    have hr1 x hx := hr 1 x hx
    have hr2 x hx := hr 2 x hx
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hr1 hr2
    have hFd x hx := (hFa x hx).differentiableAt.hasDerivAt
    have hφd x hx := (hg.1 x hx).differentiableAt.hasDerivAt
    have hφ1d x hx := (hg.1 x hx).deriv.differentiableAt.hasDerivAt
    have hA x hx :=
      hasDerivAt_unique_of_eqOn_I hx ((hφd _ (hf.re_mem_I x hx)).comp x (hFd x hx))
        (((hφd x hx).const_mul (lam k)).add_const (t k)) (hconj k).2.2
    have hB x hx :=
      hasDerivAt_unique_of_eqOn_I hx
        (((hφ1d _ (hf.re_mem_I x hx)).comp x (hFd x hx)).mul (hFa x hx).deriv.differentiableAt.hasDerivAt)
        ((hφ1d x hx).const_mul (lam k)) (by simpa [] using hA)
    intro x hx
    have : deriv F x ≠ 0 := by
      intro hzero
      apply hf.deriv_ne_zero _ (ofReal_mem_closure Φ.ε_pos hx)
      rw [hr1 x hx, hzero, Complex.ofReal_zero]
    dsimp only [G, nonlin]
    rw [hr1 x hx, hr2 x hx, ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    apply congrArg ((↑) : ℝ → ℂ)
    have ha := hA x hx
    have hb := hB x hx
    dsimp [F] at *
    field_simp [hg' x hx, hg' _ (hf.re_mem_I x hx)]
    linear_combination D² g x * ha - deriv g x * hb
  have :=
    Φ.dualProj_eq_of_cocycle
      (fun x hx =>
        (Complex.continuous_ofReal.continuousAt.comp
            ((hg.1 x hx).deriv.deriv.continuousAt.div (hg.1 x hx).deriv.continuousAt (hg' x hx))).continuousWithinAt)
      hc
  grind

/-! ## The converse -/

/-- Theorem 1.12 (a), the converse, along the paper: if all dual natural projections agree on
`[0,1]`, then Lemma 5.1 for `f_{k₀}` gives an invertible `g` with `g'' = H g'`, and the second
part of Lemma 5.1 conjugates each `f_k` by `g` to a similarity. -/
theorem conjSelfSimilar_of_dualProj_eq (h : ∀ i j : Address N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) :
    ConjSelfSimilar Φ.realMap := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun j => j.elim0⟩
  let k₀ : Fin N := ⟨0, hN⟩
  have : ∀ k, ∀ x ∈ I, hatH (Φ.f k) x = hatH (Φ.f k₀) x := fun k x hx => by
    grind [AnalyticESC.IFS.periodic_hatH_f_eq_dualProj_const]
  obtain ⟨g, hco, -, hode⟩ := exists_real_ode_coord Φ.ε_pos (Φ.inClass k₀)
  choose lam t hc using fun k => char_exists_conj_of_ode Φ.ε_pos (Φ.inClass k) hco.1 fun x hx => by grind
  exact ⟨_, hco, lam, t, hc⟩

/-- Theorem 1.12 (b), for every system. -/
theorem subConjSelfSimilar_iff :
    Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Block N m),
        i ≠ j ∧ ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x :=
  by
  have hne : ∀ {m} (w : Block N m), 0 < m → List.ofFn w ≠ [] := by aesop
  have hrev_ne : ∀ {m} {u v : Block N m}, u ≠ v → u ∘ Fin.rev ≠ v ∘ Fin.rev :=
    Fin.rev_surjective.injective_comp_right.ne
  constructor
  · rintro ⟨m, i, j, hij, g, ⟨hg, hinj⟩, lam, t, hconj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hij (by subst h; exact Subsingleton.elim _ _)
    have hf₁ := Φ.inClass_comp (hne i hm)
    have hf₂ := Φ.inClass_comp (hne j hm)
    let Ψ : IFS 2 (ε / 4) :=
      ⟨![Φ.comp (List.ofFn i), Φ.comp (List.ofFn j)], by linarith [Φ.ε_pos], Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩⟩
    by_cases hnd : ∃ x, Ψ.attractor = { x }
    · obtain ⟨p, hp, hfp⟩ := (Ψ.exists_attractor_eq_singleton_iff (by decide)).1 hnd
      have hf0 := hfp 0
      have hf1 := hfp 1
      simp [Ψ, realMap] at hf0 hf1
      have hc0 := (hconj 0).2.2
      have hc1 := (hconj 1).2.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc0 hc1
      have hcomm x (hx : x ∈ I) :=
        hinj (hf₁.re_mem_I _ (hf₂.re_mem_I _ hx)) (hf₂.re_mem_I _ (hf₁.re_mem_I _ hx))
          (by
            rw [hc0 _ (hf₂.re_mem_I _ hx), hc1 _ (hf₁.re_mem_I _ hx)]
            grind)
      have hm' : 0 < m + m := by omega
      have :
        ∀ {u v : Block N m},
          ∀ y ∈ I, Φ.comp (List.ofFn (Fin.append u v)) y = (Φ.comp (List.ofFn u) (Φ.comp (List.ofFn v) y).re).re :=
        fun y hy => by
        rw [List.ofFn_fin_append, Φ.comp_append]
        grind [AnalyticESC.IFS.comp_ofReal, AnalyticESC.IFS.re_comp_mem_I]
      let a := List.ofFn (Fin.append i j)
      let b := List.ofFn (Fin.append j i)
      have hfg :=
        eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b) zero_lt_one subset_rfl
          (by
            intro y hy
            dsimp [a, b]
            grind)
      refine
        ⟨m + m, hm', Fin.append i j ∘ Fin.rev, Fin.append j i ∘ Fin.rev, hrev_ne fun h => hij (funext fun k => ?_),
          fun x hx => ?_⟩
      · simpa using congrFun h (Fin.castAdd m k)
      · rw [← Φ.hatH_comp_eq_dualProj hm' _ x hx, ← Φ.hatH_comp_eq_dualProj hm' _ x hx]
        change hatH (Φ.comp a) x = hatH (Φ.comp b) x
        have hi n : EqOn (Φ.comp a)^[n] (Φ.comp b)^[n] (nbhd ε) := by
          induction n with
          | zero => exact eqOn_refl _ _
          | succ n ih =>
            simpa only [Function.iterate_succ'] using (hfg.comp_right ((Φ.mapsTo_comp a).iterate n)).trans ih.comp_left
        have hz := ofReal_mem_nbhd Φ.ε_pos hx
        apply tsum_congr
        intro n
        rw [hi n hz, (hi n).deriv (isOpen_nbhd _) hz, hfg.deriv (isOpen_nbhd _) ((Φ.mapsTo_comp b).iterate n hz),
          (hfg.deriv (isOpen_nbhd _)).deriv (isOpen_nbhd _) ((Φ.mapsTo_comp b).iterate n hz)]
    · have hH : ∀ x ∈ I, hatH (Φ.comp (List.ofFn i)) x = hatH (Φ.comp (List.ofFn j)) x :=
        by
        intro x hx
        have h :=
          (Ψ.dualProj_eq_of_conjSelfSimilar hnd
              ⟨g, ⟨hg, hinj⟩, lam, t, Fin.forall_fin_two.2 ⟨by solve_by_elim, by solve_by_elim⟩⟩)
            (fun _ => 0) (fun _ => 1) x hx
        rw [← Ψ.periodic_hatH_f_eq_dualProj_const 0 x hx, ← Ψ.periodic_hatH_f_eq_dualProj_const 1 x hx] at h
        simpa [Ψ] using h
      refine ⟨m, hm, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, fun x hx => ?_⟩
      grind [AnalyticESC.IFS.hatH_comp_eq_dualProj]
  · rintro ⟨m, hm, i, j, hij, h⟩
    have hH : ∀ x ∈ I, hatH (Φ.comp (List.ofFn (i ∘ Fin.rev))) x = hatH (Φ.comp (List.ofFn (j ∘ Fin.rev))) x :=
      fun x hx => by
      rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx]
      simpa [Function.comp_def, Fin.rev_rev] using h x hx
    have hε₁ : 0 < ε / 4 := by linarith [Φ.ε_pos]
    have hf₁ := Φ.inClass_comp (hne (i ∘ Fin.rev) hm)
    have hf₂ := Φ.inClass_comp (hne (j ∘ Fin.rev) hm)
    obtain ⟨g, hco, -, hode⟩ := exists_real_ode_coord hε₁ hf₁
    obtain ⟨l₁, t₁, c₁⟩ := char_exists_conj_of_ode hε₁ hf₁ hco.1 hode
    obtain ⟨l₂, t₂, c₂⟩ := char_exists_conj_of_ode hε₁ hf₂ hco.1 fun x hx => by grind
    exact ⟨m, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, _, hco, ![l₁, l₂], ![t₁, t₂], Fin.forall_fin_two.2 ⟨c₁, c₂⟩⟩

/-! ## AnalyticESC.Dual.Derivatives -/

/-- Uniform bounds and common-prefix decay for every derivative, by Cauchy's estimate. -/
theorem exists_iteratedDeriv_bounds :
    ∃ C : ℕ → ℝ,
      (∀ k, 0 < C k) ∧
        (∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) ∧
          ∀ k,
            ∀ x ∈ I,
              ∀ (i j) m,
                Word.AgreePrefix i j m →
                  ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤ 2 * C k * Φ.cmax ^ m :=
  by
  have := Φ.ε_pos
  obtain ⟨M, hM0, hM, hdiff⟩ := Φ.exists_dualProj_bounds
  let C k := k.factorial * M / (ε / 2) ^ k + 1
  refine ⟨C, fun k => by positivity, ?_, ?_⟩
  · intro k x hx w
    exact (norm_iteratedDeriv_le_on_I Φ.ε_pos (Φ.differentiableOn_dualProj w) (hM w) k hx).trans (by linarith)
  · intro k x hx i j m hm
    have h :=
      norm_iteratedDeriv_le_on_I Φ.ε_pos ((Φ.differentiableOn_dualProj i).sub (Φ.differentiableOn_dualProj j))
        (hdiff i j m hm) k hx
    rw [iteratedDeriv_sub
        ((Φ.differentiableOn_dualProj i).analyticOnNhd (isOpen_nbhd ε) x (ofReal_mem_nbhd Φ.ε_pos hx)).contDiffAt
        ((Φ.differentiableOn_dualProj j).analyticOnNhd (isOpen_nbhd ε) x (ofReal_mem_nbhd Φ.ε_pos hx)).contDiffAt] at h
    grind [pow_nonneg, AnalyticESC.IFS.cmax_nonneg]

end IFS

/-! ## AnalyticESC.Main.Dichotomy -/

/-!
# Theorems 1.5 and 2.2

The three cases in the proof of Theorem 2.2, after extracting pairs `a_k u_k`, `b_k u_k`
whose compositions are super-exponentially close:

1. Bounded common suffixes: fix `u_k = u`, pass to the limit on the nondegenerate interval
   `f_u(I)`, and apply the identity theorem.
2. Unbounded suffixes and finite limit words: finite order of vanishing at the limiting point
   contradicts the interval-length lower bound unless the two fixed compositions coincide.
3. Infinite limit words: (3.2), Lemma 3.1 and Lemma 2.9 give (3.3), including the denominator
   `|f_u'|^k`; Lemma 2.11 and analyticity then identify the limiting dual projections.

Theorem 1.5 follows from compactness, Lemma 2.6(c) and Theorem 2.2.
-/

structure RealAnalyticFamily {α : Type*} (ε : ℝ) (F : α → CMap) : Prop where
  holomorphic : ∀ a, DifferentiableOn ℂ (F a) (nbhd ε)
  real_on : ∀ a (x : ℝ), (x : ℂ) ∈ nbhd ε → (F a x).im = 0
  bounded : ∃ M ≥ 0, ∀ a, ∀ z ∈ closedNbhd ε, ‖F a z‖ ≤ M

/-! ## Super-exponentially small sequences -/

/-- `η k` is eventually below `θ ^ n k`, for every `θ > 0`. -/
def SupExpSmall (n : ℕ → ℕ) (η : ℕ → ℝ) :=
  ∀ θ > 0, ∀ᶠ k in atTop, η k ≤ θ ^ n k

namespace SupExpSmall

variable {n : ℕ → ℕ} {η : ℕ → ℝ}

theorem comp (h : SupExpSmall n η)  (hφ : Tendsto φ atTop atTop) :
    SupExpSmall (n ∘ φ) (η ∘ φ) := fun θ hθ => hφ.eventually (h θ hθ)

theorem eventually_le (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η)  (hδ : 0 < δ) :
    ∀ᶠ k in atTop, η k ≤ δ := by
  filter_upwards [h (min δ 1) (lt_min hδ one_pos)] with k hk
  grind [pow_le_of_le_one]

theorem eventually_lt_pow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η)  (hc : 0 < c) :
    ∀ᶠ k in atTop, η k < c ^ n k := by
  filter_upwards [h (c / 2) (half_pos hc)] with k hk
  grind [LE.le.trans_lt, pow_lt_pow_left₀]

/-- `K A^{n_k} η_k^s` is super-exponentially small along with `η_k`. -/
theorem mul_pow_rpow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) (hη : ∀ k, 0 ≤ η k) K
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 < s) :
    SupExpSmall n fun k => K * A ^ n k * η k ^ s := by
  intro θ hθ
  set L := max K 1 * (A + 1)
  have hL : 0 < L := by positivity
  have hθL  := div_pos hθ hL
  
  filter_upwards [h _ (Real.rpow_pos_of_pos hθL _
    )] with k hk
  have h1 := Real.rpow_le_rpow (hη k) hk hs.le
  rw [← Real.rpow_pow_comm (Real.rpow_nonneg hθL.le _),
    Real.rpow_inv_rpow hθL.le hs.ne'] at h1
  have  : K ≤ max K 1 ^ n k := by grind [le_self_pow₀]
  have  : A ^ n k ≤ (A + 1) ^ n k := pow_le_pow_left₀ hA (by linarith) _
  calc K * A ^ n k * η k ^ s ≤ max K 1 ^ n k * (A + 1) ^ n k * (θ / L) ^ n k := by gcongr; exact Real.rpow_nonneg (hη k) _
    _ = (L * (θ / L)) ^ n k := by rw [ mul_pow, mul_pow]
    _ = θ ^ n k := by rw [mul_div_cancel₀ _ hL.ne']

end SupExpSmall

/-! ## Two elementary lemmas -/

/-- Identity theorem along a convergent sequence: if all derivatives of two holomorphic maps are
asymptotically equal along points `p_k → p₀ ∈ I`, the maps agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_close (hε : 0 < ε) {g h : CMap} (hg : DifferentiableOn ℂ g (nbhd ε))
    (hh : DifferentiableOn ℂ h (nbhd ε)) {p : ℕ → ℝ} (hp : ∀ k, p k ∈ I)
    (hclose : ∀ r, ∀ δ > 0, ∀ᶠ k in atTop, ‖iteratedDeriv r g (p k) - iteratedDeriv r h (p k)‖ ≤ δ) :
    EqOn g h (nbhd ε) := by
  obtain ⟨p₀, hp₀, φ, hφ, htend⟩ := isCompact_Icc.tendsto_subseq hp
  suffices heq : ∀ k, iteratedDeriv k g p₀ = iteratedDeriv k h p₀
    by
    have hU := isOpen_nbhd ε
    have hball : ball (p₀ : ℂ) ε ⊆ nbhd ε := ball_subset_nbhd hp₀
    exact
      (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hh.analyticOnNhd hU) (isPreconnected_nbhd ε)
        (ofReal_mem_nbhd hε hp₀)
        (by
          filter_upwards [ball_mem_nhds (p₀ : ℂ) hε] with z hz
          rw [← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball), ←
            Complex.taylorSeries_eq_on_ball' hz (hh.mono hball)]
          simp_rw [heq])
  intro r
  have hcont :
    ∀ f : CMap,
      DifferentiableOn ℂ f (nbhd ε) → Tendsto (fun k => iteratedDeriv r f (p (φ k))) atTop (𝓝 (iteratedDeriv r f p₀)) :=
    by
    intro f hf
    have : ContinuousAt (iteratedDeriv r f) p₀ :=
      by
      rw [iteratedDeriv_eq_iterate]
      exact ((hf.analyticOnNhd (isOpen_nbhd ε)).iterated_deriv r _ (ofReal_mem_nbhd hε hp₀)).continuousAt
    exact this.tendsto.comp ((Complex.continuous_ofReal.tendsto p₀).comp htend)
  have := fun δ hδ => le_of_tendsto ((hcont g hg).sub (hcont h hh)).norm (hφ.tendsto_atTop.eventually (hclose r δ hδ))
  grind [norm_le_zero_iff, le_of_forall_pos_le_add]

namespace IFS

lemma compFamily : RealAnalyticFamily ε Φ.comp :=
  ⟨Φ.differentiableOn_comp, fun w x => Φ.im_comp_ofReal w, by
    obtain ⟨R, hR0, hR⟩ := (isCompact_closure_nbhd ε).isBounded.exists_pos_norm_le
    exact ⟨R, hR0.le, fun w z hz => hR _ (Φ.mapsTo_comp_closure w hz)⟩⟩

lemma dualFamily : RealAnalyticFamily ε Φ.dualProj :=
  ⟨Φ.differentiableOn_dualProj, fun w x => Φ.im_dualProj_ofReal w, Φ.exists_norm_dualProj_le⟩

/-! ## Condensing sequences -/

/-- A condensing sequence, extracted from the failure of the SESC: words `a_k u_k` and `b_k u_k`
of length `n_k = |a_k| + |u_k|`, with `|a_k| = |b_k| ≥ 1` and different last letters of `a_k`
and `b_k`, whose compositions are `η_k`-close on `I`, where `η_k` is super-exponentially small
in `n_k`; together with `f_{u_k}(I) = [p_k, q_k]` and a limit `p_k → p₀`. -/
structure CondSeq where
  a : ℕ → FWord N
  b : ℕ → FWord N
  n : ℕ → ℕ
  η : ℕ → ℝ
  p : ℕ → ℝ
  q : ℕ → ℝ
  length_eq : ∀ k, (a k).length = (b k).length
  length_pos : ∀ k, 0 < (a k).length
  length_le : ∀ k, (a k).length ≤ n k
  getLast?_ne : ∀ k, (a k).getLast? ≠ (b k).getLast?
  η_pos : ∀ k, 0 < η k
  close : ∀ k, ∀ x ∈ Icc (p k) (q k), ‖Φ.comp (a k) x - Φ.comp (b k) x‖ ≤ η k
  small : SupExpSmall n η
  p_nonneg : ∀ k, 0 ≤ p k
  p_lt_q : ∀ k, p k < q k
  q_le_one : ∀ k, q k ≤ 1
  cmin_pow_le : ∀ k, Φ.cmin ^ n k ≤ q k - p k

/-- The failure of the SESC gives a condensing sequence. -/
theorem nonempty_condSeq (h : ¬Φ.SESC) : Nonempty Φ.CondSeq :=
  by
  have h₁ := by simpa [Challenge.SESC] using h
  have h₂ :
    ∀ k : ℕ,
      ∃ a b u : FWord N,
        a.length = b.length ∧
          0 < a.length ∧
            a.getLast? ≠ b.getLast? ∧
              ∀ x ∈ I, ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ ((k : ℝ) + 2)⁻¹ ^ (a.length + u.length) :=
    by
    intro k
    obtain ⟨n, i, j, hij, hlt⟩ := h₁ (k + 2)⁻¹ (by positivity)
    obtain ⟨a, b, u, hi, hj, hlen, hpos, hlast⟩ :=
      List.exists_decomp_of_ne (by simp) fun h => hij (List.ofFn_injective h)
    have : a.length + u.length = n := by rw [← List.length_append, ← hi, List.length_ofFn]
    refine ⟨a, b, u, hlen, hpos, hlast, fun x hx => ?_⟩
    grind [AnalyticESC.IFS.norm_le_supDist]
  choose a b u hlen hpos hlast hclose using h₂
  have hcmin := Φ.cmin_pos
  choose p q hp0 hpq hq1 hmin himg using fun k => Φ.exists_image_comp_eq_Icc (u k)
  exact
    ⟨{  a := a
        b := b
        n := fun k => (a k).length + (u k).length
        η := fun k => ((k : ℝ) + 2)⁻¹ ^ ((a k).length + (u k).length)
        p := p
        q := q
        length_eq := hlen
        length_pos := hpos
        length_le := by omega
        getLast?_ne := hlast
        η_pos := fun k => by positivity
        close := fun k y hy => by
          rw [← himg k] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          rw [← Φ.comp_ofReal _ hx]
          simpa [Φ.comp_append] using hclose k x hx
        small := by
          intro θ hθ
          have h := (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop).inv_tendsto_atTop
          filter_upwards [h.eventually (gt_mem_nhds hθ)] with k hk
          exact pow_le_pow_left₀ (by positivity : 0 ≤ ((k : ℝ) + 2)⁻¹) hk.le _
        p_nonneg := hp0
        p_lt_q := fun k => by
          have := hmin k
          have := pow_pos hcmin (u k).length
          linarith
        q_le_one := hq1
        cmin_pow_le := fun k =>
          (pow_le_pow_of_le_one hcmin.le
                ((Φ.cmin_le_cmax ((a 0).head (List.ne_nil_of_length_pos (hpos 0))).pos).trans Φ.cmax_lt_one.le)
                (Nat.le_add_left _ _)).trans
            (hmin k) }⟩

namespace CondSeq

variable {Φ}

/-- Reindexing a condensing sequence along a strictly increasing map. -/
def comp (S : Φ.CondSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Φ.CondSeq where
  a := S.a ∘ φ
  b := S.b ∘ φ
  n := S.n ∘ φ
  η := S.η ∘ φ
  p := S.p ∘ φ
  q := S.q ∘ φ
  length_eq k := S.length_eq (φ k)
  length_pos k := S.length_pos (φ k)
  length_le k := S.length_le (φ k)
  getLast?_ne k := S.getLast?_ne (φ k)
  η_pos k := S.η_pos (φ k)
  close k := S.close (φ k)
  small := S.small.comp hφ.tendsto_atTop
  p_nonneg k := S.p_nonneg (φ k)
  p_lt_q k := S.p_lt_q (φ k)
  q_le_one k := S.q_le_one (φ k)
  cmin_pow_le k := S.cmin_pow_le (φ k)

def pos_N (S : Φ.CondSeq) :=
  ((S.a 0).head (List.ne_nil_of_length_pos (S.length_pos 0))).pos
lemma one_le_n (S : Φ.CondSeq) k : 1 ≤ S.n k := by
  have := S.length_pos k
  have := S.length_le k
  omega
theorem p_mem (S : Φ.CondSeq) k : S.p k ∈ I :=
  ⟨S.p_nonneg k, (S.p_lt_q k).le.trans (S.q_le_one k)⟩

lemma small_derivatives (S : Φ.CondSeq) {F} (hF : RealAnalyticFamily ε F) (v w : ℕ → α) {η} (hη : ∀ k, 0 < η k)
    (hs : SupExpSmall S.n η) (hc : ∀ᶠ k in atTop, ∀ x ∈ Icc (S.p k) (S.q k), ‖F (v k) x - F (w k) x‖ ≤ η k) r :
    ∃ ζ : ℕ → ℝ,
      (∀ k, 0 < ζ k) ∧
        SupExpSmall S.n ζ ∧
          ∀ᶠ k in atTop,
            ∀ j ≤ r, ∀ x ∈ Icc (S.p k) (S.q k), ‖iteratedDeriv j (F (v k)) x - iteratedDeriv j (F (w k)) x‖ ≤ ζ k :=
  by
  obtain ⟨M, hM, hb⟩ := hF.bounded
  have hε := Φ.ε_pos
  let B (j : ℕ) := j.factorial * M / (ε / 2) ^ j
  have hB j : 0 ≤ B j := by positivity
  let Q := ∑ j ∈ Finset.range (r + 2), B j
  have : 0 ≤ Q := by positivity
  have hexp : 0 < (2 : ℝ)⁻¹ ^ r := by positivity
  let ζ k := (2 + Q) ^ 2 * η k ^ (2 : ℝ)⁻¹ ^ r
  refine
    ⟨ζ, fun k => by have := hη k; positivity, by
      simpa [ζ] using hs.mul_pow_rpow S.one_le_n (fun k => (hη k).le) ((2 + Q) ^ 2) zero_le_one hexp, ?_⟩
  have hj :=
    (hs.mul_pow_rpow S.one_le_n (fun k => (hη k).le) (2 * (2 + Q)) zero_le_one hexp).eventually_lt_pow S.one_le_n
      Φ.cmin_pos
  filter_upwards [hs.eventually_le S.one_le_n one_pos, hj, hc] with k h1 h2 h3
  simp only [one_pow, mul_one] at h2
  have hsub x (hx : x ∈ Icc (S.p k) (S.q k)) := ofReal_mem_nbhd hε (Icc_subset_Icc (S.p_nonneg k) (S.q_le_one k) hx)
  have hd a j x (hx : x ∈ Icc (S.p k) (S.q k)) :=
    iteratedDeriv_ofReal (isOpen_nbhd _) (hF.holomorphic a) (hF.real_on a) j (hsub x hx)
  have hc a j : ContDiffOn ℝ 2 (iteratedDeriv j realRestrict(F a)) {t : ℝ | (t : ℂ) ∈ nbhd ε} :=
    by
    rw [iteratedDeriv_eq_iterate]
    exact fun x hx =>
      (((hF.holomorphic a).analyticOnNhd (isOpen_nbhd _) _ hx).re_ofReal.iterated_deriv j).contDiffAt.contDiffWithinAt
  have hb a j (hj : j ≤ r + 1) x (hx : x ∈ Icc (S.p k) (S.q k)) : |iteratedDeriv j (realRestrict(F a)) x| ≤ Q :=
    by
    have h : ‖iteratedDeriv j (F a) x‖ ≤ Q :=
      (norm_iteratedDeriv_le_on_I hε (hF.holomorphic a) (hb a) j
            (Icc_subset_Icc (S.p_nonneg k) (S.q_le_one k) hx)).trans
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.2 (by omega)))
    rwa [hd a j x hx, Complex.norm_real, Real.norm_eq_abs] at h
  have hηk := hη k
  have : 1 ≤ (2 + Q) ^ 2 := by nlinarith
  have := h2.trans_le (S.cmin_pow_le k)
  suffices H :
    ∀ j ≤ r,
      ∀ x ∈ Icc (S.p k) (S.q k),
        |iteratedDeriv j (realRestrict(F (v k))) x - iteratedDeriv j (realRestrict(F (w k))) x| ≤
          (2 + Q) ^ 2 * η k ^ (2 : ℝ)⁻¹ ^ j
    by
    intro j hj x hx
    rw [hd _ j x hx, hd _ j x hx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact
      (H j hj x hx).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hηk h1 (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)) (sq_nonneg _))
  intro j
  induction j with
  | zero =>
    intro _ x hx
    simp
    have hfg := (Complex.abs_re_le_norm _).trans (h3 x hx)
    simp only [Complex.sub_re] at hfg
    nlinarith
  | succ j ih =>
    intro hjr x hx
    let e := (2 + Q) ^ 2 * η k ^ (2 : ℝ)⁻¹ ^ j
    let f := iteratedDeriv j realRestrict(F (v k))
    let g := iteratedDeriv j realRestrict(F (w k))
    have hM : 0 < e := by positivity
    have hsqrt : Real.sqrt e = (2 + Q) * η k ^ (2 : ℝ)⁻¹ ^ (j + 1) :=
      by
      dsimp [e]
      grind only [Real.sqrt_mul, Real.sqrt_sq, Real.sqrt_eq_rpow, Real.rpow_mul]
    have hexp : η k ^ (2 : ℝ)⁻¹ ^ (j + 1) ≤ η k ^ (2 : ℝ)⁻¹ ^ r :=
      Real.rpow_le_rpow_of_exponent_ge hηk h1 (pow_le_pow_of_le_one (by norm_num) (by norm_num) hjr)
    have : 2 * Real.sqrt e < S.q k - S.p k := by nlinarith
    have hdd : ∀ φ : RMap, D²(iteratedDeriv j φ) = iteratedDeriv (j + 2) φ := by grind only [iteratedDeriv_succ]
    have hs := Real.sqrt_pos.2 hM
    have hs2 := Real.sq_sqrt hM.le
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc (S.p k) (S.q k), |y - x| = Real.sqrt e :=
      by
      by_cases h : x + Real.sqrt e ≤ S.q k
      · exact ⟨x + Real.sqrt e, ⟨by linarith [hx.1], h⟩, by simp⟩
      · refine ⟨x - Real.sqrt e, ?_⟩
        grind only [Set.mem_Icc, abs_of_nonpos]
    have hxy : x ≠ y := by grind only [sub_self, abs_zero]
    have hseg := uIcc_subset_Icc hx hy
    have hTaylor a :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy (((hc a j).mono (hseg.trans hsub)).of_le (by norm_num))
    obtain ⟨ξ₁, hξ₁, h₁⟩ := hTaylor (v k)
    obtain ⟨ξ₂, hξ₂, h₂⟩ := hTaylor (w k)
    have hdx a :=
      ((hc a j).contDiffAt (((isOpen_nbhd ε).preimage Complex.continuous_ofReal).mem_nhds (hsub x hx))).differentiableAt
          (by norm_num) |>.derivWithin
        (uniqueDiffOn_uIcc hxy x left_mem_uIcc)
    simp [hdx] at h₁ h₂
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h₁ h₂
    have hd2 : (y - x) ^ 2 = e := by nlinarith [sq_abs (y - x)]
    rw [hd2] at h₁ h₂
    have hb₁ := hb (v k) (j + 2) (by omega) ξ₁ (hseg (Ioo_subset_Icc_self hξ₁))
    have hb₂ := hb (w k) (j + 2) (by omega) ξ₂ (hseg (Ioo_subset_Icc_self hξ₂))
    rw [← hdd] at hb₁ hb₂
    have : |D² f ξ₁ - D² g ξ₂| ≤ 2 * Q := by grind only [abs_le]
    have hfg := ih (by omega)
    have hmain : |deriv f x - deriv g x| * Real.sqrt e ≤ (2 + Q) * Real.sqrt e * Real.sqrt e :=
      by
      rw [← hyx, ← abs_mul, hyx, mul_assoc, Real.mul_self_sqrt hM.le]
      have e3 : |(D² f ξ₁ - D² g ξ₂) * e / 2| ≤ Q * e :=
        by
        rw [abs_div, abs_mul, abs_of_pos hM]
        nlinarith
      rw [abs_le]
      dsimp only [f, g, e] at *
      constructor <;> nlinarith only [h₁, h₂, hs2, abs_le.mp (hfg x hx), abs_le.mp (hfg y hy), abs_le.mp e3]
    have key := le_of_mul_le_mul_right hmain hs
    dsimp [f, g] at key
    rw [hsqrt, ← iteratedDeriv_succ, ← iteratedDeriv_succ] at key
    nlinarith only [key]

lemma exists_dualProj_small (S : Φ.CondSeq) :
    ∃ η' : ℕ → ℝ,
      (∀ k, 0 < η' k) ∧
        SupExpSmall S.n η' ∧
          ∀ᶠ k in atTop,
            ∀ y ∈ Icc (S.p k) (S.q k),
              ‖Φ.dualProj (.fin (S.a k).reverse) y - Φ.dualProj (.fin (S.b k).reverse) y‖ ≤ η' k :=
  by
  obtain ⟨e, he, hs, hc⟩ := S.small_derivatives Φ.compFamily S.a S.b S.η_pos S.small (Eventually.of_forall S.close) 2
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  have hm := Φ.cmin_pos
  let ζ k := (1 + M) * Φ.cmin⁻¹ ^ S.n k * e k
  refine ⟨ζ, fun k => by have := he k; positivity, ?_, ?_⟩
  · simpa [ζ] using hs.mul_pow_rpow S.one_le_n (fun k => (he k).le) (1 + M) (inv_nonneg.2 hm.le) one_pos
  · filter_upwards [hc] with k hk y hy
    have hz := Φ.mem_closure (Icc_subset_Icc (S.p_nonneg k) (S.q_le_one k) hy)
    have : ‖deriv (Φ.comp (S.b k)) y‖⁻¹ ≤ Φ.cmin⁻¹ ^ S.n k :=
      by
      rw [inv_pow]
      exact
        inv_anti₀ (pow_pos hm _)
          ((pow_le_pow_of_le_one hm.le ((Φ.cmin_le_cmax S.pos_N).trans Φ.cmax_lt_one.le)
                (S.length_eq k ▸ S.length_le k)).trans
            (Φ.cmin_pow_le_norm_deriv_comp (S.b k) hz))
    have h1' := hk 1 (by decide) y hy
    have h2' := hk 2 le_rfl y hy
    simp only [iteratedDeriv_one] at h1'
    simp only [iteratedDeriv_succ] at h2'
    have := (he k).le
    have hM' := hM (.fin (S.a k).reverse) y hz
    rw [Φ.dualProj_fin_reverse _ hz] at hM'
    rw [Φ.dualProj_fin_reverse _ hz, Φ.dualProj_fin_reverse _ hz]
    refine (norm_div_sub_div_le (Φ.deriv_comp_ne_zero _ hz) (Φ.deriv_comp_ne_zero _ hz) h2' h1' hM').trans ?_
    calc
      (1 + M) * e k / ‖deriv (Φ.comp (S.b k)) y‖ ≤ (1 + M) * e k * Φ.cmin⁻¹ ^ S.n k :=
        by
        rw [div_eq_mul_inv]
        gcongr
      _ = ζ k := by ring

/-- Unbounded case: if `|a_k| → ∞`, then two infinite words with different first letters have
equal dual natural projections on `I`. -/
theorem exists_dualProj_eq (S : Φ.CondSeq) (h : Tendsto (fun k => (S.a k).length) atTop atTop)
    :
    ∃ i j : Address N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨φ₁, hφ₁, i, hi⟩ := Word.exists_subseq_tendstoPrefix
    (fun k => (S.a k).reverse) (by simpa using h) ⟨0,S.pos_N⟩
  obtain ⟨φ₂, hφ₂, j, hj⟩ := Word.exists_subseq_tendstoPrefix
    (fun k => (S.b (φ₁ k)).reverse)
    (by simpa  [ ← S.length_eq, Function.comp_def]
        using h.comp hφ₁.tendsto_atTop) ⟨0,S.pos_N⟩
  set T := S.comp (φ₁ ∘ φ₂) (hφ₁.comp hφ₂)
  have hT1 n := hφ₂.tendsto_atTop.eventually (hi n)
  refine ⟨i, j, ?_, ?_⟩
  · intro hij
    obtain ⟨ ⟩ := ((hT1 1).and (hj 1)).exists
    grind [Word.take_eq_take_iff, AnalyticESC.IFS.CondSeq.getLast?_ne, AnalyticESC.Word.get?.eq_1, AnalyticESC.Word.get?.eq_2]
  ·
    obtain ⟨η, hη, hs, hc⟩ := T.exists_dualProj_small
    obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
    have heq : EqOn (Φ.dualProj (.inf i)) (Φ.dualProj (.inf j)) (nbhd ε) := by
      refine eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos (Φ.differentiableOn_dualProj _)
        (Φ.differentiableOn_dualProj _) T.p_mem fun r δ hδ => ?_
      obtain ⟨ζ, -, hζ, hcζ⟩ := T.small_derivatives Φ.dualFamily
        (fun k => .fin (T.a k).reverse) (fun k => .fin (T.b k).reverse) hη hs hc r
      have hδ3 : 0 < δ / 3 := by positivity
      obtain ⟨m⟩ : ∃ m : ℕ, 2 * C r * Φ.cmax ^ m ≤ δ / 3 := by
        have  := by
          simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
            Φ.cmax_lt_one).const_mul (2 * C r)
        exact (this.eventually (ge_mem_nhds hδ3)).exists
      filter_upwards [hζ.eventually_le T.one_le_n hδ3, hcζ,
        hT1 m, hj m]
        with k h1 h2 h3 h4
      have  := hC r _ (T.p_mem k) _ _ m ⟨h3,by simp [h3]⟩
      have  := hC r _ (T.p_mem k) _ _ m ⟨h4,by simp [h4]⟩
      have  := (h2 r le_rfl _ (left_mem_Icc.2 (T.p_lt_q k).le)).trans h1
      rw [← dist_eq_norm]
      refine (dist_triangle4 _
        (iteratedDeriv r (Φ.dualProj (.fin (T.a k).reverse)) (T.p k))
        (iteratedDeriv r (Φ.dualProj (.fin (T.b k).reverse)) (T.p k)) _).trans ?_
      simp only [dist_eq_norm, norm_sub_rev] at *
      linarith!
    exact fun x hx => heq (ofReal_mem_nbhd Φ.ε_pos hx)

end CondSeq

/-- Theorem 2.2: dual separation implies the SESC. -/
theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  obtain ⟨S⟩ := Φ.nonempty_condSeq hS
  by_cases hB : ∃ B, ∃ᶠ k in atTop, (S.a k).length ≤ B
  · obtain ⟨B, hB⟩ := hB
    obtain ⟨⟨a, b⟩, -, hab⟩ :=
      ((List.finite_length_le (Fin N) B).prod (List.finite_length_le (Fin N) B)).frequently_exists (p := fun v k =>
            (S.a k, S.b k) = v).mp
        (hB.mono fun k hk => ⟨(S.a k, S.b k), ⟨hk, (S.length_eq k ▸ hk : (S.b k).length ≤ B)⟩, rfl⟩)
    obtain ⟨φ, hφ, hφab⟩ := extraction_of_frequently_atTop hab
    set T := S.comp φ hφ
    have ha : ∀ k, T.a k = a := fun k => congrArg Prod.fst (hφab k)
    have hb : ∀ k, T.b k = b := fun k => congrArg Prod.snd (hφab k)
    exact
      Φ.not_dualSSC_of_comp_eq (by simpa [ha 0, hb 0] using T.length_eq 0) (by simpa [ha 0, hb 0] using T.getLast?_ne 0)
        (by
          have heq :=
            by
            refine
              eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b) T.p_mem
                fun r δ hδ => ?_
            obtain ⟨ζ, -, hζ, hc⟩ :=
              T.small_derivatives Φ.compFamily T.a T.b T.η_pos T.small (Eventually.of_forall T.close) r
            filter_upwards [hζ.eventually_le T.one_le_n hδ, hc] with k h1 h2
            simpa [ha k, hb k] using (h2 r le_rfl _ (left_mem_Icc.2 (T.p_lt_q k).le)).trans h1
          exact fun x hx => heq (ofReal_mem_nbhd Φ.ε_pos hx))
        h
  · simp only [not_exists, not_frequently, not_le] at hB
    obtain ⟨i, j, hij, heq⟩ := S.exists_dualProj_eq (Filter.tendsto_atTop.2 fun B => (hB B).mono fun k hk => hk.le)
    obtain ⟨x, hx, hne⟩ := h.2 i j hij
    exact hne (heq x hx)

end IFS

/-! ## AnalyticESC.Main.Criterion -/

/-!
# Proposition 1.8

An explicit sufficient condition for the hypothesis of Theorem 1.5: if the distortions
`f_i''/f_i'` of different maps are `α`-apart somewhere on `[0,1]` and `α > 2β c_max/(1 - c_max)`,
then dual natural projections of distinct words of equal length differ, and `Φ` satisfies the
SESC.

The first term of the series (1.4) for `H_w` is `f_a''/f_a'`, where `a` is the first letter of
`w`, and the remaining terms sum to at most `β c_max/(1 - c_max)` on `I`. Hence words with
different first letters have different dual projections at a point of `I`, and, by the identity
theorem, on every nondegenerate subinterval of `I`. Distinct words of equal length are reduced to
this case by the cocycle identity for their longest common prefix.
-/

namespace IFS

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
def beta :=
  ⨆ (x : I) (i : Fin N), ‖Φ.nonlin i x‖

theorem beta_nonneg : 0 ≤ Φ.beta :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_nonlin_le_beta i  (hx : x ∈ I) : ‖Φ.nonlin i x‖ ≤ Φ.beta :=
  le_ciSup_of_le (by
    obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Real.iSup_le (fun i => hM i _ (Φ.mem_closure x.2)) hM0) ⟨x, hx⟩
    (le_ciSup (f := fun i : Fin N => ‖Φ.nonlin i x‖) (by norm_num) i)

/-- If `w` begins with `a`, then `|H_w(x) - (f_a''/f_a')(x)| ≤ β c_max/(1 - c_max)` on `I`. -/
theorem norm_dualProj_sub_nonlin_le   (h : w.get? 0 = some a) 
    (hx : x ∈ I) : ‖Φ.dualProj w x - Φ.nonlin a x‖ ≤ Φ.beta * Φ.cmax / (1 - Φ.cmax) := by
  have hxn  := Φ.mem_closure hx
  have h0 : Φ.dualTerm w 0 x = Φ.nonlin a x := by
    rw [Φ.dualTerm_of_get?_eq_some h]
    cases w <;> simp
  rw [dualProj, (Φ.summable_dualTerm w hxn).tsum_eq_zero_add, h0, add_sub_cancel_left]
  
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left _
  ) fun n => ?_
  calc _ ≤ Φ.beta * Φ.cmax ^ (n + 1) := by
        cases h : w.get? (n + 1) with
        | none =>
          grind [AnalyticESC.IFS.dualTerm_of_get?_eq_none, norm_zero, mul_nonneg, AnalyticESC.IFS.beta_nonneg, pow_nonneg, AnalyticESC.IFS.cmax_nonneg]
        | some i =>
          rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
          have  := Word.length_take_of_get?_eq_some h
          grind [    AnalyticESC.IFS.comp_ofReal, AnalyticESC.IFS.norm_nonlin_le_beta, AnalyticESC.IFS.re_comp_mem_I, AnalyticESC.IFS.norm_deriv_comp_le, mul_le_mul, norm_nonneg]
    _ = _ := by ring

/-- Proposition 1.8. -/
theorem proposition_1_8 (hN : 2 ≤ N) (hα : 0 < α)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖) :
    0 < Φ.beta ∧
      (2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α →
        (∀ i j : Word N, i ≠ j → i.length = j.length → 0 < ⨆ x : I, ‖Φ.dualProj i x - Φ.dualProj j x‖) ∧ Φ.SESC) :=
  by
  refine
    ⟨by
      obtain ⟨x, hx, hαx⟩ := hsep ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      grind [AnalyticESC.IFS.norm_nonlin_le_beta, norm_sub_le], fun hlt => ?_⟩
  have hne : ∀ i j : Word N, i ≠ j → i.length = j.length → ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x :=
    by
    intro i j hij hlen
    have hex : ∃ n, i.get? n ≠ j.get? n := by
      by_contra h
      exact hij (Word.ext_get? (by simpa using h))
    let m := Nat.find hex
    have hm : i.get? m ≠ j.get? m := Nat.find_spec hex
    have hp : ∀ k < m, i.get? k = j.get? k := by
      intro k hk
      simpa using Nat.find_min hex hk
    have hs : (i.get? m).isSome ↔ (j.get? m).isSome := by cases i <;> cases j <;> aesop
    obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d, i.get? m = some c ∧ j.get? m = some d ∧ c ≠ d :=
      by
      cases hi : i.get? m <;> cases hj : j.get? m <;> simp [hi, hj] at hs hm
      exact ⟨_, _, rfl, rfl, hm⟩
    obtain ⟨u, i', j', hu, rfl, rfl⟩ :=
      Word.exists_eq_prepend
        (show Word.AgreePrefix i j m from ⟨Word.take_eq_take_iff.2 hp, Word.length_take_of_get?_eq_some hc⟩)
    rw [← hu, ← Nat.zero_add u.length, Word.get?_prepend_add] at hc hd
    obtain ⟨y, hy, hαy⟩ := hsep c d hcd
    have hne : Φ.dualProj i' y ≠ Φ.dualProj j' y := by
      intro heq
      have := Φ.norm_dualProj_sub_nonlin_le hc hy
      have := Φ.norm_dualProj_sub_nonlin_le hd hy
      have key := norm_sub_le_norm_sub_add_norm_sub (Φ.nonlin c y) (Φ.dualProj i' y) (Φ.nonlin d y)
      rw [norm_sub_rev (Φ.nonlin c y) (Φ.dualProj i' y), heq] at key
      grind
    obtain ⟨p, q, hp, -, hq, hcmin, himg⟩ := Φ.exists_image_comp_eq_Icc u.reverse
    by_contra hall
    have heq : ∀ z ∈ Icc p q, Φ.dualProj i' z = Φ.dualProj j' z :=
      by
      intro z hz
      rw [← himg] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have := Φ.mem_closure hx
      grind [AnalyticESC.IFS.dualProj_prepend, AnalyticESC.IFS.comp_ofReal, @AnalyticESC.IFS.deriv_comp_ne_zero]
    exact
      hne
        ((eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj i') (Φ.differentiableOn_dualProj j')
            (sub_pos.1 ((pow_pos Φ.cmin_pos _).trans_le hcmin)) (Icc_subset_Icc hp hq) heq)
          (ofReal_mem_nbhd Φ.ε_pos hy))
  refine ⟨fun i j hij hlen => ?_, Φ.theorem_2_2 ⟨by omega, fun i j hij => hne (.inf i) (.inf j) (by grind) rfl⟩⟩
  obtain ⟨x, hx, h⟩ := hne i j hij hlen
  exact (norm_pos_iff.2 (sub_ne_zero.2 h)).trans_le (le_ciSup (Φ.bddAbove_dualProj_sub i j) ⟨x, hx⟩)

end IFS

/-! ## AnalyticESC.Main.Example -/

/-!
# The polynomial example of Section 1.2.2

The system `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` lies in `𝔖_3` for
`ε = 1/100`, has `c_max < 1/5`, `β ≤ 1` and distortions `1/2`-apart at `0`, so Proposition 1.8
shows that it satisfies the SESC.
-/

/-! ### Points of `cl B_{1/100}` -/

/-- Elementary bounds on the closed complex neighbourhood. -/
private lemma example_bounds  (hz : z ∈ closedNbhd (1 / 100)) :
    ‖z‖ ≤ 101 / 100 ∧ -(1 / 100) ≤ z.re := by
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le (by norm_num) hz
  have h1 := norm_sub_norm_le z x
  have h2 := Complex.abs_re_le_norm (z - x)
  rw [Complex.norm_real, Real.norm_of_nonneg hx.1] at h1
  rw [Complex.sub_re, Complex.ofReal_re] at h2
  grind

/-! ### The maps and their derivatives -/

theorem deriv_exampleMaps i : deriv (exampleMaps i) =
    ![fun _ => 1 / 8, fun z => 1 / 8 + z / 16, fun z => 1 / 16 + z / 16] i := by
  fin_cases i <;> ext z <;> simp [exampleMaps, differentiableAt_pow] <;> ring

theorem exampleMaps_ofReal i (x : ℝ) :
    exampleMaps i x = ![x / 8, x / 8 + x ^ 2 / 32, x / 16 + x ^ 2 / 32 + 29 / 32] i := by
  fin_cases i <;> push_cast <;> rfl

/-! ### Norm estimates -/

private lemma example_norm_deriv_le c  (hz : z ∈ closedNbhd (1 / 100)) :
    ‖c + z / 16‖ ≤ ‖c‖ + 101 / 100 / 16 := by
  apply norm_add_le_of_le le_rfl
  norm_num [norm_div]
  linarith [(example_bounds hz).1]

private lemma example_norm_deriv_le_all i  (hz : z ∈ closedNbhd (1 / 100)) :
    ‖deriv (exampleMaps i) z‖ ≤ 19 / 100 := by
  fin_cases i <;> rw [deriv_exampleMaps]
  · norm_num
  all_goals exact (example_norm_deriv_le _ hz).trans (by norm_num)

/-! ### The three maps lie in the class -/

theorem exampleMaps_inClass i : InClass (1 / 100) (exampleMaps i) := by
  fin_cases i <;> apply Challenge.InClass.of_deriv (by norm_num)
  all_goals solve
    | dsimp [exampleMaps]; fun_prop
    | intro x _; simp only [exampleMaps_ofReal, Complex.ofReal_im]
    | intro x hx
      simp only [exampleMaps_ofReal]
      dsimp
      constructor <;> nlinarith [hx.1, hx.2]
    | intro z hz h
      have := (example_bounds hz).2
      rw [deriv_exampleMaps] at h
      have h := congrArg Complex.re h
      norm_num at h <;> linarith
    | intro z hz
      exact (example_norm_deriv_le_all _ hz).trans_lt (by norm_num)

/-- The example as an IFS in `𝔖_3`, with `ε = 1/100`. -/
def exampleIFS : IFS 3 (1 / 100) where
  f := exampleMaps
  ε_pos := by norm_num
  inClass := exampleMaps_inClass

/-! ### The constants `c_max` and `β` -/

theorem exampleIFS_cmax_lt : exampleIFS.cmax < 1 / 5 := by
  have  : exampleIFS.cmax ≤ 19 / 100 :=
    ciSup_le fun i => Real.iSup_le (fun z => example_norm_deriv_le_all i z.2) (by norm_num)
  linarith

private lemma example_nonlin i z : exampleIFS.nonlin i z =
    ![0, 1 / 16 / (1 / 8 + z / 16), 1 / 16 / (1 / 16 + z / 16)] i := by
  fin_cases i <;> simp [exampleIFS, IFS.nonlin, deriv_exampleMaps]

/-! ### Separation of the distortions and the SESC -/

/-- The example satisfies the SESC. -/
theorem exampleIFS_sesc : exampleIFS.SESC :=
  by
  obtain ⟨hβ, h⟩ :=
    exampleIFS.proposition_1_8 (α := 1 / 2) (by norm_num) (by norm_num) fun i j hij =>
      ⟨0, by norm_num, by fin_cases i <;> fin_cases j <;> norm_num [example_nonlin] at *⟩
  have := exampleIFS_cmax_lt
  have : exampleIFS.beta ≤ 1 := by
    refine ciSup_le fun x => ciSup_le fun i => ?_
    have := x.2.1
    fin_cases i <;> simp [example_nonlin]
    all_goals
      refine div_le_one_of_le₀ (le_trans ?_ (Complex.re_le_norm _)) (norm_nonneg _)
      norm_num
      linarith
  refine (h ?_).2
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The example lies in `𝔖_3` for some `ε > 0` and satisfies the SESC. -/
theorem example_sesc :
    ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ Challenge.SESC exampleMaps :=
  ⟨1 / 100, by norm_num, exampleMaps_inClass, exampleIFS_sesc⟩

/-! ## AnalyticESC.Main.LocalDimension -/

/-!
# The local dimension of the natural measure of the polynomial example

The natural measure `μ = ν ∘ π⁻¹` of the polynomial example in Section 1.2.2, where
`ν` is the Gibbs measure of the potential `s(Φ) log|f'_{ω₁}(π(σω))|`, has local dimension
`s(Φ) - 1/3 < s(Φ)` at `0`.

The Gibbs measure is not constructed here. The results assume a probability measure `ν` on `Σ`
with the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s` for every finite word `w`, which Bowen's
theorem provides for `s = s(Φ)`. The Gibbs property determines `s`: the pressure
`P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` vanishes at `t = s` and at no other `t`.
-/

/-- The cylinder `[w] = {ω ∈ Σ : ω₁ ⋯ ω_{|w|} = w}` of a finite word. -/
def wordCylinder  (w : FWord N) : Set (Address N) :=
  {ω | ∀ k : Fin w.length, ω k = w[k]}

namespace IFS

/-- `‖f_w'‖ = sup_{x ∈ [0,1]} |f_w'(x)|`. -/
def supDeriv w :=
  ⨆ x : I, ‖deriv (Φ.comp w) x‖

/-- The sum `∑_{w ∈ Σ_n} ‖f_w'‖^t`, whose exponential growth rate is the pressure `P(t)`. -/
def pressureSum (t : ℝ) n :=
  ∑ w : Block N n, Φ.supDeriv (List.ofFn w) ^ t

/-- `ν` has the Gibbs property for the potential `s log|f'|`: `ν[w]` is comparable to `‖f_w'‖^s`,
uniformly over finite words `w`. -/
def IsGibbs (s : ℝ) (ν : Measure (Address N)) :=
  ∃ C > 0,
    ∀ w : FWord N, C⁻¹ * Φ.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧ ν.real (wordCylinder w) ≤ C * Φ.supDeriv w ^ s

/-- The prefix map `ω ↦ ω₁ ⋯ ωₙ` is measurable. -/
theorem measurable_prefix n : Measurable fun (ω : Address N) (k : Fin n) => ω k := by fun_prop

/-- The natural projection is measurable, so `ν ∘ π⁻¹` is the image measure of `ν`. -/
def measurable_natProj :=
  Φ.continuous_natProj.measurable

/-- The cylinder of a word of length `n` is the preimage of the word under the prefix map. -/
theorem wordCylinder_ofFn  v :
    wordCylinder (List.ofFn v) = (fun (ω : Address N) (k : Fin n) => ω k) ⁻¹' {v} := by
  simp [wordCylinder]
  all_goals grind

/-- The measure of the set of infinite words whose prefix of length `n` lies in `S` is the sum of
the measures of the cylinders of the words in `S`. -/
theorem sum_measureReal_wordCylinder (ν : Measure (Address N)) [IsFiniteMeasure ν] n
    (S : Finset (Block N n)) :
    ∑ v ∈ S, ν.real (wordCylinder (List.ofFn v)) =
      ν.real ((fun ω (k : Fin n) => ω k) ⁻¹' ↑S) := by
  rw [← map_measureReal_apply (measurable_prefix n) MeasurableSet.of_discrete,
    ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [wordCylinder_ofFn, map_measureReal_apply (measurable_prefix n) MeasurableSet.of_discrete]

/-- `|f_w'(x)| ≤ ‖f_w'‖` for `x ∈ [0,1]`. -/
theorem norm_deriv_le_supDeriv w  (hx : x ∈ I) :
    ‖deriv (Φ.comp w) x‖ ≤ Φ.supDeriv w :=
  le_ciSup (f := fun x : I => ‖deriv (Φ.comp w) x‖) ⟨Φ.cmax ^ w.length, by
    rintro _ ⟨x, rfl⟩
    exact Φ.norm_deriv_comp_le w (Φ.mem_closure x.2)⟩ ⟨x, hx⟩

/-- `‖f_w'‖ ≤ c_max^{|w|}`. -/
theorem supDeriv_le w : Φ.supDeriv w ≤ Φ.cmax ^ w.length := ciSup_le fun x => Φ.norm_deriv_comp_le w (Φ.mem_closure x.2)

/-- `c_min^{|w|} ≤ ‖f_w'‖`. -/
def cmin_pow_le_supDeriv w :=
  (Φ.cmin_pow_le_norm_deriv_comp w (Φ.mem_closure unitInterval.zero_mem)).trans
    (Φ.norm_deriv_le_supDeriv w unitInterval.zero_mem)

/-- `‖f_w'‖ > 0` for a nonempty alphabet. -/
def supDeriv_pos w :=
  (pow_pos Φ.cmin_pos _).trans_le (Φ.cmin_pow_le_supDeriv w)

/-- Bounded distortion: `log ‖f_w'‖` and `log |f_w'(y)|` differ by at most a constant, for all
finite words `w` and `y ∈ I`. -/
theorem exists_log_distortion :
    ∃ Δ, 0 ≤ Δ ∧ ∀ w {y}, y ∈ I → |Real.log (Φ.supDeriv w) - Real.log ‖deriv (Φ.comp w) y‖| ≤ Δ :=
  by
  have hmem := fun {x} (hx : x ∈ I) => Φ.mem_closure hx
  obtain ⟨M, hM0, hM, -⟩ := Φ.exists_dualProj_bounds
  refine ⟨M, hM0, fun w y hy => ?_⟩
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (((Φ.differentiableOn_comp w).deriv (isOpen_nbhd ε)).continuousOn.comp Complex.continuous_ofReal.continuousOn
          fun x => ofReal_mem_nbhd Φ.ε_pos).norm
  have he : Φ.supDeriv w = ‖deriv (Φ.comp w) x‖ :=
    le_antisymm (ciSup_le fun t => hmax t.2) (Φ.norm_deriv_le_supDeriv w hx)
  rw [he]
  have hxy : |x - y| ≤ 1 := by grind
  exact
    (abs_log_norm_sub_le (fun t ht => (Φ.analyticAt_comp w (hmem ht)).deriv.differentiableAt)
          (fun t ht => Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos ht))
          (fun t ht => Φ.deriv_comp_ne_zero w (hmem ht))
          (fun t ht => by
            rw [← Φ.dualProj_fin_reverse w (hmem ht)]
            exact hM _ _ (hmem ht))
          hx hy).trans
      (by simpa using mul_le_mul_of_nonneg_left hxy hM0)

theorem pr_pressureSum_pos (hN : 0 < N) t n : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos _) t)
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩

/-- Raising the exponent from `t` to `t + h` multiplies each term by a factor between
`c_min^{nh}` and `c_max^{nh}`. -/
theorem pr_log_pressureSum_add (hN : 0 < N) t (hh : 0 ≤ h) n :
    Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmin) ≤ Real.log (Φ.pressureSum (t + h) n) ∧
      Real.log (Φ.pressureSum (t + h) n) ≤ Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmax) :=
  by
  have hcmin := Φ.cmin_pos
  have := hcmin.trans_le (Φ.cmin_le_cmax hN)
  have : ∀ c : ℝ, 0 < c → Real.log ((c ^ n) ^ h) = n * (h * Real.log c) := fun c hc =>
    by
    rw [Real.log_rpow (pow_pos hc n), Real.log_pow]
    ring
  have hP := Φ.pr_pressureSum_pos hN
  have hle :
    Φ.pressureSum t n * (Φ.cmin ^ n) ^ h ≤ Φ.pressureSum (t + h) n ∧
      Φ.pressureSum (t + h) n ≤ Φ.pressureSum t n * (Φ.cmax ^ n) ^ h :=
    by
    constructor <;> simp only [pressureSum, Finset.sum_mul] <;> apply Finset.sum_le_sum <;> intro v hv
    all_goals
      have := Φ.supDeriv_pos (List.ofFn v)
      rw [Real.rpow_add (Φ.supDeriv_pos _) t h]
      gcongr
    · simpa using Φ.cmin_pow_le_supDeriv (List.ofFn v)
    · simpa using Φ.supDeriv_le (List.ofFn v)
  have := Real.log_le_log (mul_pos (hP t n) (by positivity)) hle.1
  have := Real.log_le_log (hP (t + h) n) hle.2
  constructor <;> grind [Real.log_mul, Real.rpow_pos_of_pos, pow_pos]

/-- The pressure has a unique zero `s(Φ) ≥ 0`: the limit `lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t`
exists and equals `0` exactly for `t = s(Φ)`. -/
theorem exists_pressure_zero (hN : 0 < N) :
    ∃ s : ℝ,
      0 ≤ s ∧
        0 ≤ Real.log N + s * Real.log Φ.cmax ∧
          ∀ t, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s :=
  by
  set a := fun t n => Real.log (Φ.pressureSum t n) / n
  set P := fun t => limUnder atTop (a t)
  have hP : ∀ t, 0 ≤ t → Tendsto (a t) atTop (𝓝 (P t)) :=
    by
    intro t ht
    apply tendsto_nhds_limUnder
    have hsub : Subadditive fun n => Real.log (Φ.pressureSum t n) :=
      by
      intro m n
      have hP := Φ.pr_pressureSum_pos hN t
      rw [← Real.log_mul (hP m).ne' (hP n).ne']
      apply Real.log_le_log (hP _)
      rw [AnalyticESC.IFS.pressureSum, AnalyticESC.IFS.pressureSum, AnalyticESC.IFS.pressureSum, Finset.sum_mul_sum, ←
        Fintype.sum_prod_type', ← (Fin.appendEquiv m n).sum_comp]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [funext (Fin.appendEquiv_apply m n p), List.ofFn_fin_append, ←
        Real.mul_rpow (Φ.supDeriv_pos _).le (Φ.supDeriv_pos _).le]
      refine Real.rpow_le_rpow (Φ.supDeriv_pos _).le ?_ ht
      refine ciSup_le fun x => ?_
      have hx := x.2
      have := Φ.mem_closure hx
      grind [AnalyticESC.IFS.norm_deriv_le_supDeriv, AnalyticESC.IFS.re_comp_mem_I, AnalyticESC.IFS.deriv_comp_append,
        norm_mul, AnalyticESC.IFS.comp_ofReal, mul_le_mul, norm_nonneg]
    refine ⟨hsub.lim, hsub.tendsto_lim ⟨t * Real.log Φ.cmin, ?_⟩⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      exact mul_nonpos_of_nonneg_of_nonpos ht (Real.log_neg Φ.cmin_pos ((Φ.cmin_le_cmax hN).trans_lt Φ.cmax_lt_one)).le
    · have h := (Φ.pr_log_pressureSum_add hN 0 ht n).1
      have h0 : 0 ≤ Real.log (Φ.pressureSum 0 n) := by simp [pressureSum] <;> positivity
      rw [zero_add] at h
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hn']
      nlinarith
  set lmin := Real.log Φ.cmin
  set lmax := Real.log Φ.cmax with hlmax_def
  have hlmax := Real.log_neg (Φ.cmin_pos.trans_le (Φ.cmin_le_cmax hN)) Φ.cmax_lt_one
  have hmono : ∀ t h, 0 ≤ t → 0 ≤ h → P t + h * lmin ≤ P (t + h) ∧ P (t + h) ≤ P t + h * lmax :=
    by
    intro t h ht hh
    have hev : ∀ᶠ n : ℕ in atTop, a (t + h) n - a t n ∈ Icc (h * lmin) (h * lmax) :=
      by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨⟩ := Φ.pr_log_pressureSum_add hN t hh n
      dsimp only [a]
      rw [← sub_div, mem_Icc, le_div_iff₀ hn', div_le_iff₀ hn']
      constructor <;> linarith
    have H := isClosed_Icc.mem_of_tendsto ((hP (t + h) (by linarith)).sub (hP t ht)) hev
    constructor <;> linarith [H.1, H.2]
  have hPzero : P 0 = Real.log N := by
    apply tendsto_nhds_unique (hP 0 le_rfl)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : n ≠ 0 := by positivity
    simp [a, pressureSum, Real.log_pow, hn', mul_div_cancel_left₀]
  have hP0 : 0 ≤ P 0 := hPzero ▸ by positivity
  have hcont : ContinuousOn P (Ici 0) :=
    by
    refine (LipschitzOnWith.of_dist_le' (K := -lmin) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq]
    wlog hxy : x ≤ y generalizing x y
    · simpa only [abs_sub_comm] using this y hy x hx (le_of_not_ge hxy)
    obtain ⟨h1, h2⟩ := hmono x (y - x) hx (sub_nonneg.2 hxy)
    rw [add_sub_cancel] at h1 h2
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    constructor <;>
      nlinarith
        -- the intermediate value theorem on `[0, T]` with `P(T) ≤ 0`
        
  set T := P 0 / -lmax with hT_def
  have hT : 0 ≤ T := div_nonneg hP0 (by linarith)
  obtain ⟨s, hs, hPs⟩ : 0 ∈ P '' Icc 0 T :=
    intermediate_value_Icc' hT (hcont.mono fun x hx => hx.1)
      ⟨by
        have h2 := (hmono 0 T le_rfl hT).2
        simp_all [div_neg, LT.lt.ne], hP0⟩
  refine ⟨s, hs.1, ?_, fun t => ⟨fun h => ?_, ?_⟩⟩
  · simpa [zero_add, hPzero, hPs, lmax] using (hmono 0 s le_rfl hs.1).2
  · rcases lt_or_ge t 0 with ht | ht
    · -- for `t < 0`, every term is at least `c_max^{nt} ≥ 1`
      
      have := mul_pos_of_neg_of_neg ht hlmax
      have hev : ∀ᶠ n : ℕ in atTop, t * lmax ≤ a t n :=
        by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have h1 := (Φ.pr_log_pressureSum_add hN t (neg_nonneg.2 ht.le) n).2
        have h0 : 0 ≤ Real.log (Φ.pressureSum 0 n) := by simp [pressureSum, Real.log_pow] <;> positivity
        simp only [add_neg_cancel] at h1
        rw [le_div_iff₀ hn']
        nlinarith
      have := ge_of_tendsto h hev
      linarith
    · have := tendsto_nhds_unique (hP t ht) h
      by_contra hts
      rcases lt_or_gt_of_ne hts with hts | hts
      · have := (hmono t (s - t) ht (sub_nonneg.2 hts.le)).2
        rw [add_sub_cancel] at this
        nlinarith
      · have := (hmono s (t - s) hs.1 (sub_nonneg.2 hts.le)).2
        rw [add_sub_cancel] at this
        nlinarith
  · rintro rfl
    rw [← hPs]
    exact hP t hs.1

end IFS

/-! ### The local dimension: an analytic lemma -/

/-- If `a ρ^n ≤ m(r) ≤ b ρ^n` whenever `λ^{n+2} < r ≤ λ^{n+1}`, then
`log m(r) / log r → log ρ / log λ` as `r → 0⁺`. -/
private theorem tendsto_log_div_log_of_bounds {m : RMap} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hρ : 0 < ρ) (ha : 0 < a)
    (hb : 0 < b) (h : ∀ n r, lam ^ (n + 2) < r → r ≤ lam ^ (n + 1) → a * ρ ^ n ≤ m r ∧ m r ≤ b * ρ ^ n) :
    Tendsto (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0) (𝓝 (Real.log ρ / Real.log lam)) :=
  by
  set d := Real.log ρ / Real.log lam
  set K := |Real.log a| + |Real.log b| + |d| * (2 * |Real.log lam|)
  have hL := Real.log_neg hlam0 hlam1
  have hbound : ∀ r, 0 < r → r < lam → |Real.log (m r) - d * Real.log r| ≤ K :=
    by
    intro r hr0 hr
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr0 (hr.le.trans hlam1.le) hlam0 hlam1
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := by
      rcases k with _ | n
      · rw [zero_add] at hk1
        linarith
      · exact ⟨n, rfl⟩
    obtain ⟨h1, h2⟩ := h n r hk1 hk2
    have hρn := pow_pos hρ n
    have hl1 := Real.log_le_log (mul_pos ha hρn) h1
    have hl2 := Real.log_le_log ((mul_pos ha hρn).trans_le h1) h2
    have hr1 := Real.log_lt_log (pow_pos hlam0 _) hk1
    have hr2 := Real.log_le_log hr0 hk2
    simp [Real.log_mul ha.ne' hρn.ne', Real.log_mul hb.ne' hρn.ne', Real.log_pow] at hl1 hl2
    simp [Real.log_pow, Nat.cast_add, Nat.cast_one] at hr1 hr2
    have : |n * Real.log lam - Real.log r| ≤ 2 * |Real.log lam| := by grind [abs_le, abs_of_neg hL]
    have : |Real.log (m r) - n * Real.log ρ| ≤ |Real.log a| + |Real.log b| := by
      grind [abs_le, le_abs_self, neg_abs_le, abs_nonneg]
    rw [show Real.log (m r) - d * Real.log r = Real.log (m r) - n * Real.log ρ + d * (n * Real.log lam - Real.log r) by
        dsimp [d]; field_simp [hL.ne]; ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    dsimp [K]
    gcongr
  have H :=
    (bdd_le_mul_tendsto_zero' K
          (by
            filter_upwards [Ioo_mem_nhdsGT hlam0] with r hr
            exact hbound r hr.1 hr.2)
          Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot).add_const
      d
  simp only [zero_add] at H
  apply H.congr'
  filter_upwards [Ioo_mem_nhdsGT hlam0] with r hr
  have := (Real.log_neg hr.1 (hr.2.trans hlam1)).ne
  dsimp
  field_simp
  ring

/-! ### The local dimension: the maps `f₁` and `f₂` of the example

The Lean letters `0, 1, 2` index the maps `f₁, f₂, f₃` of the paper. Words over the letters `0, 1`
are the words `w` with `i ≠ 2` for every letter `i` of `w`. -/

/-- The common fixed point and multiplier of words over the first two maps. -/
private theorem ld_comp_zero (hw : ∀ i ∈ w, i ≠ 2) :
    exampleIFS.comp w 0 = 0 ∧ deriv (exampleIFS.comp w) 0 = (1 / 8) ^ w.length := by
  induction w with
  | nil => simp
  | cons i w
    ih =>
    have hf : exampleIFS.f i 0 = 0 ∧ deriv (exampleIFS.f i) 0 = 1 / 8 := by
      fin_cases i <;> simp [exampleIFS, deriv_exampleMaps] <;> simp_all [exampleMaps]
    rw [exampleIFS.deriv_comp_cons i w (zero_mem_closure_nbhd (by norm_num))]
    simp [ih (by grind), hf, pow_succ, mul_comm]

/-- A fixed distortion constant for the example. -/
def ldD :=
  Real.exp exampleIFS.exists_log_distortion.choose
theorem ldD_pos : 0 < ldD := Real.exp_pos _

/-- Uniform derivative bounds for words over `0, 1`. -/
private theorem ld_supDeriv_bounds  (hw : ∀ i ∈ w, i ≠ 2) :
    (1 / 8 ) ^ w.length ≤ exampleIFS.supDeriv w ∧
      exampleIFS.supDeriv w ≤ ldD * (1 / 8 ) ^ w.length := by
  have hd : ‖deriv (exampleIFS.comp w) 0‖ = (1 / 8 )^w.length := by
    rw [(ld_comp_zero hw).2]
    norm_num
  refine ⟨hd ▸ exampleIFS.norm_deriv_le_supDeriv w unitInterval.zero_mem, ?_⟩
  have h := (abs_le.1 (exampleIFS.exists_log_distortion.choose_spec.2 w unitInterval.zero_mem)).2
  simp only [Complex.ofReal_zero] at h
  rw [hd] at h
  have hp : 0 < (1 / 8 : ℝ)^w.length := by positivity
  simpa only [Real.exp_add, Real.exp_log hp, ldD] using
    Real.le_exp_of_log_le (sub_le_iff_le_add.1 h)

/-! ### The local dimension: cylinders of words over the letters `0, 1` -/

/-- The words of length `n` over the letters `0, 1`. -/
private def ldWords n : Finset (Block 3 n) := Fintype.piFinset fun _ => {0, 1}

private theorem ld_mem_words   : v ∈ ldWords n ↔ ∀ k, v k ≠ 2 := by
  grind [AnalyticESC.ldWords]

private theorem ld_ofFn_ne_two   (hv : v ∈ ldWords n) :
    ∀ i ∈ List.ofFn v, i ≠ 2 := by
  grind [AnalyticESC.ld_mem_words]

/-! ### The local dimension: the natural projection near `0` -/

/-- Prefixes over `0, 1` give geometrically small natural projections. -/
theorem example_natProj_le (h : ∀ k : Fin n, ω k ≠ 2) : exampleIFS.natProj ω ≤ ldD * (1 / 8) ^ n :=
  by
  have hy := exampleIFS.attractor_subset_I ⟨shift n ω, rfl⟩
  let w := prefix n ω
  have hw := ld_ofFn_ne_two (ld_mem_words.2 h)
  have H :=
    (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz =>
        (exampleIFS.differentiableAt_comp w (exampleIFS.mem_closure hz)).hasDerivAt.comp_ofReal.hasDerivWithinAt)
      (fun z hz => (exampleIFS.norm_deriv_le_supDeriv w hz).trans (ld_supDeriv_bounds hw).2) unitInterval.zero_mem hy
  simp only [Complex.ofReal_zero] at H
  rw [(ld_comp_zero hw).1, sub_zero, sub_zero, Real.norm_of_nonneg hy.1] at H
  rw [exampleIFS.natProj_eq_comp_prefix ω n]
  refine (Complex.re_le_norm _).trans (H.trans ?_)
  simpa [] using mul_le_of_le_one_right (mul_nonneg ldD_pos.le (by positivity)) hy.2

/-- Any occurrence of `2` in position `k` forces `π(ω) ≥ (29/32) 8^{-k}`. -/
private theorem ld_le_natProj (hk : ω k = 2) : 29 / 32 * (1 / 8) ^ k ≤ exampleIFS.natProj ω := by
  induction k generalizing ω with
  | zero =>
    have h := (exampleIFS.attractor_subset_I ⟨shift 1ω, rfl⟩).1
    rw [exampleIFS.natProj_eq_realMap]
    simp [pow_zero, mul_one]
    change 29 / 32 ≤ (exampleMaps (ω 0) (exampleIFS.natProj shift 1ω)).re
    rw [hk, exampleMaps_ofReal]
    dsimp
    nlinarith
  | succ k ih =>
    rw [exampleIFS.natProj_eq_realMap, pow_succ]
    change _ ≤ (exampleIFS.f (ω 0) (exampleIFS.natProj shift 1ω)).re
    calc
      _ ≤ exampleIFS.natProj shift 1ω / 8 := by nlinarith [ih (ω := shift 1ω) hk]
      _ ≤ _ := by
        generalize ω 0 = i
        fin_cases i <;> simp [exampleIFS, exampleMaps, ← Complex.ofReal_pow] <;>
          nlinarith [sq_nonneg (exampleIFS.natProj shift 1ω - 1)]

/-- The natural measure of the polynomial example in Section 1.2.2: a measure `ν` with the Gibbs
property for the potential `s log|f'|` fixes `s = s(Φ)` as the unique zero of the pressure,
and the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim [IsProbabilityMeasure ν] (hs0 : 0 ≤ s) (hν : exampleIFS.IsGibbs s ν) :
    Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r) (𝓝[>] 0)
      (𝓝 (s - 1 / 3)) :=
  by
  obtain ⟨C, hC, hG⟩ := hν
  set ρ : ℝ := 2 * (1 / 8) ^ s
  have hρ : 0 < ρ := by positivity
  have hsum n :
    C⁻¹ * ρ ^ n ≤ ∑ v ∈ ldWords n, ν.real (wordCylinder (List.ofFn v)) ∧
      ∑ v ∈ ldWords n, ν.real (wordCylinder (List.ofFn v)) ≤ C * ldD ^ s * ρ ^ n :=
    by
    dsimp only [ρ]
    have hterm :
      ∀ v ∈ ldWords n,
        C⁻¹ * ((1 / 8) ^ s) ^ n ≤ ν.real (wordCylinder (List.ofFn v)) ∧
          ν.real (wordCylinder (List.ofFn v)) ≤ C * ldD ^ s * ((1 / 8) ^ s) ^ n :=
      by
      intro v hv
      obtain ⟨h1, h2⟩ := ld_supDeriv_bounds (ld_ofFn_ne_two hv)
      rw [List.length_ofFn] at h1 h2
      have h3 := Real.rpow_le_rpow (by positivity) h1 hs0
      have h4 := Real.rpow_le_rpow (by linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 8) n]) h2 hs0
      rw [Real.mul_rpow ldD_pos.le (by positivity), ← Real.rpow_pow_comm (by norm_num)] at h4
      rw [← Real.rpow_pow_comm (by norm_num)] at h3
      constructor
      · exact (mul_le_mul_of_nonneg_left h3 (inv_pos.2 hC).le).trans (hG _).1
      ·
        calc
          _ ≤ C * (ldD ^ s * ((1 / 8) ^ s) ^ n) := (hG _).2.trans (mul_le_mul_of_nonneg_left h4 hC.le)
          _ = _ := by ring
    simpa [ldWords, Fintype.card_piFinset, mul_pow, mul_comm, mul_left_comm, mul_assoc] using
      And.intro (Finset.sum_le_sum fun v hv => (hterm v hv).1) (Finset.sum_le_sum fun v hv => (hterm v hv).2)
  have hlow : ∀ n, C⁻¹ * ρ ^ n ≤ ν.real (exampleIFS.natProj ⁻¹' closedBall 0 (ldD * (1 / 8) ^ n)) :=
    by
    intro n
    refine (hsum n).1.trans ?_
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1]
    exact example_natProj_le (ld_mem_words.1 hω)
  have hup :
    ∀ n r, r < 29 / 32 * (1 / 8) ^ n → ν.real (exampleIFS.natProj ⁻¹' closedBall 0 r) ≤ C * ldD ^ s * ρ ^ (n + 1) :=
    by
    intro n r hr
    refine le_trans ?_ (hsum (n + 1)).2
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, mem_closedBall] at hω
    have := (le_abs_self _).trans hω
    rw [mem_preimage, Finset.mem_coe, ld_mem_words]
    intro k h2
    have h1 := ld_le_natProj h2
    have h3 : (1 / 8 : ℝ) ^ n ≤ (1 / 8) ^ (k : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_succ_iff.1 k.2)
    linarith
  have hd : s - 1 / 3 = Real.log ρ / Real.log (1 / 8) :=
    by
    have h8 : Real.log (1 / 8) = -(3 * Real.log 2) :=
      by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      ring
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_rpow (by norm_num), h8]
    field_simp
    ring
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one (div_pos (by norm_num : (0 : ℝ) < (1 / 8) ^ 2) ldD_pos) (by norm_num : (1 / 8 : ℝ) < 1)
  rw [hd]
  refine
    tendsto_log_div_log_of_bounds (by norm_num) (by norm_num) hρ (mul_pos (inv_pos.2 hC) (pow_pos hρ k))
      (mul_pos (mul_pos hC (Real.rpow_pos_of_pos ldD_pos s)) hρ) ?_
  intro n r hr1 hr2
  have : (1 / 8 : ℝ) ^ (n + 1) = (1 / 8) ^ n * (1 / 8) := pow_succ _ _
  rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
  constructor
  · have hr : ldD * (1 / 8) ^ (n + k) ≤ r :=
      by
      have := (lt_div_iff₀ ldD_pos).1 hk
      rw [pow_add] at hr1 ⊢
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 8) n]
    calc
      C⁻¹ * ρ ^ k * ρ ^ n = C⁻¹ * ρ ^ (n + k) := by ring
      _ ≤ _ := (hlow (n + k))
      _ ≤ _ := measureReal_mono (preimage_mono (closedBall_subset_closedBall hr))
  · have hr : r < 29 / 32 * (1 / 8) ^ n := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 8) n]
    calc
      _ ≤ C * ldD ^ s * ρ ^ (n + 1) := hup n r hr
      _ = C * ldD ^ s * ρ * ρ ^ n := by ring

/-! ## AnalyticESC.Dimension.Defs -/

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

/-! ### Rapaport's setting: real analytic IFSs on `I` -/

/-! ### Gibbs measures -/

/-! ### Entropy, Lyapunov exponent and self-conformal measures -/

namespace IFS

theorem log_norm_deriv_bounds i  (hx : x ∈ I) :
    Real.log Φ.cmin ≤ Real.log ‖deriv (Φ.f i) x‖ ∧
      Real.log ‖deriv (Φ.f i) x‖ ≤ Real.log Φ.cmax := by
  have  := Φ.cmin_pos
  have  := Φ.cmin_le_norm_deriv i (Φ.mem_closure hx)
  have  := Φ.norm_deriv_le_cmax i (Φ.mem_closure hx)
  grind [Real.log_le_log]

end IFS

/-- Restricting to scales in `(0,1)` does not change the filter at zero from above. -/
theorem scaleZero_map : map (fun r : Scale => (r : ℝ)) scaleZero = 𝓝[>] 0 := by
  apply map_comap_of_mem
  filter_upwards [Ioo_mem_nhdsGT (show 0 < 1 from zero_lt_one)] with r hr
  tauto

theorem scale_tendsto_iff (g : RMap) l :
    Tendsto (fun r : Scale => g r) scaleZero l ↔ Tendsto g (𝓝[>] 0) l := by
  rw [← scaleZero_map]
  rfl

/-! ## AnalyticESC.Dimension.Rapaport -/

/-!
# Theorem 1.6

Rapaport's theorem, as stated in Theorem 1.6 for the class `𝔖_N`: an analytic IFS with a
non-singleton attractor that satisfies the ESC has equality in (1.6). It follows from Rapaport's
Theorem 1.2 and Corollary 1.3 (`RapaportMeasureStatement`, `RapaportSetStatement`), stated for real
analytic maps of `I`, and from the remark after Theorem 1.6: the attractor is a singleton exactly
when the maps have a common fixed point.
-/

namespace IFS

/-! ### The natural projection and the attractor -/

/-- The attractor is invariant: `Λ = ⋃_i f_i(Λ)`. -/
theorem attractor_eq_iUnion : Φ.attractor = ⋃ i, Φ.realMap i '' Φ.attractor := by
  ext x
  simp
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω 0, _, ⟨_, rfl⟩, (Φ.natProj_eq_realMap ω).symm⟩
  · rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩
    let ω'  := fun j => match j with
      | 0 => i
      | j + 1 => ω j
    exact ⟨ω', Φ.natProj_eq_realMap ω'⟩

/-! ### The real maps in Rapaport's setting -/

/-- The compositions of the real maps are the real restrictions of the compositions. -/
theorem realComp_realMap w {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) : realComp Φ.realMap w x = (Φ.comp w x).re := by
  induction w with
  | nil => rfl
  | cons i w
    ih =>
    have : (Φ.comp w x).re = Φ.comp w x := Complex.ext (by simp) (by simp [Φ.im_comp_ofReal w hx])
    simp_all [AnalyticESC.IFS.realMap, Challenge.realComp]

/-- `(φ_w)'(x) = f_w'(x)` at the real points of `B_ε`. -/
theorem abs_deriv_realComp_realMap w {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv (realComp Φ.realMap w) x| = ‖deriv (Φ.comp w) x‖ :=
  by
  have heq : realComp Φ.realMap w =ᶠ[𝓝 x] fun t => (Φ.comp w t).re :=
    by
    filter_upwards [((isOpen_nbhd ε).preimage Complex.continuous_ofReal).mem_nhds hx] with t ht
    exact Φ.realComp_realMap w ht
  rw [heq.deriv_eq, (Φ.differentiableAt_comp w (subset_closure hx)).hasDerivAt.real_of_complex.deriv]
  exact Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w hx)

/-- `|φ_i'(x)| = |f_i'(x)|` at the real points of `B_ε`. -/
theorem abs_deriv_realMap i {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv (Φ.realMap i) x| = ‖deriv (Φ.f i) x‖ :=
  Φ.abs_deriv_realComp_realMap [i] hx

/-- `‖f_w'‖ = sup_{x ∈ I} |φ_w'(x)|`. -/
theorem supDeriv_eq_iSup_realComp w :
    Φ.supDeriv w = ⨆ x : I, |deriv (realComp Φ.realMap w) x| :=
  iSup_congr fun x => (Φ.abs_deriv_realComp_realMap w (ofReal_mem_nbhd Φ.ε_pos x.2)).symm

/-- An analytic IFS with a non-singleton attractor that satisfies the ESC satisfies the
hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3. -/
theorem rapaportHyp (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Challenge.ESC Φ.f) :
    RapaportHyp Φ.realMap where
  mapsTo i x hx := (Φ.inClass i).re_mem_I x hx
  analytic i := (Φ.inClass i).analytic_real Φ.ε_pos
  deriv_pos i x hx := by
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    grind [AnalyticESC.IFS.abs_deriv_realMap, norm_pos_iff, AnalyticESC.IFS.inClass, Challenge.InClass.deriv_ne_zero, subset_closure]
  deriv_lt_one i x hx := by
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    grind [AnalyticESC.IFS.abs_deriv_realMap, AnalyticESC.IFS.inClass, Challenge.InClass.norm_deriv_lt_one, subset_closure]
  no_common_fixed_point h := hnd ((Φ.exists_attractor_eq_singleton_iff hN).2 h)
  exp_separated := by
    obtain ⟨c, hc, hfreq⟩ := hesc
    refine ⟨c, hc, hfreq.mono fun n hn u v huv => ?_⟩
    refine (hn u v huv).trans_eq (iSup_congr fun x => ?_)
    have hx := ofReal_mem_nbhd Φ.ε_pos x.2
    rw [Φ.realComp_realMap _ hx, Φ.realComp_realMap _ hx]
    conv_lhs =>
      change ‖Φ.comp (List.ofFn u) x - Φ.comp (List.ofFn v) x‖
      rw [Φ.comp_ofReal (List.ofFn u) x.2, Φ.comp_ofReal (List.ofFn v) x.2]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The Lyapunov exponent of a self-conformal measure satisfies `χ ≥ -log c_max`. -/
theorem neg_log_cmax_le_lyapunov (hp : IsProbVec p) (hμ : Challenge.IsSelfConformal Φ.f p μ) : -Real.log Φ.cmax ≤ Challenge.lyapunov Φ.f p μ :=
  by
  obtain ⟨hμ1, hμ2, -⟩ := hμ
  rw [Challenge.lyapunov, neg_le_neg_iff]
  calc
    ∑ i, p i * ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ ≤ ∑ i, p i * Real.log Φ.cmax :=
      by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp.1 i).le
      have hb :
        ∀ᵐ x ∂μ,
          Real.log Φ.cmin ≤ Real.log |deriv (Φ.realMap i) x| ∧ Real.log |deriv (Φ.realMap i) x| ≤ Real.log Φ.cmax :=
        (ae_iff.2 hμ2).mono fun x hx =>
          by
          rw [Φ.abs_deriv_realMap i (ofReal_mem_nbhd Φ.ε_pos hx)]
          exact Φ.log_norm_deriv_bounds i hx
      calc
        ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ ≤ ∫ _x, Real.log Φ.cmax ∂μ :=
          integral_mono_ae
            (by
              refine
                Integrable.of_bound (measurable_deriv (Φ.realMap i)).abs.log.aestronglyMeasurable
                  (|Real.log Φ.cmin| + |Real.log Φ.cmax|) (hb.mono fun x hx => ?_)
              grind [Real.norm_eq_abs])
            (integrable_const _) (hb.mono fun x hx => hx.2)
        _ = Real.log Φ.cmax := by simp
    _ = Real.log Φ.cmax := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Theorem 1.6 (Rapaport). An analytic IFS whose attractor is not a singleton and which
satisfies the ESC has equality in (1.6). -/
theorem theorem_1_6 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 0 < N)
    (hnd : ¬∃ x, Φ.attractor = { x }) (hesc : Challenge.ESC Φ.f) : Challenge.DimEquality Φ.f :=
  by
  have hφ := Φ.rapaportHyp hN hnd hesc
  obtain ⟨s, -, -, hs⟩ := Φ.exists_pressure_zero hN
  refine ⟨⟨s, fun t => (tendsto_add_atTop_iff_nat 1).trans (hs t), ?_⟩, ?_⟩
  · apply
      hS Φ.realMap hφ Φ.attractor ⟨_, mem_range_self fun _ => ⟨0, hN⟩⟩ (isCompact_range Φ.continuous_natProj)
        Φ.attractor_subset_I Φ.attractor_eq_iUnion s
    apply
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ =>
          Real.log (∑ u : Block N n, (⨆ x : I, |deriv (realComp Φ.realMap (List.ofFn u)) x|) ^ s) / n) 1).mpr
    refine ((hs s).2 rfl).congr fun n => ?_
    simp [AnalyticESC.IFS.pressureSum, supDeriv_eq_iSup_realComp]
  · intro p hp μ hμ hχ
    exact hM Φ.realMap hφ p hp.1 hp.2 μ hμ.1 hμ.2.1 hμ.2.2 hχ

end IFS

/-! ## AnalyticESC.Dimension.Example -/

/-!
# Dimensions in the polynomial example of Section 1.2.2

The example satisfies the Challenge.SESC, hence the Challenge.ESC, and its attractor is not a singleton, since `f₁`
fixes `0` and `f₃` fixes `1`. By Theorem 1.6, `dim_H Λ = s(Φ)` and `dim μ_p = H(p)/χ` for every
positive probability vector `p`; here `s(Φ) < 1` and `H(p) < χ`, so the minima with `1` in (1.6)
are not attained. Both inequalities follow from `3 c_max < 1`.
-/


/-- The polynomial example of Section 1.2.2: `dim_H Λ = s(Φ) < 1`, and `dim μ_p = H(p)/χ < 1` for every
positive probability vector `p`. -/
theorem example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
        s < 1 ∧
          dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
            ∀ p : Fin 3 → ℝ,
              IsProbVec p →
                ∀ μ : Measure ℝ,
                  IsSelfConformal exampleMaps p μ →
                    ∀ hχ : lyapunov exampleMaps p μ ≠ 0,
                      entropy p < lyapunov exampleMaps p μ ∧
                        ∀ᵐ x ∂μ,
                          Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
                            (𝓝 (divide (entropy p) (lyapunov exampleMaps p μ) hχ)) :=
  by
  have hN : 0 < 3 := by norm_num
  have hc : 3 * exampleIFS.cmax < 1 := by
    have := exampleIFS_cmax_lt
    linarith
  have hc0 := exampleIFS.cmin_pos.trans_le (exampleIFS.cmin_le_cmax hN)
  have hl := Real.log_neg hc0 exampleIFS.cmax_lt_one
  have hl3 := Real.log_neg (by positivity) hc
  rw [Real.log_mul (by norm_num) hc0.ne'] at hl3
  obtain ⟨⟨s, hs, hdim⟩, hloc⟩ :=
    exampleIFS.theorem_1_6 hM hS hN
      (by
        rw [exampleIFS.exists_attractor_eq_singleton_iff hN]
        rintro ⟨x, -, hx⟩
        have h0 := hx 0
        have h2 := hx 2
        change ((x : ℂ) / 8).re = x at h0
        change ((x : ℂ) / 16 + x ^ 2 / 32 + 29 / 32).re = x at h2
        simp at h0
        obtain rfl : x = 0 := by linarith
        norm_num at h2)
      (exampleIFS.esc_of_sesc exampleIFS_sesc)
  obtain ⟨t, -, hb, ht⟩ := exampleIFS.exists_pressure_zero hN
  rw [(hs t).mp ((tendsto_add_atTop_iff_nat 1).mpr ((ht t).2 rfl))] at hb
  have hs1 : s < 1 := by
    by_contra! h1
    have := mul_le_mul_of_nonpos_right h1 hl.le
    linarith
  refine ⟨s, hs, hs1, by simpa [exampleIFS, min_eq_right hs1.le] using hdim, fun p hp μ hμ hχ => ?_⟩
  have hH : entropy p < lyapunov exampleIFS.f p μ :=
    by
    apply lt_of_lt_of_le ?_ (exampleIFS.neg_log_cmax_le_lyapunov hp hμ)
    have hne i := (hp.1 i).ne'
    have h :=
      strictConcaveOn_log_Ioi.concaveOn.le_map_sum (p := fun i => (p i)⁻¹) (fun i _ => (hp.1 i).le) hp.2 fun i _ =>
        inv_pos.2 (hp.1 i)
    simp [smul_eq_mul, hne, Real.log_inv, mul_neg, Finset.sum_neg_distrib] at h
    unfold entropy
    linarith
  refine ⟨hH, ?_⟩
  have h := hloc p hp μ hμ hχ
  unfold divide at h ⊢
  rwa [min_eq_right ((div_lt_one ((neg_pos.mpr hl).trans_le (exampleIFS.neg_log_cmax_le_lyapunov hp hμ))).2 hH).le] at h

/-! ## AnalyticESC.Dimension.NaturalMeasure -/

/-!
# The natural measure

From Bowen's theorem (`BowenGibbsStatement`), the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs
measure `ν`. When `s = s(Φ)`, `ν` has the Gibbs property `ν[w] ≍ ‖f_w'‖^s` of `IFS.IsGibbs`, so the
results of `Main.LocalDimension` apply to the natural measure `ν ∘ π⁻¹`.
-/

namespace IFS

/-! ### Cylinders -/

/-- The cylinder `[w]` is the set of sequences that agree with `w` in the first `|w|` places. -/
private theorem nm_wordCylinder_eq n (x : Address N) : wordCylinder prefix n x = {y | ∀ i < n, y i = x i} :=
  by
  rw [wordCylinder_ofFn]
  ext y
  simp [funext_iff, Fin.forall_iff]

/-! ### Distortion -/

/-! ### The natural projection and Birkhoff sums -/

/-- The Birkhoff sum of the potential: `∑_{k<m} φ_s(σ^k x) = s log |f_w'(π(σ^m x))|` with
`w = x₀ ⋯ x_{m-1}`. -/
private theorem nm_birkhoff s m (x : Address N) :
    ∑ k ∈ Finset.range m, Challenge.potential Φ.f s shift k x = s * Real.log ‖deriv (Φ.comp prefix m x) (Φ.natProj shift m x)‖ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have hπ : (Φ.natProj fun i => x (i + m + 1)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have hz := Φ.mem_closure hπ
    set v := List.ofFn fun j : Fin m => x (j + 1) with hv
    have hlist : prefix(m + 1)x = x 0 :: v := by simp [hv]
    have hc : Φ.comp v (Φ.natProj fun i => x (i + m + 1)) = Φ.natProj shift 1x := by
      rw [Φ.comp_ofReal _ hπ, ← Φ.natProj_eq_comp_prefix (shift 1x) m]
    rw [Finset.sum_range_succ']
    simp only [← Nat.add_assoc]
    rw [ih shift 1x, hlist, Φ.deriv_comp_cons _ _ hz, hc, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 ((Φ.inClass _).deriv_ne_zero _ (Φ.mem_closure (Φ.attractor_subset_I ⟨_, rfl⟩))))
        (norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero _ hz))]
    simp [Challenge.potential]
    ring

/-- Bowen's theorem gives a Gibbs measure for the potential `s log|f'_{ω₀}(π(σω))|`. -/
theorem exists_isGibbsMeasure (hB : BowenGibbsStatement) (hN : 0 < N) s :
    ∃ ν : Measure (Address N), IsProbabilityMeasure ν ∧ IsGibbsMeasure (Challenge.potential Φ.f s) ν :=
  by
  obtain ⟨L, hL0, hL⟩ := Φ.exists_nonlin_bound
  have hcmin := Φ.cmin_pos
  have hcmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  have hlog := sub_nonneg.2 (Real.log_le_log hcmin (Φ.cmin_le_cmax hN))
  set b := |s| * (L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin)) + 1
  refine hB hN (Challenge.potential Φ.f s) (b := b) (by positivity) hcmax Φ.cmax_lt_one fun k x y hxy => ?_
  simp [Challenge.potential]
  rw [← mul_sub, abs_mul]
  have hx := Φ.attractor_subset_I ⟨shift 1x, rfl⟩
  have hy := Φ.attractor_subset_I ⟨shift 1y, rfl⟩
  rcases k with _ | k
  · -- no common prefix: `log |f_i'|` takes values in `[log c_min, log c_max]`
    
    obtain ⟨h1, h2⟩ := Φ.log_norm_deriv_bounds (x 0) hx
    obtain ⟨⟩ := Φ.log_norm_deriv_bounds (y 0) hy
    have hd :
      |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj shift 1x)‖ - Real.log ‖deriv (Φ.f (y 0)) (Φ.natProj shift 1y)‖| ≤
        L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin) :=
      by
      have := div_nonneg hL0 hcmax.le
      rw [abs_le]
      constructor <;> linarith
    have := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
    linarith
  · -- a common prefix of length `k + 1`: the two points lie in `f_u(I)`, `|u| = k`
    
    have he : (List.ofFn fun j : Fin k => x (j + 1)) = List.ofFn fun j : Fin k => y (j + 1) := by grind
    have hdist : |Φ.natProj shift 1x - Φ.natProj shift 1y| ≤ Φ.cmax ^ k :=
      by
      rw [Φ.natProj_eq_comp_prefix (shift 1x) k, Φ.natProj_eq_comp_prefix (shift 1y) k, ← he]
      simpa using
        Φ.abs_re_comp_sub_le (List.ofFn fun j : Fin k => x (j + 1)) (Φ.attractor_subset_I ⟨fun j => x (j + k + 1), rfl⟩)
          (Φ.attractor_subset_I ⟨fun j => y (j + k + 1), rfl⟩)
    have hd :=
      (abs_log_norm_sub_le (fun t ht => (Φ.analyticAt_f (x 0) (Φ.mem_closure ht)).deriv.differentiableAt)
            (fun t ht => Φ.im_deriv_f_ofReal (x 0) (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) ht))
            (fun t ht => (Φ.inClass (x 0)).deriv_ne_zero t (Φ.mem_closure ht))
            (fun t ht => hL (x 0) t (Φ.mem_closure ht)) hx hy).trans
        (mul_le_mul_of_nonneg_left hdist hL0)
    rw [← hxy 0 (Nat.succ_pos k)]
    calc
      |s| * |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj shift 1x)‖ - Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj shift 1y)‖| ≤
          |s| * (L * Φ.cmax ^ k) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg s)
      _ = |s| * (L / Φ.cmax) * Φ.cmax ^ (k + 1) := by
        rw [pow_succ]
        field_simp
      _ ≤ b * Φ.cmax ^ (k + 1) := mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg s]) (pow_nonneg hcmax.le _)

/-- A Gibbs measure of the potential `s log|f'_{ω₀}(π(σω))|`, for the zero `s` of the pressure, has
the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s`. -/
theorem isGibbs_of_isGibbsMeasure (hN : 0 < N)
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0)) [IsProbabilityMeasure ν]
    (hν : IsGibbsMeasure (Challenge.potential Φ.f s) ν) : Φ.IsGibbs s ν :=
  by
  obtain ⟨c₁, hc₁, c₂, hc₂, P, hG⟩ := hν
  obtain ⟨Δ, hΔ0, hΔ⟩ := Φ.exists_log_distortion
  set A := |s| * Δ
  set K₁ := c₁ * Real.exp (-A)
  set K₂ := c₂ * Real.exp A
  have : 0 < K₁ := by positivity
  have key :
    ∀ w : FWord N,
      K₁ * Real.exp (-P * w.length) * Φ.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
        ν.real (wordCylinder w) ≤ K₂ * Real.exp (-P * w.length) * Φ.supDeriv w ^ s :=
    by
    intro w
    set x := fun i => w.getD i ⟨0, hN⟩
    obtain ⟨h1, h2⟩ := hG x w.length
    have hw : prefix w.length x = w := by simp [x]
    rw [← nm_wordCylinder_eq w.length x, Φ.nm_birkhoff, hw] at h1 h2
    have : Φ.natProj shift w.length x ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have hd : |s * Real.log (Φ.supDeriv w) - s * Real.log ‖deriv (Φ.comp w) (Φ.natProj shift w.length x)‖| ≤ A :=
      by
      rw [← mul_sub, abs_mul]
      bound
    rw [abs_le] at hd
    have hrpow : Φ.supDeriv w ^ s = Real.exp (s * Real.log (Φ.supDeriv w)) := by
      grind [Real.rpow_def_of_pos, @AnalyticESC.IFS.supDeriv_pos, mul_comm]
    constructor
    · refine le_trans ?_ h1
      simp only [K₁, hrpow, mul_assoc, ← Real.exp_add]
      gcongr 2
      linarith
    · refine h2.trans ?_
      simp only [K₂, hrpow, mul_assoc, ← Real.exp_add]
      gcongr 2
      linarith
        -- summing over the words of length `m`: `exp(-Pm) ∑_{|w| = m} ‖f_w'‖^s ≍ 1`
        
  have hsum :
    ∀ m : ℕ, K₁ * Real.exp (-P * m) * Φ.pressureSum s m ≤ 1 ∧ 1 ≤ K₂ * Real.exp (-P * m) * Φ.pressureSum s m :=
    by
    intro m
    have h1 := sum_measureReal_wordCylinder ν m Finset.univ
    simp only [Finset.coe_univ, preimage_univ, probReal_univ] at h1
    constructor <;> grind [AnalyticESC.IFS.pressureSum, Finset.mul_sum, Finset.sum_le_sum]
  have hlog :
    ∀ m : ℕ,
      -Real.log K₂ ≤ Real.log (Φ.pressureSum s m) - P * m ∧ Real.log (Φ.pressureSum s m) - P * m ≤ -Real.log K₁ :=
    by
    intro m
    obtain ⟨h1, h2⟩ := hsum m
    have := (Φ.pr_pressureSum_pos hN s) m
    have := Real.log_le_log (by positivity) h1
    have := Real.log_le_log one_pos h2
    grind [Real.log_mul, Real.log_exp, Real.log_one]
      -- hence `(1/m) log ∑_{|w| = m} ‖f_w'‖^s → P`, so `P = 0`
      
  have hlim : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 P) :=
    by
    have ht :=
      (tendsto_bdd_div_atTop_nhds_zero (Eventually.of_forall fun n => (hlog n).1)
            (Eventually.of_forall fun n => (hlog n).2) tendsto_natCast_atTop_atTop).add_const
        P
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : n ≠ 0 := by positivity
    field_simp
    ring
      -- the Gibbs property with `C = max(K₂, K₁⁻¹)`
      
  refine ⟨max K₂ K₁⁻¹, by positivity, fun w => ?_⟩
  obtain ⟨h1, h2⟩ := key w
  rw [tendsto_nhds_unique hlim hs, neg_zero, zero_mul, Real.exp_zero, mul_one] at h1 h2
  have hw := Real.rpow_nonneg (Φ.supDeriv_pos w).le s
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hw) h1
    grind [inv_le_of_inv_le₀, le_max_right]
  grind [LE.le.trans, mul_le_mul_of_nonneg_right, le_max_left]

end IFS

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem: the pressure of the example has
a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure, and for every
such Gibbs measure `ν` the natural measure `ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim_of_bowen (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (Challenge.pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (Challenge.potential exampleMaps s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (Challenge.potential exampleMaps s) ν →
        Tendsto (fun r : Challenge.Scale => Challenge.logRatio ((ν.map (Challenge.natProj exampleMaps)).real (closedBall 0 r)) r)
          Challenge.scaleZero (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, hs0, -, hs⟩ := exampleIFS.exists_pressure_zero (by norm_num)
  refine ⟨s, fun t => (tendsto_add_atTop_iff_nat 1).trans (hs t),
    exampleIFS.exists_isGibbsMeasure hB (by norm_num) s, fun ν hν hG => ?_⟩
  exact (scale_tendsto_iff _ _).mpr
    (example_localDim hs0 (exampleIFS.isGibbs_of_isGibbsMeasure (by norm_num) ((hs s).2 rfl) hG))

/-! ## AnalyticESC.Dimension.Lq -/

/-!
# The `L^q` dimension of the natural measure of the polynomial example

`L^q` dimensions of the polynomial example in Section 1.2.2: for `q > 1`, the `L^q` spectrum
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r` and the `L^q` dimension
`D_μ(q) = τ_μ(q)/(q - 1)` of the natural measure `μ` of the example satisfy
`D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. The sum
contains the term `μ([0,r))^q ≥ μ(B(0,r/2))^q`, and `μ(B(0,r))` has local dimension `s(Φ) - 1/3`
at `0` (`example_localDim`). The bound follows directly by comparing the limit inferior with the local-dimensional limit.
-/

theorem example_lq_of_bowen (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (Challenge.pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
        ∀ ν : Measure (ℕ → Fin 3),
          IsProbabilityMeasure ν →
            IsGibbsMeasure (Challenge.potential exampleMaps s) ν →
              ∀ q > 1,
                ∀ hq : q - 1 ≠ 0,
                  Challenge.lqDim (ν.map (Challenge.natProj exampleMaps)) q hq ≤
                      Challenge.divide q (q - 1) hq * (s - 1 / 3) ∧
                    (3 * s < q → Challenge.lqDim (ν.map (Challenge.natProj exampleMaps)) q hq < s) :=
  by
  obtain ⟨s, hs, -, hloc⟩ := example_localDim_of_bowen hB
  refine ⟨s, hs, fun ν hν hG q hq hq0 => ?_⟩
  let μ := ν.map exampleIFS.natProj
  let cell (r : ℝ) (k : ℤ) := Ico (k * r) ((k + 1) * r)
  let S r := ∑' k : ℤ, μ.real (cell r k) ^ q
  let R r := Real.log (S r) / Real.log r
  have hsum {r} (hr : 0 < r) : (Summable fun k : ℤ => μ.real (cell r k) ^ q) ∧ 0 ≤ S r ∧ S r ≤ 1 :=
    by
    have hS :=
      by
      have h :=
        VectorMeasure.hasSum_of_disjoint_iUnion (v := μ.toSignedMeasure) (f := cell r) (fun _ => measurableSet_Ico)
          (by simpa [cell] using pairwise_disjoint_Ico_zsmul r)
      simpa [Measure.toSignedMeasure_apply, by simpa [cell] using iUnion_Ico_zsmul hr, cell] using h
    have hle : ∀ k : ℤ, μ.real (cell r k) ^ q ≤ μ.real (cell r k) := fun _ =>
      Real.rpow_le_self_of_le_one measureReal_nonneg measureReal_le_one hq.le
    have hsum := Summable.of_nonneg_of_le (fun _ => by positivity) hle hS.summable
    refine ⟨hsum, by positivity, ?_⟩
    calc
      S r ≤ ∑' k : ℤ, μ.real (cell r k) := hsum.tsum_le_tsum hle hS.summable
      _ = 1 := hS.tsum_eq
  have hpos {r} (hr : 0 < r) : 0 < μ.real (closedBall 0 r) :=
    by
    obtain ⟨c₁, hc₁, c₂, -, P, hG⟩ := hG
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hr ldD_pos) (by norm_num : (1 / 8 : ℝ) < 1)
    rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
    refine (mul_pos hc₁ (Real.exp_pos _)).trans_le ((hG (fun _ => 0) m).1.trans (measureReal_mono fun y hy => ?_))
    have h0 := exampleIFS.attractor_subset_I ⟨y, rfl⟩
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0.1]
    exact (example_natProj_le fun k => by rw [hy k k.2]; decide).trans (by nlinarith [(lt_div_iff₀ ldD_pos).1 hm])
  have hloc := (scale_tendsto_iff (fun r => Real.log (μ.real (closedBall 0 r)) / Real.log r) _).mp (hloc ν hν hG)
  let d := s - 1 / 3
  have hlim : liminf R (𝓝[>] 0) ≤ q * d :=
    by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
    set g := fun r => q * Real.log (μ.real (closedBall 0 (r / 2))) / Real.log r
    have hg : Tendsto g (𝓝[>] 0) (𝓝 (q * d)) :=
      by
      have h2 : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) :=
        by
        simp_rw [tendsto_iff_comap, div_eq_inv_mul]
        rw [comap_mulLeft_nhdsGT_zero (by norm_num)]
      have hB : Tendsto (fun r => Real.log (r / 2) / Real.log r) (𝓝[>] 0) (𝓝 1) :=
        by
        have h :=
          tendsto_const_nhds (x := 1).sub (tendsto_const_nhds (x := Real.log 2).div_atBot Real.tendsto_log_nhdsGT_zero)
        rw [sub_zero] at h
        refine h.congr' (hev.mono fun r hr => ?_)
        grind [Real.log_neg, Real.log_div]
      have h := ((hloc.comp h2).mul hB).const_mul q
      rw [mul_one] at h
      refine h.congr' (hev.mono fun r hr => ?_)
      grind [Real.log_neg]
    have hle := by
      filter_upwards [hev] with r hr
      have hm := hpos (half_pos hr.1)
      obtain ⟨hsum, -, -⟩ := hsum hr.1
      set m := μ.real (closedBall 0 (r / 2))
      have hmI : m ≤ μ.real (Ico 0 r) := by
        dsimp only [m, μ]
        rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall,
          map_measureReal_apply exampleIFS.measurable_natProj measurableSet_Ico]
        refine measureReal_mono ?_
        intro ω hω
        have := (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1
        grind [Metric.mem_closedBall, Real.dist_eq]
      have hpos := Real.rpow_pos_of_pos hm q
      have hlog : q * Real.log m ≤ Real.log (S r) :=
        by
        rw [← Real.log_rpow hm]
        exact
          Real.log_le_log hpos
            ((Real.rpow_le_rpow hm.le hmI (by linarith)).trans
              (by
                have h := hsum.le_tsum 0 fun _ _ => by positivity
                simp only [cell, Int.cast_zero, zero_mul, zero_add, one_mul] at h
                exact h))
      exact div_le_div_of_nonpos_of_le (Real.log_neg hr.1 hr.2).le hlog
    rw [← hg.liminf_eq]
    exact
      Filter.liminf_le_liminf hle
        (isBoundedUnder_of_eventually_ge
          (hev.mono fun r hr => by
            obtain ⟨-, h0, h1⟩ := hsum hr.1
            exact div_nonneg_of_nonpos (Real.log_nonpos h0 h1) (Real.log_neg hr.1 hr.2).le))
        hg.isCoboundedUnder_ge
  have hq1 := sub_pos.2 hq
  rw [← scaleZero_map] at hlim
  unfold Challenge.lqDim Challenge.logRatio Challenge.divide
  have hdim := div_le_div_of_nonneg_right hlim hq1.le
  refine
    ⟨by
      convert! hdim using 1 <;> ring,
      fun h3 => ?_⟩
  apply hdim.trans_lt
  rw [div_lt_iff₀ hq1]
  dsimp [d]
  linarith

/-! ## AnalyticESC.Generic.Continuity -/

/-!
# Lemma 2.7

The dual natural projection depends Lipschitz-continuously on the system in the `𝒞²` metric,
uniformly in the word (2.6), so the strong separation of the dual is an open condition.

We write `f_i = Φ.f i`, `g_i = Ψ.f i` and `d = d₂(Φ, Ψ)`, with `Φ ∈ 𝔖_N(ε)` and `Ψ ∈ 𝔖_N(ε')`
for arbitrary `ε, ε' > 0`; all constants depend on `Φ` only. The estimates (2.3)–(2.5) are proved
at the real points of `I`, where all compositions take values in `I`. Since `d₂(Φ, Ψ)` small does
not give `|g_i'| ≤ c_max`, the contraction ratio of `Ψ` on `I` is bounded by `c' = c_max + δ₀ < 1`
and `|g_i'|` from below by `c_min / 2`. Auxiliary results are in the namespace `IFS.Continuity`.
-/

private theorem word_cases w : w = .fin [] ∨ ∃ (i : Fin N) (v : Word N), w = v.prepend [i] := by
  cases w with
  | fin w =>
    cases w with
    | nil => exact Or.inl rfl
    | cons i v => tauto
  | inf w =>
    right
    refine ⟨w 0, .inf shift 1w, ?_⟩
    simpa [] using Word.inf_eq_prepend_ofFn w 1

namespace IFS.Continuity


/-! ## Pointwise bounds from `d₂` -/

def d2Map_le_d2 (Φ : IFS N ε) (Ψ : IFS N ε') i :=
  le_ciSup (f := fun i => d2Map (Φ.f i) (Ψ.f i)) (by norm_num) i

theorem d2_nonneg (Φ : IFS N ε) (Ψ : IFS N ε') : 0 ≤ d2 Φ Ψ :=
  by grind [d2, d2Map, Real.iSup_nonneg]

/-- At a point of `I`, the maps, their derivatives and their second derivatives differ by at
most `d₂(Φ, Ψ)`. -/
theorem norm_sub_le_d2 (Φ : IFS N ε) (Ψ : IFS N ε') i (hx : x ∈ I) :
    ‖Φ.f i x - Ψ.f i x‖ ≤ d2 Φ Ψ ∧
      ‖deriv (Φ.f i) x - deriv (Ψ.f i) x‖ ≤ d2 Φ Ψ ∧ ‖D²(Φ.f i) x - D²(Ψ.f i) x‖ ≤ d2 Φ Ψ :=
  by
  have e k :=
    le_ciSup
      (isCompact_range ((Φ.continuous_iteratedDeriv_on_I i k).sub (Ψ.continuous_iteratedDeriv_on_I i k)).norm).bddAbove
      ⟨x, hx⟩
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp [iteratedDeriv_succ] at e0 e1 e2
  have := (norm_nonneg _).trans e0
  have := (norm_nonneg _).trans e1
  have := (norm_nonneg _).trans e2
  have := d2Map_le_d2 Φ Ψ i
  grind [d2, AnalyticESC.d2Map]

/-! ## The estimates (2.3)–(2.5) -/

end IFS.Continuity

namespace IFS

/-- (2.6): `|H_w(x) - Ĥ_w(x)| ≤ C' d₂(Φ, Ψ)` on `I`, for all words, when `Ψ` is close to `Φ`. -/
private theorem lipschitz_dualProj :
    ∃ L ≥ 0, ∀ w : Word N, ∀ x ∈ I, ∀ y ∈ I, ‖Φ.dualProj w x - Φ.dualProj w y‖ ≤ L * ‖(x : ℂ) - y‖ :=
  by
  obtain ⟨C, hC, hb, -⟩ := Φ.exists_iteratedDeriv_bounds
  refine ⟨C 1, (hC 1).le, fun w x hx y hy => ?_⟩
  simpa [← Complex.ofReal_sub] using
    (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht =>
        ((Φ.differentiableOn_dualProj w).differentiableAt
            ((isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd Φ.ε_pos ht))).hasDerivAt.comp_ofReal.hasDerivWithinAt)
      (fun t ht => by simpa using hb 1 t ht w) hy hx

theorem exists_dualProj_sub_le_d2 :
    ∃ C' δ₀ : ℝ,
      0 < δ₀ ∧ ∀ {ε'} (Ψ : IFS N ε'), d2 Φ Ψ < δ₀ → ∀ w, ∀ x ∈ I, ‖Φ.dualProj w x - Ψ.dualProj w x‖ ≤ C' * d2 Φ Ψ :=
  by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  obtain ⟨B, hB0, hB⟩ := Φ.exists_norm_dualProj_le
  obtain ⟨L, hL0, hL⟩ := Φ.lipschitz_dualProj
  let m := Φ.cmin / 2
  let δ₀ := min ((1 - Φ.cmax) / 2) m
  have hm := half_pos Φ.cmin_pos
  have hδ₀ := lt_min (half_pos (sub_pos.2 Φ.cmax_lt_one)) hm
  let c := Φ.cmax + δ₀
  have hc0 : 0 ≤ c := by linarith [Φ.cmax_nonneg]
  let E := (1 + M) / m + B + c * L
  refine ⟨E / (1 - c), δ₀, hδ₀, fun {ε'} Ψ hΨ => ?_⟩
  have := Continuity.d2_nonneg Φ Ψ
  have hP i x (hx : x ∈ I) : m ≤ ‖deriv (Ψ.f i) x‖ ∧ ‖deriv (Ψ.f i) x‖ ≤ c :=
    by
    have := (abs_norm_sub_norm_le (deriv (Φ.f i) x) (deriv (Ψ.f i) x)).trans (Continuity.norm_sub_le_d2 Φ Ψ i hx).2.1
    have := Φ.mem_closure hx
    dsimp [m, c, δ₀] at *
    grind [abs_le, IFS.norm_deriv_le_cmax, IFS.cmin_le_norm_deriv, min_le_right]
  have hn i x (hx : x ∈ I) : ‖Φ.nonlin i x - Ψ.nonlin i x‖ ≤ (1 + M) / m * d2 Φ Ψ :=
    by
    obtain ⟨-, h1, h2⟩ := Continuity.norm_sub_le_d2 Φ Ψ i hx
    calc
      ‖Φ.nonlin i x - Ψ.nonlin i x‖ ≤ (1 + M) * d2 Φ Ψ / ‖deriv (Ψ.f i) x‖ :=
        norm_div_sub_div_le ((Φ.inClass i).deriv_ne_zero _ (Φ.mem_closure hx))
          ((Ψ.inClass i).deriv_ne_zero _ (Ψ.mem_closure hx)) h2 h1 (hM i x (Φ.mem_closure hx))
      _ ≤ (1 + M) * d2 Φ Ψ / m := (div_le_div_of_nonneg_left (by positivity) hm (hP i x hx).1)
      _ = _ := by ring
  have hstep :
    ∀ i v x,
      x ∈ I →
        ‖Φ.dualProj (v.prepend [i]) x - Ψ.dualProj (v.prepend [i]) x‖ ≤
          E * d2 Φ Ψ + c * ‖Φ.dualProj v (Ψ.f i x).re - Ψ.dualProj v (Ψ.f i x).re‖ :=
    by
    intro i v x hx
    have := (hP i x hx).2
    have hxΦ := Φ.mem_closure hx
    have ha := by simpa using Φ.comp_ofReal [i] hx
    have hb := by simpa using Ψ.comp_ofReal [i] hx
    have hl := hL v _ ((Φ.inClass i).re_mem_I x hx) _ ((Ψ.inClass i).re_mem_I x hx)
    rw [← ha, ← hb] at hl
    have := hl.trans (mul_le_mul_of_nonneg_left (Continuity.norm_sub_le_d2 Φ Ψ i hx).1 hL0)
    have := hB v _ (subset_closure ((Φ.inClass i).mapsTo _ hxΦ))
    have := (Continuity.norm_sub_le_d2 Φ Ψ i hx).2.1
    rw [Φ.dualProj_prepend_singleton _ _ hxΦ, Ψ.dualProj_prepend_singleton _ _ (Ψ.mem_closure hx)]
    rw [show
        deriv (Φ.f i) x * Φ.dualProj v (Φ.f i x) + Φ.nonlin i x -
            (deriv (Ψ.f i) x * Ψ.dualProj v (Ψ.f i x) + Ψ.nonlin i x) =
          Φ.nonlin i x - Ψ.nonlin i x + (deriv (Φ.f i) x - deriv (Ψ.f i) x) * Φ.dualProj v (Φ.f i x) +
              deriv (Ψ.f i) x * (Φ.dualProj v (Φ.f i x) - Φ.dualProj v (Ψ.f i x)) +
            deriv (Ψ.f i) x * (Φ.dualProj v (Ψ.f i x) - Ψ.dualProj v (Ψ.f i x))
        by ring]
    calc
      _ ≤
          (1 + M) / m * d2 Φ Ψ + d2 Φ Ψ * B + c * (L * d2 Φ Ψ) +
            c * ‖Φ.dualProj v (Ψ.f i x) - Ψ.dualProj v (Ψ.f i x)‖ :=
        by bound
      _ = _ := by rw [hb]; dsimp; ring
  obtain ⟨B', hB'0, hB'⟩ := Ψ.exists_norm_dualProj_le
  let u (p : Word N × I) := ‖Φ.dualProj p.1 p.2 - Ψ.dualProj p.1 p.2‖
  have hb : BddAbove (range u) := by
    refine ⟨B + B', ?_⟩
    rintro _ ⟨⟨w, x⟩, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hB w _ (Φ.mem_closure x.2)) (hB' w _ (Ψ.mem_closure x.2)))
  intro w x hx
  simpa [div_mul_eq_mul_div] using
    bounded_le_of_le_add_mul hb hc0 (by linarith [min_le_left ((1 - Φ.cmax) / 2) m])
      (by
        rintro ⟨w, x⟩
        rcases word_cases w with rfl | ⟨i, v, rfl⟩
        · exact ⟨(.fin [], x), by dsimp [u]; simp [dualProj_nil, sub_self, norm_zero]; positivity⟩
        · exact ⟨(v, ⟨_, (Ψ.inClass i).re_mem_I x x.2⟩), hstep i v x x.2⟩)
      (w, ⟨x, hx⟩)

/-- Lemma 2.7 for `𝔖_N`: if the dual of `Φ` satisfies the SSC, so does the dual of every
`Ψ ∈ 𝔖_N` close to `Φ` in the `𝒞²` metric. The radius depends only on `Φ`, and `Ψ` may lie in
`𝔖_N(ε')` for any `ε'`. -/
theorem lemma_2_7_union (Φ : IFS N ε) (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ {ε' } (Ψ : IFS N ε'), d2 Φ Ψ < δ → Ψ.DualSSC := by
  have hN := h.1
  obtain ⟨δ, hδ, hsep⟩ := (Φ.dualSSC_iff_exists_delta hN).1 h
  obtain ⟨C', δ₀, hδ₀, hC'⟩ := Φ.exists_dualProj_sub_le_d2
  refine ⟨min δ₀ (δ / (3 * (|C'| + 1))), lt_min hδ₀ (by positivity), fun {ε'} Ψ hΨ => ?_⟩
  
  have hΨδ₀  := hΨ.trans_le (min_le_left _ _)
  have  : C' * d2 Φ Ψ < δ / 3 := by
    have h1  := hΨ.trans_le (min_le_right _ _)
    have  : C' * d2 Φ Ψ ≤ |C'| * d2 Φ Ψ := mul_le_mul_of_nonneg_right (le_abs_self _) (Continuity.d2_nonneg Φ Ψ
    )
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg C']
  refine (Ψ.dualSSC_iff_exists_delta hN).2 ⟨δ / 3, by positivity, fun i j hij => ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := exists_lt_of_lt_ciSup (hsep i j hij)
  
  refine lt_of_lt_of_le ?_ (le_ciSup (Ψ.bddAbove_dualProj_sub (.inf i) (.inf j)
  ) ⟨x, hx⟩)
  have  := hC' Ψ hΨδ₀ (.inf i) x hx
  have  := hC' Ψ hΨδ₀ (.inf j) x hx
  have  := dist_triangle4_right (Φ.dualProj (.inf i) x) (Φ.dualProj (.inf j) x)
    (Ψ.dualProj (.inf i) x) (Ψ.dualProj (.inf j) x)
  simp only [dist_eq_norm] at *
  linarith

end IFS

/-! ## AnalyticESC.Dual.Cylinders -/

/-!
# Lemma 2.6

The strong separation of the dual IFS in terms of cylinder sets, (a) ⇔ (b), and in terms of the
dual natural projection, (a) ⇔ (c).
-/

namespace IFS

/-! ## Words -/

/-! ## Iterates of the dual operators on `I` -/

/-- On `I`, `F_w` applied to a constant `c` is affine in `c`. -/
theorem re_dualComp_const w (c : ℝ)  (hx : x ∈ I) :
    (Φ.dualComp w (fun _ => c) x).re =
      (deriv (Φ.comp w.reverse) x).re * c + (Φ.dualProj (.fin w) x).re := by
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos hx)]
  simp

/-- Points of one cylinder interval of `Φ` at `x ∈ I` are `c_max^{|w|} (K - k)` close. -/
theorem abs_sub_le_cmax_pow_of_mem_dualCylAt  (hkK : k ≤ K) w
     (hx : x ∈ I)  (hp : p ∈ Φ.dualCylAt k K w x)
    (hq : q ∈ Φ.dualCylAt k K w x) : |p - q| ≤ Φ.cmax ^ w.length * (K - k) := by
  refine (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc hq hp)).trans ?_
  rw [Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx]
  calc _ = |(deriv (Φ.comp w.reverse) x).re| * (K - k) := by
        rw [← abs_of_nonneg (sub_nonneg.2 hkK), ← abs_mul]
        
        ring
    _ ≤ Φ.cmax ^ w.length * (K - k) :=
        mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans (by simpa using Φ.norm_deriv_comp_le w.reverse (Φ.mem_closure hx))) (sub_nonneg.2 hkK)

end IFS

/-! ## AnalyticESC.Generic.Agreement -/

/-!
# Dual compositions of two systems that agree along an orbit

Tools for the proof of Theorem 1.4 in Section 4.2. If the maps of `Ψ` agree with those of `Φ` to
second order along the orbit of a point `x`, then `G_w h = F_w h` at `x`. If they agree only to
first order at `x` itself, then `G_w h` at `x` is `F_w h` shifted by the change of `f''/f'` at
`x`. The section also bounds the width of the cylinder intervals and shows that the dual maps send
the closed cylinder into the open one under bounds on `[0,1]` alone.
-/

/-- `g` agrees with `f` to second order at `y`: equal values, first and second derivatives. -/
def AgreeAt (f g : CMap) y :=
  g y = f y ∧ deriv g y = deriv f y ∧ D²g y = D²f y

namespace IFS


/-! ## Dual compositions along an orbit -/

/-- One step of `F_{i w}`: `F_{i w} h = f_i' · (F_w h ∘ f_i) + f_i''/f_i'`. -/
theorem dualComp_cons_apply (Φ : IFS N ε) i w h
    z :
    Φ.dualComp (i :: w) h z = deriv (Φ.f i) z * Φ.dualComp w h (Φ.f i z) + Φ.nonlin i z :=
  rfl

/-- If `g_{w_m}` agrees with `f_{w_m}` to second order at `f_{w_{m-1}} ∘ ⋯ ∘ f_{w_0}(z)` for every
`m < |w|`, then `G_w h = F_w h` at `z`. -/
theorem dualComp_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε')
    (hag : ∀ m hm, AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse z)) h :
    Ψ.dualComp w h z = Φ.dualComp w h z := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih =>
    obtain ⟨h0, h1, h2⟩ := hag 0 (by simp)
    simp at h0 h1 h2
    have :=
      ih (z := Φ.f i z) fun m hm => by
        have := hag (m + 1) (by simp [hm])
        simpa [comp_append] using this
    simp_all [dualComp, dualOp, nonlin]

end IFS

/-! ## AnalyticESC.Generic.MultiplicativeBump -/

namespace RationalBump

def B (r : ℝ) z := (r : ℂ)^2*z^2/(r^2+z^2)
def B1 (r : ℝ) z := 2*(r : ℂ)^4*z/(r^2+z^2)^2
def B2 (r : ℝ) z := 2*(r : ℂ)^4*(r^2-3*z^2)/(r^2+z^2)^3
lemma hasDerivAt_B {r : ℝ}  (hz : (r : ℂ)^2+z^2 ≠ 0) :
    HasDerivAt (B r) (B1 r z) z := by
  convert (((hasDerivAt_id z).pow 2).const_mul ((r : ℂ)^2)).div
    (((hasDerivAt_id z).pow 2).const_add ((r : ℂ)^2)) hz using 1
  · rfl
  · dsimp [B1]; ring

lemma hasDerivAt_B1 {r : ℝ}  (hz : (r : ℂ)^2+z^2 ≠ 0) :
    HasDerivAt (B1 r) (B2 r z) z := by
  convert ((hasDerivAt_id z).const_mul (2*(r : ℂ)^4)).div
    ((((hasDerivAt_id z).pow 2).const_add ((r : ℂ)^2)).pow 2) (pow_ne_zero _ hz) using 1
  · rfl
  · dsimp [B2]; field_simp <;> ring
lemma real_nonzero {r t : ℝ} (hr : 0 < r) : (r : ℂ) ^ 2 + t ^ 2 ≠ 0 := by
  norm_cast; positivity
lemma B_ofReal (r t : ℝ) : B r t = (r ^ 2 * t ^ 2 / (r ^ 2 + t ^ 2) : ℝ) := by unfold B; push_cast; rfl
lemma B_bounds  (hr : 0 < r) (t : ℝ) :
    ‖B r t‖ ≤ r^2 ∧ ‖B1 r t‖ ≤ 2*r ∧ ‖B2 r t‖ ≤ 6 ∧
      ∀ {ρ }, 0 < ρ → ρ ≤ |t| → ‖B2 r t‖ ≤ 6*r^4/ρ^4 := by
  simp only [B, B1, B2]
  norm_cast
  simp only [Real.norm_eq_abs]
  have hd : 0 < r^2+t^2 := by positivity
  have h2 : |2*r^4*(r^2-3*t^2)/(r^2+t^2)^3| ≤ 6*r^4/(r^2+t^2)^2 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity ),
      abs_of_pos (pow_pos hd 3)]
    have  : |r^2-3*t^2| ≤ 3*(r^2+t^2) := by
      rw [abs_le]; constructor <;> nlinarith
    calc 2*r^4*|r^2-3*t^2|/(r^2+t^2)^3 ≤ 2*r^4*(3*(r^2+t^2))/(r^2+t^2)^3 := by gcongr
      _ = _ := by field_simp <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (by positivity), div_le_iff₀ hd]
    nlinarith
  · rw [abs_div, abs_mul, abs_of_pos (by positivity ),
      abs_of_pos (pow_pos hd 2), div_le_iff₀ (pow_pos hd 2)]
    nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg (r-|t|)), sq_abs t,
      mul_nonneg (sq_nonneg r) (sq_nonneg t), sq_nonneg (t^2)]
  · refine h2.trans ?_
    rw [div_le_iff₀ (pow_pos hd 2)]
    apply le_of_sub_nonneg
    ring_nf
    positivity
  · intro ρ hρ hρt
    refine h2.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hρ 4) ?_)
    have  : ρ^2 ≤ t^2 := by nlinarith [sq_abs t]
    nlinarith

theorem eventually_sep (Y : Finset ℝ) :
    ∀ᶠ ρ in 𝓝[>] 0, ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'| := by
  refine (eventually_all_finset Y).2 fun k _ => (eventually_all_finset Y).2 fun k' _ => ?_
  by_cases hkk : k = k'
  · exact Eventually.of_forall fun _ => absurd hkk
  · have h : 0 < |k - k'| / 2 := by
      positivity
    filter_upwards [Ioo_mem_nhdsGT h] with ρ hρ _
    linarith [hρ.2]

def H Y (q : ℝ → CMap) r z :=
  ∑ y ∈ Y, q y z * B r (z-y)
def H1 Y (q : ℝ → CMap) r z :=
  ∑ y ∈ Y, (deriv (q y) z * B r (z-y) + q y z * B1 r (z-y))
def H2 Y (q : ℝ → CMap) r z :=
  ∑ y ∈ Y, (D² (q y) z * B r (z-y) + 2 * deriv (q y) z * B1 r (z-y) + q y z * B2 r (z-y))
lemma hasDerivAt_H {Y : Finset ℝ} {r : ℝ} (hq : ∀ y ∈ Y, Differentiable ℂ (q y))
    (hz : ∀ y ∈ Y, (r : ℂ) ^ 2 + (z - y) ^ 2 ≠ 0) : HasDerivAt (H Y q r) (H1 Y q r z) z :=
  HasDerivAt.fun_sum fun y hy => by
    convert! (hq y hy z).hasDerivAt.mul ((hasDerivAt_B (hz y hy)).comp z ((hasDerivAt_id z).sub_const (y : ℂ))) using
        1 <;>
      simp
lemma hasDerivAt_H1 {Y : Finset ℝ}  {r : ℝ} 
    (hq : ∀ y ∈ Y, Differentiable ℂ (q y))
    (hz : ∀ y ∈ Y, (r : ℂ)^2+(z-y)^2 ≠ 0) : HasDerivAt (H1 Y q r) (H2 Y q r z) z := by
  refine HasDerivAt.fun_sum fun y hy => ?_
  
  
  convert! (((hq y hy).deriv z).hasDerivAt.mul ((hasDerivAt_B (hz y hy)).comp z ((hasDerivAt_id z).sub_const (y : ℂ))
  )).add
    ((hq y hy z).hasDerivAt.mul ((hasDerivAt_B1 (hz y hy)).comp z ((hasDerivAt_id z).sub_const (y : ℂ))
    )) using 1 <;> first
  | (funext w)
  | (dsimp; ring)

lemma exists_width (hδ : 0 < δ) (hq : ∀ y ∈ Y, Differentiable ℂ (q y)) (hval : ∀ y ∈ Y, ‖q y y‖ ≤ δ / 2) (he : 0 < e) :
    ∃ r > 0, ∀ x ∈ I, ‖H Y q r x‖ < e ∧ ‖H1 Y q r x‖ < e ∧ ‖H2 Y q r x‖ < 6 * δ + e :=
  by
  obtain ⟨M, hM0, hB⟩ :=
    uniform_norm_bound isCompact_Icc (F := fun y : Y => fun x : ℝ => (q y x, deriv (q y) x, D²(q y) x)) fun y =>
      by
      have h0 := (hq y y.2).continuous
      have h1 := (hq y y.2).deriv.continuous
      have h2 := (hq y y.2).deriv.deriv.continuous
      exact ((h0.prodMk (h1.prodMk h2)).comp Complex.continuous_ofReal).continuousOn
  have hM := fun y hy x hx => by simpa [Prod.norm_def, max_le_iff] using hB ⟨y, hy⟩ x hx
  have hnear : ∀ y ∈ Y, ∀ᶠ ρ in 𝓝[>] 0, ∀ x : ℝ, |x - y| < ρ → ‖q y x‖ ≤ δ :=
    by
    intro y hy
    obtain ⟨s, hs, h⟩ := Metric.continuousAt_iff.1 (hq y hy).continuous.continuousAt (δ / 2) (half_pos hδ)
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ x hh
    have h1 := h (by rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hh.trans hρ.2)
    rw [dist_eq_norm] at h1
    linarith [hval y hy, norm_le_insert' (q y x) (q y y)]
  obtain ⟨ρ, ⟨hsep, hnear⟩, hρ⟩ :=
    (((eventually_sep Y).and ((eventually_all_finset Y).2 hnear)).and self_mem_nhdsWithin).exists
  let F (r : ℝ) := Y.card * M * (r ^ 2 + 4 * r + 6 * r ^ 4 / ρ ^ 4)
  have hF : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    simpa [F] using ((show Continuous F by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨r, hs, hr⟩ := ((hF.eventually (gt_mem_nhds he)).and self_mem_nhdsWithin).exists
  refine ⟨r, hr, fun x hx => ?_⟩
  obtain ⟨h0, h1, h2⟩ :
    ‖H Y q r x‖ ≤ Y.card * M * r ^ 2 ∧
      ‖H1 Y q r x‖ ≤ Y.card * M * (r ^ 2 + 2 * r) ∧
        ‖H2 Y q r x‖ ≤ 6 * δ + Y.card * M * (r ^ 2 + 4 * r + 6 * r ^ 4 / ρ ^ 4) :=
    by
    have hb (y : ℝ) := B_bounds hr (x - y)
    simp [Complex.ofReal_sub] at hb
    let w y := ‖q y x‖
    let f (y : ℝ) := ‖B2 r (x - y)‖
    let b := 6 * r ^ 4 / ρ ^ 4
    have hb0 : 0 ≤ b := by positivity
    have hs : ∑ y ∈ Y, w y * f y ≤ 6 * δ + Y.card * M * b := by
      calc
        _ ≤ ∑ y ∈ Y, (M * b + if |x - y| < ρ then 6 * δ else 0) :=
          Finset.sum_le_sum fun y hy => by
            dsimp [w, f]
            split_ifs with hxy
            · have h := mul_le_mul (hnear y hy x hxy) (hb y).2.2.1 (norm_nonneg _) hδ.le
              linarith [mul_nonneg hM0 hb0]
            · simpa [b] using mul_le_mul (hM y hy x hx).1 ((hb y).2.2.2 hρ (le_of_not_gt hxy)) (norm_nonneg _) hM0
        _ = Y.card * (M * b) + (Y.filter fun y => |x - y| < ρ).card * (6 * δ) :=
          by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter]
          simp
        _ ≤ _ :=
          by
          have : ((Y.filter fun y => |x - y| < ρ).card : ℝ) ≤ 1 := by
            exact_mod_cast by
              refine Finset.card_le_one.2 fun y hy y' hy' => ?_
              have := abs_sub_le y x y'
              grind only [Finset.mem_filter, abs_sub_comm]
          nlinarith
    refine ⟨?_, ?_, ?_⟩
    · have h := norm_sum_le_of_le Y fun y hy => norm_mul_le_of_le (hM y hy x hx).1 (hb y).1
      simpa [H, mul_assoc] using h
    ·
      calc
        _ ≤ ∑ y ∈ Y, (M * r ^ 2 + M * (2 * r)) := by
          apply norm_sum_le_of_le
          intro y hy
          bound [hM y hy x hx, hb y]
        _ = _ := by simp [mul_add]; ring
    ·
      calc
        _ ≤ ∑ y ∈ Y, (M * r ^ 2 + 2 * M * (2 * r) + ‖q y x‖ * ‖B2 r (x - y)‖) :=
          by
          apply norm_sum_le_of_le
          intro y hy
          bound [hM y hy x hx, hb y]
        _ = Y.card * (M * r ^ 2 + 2 * M * (2 * r)) + ∑ y ∈ Y, ‖q y x‖ * ‖B2 r (x - y)‖ := by
          simp [Finset.sum_add_distrib, mul_add]
        _ ≤ Y.card * (M * r ^ 2 + 2 * M * (2 * r)) + (6 * δ + Y.card * M * (6 * r ^ 4 / ρ ^ 4)) :=
          (add_le_add le_rfl hs)
        _ = _ := by ring
  have hn : 0 ≤ Y.card * M := mul_nonneg (Nat.cast_nonneg _) hM0
  have hR : 0 ≤ 6 * r ^ 4 / ρ ^ 4 := by positivity
  dsimp [F] at hs
  exact
    ⟨by nlinarith [mul_nonneg hn hR, mul_nonneg hn hr.le], by nlinarith [mul_nonneg hn hR, mul_nonneg hn hr.le], by
      linarith⟩

def R (W : Finset ℝ) (y : ℝ) z := ∏ w ∈ W, (z-w)/((y : ℂ)-w)
def Q (Y Z : Finset ℝ) (a : ℝ → ℂ) y z :=
  a y * R (Y.erase y ∪ Z) y z ^ 4
lemma differentiable_R W y : Differentiable ℂ (R W y) := by unfold R; fun_prop
lemma R_ofReal W (x y : ℝ) : R W y x = (∏ w ∈ W, (x - w) / (y - w) : ℝ) := by unfold R; push_cast; rfl
lemma R_self (hy : y ∉ W) : R W y y = 1 := by
  apply Finset.prod_eq_one
  intro w hw
  apply div_self
  exact sub_ne_zero.2 (by exact_mod_cast show y ≠ w by rintro rfl; exact hy hw)
lemma R_zero {W : Finset ℝ}  (hw : w ∈ W) y : R W y w = 0 :=
  Finset.prod_eq_zero hw (by simp)
lemma Q_self    (hYZ : Disjoint Y Z) (hy : y ∈ Y) : Q Y Z a y y = a y := by
  have hn : y ∉ Y.erase y ∪ Z := by simp [Finset.disjoint_left.1 hYZ hy]
  simp [Q, R_self hn]
lemma B_zero  (hr : 0 < r) : B r 0 = 0 ∧ B1 r 0 = 0 ∧ B2 r 0 = 2 := by
  have  : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [B, B1, B2]
  field_simp
lemma H_Q_im (Y Z ) a (r x : ℝ)
    (ha : ∀ y ∈ Y, (a y).im = 0) : (H Y (Q Y Z a) r x).im = 0 := by
  rw [H, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro y hy
  rw [Q, R_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_sub, B_ofReal]
  simp only [Complex.mul_im,  Complex.ofReal_im, ha y hy,
    mul_zero, zero_mul, add_zero]
lemma H_Q_jets {Y Z : Finset ℝ} (hr : 0 < r) (hYZ : Disjoint Y Z) :
    (∀ w ∈ Y ∪ Z, H Y (Q Y Z a) r w = 0 ∧ H1 Y (Q Y Z a) r w = 0) ∧
      (∀ w ∈ Z, H2 Y (Q Y Z a) r w = 0) ∧ ∀ y ∈ Y, H2 Y (Q Y Z a) r y = 2 * a y :=
  by
  have hz j w (hw : w ∈ Y ∪ Z) (hne : w ≠ j) : Q Y Z a j w = 0 ∧ deriv (Q Y Z a j) w = 0 ∧ D²(Q Y Z a j) w = 0 :=
    by
    have hw' : w ∈ Y.erase j ∪ Z := by simp_all
    have := differentiable_R (Y.erase j ∪ Z) j
    unfold Q
    simp (disch := fun_prop) [R_zero hw' j]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    constructor <;> apply Finset.sum_eq_zero <;> intro j hj
    all_goals
      by_cases h : w = j
      · subst j; simp [B, B1]
      · obtain ⟨h0, h1, -⟩ := hz j w hw h
        simp [h0, h1]
  · intro w hw
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨h0, h1, h2⟩ := hz j w (Finset.mem_union_right _ hw) (by rintro rfl; exact Finset.disjoint_left.1 hYZ hj hw)
    simp [h0, h1, h2]
  · intro y hy
    rw [H2, Finset.sum_eq_single y]
    · obtain ⟨hb, hb1, hb2⟩ := B_zero hr
      simp [hb, hb1, hb2, Q_self hYZ hy]
      ring
    · intro j hj hne
      obtain ⟨h0, h1, h2⟩ := hz j y (Finset.mem_union_left _ hy) hne.symm
      simp [h0, h1, h2]
    · exact absurd hy

end RationalBump

open RationalBump

/-- A rational peak gives the same perturbation, without Gaussian asymptotics. -/
theorem proposition_4_2 (hε : 0 < ε) (hf : InClass ε f) (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∀ Y Z : Finset ℝ,
      (∀ y ∈ Y, y ∈ I) →
        (∀ z ∈ Z, z ∈ I) →
          Disjoint Y Z →
            ∀ δ > 0,
              ∃ g : CMap,
                (∃ ε' > 0, InClass ε' g) ∧
                  (∀ y ∈ Y, g y = f y ∧ deriv g y = deriv f y ∧ δ ≤ ‖D² g y / deriv g y - D² f y / deriv f y‖) ∧
                    (∀ z ∈ Z, AgreeAt f g z) ∧ d2Map f g ≤ 9 * δ :=
  by
  obtain ⟨m, hm, hmar⟩ : ∃ m > 0, ∀ x ∈ I, m ≤ (f x).re ∧ (f x).re ≤ 1 - m ∧ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 - m :=
    by
    have hmem : MapsTo (↑) I (nbhd (2 * ε)) := fun x hx => ofReal_mem_nbhd (by positivity) hx
    have hf0 := (hf.analytic_real hε).continuousOn
    have hf1 :=
      ((hf.differentiableOn.deriv (isOpen_nbhd _)).continuousOn.comp Complex.continuous_ofReal.continuousOn hmem).norm
    set h : RMap := fun x => min (min (f x).re (1 - (f x).re)) (min ‖deriv f x‖ (1 - ‖deriv f x‖))
    have hcont : ContinuousOn h I := (hf0.inf (continuousOn_const.sub hf0)).inf (hf1.inf (continuousOn_const.sub hf1))
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩ hcont
    have : ∀ x ∈ I, 0 < h x := fun x hx => by
      grind [subset_closure, AnalyticESC.ofReal_mem_nbhd, norm_pos_iff, Challenge.InClass.deriv_ne_zero,
        Challenge.InClass.norm_deriv_lt_one, lt_min_iff]
    grind [isMinOn_iff, le_min_iff]
  intro Y Z hY hZ hYZ δ hδ
  let a (y : ℝ) := δ / 2 * deriv f y
  let q := Q Y Z a
  have hq : ∀ y ∈ Y, Differentiable ℂ (q y) := fun y _ => by unfold q Q R; fun_prop
  have ha : ∀ y ∈ Y, (a y).im = 0 := by
    intro y hy
    have h :=
      im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero (ofReal_mem_nbhd (by linarith) (hY y hy))
    simp [a, Complex.mul_im, h]
  let e := min δ (m / 2)
  have he : 0 < e := by positivity
  have : e ≤ m / 2 := min_le_right _ _
  have heδ : e ≤ δ := min_le_left _ _
  obtain ⟨r, hr, hs⟩ :=
    exists_width hδ hq
      (by
        intro y hy
        change ‖Q Y Z a y y‖ ≤ δ / 2
        rw [Q_self hYZ hy]
        have h := (hf.norm_deriv_lt_one _ (ofReal_mem_closure hε (hY y hy))).le
        simp [a, Complex.norm_real, abs_of_pos hδ]
        nlinarith)
      he
  let U := nbhd (2 * ε) ∩ {z : ℂ | ∀ y ∈ Y, r ^ 2 + (z - y) ^ 2 ≠ 0}
  have hU : IsOpen U := by
    refine (isOpen_nbhd _).inter ?_
    simp only [ofPred_forall]
    exact isOpen_biInter_finset fun y _ => isOpen_ne.preimage (by fun_prop)
  have hmem : ∀ x ∈ I, (x : ℂ) ∈ U := fun x hx =>
    ⟨ofReal_mem_nbhd (by linarith) hx, fun y _ => by simpa [← Complex.ofReal_sub] using real_nonzero hr⟩
  let g z := f z + H Y q r z
  have hd : ∀ z ∈ U, HasDerivAt g (deriv f z + H1 Y q r z) z := fun z hz =>
    (hf.differentiableOn.differentiableAt ((isOpen_nbhd _).mem_nhds hz.1)).hasDerivAt.add (hasDerivAt_H hq hz.2)
  have hd1 := fun z hz => (hd z hz).deriv
  have hd2 : ∀ z ∈ U, D² g z = D² f z + H2 Y q r z := by
    intro z hz
    have h := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hd1
    rw [h.deriv_eq]
    exact
      ((hf.differentiableOn.deriv (isOpen_nbhd _)).differentiableAt ((isOpen_nbhd _).mem_nhds hz.1)).hasDerivAt.add
          (hasDerivAt_H1 hq hz.2) |>.deriv
  have hest : ∀ x ∈ I, ‖g x - f x‖ < e ∧ ‖deriv g x - deriv f x‖ < e ∧ ‖D² g x - D² f x‖ < 6 * δ + e :=
    by
    intro x hx
    rw [hd1 _ (hmem x hx), hd2 _ (hmem x hx)]
    simpa [g] using hs x hx
  obtain ⟨h0, hz, hy⟩ := H_Q_jets hr hYZ
  have h01 : ∀ w ∈ Y ∪ Z, g w = f w ∧ deriv g w = deriv f w :=
    by
    intro w hw
    constructor
    · change f w + H Y (Q Y Z a) r w = f w
      rw [(h0 w hw).1, add_zero]
    · rw [hd1 _ (hmem w ((Finset.mem_union.1 hw).elim (hY w) (hZ w))), (h0 w hw).2, add_zero]
  refine
    ⟨g, by
      have hgd : DifferentiableOn ℂ g U := fun z hz => (hd z hz).differentiableAt.differentiableWithinAt
      let V := U ∩ deriv g ⁻¹' ({0}ᶜ ∩ ball 0 1)
      have hV : IsOpen V :=
        (hgd.deriv hU).continuousOn.isOpen_inter_preimage hU (isOpen_compl_singleton.inter isOpen_ball)
      obtain ⟨d, hd0, hdV⟩ :=
        isCompact_image_I.exists_cthickening_subset_open hV
          (by
            rintro _ ⟨x, hx, rfl⟩
            refine ⟨hmem x hx, ?_, mem_ball_zero_iff.2 ?_⟩
            · intro hzero
              have h := (hest x hx).2.1
              rw [hzero, zero_sub, norm_neg] at h
              linarith [(hmar x hx).2.2.1]
            · have h := norm_sub_norm_le (deriv g x) (deriv f x)
              linarith [(hest x hx).2.1, (hmar x hx).2.2.2])
      have h2 : nbhd (2 * (d / 2)) ⊆ U := by
        rw [nbhd_eq_thickening]
        exact fun z hz => (hdV (thickening_subset_cthickening_of_le (by linarith) _ hz)).1
      have hcl : closedNbhd(d / 2) ⊆ V := by
        rw [nbhd_eq_thickening]
        exact fun z hz => hdV (cthickening_mono (by linarith) _ (closure_thickening_subset_cthickening _ _ hz))
      refine
        ⟨d / 2, half_pos hd0,
          Challenge.InClass.of_deriv (half_pos hd0) (hgd.mono h2) ?_ ?_ (fun z hz => (hcl hz).2.1) fun z hz =>
            mem_ball_zero_iff.1 (hcl hz).2.2⟩
      · intro x hx
        simp [g, q, Complex.add_im, H_Q_im Y Z a r x ha]
        exact hf.im_eq_zero x (h2 hx).1
      · intro x hx
        obtain ⟨⟩ := hmar x hx
        have h := (Complex.abs_re_le_norm (g x - f x)).trans_lt (hest x hx).1
        rw [Complex.sub_re, abs_lt] at h
        exact ⟨by linarith, by linarith⟩, ?_, ?_, ?_⟩
  · intro y hyy
    refine ⟨(h01 y (Finset.mem_union_left _ hyy)).1, (h01 y (Finset.mem_union_left _ hyy)).2, ?_⟩
    have hyI := hY y hyy
    rw [hd1 _ (hmem y hyI), (h0 y (Finset.mem_union_left _ hyy)).2, add_zero, hd2 _ (hmem y hyI), hy y hyy]
    have ha : 2 * a y = δ * deriv f y := by dsimp [a]; ring
    rw [ha]
    have := hf.deriv_ne_zero _ (ofReal_mem_closure hε hyI)
    have h : (D² f y + δ * deriv f y) / deriv f y - D² f y / deriv f y = δ := by field_simp; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  · intro w hw
    refine ⟨(h01 w (Finset.mem_union_right _ hw)).1, (h01 w (Finset.mem_union_right _ hw)).2, ?_⟩
    rw [hd2 _ (hmem w (hZ w hw)), hz w hw, add_zero]
  · have : d2Map f g ≤ δ + δ + (6 * δ + δ) :=
      by
      refine add_le_add (add_le_add (ciSup_le fun x : I => ?_) (ciSup_le fun x : I => ?_)) (ciSup_le fun x : I => ?_)
      · simpa only [norm_sub_rev] using (hest x x.2).1.le.trans heδ
      · simpa only [norm_sub_rev] using (hest x x.2).2.1.le.trans heδ
      · simpa only [norm_sub_rev] using (hest x x.2).2.2.le.trans (add_le_add le_rfl heδ)
    linarith

/-! ## AnalyticESC.Generic.Points -/

/-!
# Lemma 4.1

For a system whose compositions along distinct finite words differ on `[0,1]`, a choice of
points `x_{i,j}`, `(i, j) ∈ ℬ_n`, at which the cylinders of pairs that are not bad are disjoint,
with orbits that are injective, meet only at the base point, and are disjoint for different
pairs. Systems without exact overlaps satisfy the hypothesis.

The points are chosen one pair at a time, by induction over finite sets of pairs. At each step
the admissible points form an infinite subset of `I` (all of `I` for a bad pair, a relative
neighbourhood of a point of disjointness otherwise), and the excluded points are finite: by the
identity theorem two distinct compositions agree at finitely many points of `I`, and each
composition is injective on `I`.
-/

namespace IFS

/-! ## Compositions on `I` -/

/-- Two compositions along distinct words agree at finitely many points of `I`. -/
private theorem finite_eq_comp (h : Φ.NoCoincidence)  (hvw : v ≠ w) :
    {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = (Φ.comp w t).re}.Finite := by
  obtain ⟨x, hx, hne⟩ := h v w hvw
  refine (finite_zeros Φ.ε_pos ((Φ.differentiableOn_comp v).sub (Φ.differentiableOn_comp w))
    ⟨x, hx, sub_ne_zero.2 hne⟩).subset ?_
  rintro t ⟨ht, heq⟩
  refine ⟨ht, ?_⟩
  show Φ.comp v t - Φ.comp w t = 0
  rw [Φ.comp_ofReal v ht, Φ.comp_ofReal w ht, heq, sub_self]

/-! ## Disjointness of the cylinders near a point -/

private theorem disjoint_uIcc_iff {a b c d : ℝ} :
    Disjoint (uIcc a b) (uIcc c d) ↔ max a b < min c d ∨ max c d < min a b := by
  simp only [uIcc, Set.disjoint_iff_inter_eq_empty, Icc_inter_Icc, Icc_eq_empty_iff]
  grind

/-- The endpoints `(F_w c)(t)` of the cylinders depend continuously on `t ∈ I`. -/
private theorem continuousOn_dualComp_const w (c : ℝ) : ContinuousOn (realRestrict(Φ.dualComp w fun _ => c)) I :=
  by
  refine
    (Complex.continuous_re.comp_continuousOn
          (((((Φ.differentiableOn_comp w.reverse).deriv (isOpen_nbhd ε)).continuousOn.mul_const c).add
                (Φ.differentiableOn_dualProj (.fin w)).continuousOn).comp
            Complex.continuous_ofReal.continuousOn fun t => ofReal_mem_nbhd Φ.ε_pos)).congr
      fun t ht => ?_
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos ht)]
  rfl

/-- The points of `I` at which the cylinders are disjoint, if they are disjoint at some point,
form an infinite set. -/
private theorem infinite_good (k K) (a b) :
    {t : ℝ | t ∈ I ∧ (Φ.DualCylDisjoint k K a b → Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t))}.Infinite :=
  by
  by_cases hd : Φ.DualCylDisjoint k K a b
  · obtain ⟨x, hx, hdx⟩ := hd
    have hc := fun w c => Φ.continuousOn_dualComp_const w c x hx
    have hev : ∀ᶠ t in 𝓝[I] x, Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t) :=
      by
      unfold dualCylAt at hdx ⊢
      simp_rw [disjoint_uIcc_iff] at hdx ⊢
      rcases hdx with h1 | h1
      · exact (((hc a k).max (hc a K)).eventually_lt ((hc b k).min (hc b K)) h1).mono fun t => Or.inl
      · exact (((hc b k).max (hc b K)).eventually_lt ((hc a k).min (hc a K)) h1).mono fun t => Or.inr
    obtain ⟨U, hU, hxU, hUS⟩ := mem_nhdsWithin.1 hev
    exact
      (Set.Infinite.of_accPt ((uniqueDiffOn_Icc zero_lt_one x hx).accPt.nhds_inter (hU.mem_nhds hxU))).mono fun t ht =>
        ⟨ht.2, fun _ => hUS ht⟩
  · exact (Set.Icc_infinite zero_lt_one).mono fun t ht => ⟨ht, fun h' => absurd h' hd⟩

/-! ## Orbits -/

private theorem mem_orbit   :
    y ∈ Φ.orbit w t ↔ ∃ l ≤ w.length, (Φ.comp (w.take l).reverse t).re = y := by
  simp [orbit, List.mem_map, List.mem_range]

/-- The properties of Lemma 4.1 (a) and (b) for one pair `p` and the point `t`. -/
abbrev Good (k K) (p : WordPair N n) t :=
  t ∈ I ∧
    (Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
        Disjoint (Φ.dualCylAt k K (List.ofFn p.1) t) (Φ.dualCylAt k K (List.ofFn p.2) t)) ∧
      (Φ.orbit (List.ofFn p.1) t).Nodup ∧ (Φ.orbit (List.ofFn p.2) t).Nodup

/-- Good points with mutually disjoint orbits. -/
structure IsPointChoice (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : WordPair N (n + 1) → ℝ) : Prop where
  good : ∀ p, Φ.Good k K p (x p)
  sep : ∀ p q, p ≠ q →
    ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
      y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)

/-- Lemma 4.1. A pair `(i, j)` is not bad when `F_i(k, K) ∩ F_j(k, K) = ∅` in the sense of (2.2). -/
theorem lemma_4_1 n (k K) (h : Φ.NoCoincidence) : ∃ x, IsPointChoice Φ k K n x := by
  let P := WordPair N (n + 1)
  have hpoint {p : P} {F : Set ℝ} (hF : F.Finite) :
    ∃ t, Φ.Good k K p t ∧ ∀ y ∈ Φ.orbit (List.ofFn p.1) t ++ Φ.orbit (List.ofFn p.2) t, y ∉ F :=
    by
    have hW := List.finite_length_le (Fin N) (n + 1)
    obtain ⟨t, ⟨ht, hdisj⟩, hex⟩ :=
      ((Φ.infinite_good k K (List.ofFn p.1) (List.ofFn p.2)).sdiff
          ((hW.biUnion fun v _ =>
                hW.biUnion fun w _ => Set.finite_iUnion fun hvw : v ≠ w => Φ.finite_eq_comp h hvw).union
            (hW.biUnion fun v _ =>
              hF.of_injOn (hi := (Φ.injOn_re_comp v).mono inter_subset_left) fun _ ht => ht.2))).nonempty
    simp only [mem_union, mem_iUnion, mem_ofPred_eq] at hex
    have hnodup : ∀ i : Block N (n + 1), (Φ.orbit (List.ofFn i) t).Nodup :=
      by
      intro i
      refine List.Nodup.map_on ?_ List.nodup_range
      grind
    refine ⟨t, ⟨ht, hdisj, hnodup p.1, hnodup p.2⟩, ?_⟩
    intro y hy hyF
    rcases List.mem_append.1 hy with hy | hy
    all_goals
      obtain ⟨l, hl, rfl⟩ := (mem_orbit Φ).1 hy
      exact hex (.inr ⟨_, by simp, ht, hyF⟩)
  have hchoice (S : Finset P) :
    ∃ x : P → ℝ,
      (∀ p ∈ S, Φ.Good k K p (x p)) ∧
        ∀ p ∈ S,
          ∀ q ∈ S,
            p ≠ q →
              ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
                y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q) :=
    by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | insert a S ha ih =>
      obtain ⟨x, hgood, hsep⟩ := ih
      let F := ⋃ q ∈ S, {y | y ∈ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)}
      have hF : F.Finite := S.finite_toSet.biUnion fun q _ => List.finite_toSet _
      obtain ⟨t, hgt, havoid⟩ := hpoint (p := a) hF
      have hxS : ∀ q ∈ S, Function.update x a t q = x q := fun q hq =>
        Function.update_of_ne (ne_of_mem_of_not_mem hq ha) _ _
      refine ⟨Function.update x a t, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · simpa only [Function.update_self] using hgt
        · rw [hxS p hp]; exact hgood p hp
      · intro p hp q hq hpq y hy hyq
        simp only [F, mem_iUnion, mem_ofPred_eq, not_exists] at havoid
        rcases Finset.mem_insert.1 hp with rfl | hpS <;> rcases Finset.mem_insert.1 hq with rfl | hqS <;>
          simp only [Function.update_self, *] at hy hyq
        all_goals grind only
  obtain ⟨x, hgood, hsep⟩ := hchoice Finset.univ
  exact ⟨x, fun p => hgood p (Finset.mem_univ _), fun p q => hsep p (Finset.mem_univ _) q (Finset.mem_univ _)⟩

end IFS

/-! ## AnalyticESC.Generic.Density -/

/-!
# The density step of Theorem 1.4

The proof of Theorem 1.4 in Section 4.2, after the interpolation `IFS.exists_noCoincidence_near`: an IFS whose maps
send `[0,1]` into `(0,1)` and whose compositions along distinct finite words differ on `[0,1]` has
arbitrarily `d₂`-close perturbations whose dual IFS satisfies the SSC.

The proof follows the paper with words of length `n + 1`, to match Lemma 2.6. The points of
Lemma 4.1 and their orbits are split, for each letter `ℓ`, into the set `𝒴_ℓ` of the points
`x_{i,j}` of the bad pairs with `i₁ = ℓ` and the set `𝒵_ℓ` of the remaining orbit points, and
Proposition 4.2 perturbs each map accordingly. A strictly invariant cylinder is fixed first;
uniform continuity estimates in the `d₂` metric give a neighbourhood where its strict
inclusions persist. Only then are `δ` and the word length chosen.
-/

namespace IFS


/-- A common bound for the dual projections persists in a `d₂` neighbourhood. -/
theorem exists_dualProj_bound_near (Φ : IFS N ε) :
    ∃ K > 0, ∃ η > 0, ∀ {ε'} (Ψ : IFS N ε'), d2 Φ Ψ < η →
      ∀ w : Address N, ∀ x ∈ I, (Ψ.dualProj (.inf w) x).re ∈ Icc (-K) K := by
  obtain ⟨B,hB0,hB⟩ := Φ.exists_norm_dualProj_le
  obtain ⟨A,η₀,hη₀,hcont⟩ := Φ.exists_dualProj_sub_le_d2
  refine ⟨B+1,by linarith,min η₀ (1/(|A|+1)),by positivity,fun {ε'} Ψ hΨ w x hx => ?_⟩
  have hd := Continuity.d2_nonneg Φ Ψ
  have  : A*d2 Φ Ψ < 1 := by
    have  := (lt_div_iff₀ (by positivity )).1 (hΨ.trans_le (min_le_right _ _))
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self A) hd]
  have  := hcont Ψ (hΨ.trans_le (min_le_left _ _)) (.inf w) x hx
  have  := hB (.inf w) x (Φ.mem_closure hx)
  have hnorm := norm_sub_norm_le (Ψ.dualProj (.inf w) x) (Φ.dualProj (.inf w) x)
  rw [norm_sub_rev] at hnorm
  have hr := Complex.abs_re_le_norm (Ψ.dualProj (.inf w) x)
  rw [abs_le] at hr
  constructor <;> linarith

/-! ## The density step -/

/-- The density step in the proof of Theorem 1.4. -/
theorem exists_dualSSC_near (hN : 0 < N) (Φ : IFS N ε)
    (hI : ∀ i, ∀ x ∈ I, (Φ.f i x).re ∈ Ioo 0 1) (hnc : Φ.NoCoincidence)  (hr : 0 < r) :
    ∃ ε' : ℝ, ∃ Ψ : IFS N ε', d2 Φ Ψ < r ∧ Ψ.DualSSC := by
  obtain ⟨K, hK0, η, hη, hstable⟩ := Φ.exists_dualProj_bound_near
  let δ := min r η / 18
  
  have hδr : 9 * δ < min r η := by dsimp [δ]; linarith [lt_min hr hη]
  let k := -K
  have hkK : k ≤ K := by dsimp [k]; linarith
  
  
  -- the length `n + 1` of the words
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Φ.cmax ^ (n + 1) * (K - k) < δ / 3 := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Φ.cmax_nonneg
    -- the length `n + 1` of the words
    ) (Φ.cmax_lt_one
    )).comp
      (tendsto_add_atTop_nat 1)).mul_const (K-k)
    exact (h.eventually (by simpa using gt_mem_nhds (by positivity : 0 < δ/3))).exists
  -- the points of Lemma 4.1
  obtain ⟨x, hx⟩ := Φ.lemma_4_1 n k K hnc
  -- The orbit partition and the perturbation of Proposition 4.2.
  let Bad (p : WordPair N (n+1)) := ¬ Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2)
  let O  := Finset.univ.biUnion fun p : WordPair N (n+1) =>
    (Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p)).toFinset
  let Y ℓ := (Finset.univ.filter fun p => Bad p ∧ p.1 0 = ℓ).image x
  let Z ℓ := O \ Y ℓ
  have hO {y } : y ∈ O ↔ ∃ p,
      y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p) := by
    simp [O, Finset.mem_biUnion]
  have hYmem {ℓ y} : y ∈ Y ℓ ↔ ∃ p, (Bad p ∧ p.1 0 = ℓ) ∧ x p = y := by
    simp [Y]
  have hZmem {ℓ y} : y ∈ Z ℓ ↔ y ∈ O ∧ y ∉ Y ℓ := by simp [Z]
  have hmem {w m} hm t : (Φ.comp (w.take m).reverse t).re ∈ Φ.orbit w t :=
    List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_of_le hm), rfl⟩
  have hself w t : t ∈ Φ.orbit w t := hmem (Nat.zero_le w.length) t
  have heq {p q} (h : x p = x q)  := by
    by_contra hpq
    refine hx.sep p q hpq (x p) (List.mem_append_left _ (hself _ _)) ?_
    rw [h]
    exact List.mem_append_left _ (hself _ _)
  have hbase {p} ℓ : x p ∈ Y ℓ ↔ Bad p ∧ p.1 0 = ℓ := by
    rw [hYmem]
    constructor
    · rintro ⟨q, hqb, hqx⟩
      rwa [← heq hqx]
    · exact fun h => ⟨p, h, rfl⟩
  have hgood {p y} (hy : y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p))
      (hne : y ≠ x p) ℓ : y ∈ Z ℓ := by
    refine hZmem.2 ⟨hO.2 ⟨p, hy⟩, fun hY => ?_⟩
    obtain ⟨q, -, rfl⟩ := hYmem.1 hY
    grind [IsPointChoice.sep]
  have hselfZ {p ℓ} (h : ¬ (Bad p ∧ p.1 0 = ℓ))  :=
    hZmem.2 ⟨hO.2 ⟨p, List.mem_append_left _ (hself _ _)⟩, fun hY => h ((hbase ℓ).1 hY)⟩
  have hne {w t} (hnd : (Φ.orbit w t).Nodup) {m} (h0 : 0 < m) (hm : m ≤ w.length) :
      (Φ.comp (w.take m).reverse t).re ≠ t := by
    intro h
    have := List.inj_on_of_nodup_map hnd (List.mem_range.2 (Nat.lt_succ_of_le hm))
      (List.mem_range.2 (Nat.succ_pos w.length)) (by simpa)
    omega
  have htail {p v} (hv : v = p.1 ∨ v = p.2) {m} (h0 : 0 < m) (hm : m ≤ n+1) ℓ :
      (Φ.comp ((List.ofFn v).take m).reverse (x p)).re ∈ Z ℓ := by
    rcases hv with rfl | rfl
    · exact hgood (List.mem_append_left _ (hmem (by simpa using hm) _))
        (hne (hx.good p).2.2.1 h0 (by simpa using hm)) ℓ
    · exact hgood (List.mem_append_right _ (hmem (by simpa using hm) _))
        (hne (hx.good p).2.2.2 h0 (by simpa using hm)) ℓ
  
  
  choose g hg hY hZ hdist using fun i => proposition_4_2 Φ.ε_pos (Φ.inClass i) (hI i)
    (Y i) (Z i) (by
        rintro y hy
        obtain ⟨p, -, rfl⟩ := hYmem.1 hy
        exact (hx.good p).1
      ) (by
        intro y hy
        obtain ⟨p, hy⟩ := hO.1 (hZmem.1 hy).1
        rcases List.mem_append.1 hy with hy | hy
        all_goals
          obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
          exact Φ.re_comp_mem_I _ (hx.good p).1
      )
    (Finset.disjoint_left.2 fun _ hY hZ => (hZmem.1 hZ).2 hY) δ ((by positivity)
    )
  choose e he hgε using hg
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min e
  let ε' := e i₀
  have hε' := he i₀
  have hgε' i := (hgε i).mono hε' (hi₀ i)
  let Ψ : IFS N ε' := ⟨g, hε', hgε'⟩
  have hag {t v ℓ} (ht : t ∈ I) (h : (Φ.comp v t).re ∈ Z ℓ) :
      AgreeAt (Φ.f ℓ) (Ψ.f ℓ) (Φ.comp v t) := by
    rw [Φ.comp_ofReal v ht]
    exact hZ ℓ _ h
  have hcyl {w t} (ht : t ∈ I)
      (h : ∀ m hm, (Φ.comp (w.take m).reverse t).re ∈ Z w[m]) :
      Ψ.dualCylAt k K w t = Φ.dualCylAt k K w t := by
    have ha c := dualComp_eq_of_agreeAt Φ Ψ (fun m hm => hag ht (h m hm)) c
    simp only [dualCylAt, ha]
  have hd := (ciSup_le hdist).trans_lt hδr
  refine ⟨ε', Ψ, hd.trans_le (min_le_left _ _), ?_⟩
  have hdisj (i j : Block N (n+1)) (hp : i 0 ≠ j 0) :
      Ψ.DualCylDisjoint k K (List.ofFn i) (List.ofFn j) := by
    let p := (i,j)
    have ht := (hx.good p).1
    refine ⟨x p, ht, ?_⟩
    -- the orbit of the second word, with its base point in `𝒵_{j₁}`
    have hall {v} (hv : v = p.1 ∨ v = p.2) (h0 : x p ∈ Z (v 0)) :
        ∀ m hm,
          (Φ.comp ((List.ofFn v).take m).reverse (x p)).re ∈
            Z (List.ofFn v)[m] := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simpa using h0
      · exact htail hv hm0 (by simpa using hm.le) _
    by_cases hb : Bad p
    · -- a bad pair: `x_{i,j} ∈ 𝒴_{i₁}` and `x_{i,j} ∈ 𝒵_{j₁}`
      obtain ⟨h0, h1, hτ⟩ := hY _ _ ((hbase _).2 ⟨hb, rfl⟩)
      have hZ0 := hselfZ (p := p) (ℓ := p.2 0) fun h => hp h.2
      change δ ≤ ‖Ψ.nonlin (p.1 0) (x p) - Φ.nonlin (p.1 0) (x p)‖ at hτ
      let τ := Ψ.nonlin (p.1 0) (x p) - Φ.nonlin (p.1 0) (x p)
      have hshift : Ψ.dualCylAt k K (List.ofFn p.1) (x p) =
          (· + τ.re) '' Φ.dualCylAt k K (List.ofFn p.1) (x p) := by
        have hs h : Ψ.dualComp (List.ofFn p.1) h (x p) =
            Φ.dualComp (List.ofFn p.1) h (x p) + τ := by
          simp only [List.ofFn_succ, dualComp_cons_apply, Ψ]
          rw [h0, h1, dualComp_eq_of_agreeAt Φ Ψ ?_ h]
          · dsimp [τ]; ring
          · intro m hm
            rw [List.length_ofFn] at hm
            have := hag ht (htail (.inl rfl) (Nat.succ_pos m) (by omega)
              (List.ofFn fun i => p.1 i.succ)[m])
            simpa [List.ofFn_succ, comp_append] using this
        rw [dualCylAt, dualCylAt, image_add_const_uIcc, hs, hs, Complex.add_re, Complex.add_re]
      have hτre : δ ≤ |τ.re| := by
        rwa [Complex.abs_re_eq_norm.2]
        rw [Complex.sub_im, Ψ.im_nonlin_ofReal _ (ofReal_mem_nbhd Ψ.ε_pos ht),
          Φ.im_nonlin_ofReal _ (ofReal_mem_nbhd Φ.ε_pos ht), sub_zero]
      rw [hshift, hcyl ht (hall (.inr rfl) hZ0)]
      have hdiam (w : Block N (n+1)) (a b ) :=
        Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK (List.ofFn w) ht (p := a) (q := b)
      simp only [List.length_ofFn] at hdiam
      obtain ⟨z, hzA, hzB⟩ := not_disjoint_iff_nonempty_inter.1
        (fun hd => hb ⟨x p, ht, hd⟩)
      clear * - hn hτre hdiam hzA hzB
      grind
    · -- a pair that is not bad: all orbit points lie in `𝒵`
      have hZ0 : ∀ ℓ, x p ∈ Z ℓ :=
        fun ℓ => hselfZ fun h => hb h.1
      rw [hcyl ht (hall (.inl rfl) (hZ0 _)), hcyl ht (hall (.inr rfl) (hZ0 _))]
      exact (hx.good p).2.1 (not_not.1 hb)
  have hH := hstable Ψ (hd.trans_le (min_le_right _ _))
  simp only [DualSSC, hN, true_and]
  intro i j hij
  obtain ⟨x, hx, hd⟩ := hdisj (fun m => i m) (fun m => j m) (by simpa )
  have hmem w v :
      (Ψ.dualProj ((Word.inf v).prepend w) x).re ∈ Ψ.dualCylAt k K w x := by
    have hxn := ofReal_mem_nbhd Ψ.ε_pos hx
    rw [dualCylAt, Ψ.re_dualComp_const _ _ hx, Ψ.re_dualComp_const _ _ hx,
      Ψ.dualProj_prepend w (.inf v) (subset_closure hxn), Ψ.comp_ofReal w.reverse hx]
    simp  [Complex.add_re, Complex.mul_re, Ψ.im_deriv_comp_ofReal _ hxn, ]
    have h := hH v _ (Ψ.re_comp_mem_I w.reverse hx)
    rw [← image_add_const_uIcc, ← image_const_mul_uIcc]
    exact ⟨_, ⟨_, Icc_subset_uIcc h, rfl⟩, by ring⟩

  
  
  grind [AnalyticESC.Word.inf_eq_prepend_ofFn]

end IFS

/-! ## AnalyticESC.Generic.Coincidences -/

/-!
# The interpolation in the proof of Theorem 1.4

A `d₂`-small perturbation of an IFS whose maps send `[0,1]` into `(0,1)` and whose compositions
along distinct finite words differ on `[0,1]`.

The perturbation is `f_i^t = (1 - t) f_i + t h_i` for a small `t > 0`, where the affine maps
`h_i(z) = a z + b_i` have pairwise disjoint images `h_i(I) ⊆ (0,1)`, so that distinct compositions
of the `h_i` differ on `I`. For fixed words and a
fixed point of `I`, compositions of the `f_i^t` are holomorphic in the complex parameter `t` on an
open set containing `[0,1]`, so two of them agree for finitely many `t ∈ [0,1]` only. A countable
union of finite sets misses some small `t > 0`. Auxiliary results are in the namespace
`IFS.Coincidences`.
-/

namespace IFS.Coincidences

/-! ## The affine maps `h_i` -/

/-- The common slope `a = 1/(2(N+2))` of the affine maps `h_i`. -/
def slope (N : ℕ) : ℝ := 1 / (2 * (N + 2))

/-- The offset `b_i = (i+1)/(N+2)` of the affine map `h_i`. -/
def offset (i : Fin N) : ℝ := (i + 1) / (N + 2)

/-- `a > 0`. -/
theorem slope_pos : 0 < slope N := by unfold slope; positivity

/-- `a < 1`. -/
theorem slope_lt_one : slope N < 1 := by
  unfold slope
  rw [div_lt_one (by positivity)]
  grind

/-- `b_i > 0`. -/
theorem offset_pos (i : Fin N) : 0 < offset i := by unfold offset; positivity

/-- The affine images are contained in `(0,1)` and separated. -/
theorem offset_add_slope_lt_one (i : Fin N) : offset i + slope N < 1 := by
  have  : (i : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  unfold offset slope
  field_simp
  nlinarith

theorem offset_add_slope_lt_offset {i j : Fin N} (hij : i < j) : offset i + slope N < offset j := by
  have  : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  unfold offset slope
  field_simp
  nlinarith

/-- The affine map `h_i(z) = a z + b_i`. -/
def target (i : Fin N) (z : ℂ) :=
  slope N * z + offset i

/-- `h_i` is real at real points. -/
theorem target_ofReal (i : Fin N) (x : ℝ) : target i x = (slope N * x + offset i : ℝ) := by simp [target]

/-! ## The perturbations `f_i^t` -/

/-- The map `f_i^t = (1 - t) f_i + t h_i`, for a complex parameter `t`. -/
def homotopy t i z :=
  (1 - t) * Φ.f i z + t * target i z

/-- The composition `f^t_w = f^t_{w₁} ∘ ⋯ ∘ f^t_{w_k}` of the maps `f_i^t`. -/
def compT t (w : FWord N) :=
  w.foldr (fun i g => homotopy Φ t i ∘ g) id

/-- `f^t_{iw} = f_i^t ∘ f^t_w`. -/
theorem compT_cons t i w :
    compT Φ t (i :: w) = homotopy Φ t i ∘ compT Φ t w :=
  rfl

/-- `f_i^1 = h_i`. -/
theorem homotopy_one i z : homotopy Φ 1 i z = target i z := by simp [homotopy]

/-- For real `t`, the map `f_i^t` is real at the real points of `B_{2ε}`. -/
theorem im_homotopy_ofReal (t : ℝ) i {x : ℝ} (hx : (x : ℂ) ∈ nbhd (2 * ε)) :
    (homotopy Φ t i x).im = 0 := by
  simp [homotopy, target, Φ.im_f_ofReal i hx]

/-- For real `t` and `x`, `Re f_i^t(x) = (1 - t) Re f_i(x) + t h_i(x)`. -/
theorem re_homotopy_ofReal (t : ℝ) i (x : ℝ) :
    (homotopy Φ t i x).re = (1 - t) * (Φ.f i x).re + t * (slope N * x + offset i) := by
  simp [homotopy, target]

/-- For `t ∈ (0,1]`, the map `f_i^t` sends `I` into `(0,1)`. -/
theorem re_homotopy_mem_Ioo {t : ℝ} (ht : t ∈ Ioc 0 1) i  (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ Ioo 0 1 := by
  rw [re_homotopy_ofReal]
  have hf := (Φ.inClass i).re_mem_I x hx
  have  := offset_pos i
  have  := offset_add_slope_lt_one i
  have  : 0 ≤ slope N * x := mul_nonneg slope_pos.le hx.1
  have  : slope N * x ≤ slope N := mul_le_of_le_one_right slope_pos.le hx.2
  obtain ⟨ht0, ht1⟩ := ht
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) hf.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hf.2)]

/-- The endpoint `t = 0` is the original map. -/
theorem re_homotopy_mem_I  (ht : t ∈ I) i  (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ I := by
  rcases ht.1.eq_or_lt with h | h
  · simp [← h, homotopy, (Φ.inClass i).re_mem_I x hx]
  · exact Ioo_subset_Icc_self (re_homotopy_mem_Ioo Φ ⟨h, ht.2⟩ i hx)

/-- For `t ∈ [0,1]`, the compositions `f^t_w` send real points of `I` to real points of `I`. -/
theorem exists_compT_ofReal  (ht : t ∈ I) w  (hx : x ∈ I) :
    ∃ y ∈ I, compT Φ t w x = y := by
  induction w with
  | nil => solve_by_elim
  | cons i w ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    refine ⟨(homotopy Φ t i y).re, re_homotopy_mem_I Φ ht i hy, ?_⟩
    rw [compT_cons, Function.comp_apply, hyx]
    refine Complex.ext (by simp) ?_
    
    exact im_homotopy_ofReal Φ t i (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy)

/-! ## Distinct compositions of the affine maps -/

/-- For `x ∈ I`, the point `h_{iw}(x)` lies in `h_i(I) = [b_i, b_i + a]`. -/
theorem re_compT_one_cons_mem i w  (hx : x ∈ I) :
    (compT Φ 1 (i :: w) x).re ∈ Icc (offset i) (offset i + slope N) := by
  obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ  unitInterval.one_mem w hx
  rw [Complex.ofReal_one] at hyx
  rw [compT_cons, Function.comp_apply, hyx, homotopy_one, target_ofReal, Complex.ofReal_re]
  have  : 0 ≤ slope N * y := mul_nonneg slope_pos.le hy.1
  have  : slope N * y ≤ slope N := mul_le_of_le_one_right slope_pos.le hy.2
  constructor <;> linarith

/-- Compositions of the affine maps `h_i` along distinct finite words differ on `I`. -/
theorem exists_compT_one_ne (u v ) (huv : u ≠ v) :
    ∃ x ∈ I, compT Φ 1 u x ≠ compT Φ 1 v x := by
  -- a nonempty word sends `0` to a point with positive real part
  have hpos  := fun i w =>
    (offset_pos i).trans_le (re_compT_one_cons_mem Φ i w unitInterval.zero_mem).1
  refine ⟨0, unitInterval.zero_mem, ?_⟩
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact absurd rfl huv
    | cons j v =>
      intro h
      apply (hpos j v).ne' 
      rw [← h]
      simp [compT]
  | cons i u ih =>
    cases v with
    | nil =>
      intro h
      apply (hpos i u).ne' 
      rw [h]
      simp [compT]
    | cons j v =>
      intro h
      have  := re_compT_one_cons_mem Φ i u unitInterval.zero_mem
      have  := re_compT_one_cons_mem Φ j v unitInterval.zero_mem
      
      by_cases hij : i = j
      · subst j
        apply huv
        congr 1
        by_contra huv
        apply ih v huv
        simpa  [compT_cons, Function.comp_apply, homotopy_one,
          target, add_left_inj, mul_right_inj' (Complex.ofReal_ne_zero.2 slope_pos.ne'
          )] using h
      · 
        rcases lt_or_gt_of_ne hij with hlt | hlt <;>
          have := offset_add_slope_lt_offset hlt <;> grind

/-! ## The perturbations lie in the class -/

theorem deriv_target (i : Fin N) : deriv (target i) = fun _ => (slope N : ℂ) := by
  funext z
  unfold target
  simp

theorem iteratedDeriv_homotopy k t i (hz : z ∈ nbhd (2 * ε)) :
    iteratedDeriv k (homotopy Φ t i) z = (1 - t) * iteratedDeriv k (Φ.f i) z + t * iteratedDeriv k (target i) z :=
  by
  unfold homotopy
  rw [iteratedDeriv_fun_add
      (contDiffAt_const.mul ((Φ.differentiableOn_f i).analyticOnNhd (isOpen_nbhd _) z hz).contDiffAt)
      (contDiffAt_const.mul (by unfold target; fun_prop))]
  simp

/-- For `0 < t < c_min/(c_min + 1)`, the map `f_i^t` lies in `S^ω_ε(I)`. -/
theorem inClass_homotopy (ht0 : 0 < t) (ht : t * (Φ.cmin + 1) < Φ.cmin) i : InClass ε (homotopy Φ t i) :=
  by
  have := Φ.cmin_pos.le
  have ht1 : t < 1 := by nlinarith
  have := slope_pos (N := N)
  have :=
    slope_lt_one (N := N)
      -- on `cl B_ε`, `(f_i^t)' = (1 - t) f_i' + t a`
      
  have hder : ∀ z ∈ closedNbhd ε, deriv (homotopy Φ t i) z = (1 - t : ℝ) * deriv (Φ.f i) z + (t * slope N : ℝ) :=
    by
    intro z hz
    simpa [deriv_target] using iteratedDeriv_homotopy Φ 1 t i (IFS.closure_nbhd_subset_two hz)
  have hn1 : ∀ z, ‖(1 - t : ℝ) * deriv (Φ.f i) z‖ = (1 - t) * ‖deriv (Φ.f i) z‖ :=
    by
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖((t * slope N : ℝ) : ℂ)‖ = t * slope N := by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine Challenge.InClass.of_deriv Φ.ε_pos ?_ ?_ ?_ ?_ ?_
  · exact ((Φ.differentiableOn_f i).const_mul _).add (((differentiableOn_id.const_mul _).add_const _).const_mul _)
  · exact fun x => im_homotopy_ofReal Φ t i
  · exact fun x => re_homotopy_mem_I Φ ⟨ht0.le, ht1.le⟩ i
  · -- `|(f_i^t)'| ≥ (1 - t) c_min - t a > 0`
    
    intro z hz h0
    have := Φ.cmin_le_norm_deriv i hz
    have h := norm_sub_le ((1 - t : ℝ) * deriv (Φ.f i) z + (t * slope N : ℝ)) (t * slope N : ℝ)
    rw [add_sub_cancel_right, ← hder z hz, h0, norm_zero, hn1] at h
    nlinarith
  · -- `|(f_i^t)'| ≤ (1 - t) |f_i'| + t a < 1`
    
    intro z hz
    have := (Φ.inClass i).norm_deriv_lt_one z hz
    rw [hder z hz]
    calc
      _ ≤ ‖(1 - t : ℝ) * deriv (Φ.f i) z‖ + ‖((t * slope N : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = (1 - t) * ‖deriv (Φ.f i) z‖ + t * slope N := by rw [hn1, hn2]
      _ < 1 := by nlinarith

/-! ## The distance to the perturbation -/

/-- A common bound for the second derivatives `f_i''` on `I`. -/
def exists_deriv_deriv_bound :=
  uniform_norm_bound isCompact_Icc fun i =>
    (((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).deriv (isOpen_nbhd _)).continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun x => ofReal_mem_nbhd (by linarith [Φ.ε_pos])

/-- `d₂(f_i, f_i^t) ≤ t (4 + K)` for `t ∈ [0,1]`, where `K` bounds `|f_i''|` on `I`. -/
theorem d2Map_homotopy_le i (hK' : ∀ x ∈ I, ‖D²(Φ.f i) x‖ ≤ K) (ht : t ∈ I) :
    d2Map (Φ.f i) (homotopy Φ t i) ≤ t * (4 + K) :=
  by
  have hnt : ‖(t : ℂ)‖ = t := by simp [Real.norm_of_nonneg ht.1]
  have e k C (hC : ∀ x : I, ‖iteratedDeriv k (Φ.f i) x‖ + ‖iteratedDeriv k (target i) x‖ ≤ C) :
    ⨆ x : I, ‖iteratedDeriv k (Φ.f i) x - iteratedDeriv k (homotopy Φ t i) x‖ ≤ t * C :=
    by
    refine ciSup_le fun x => ?_
    rw [iteratedDeriv_homotopy Φ k t i (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) x.2)]
    calc
      _ = ‖t * (iteratedDeriv k (Φ.f i) x - iteratedDeriv k (target i) x)‖ := by ring
      _ ≤ t * C := by
        rw [norm_mul, hnt]
        exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (hC x)) ht.1
  have e0 :=
    e 0 2 fun x => by
      have hf : ‖Φ.f i x‖ ≤ 1 := Φ.norm_comp_ofReal_le_one [i] x.2
      have hh : ‖target i x‖ ≤ 1 :=
        by
        have : 0 ≤ slope N * x := mul_nonneg slope_pos.le x.2.1
        have : slope N * x ≤ slope N := mul_le_of_le_one_right slope_pos.le x.2.2
        rw [target_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [offset_pos i, offset_add_slope_lt_one i]
      norm_num only [iteratedDeriv_zero] at *
      linarith
  have e1 :=
    e 1 2 fun x => by
      have hf := ((Φ.inClass i).norm_deriv_lt_one _ (Φ.mem_closure x.2)).le
      have hh : ‖(slope N : ℂ)‖ ≤ 1 := by simpa [abs_of_pos slope_pos] using slope_lt_one (N := N).le
      simpa [deriv_target] using show ‖deriv (Φ.f i) x‖ + ‖(slope N : ℂ)‖ ≤ 2 by linarith
  have e2 := e 2 K fun x => by simpa [iteratedDeriv_succ, deriv_target] using hK' x x.2
  simp [iteratedDeriv_succ] at e0 e1 e2
  dsimp [d2Map]
  linarith

/-! ## Coincidences for finitely many parameters -/

/-- For a fixed word `w` and `x ∈ I`, the map `t ↦ f^t_w(x)` is holomorphic on an open set
containing `[0,1]`. -/
theorem exists_differentiableOn_compT w (hx : x ∈ I) :
    ∃ O : Set ℂ, IsOpen O ∧ (↑) '' I ⊆ O ∧ DifferentiableOn ℂ (fun t => compT Φ t w x) O := by
  induction w with
  | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_const _⟩
  | cons i w ih =>
    obtain ⟨O, hO, hIO, hd⟩ := ih
    refine
      ⟨O ∩ (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε), hd.continuousOn.isOpen_inter_preimage hO (isOpen_nbhd _), ?_, ?_⟩
    · -- for `t ∈ [0,1]`, `f^t_w(x)` is a point of `I`
      
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ hs w hx
      refine ⟨hIO (mem_image_of_mem _ hs), ?_⟩
      show compT Φ s w x ∈ nbhd (2 * ε)
      rw [hyx]
      exact ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy
    · have hg := hd.mono (inter_subset_left (t := (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε)))
      have := (Φ.differentiableOn_f i).comp hg fun t ht => ht.2
      show DifferentiableOn ℂ (fun t => (1 - t) * Φ.f i (compT Φ t w x) + t * (slope N * compT Φ t w x + offset i)) _
      fun_prop

/-- If `h_u(x) ≠ h_v(x)`, then `f^t_u(x) = f^t_v(x)` for finitely many `t ∈ [0,1]` only. -/
theorem finite_compT_eq   (hx : x ∈ I)
    (hne : compT Φ 1 u x ≠ compT Φ 1 v x) :
    {t : ℝ | t ∈ I ∧ compT Φ t u x = compT Φ t v x}.Finite := by
  obtain ⟨Ou, hOu, hIu, hdu⟩ := exists_differentiableOn_compT Φ u hx
  obtain ⟨Ov, hOv, hIv, hdv⟩ := exists_differentiableOn_compT Φ v hx
  obtain ⟨ρ, hρ, hsub⟩ :=
    isCompact_image_I.exists_thickening_subset_open (hOu.inter hOv) (subset_inter hIu hIv)
  rw [← nbhd_eq_thickening] at hsub
  
  refine (finite_zeros hρ ((hdu.mono (hsub.trans inter_subset_left)).sub (hdv.mono (hsub.trans inter_subset_right))
  ) ⟨1,  ?_⟩).subset ?_
  · simpa [sub_eq_zero] using hne
  exact fun t ht => ⟨ht.1, sub_eq_zero.2 ht.2⟩

end IFS.Coincidences

namespace IFS

open Coincidences

/-- The interpolation at the start of the density proof of Theorem 1.4. Every `Φ ∈ 𝔖_N(ε)` has, for
every `r > 0`, a perturbation `Ψ ∈ 𝔖_N(ε)` with `d₂(Φ, Ψ) < r` whose maps send `[0,1]` into `(0,1)`
and whose compositions along distinct finite words differ on `[0,1]`. -/
theorem exists_noCoincidence_near (Φ : IFS N ε) (hr : 0 < r) :
    ∃ Ψ : IFS N ε, d2 Φ Ψ < r ∧ (∀ i, ∀ x ∈ I, (Ψ.f i x).re ∈ Ioo 0 1) ∧ Ψ.NoCoincidence :=
  by
  set c := Φ.cmin
  have := Φ.cmin_pos
  obtain ⟨K, hK, hK'⟩ := exists_deriv_deriv_bound Φ
  set B := ⋃ p : FWord N × FWord N, {t | t ∈ I ∧ p.1 ≠ p.2 ∧ ∀ x ∈ I, compT Φ t p.1 x = compT Φ t p.2 x}
  have hB : B.Countable := by
    refine countable_iUnion fun p => Finite.countable ?_
    by_cases hp : p.1 = p.2
    · simp [hp]
    · obtain ⟨⟩ := exists_compT_one_ne Φ p.1 p.2 hp
      grind [AnalyticESC.IFS.Coincidences.finite_compT_eq, Set.Finite.subset]
  set t₀ := min (c / (c + 1)) (r / (4 + K))
  have ht₀ : 0 < t₀ := by positivity
  obtain ⟨t, htB, ht⟩ := (hB.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.2 ht₀)
  have ht1 := (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_left _ _))
  have ht_lt : t < 1 := by nlinarith [ht.1]
  have htI : t ∈ I := ⟨ht.1.le, ht_lt.le⟩
  let Ψ : IFS N ε := ⟨homotopy Φ t, Φ.ε_pos, inClass_homotopy Φ ht.1 ht1⟩
  refine ⟨Ψ, ?_, fun i x => re_homotopy_mem_Ioo Φ ⟨ht.1, ht_lt.le⟩ i, ?_⟩
  · have h := fun i => d2Map_homotopy_le Φ i (hK' i) htI
    exact
      (Real.iSup_le h (mul_nonneg ht.1.le (by linarith))).trans_lt
        ((lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_right _ _)))
  · -- `t ∉ B`
    
    intro u v huv
    by_contra h
    refine htB (mem_iUnion.2 ⟨(u, v), htI, huv, fun x hx => ?_⟩)
    by_contra hne
    exact h ⟨x, hx, hne⟩

end IFS

/-! ## AnalyticESC.Generic.OpenDense -/

/-!
# Theorem 1.4

The IFSs of `𝔖_N` that satisfy the SESC contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, the
union class of decision D1. The open set consists of the systems whose dual IFS satisfies the SSC:
it is open by Lemma 2.7, its systems satisfy the SESC by Theorem 2.2, and it is dense by the
interpolation `IFS.exists_noCoincidence_near` and the density step. The density step combines two perturbations, so
it uses the triangle inequality for `d₂` between systems of `𝔖_N(ε)` for different `ε`. For `N = 0`
the dual IFS has no Challenge.attractor, and the open set consists of all systems.
-/

namespace OpenDense

/-- The triangle inequality follows by viewing each derivative as a continuous map on `I`. -/
theorem d2_le_add (Φ : IFS N ε) (Φ' : IFS N ε') (Ψ : IFS N ε'') : d2 Φ Ψ ≤ d2 Φ Φ' + d2 Φ' Ψ :=
  by
  refine Real.iSup_le (fun i => ?_) (add_nonneg (IFS.Continuity.d2_nonneg Φ Φ') (IFS.Continuity.d2_nonneg Φ' Ψ))
  have H k :=
    dist_triangle (⟨_, Φ.continuous_iteratedDeriv_on_I i k⟩ : C(I, ℂ)) ⟨_, Φ'.continuous_iteratedDeriv_on_I i k⟩
      ⟨_, Ψ.continuous_iteratedDeriv_on_I i k⟩
  simp [dist_eq_norm, ContinuousMap.norm_eq_iSup_norm] at H
  have h0 := H 0
  have h1 := H 1
  have h2 := H 2
  simp [iteratedDeriv_succ] at h0 h1 h2
  have := IFS.Continuity.d2Map_le_d2 Φ Φ' i
  have := IFS.Continuity.d2Map_le_d2 Φ' Ψ i
  dsimp [d2, d2Map] at *
  linarith

end OpenDense

/-- Theorem 1.4. The systems of `𝔖_N` satisfying the SESC contain a subset `U` of `𝔖_N` that is
open and dense in the `𝒞²` metric. -/
theorem theorem_1_4 N :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, InUnionClass f ∧ Challenge.SESC f) ∧
        (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → Challenge.d2 f g < r → g ∈ U) ∧
          ∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, Challenge.d2 f g < r :=
  by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨{f | InUnionClass f}, ?_, ?_, ?_⟩
    · exact fun f hf => ⟨hf, 1, one_pos, fun n i j hij => False.elim (hij (Subsingleton.elim _ _))⟩
    · exact fun f hf => ⟨1, one_pos, fun g hg _ => hg⟩
    · exact fun f hf r hr => ⟨f, hf, by simpa [Challenge.d2] using hr⟩
  refine ⟨{f | ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.DualSSC}, ?_, ?_, ?_⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    exact ⟨⟨ε, Φ.ε_pos, Φ.inClass⟩, Φ.theorem_2_2 hΦ⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    obtain ⟨δ, hδ, hΨ⟩ := Φ.lemma_2_7_union hΦ
    exact ⟨δ, hδ, fun g ⟨ε', hε', hg⟩ hfg => ⟨ε', ⟨g, hε', hg⟩, rfl, by solve_by_elim⟩⟩
  · rintro f ⟨ε, hε, hf⟩ r hr
    let Φ : IFS N ε := ⟨f, hε, hf⟩
    obtain ⟨Φ₁, hΦ₁, hI, hnc⟩ := Φ.exists_noCoincidence_near (half_pos hr)
    obtain ⟨ε', Ψ, hΨ, hssc⟩ := IFS.exists_dualSSC_near hN Φ₁ hI hnc (half_pos hr)
    refine ⟨Ψ.f, ⟨ε', Ψ, rfl, hssc⟩, ?_⟩
    have := OpenDense.d2_le_add Φ Φ₁ Ψ
    change d2 Φ Ψ < r
    linarith

/-! ## AnalyticESC.Dimension.OpenDense -/

/-!
# Corollary 1.7

The systems of `𝔖_N` with equality in (1.6) contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, for
`N ≥ 2`. The open set is the open set of Theorem 1.4 intersected with the systems whose attractor
is not a singleton, which is open and dense for `N ≥ 2`; Theorem 1.6 applies to its systems.
-/

namespace OpenDense

/-- Having no common fixed point in `I` is a `d₂`-open condition in `𝔖_N`: the continuous
function `‖(f_i(x) - x)_i‖` has a positive minimum `m` on `I`, and `d₂(f, g) < m` keeps
some `|g_i(x) - x|` positive at every `x ∈ I`. -/
theorem exists_forall_d2Sys_lt_not_fixed  {f : Fin N → CMap} (hf : InUnionClass f)
    (hfix : ¬ ∃ x ∈ I, ∀ i, (f i x).re = x) :
    ∃ r > 0, ∀ g, InUnionClass g → Challenge.d2 f g < r → ¬ ∃ x ∈ I, ∀ i, (g i x).re = x := by
  obtain ⟨ε, hε, hfε⟩ := hf
  let F (x : ℝ) i := (f i x).re - x
  
  have hpos : ∀ x ∈ I, 0 < ‖F x‖ := by
    intro x hx
    apply norm_pos_iff.2
    intro h
    exact hfix ⟨x, hx, fun i => sub_eq_zero.1 (congrFun h i)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) ((continuousOn_pi.2 fun i => ((hfε i).analytic_real hε).continuousOn.sub continuousOn_id).norm
  )
  refine ⟨‖F x₀‖, hpos x₀ hx₀, ?_⟩
  rintro g ⟨ε', hε', hgε⟩ hd ⟨x, hx, hgx⟩
  let Φ : IFS N ε := ⟨f, hε, hfε⟩
  let Ψ : IFS N ε' := ⟨g, hε', hgε⟩
  
  exact not_lt_of_ge ((isMinOn_iff.1 hmin x hx).trans (by
    change ‖F x‖ ≤ d2 Φ Ψ
    rw [pi_norm_le_iff_of_nonneg (IFS.Continuity.d2_nonneg Φ Ψ)]
    intro i
    
    calc |(f i x).re - x| = |(f i x - g i x).re| := by rw [Complex.sub_re, hgx i]
      _ ≤ ‖f i x - g i x‖ := Complex.abs_re_le_norm _
      _ ≤ Challenge.d2 f g := (IFS.Continuity.norm_sub_le_d2 Φ Ψ i hx).1
  )) hd

/-- Having no common fixed point in `I` is a `d₂`-dense condition in `𝔖_N` for `N ≥ 2`. If the maps
`f_i` fix a common point `p`, replace one map `f_j` by the perturbation
`f_j^t = (1 - t) f_j + t h_j` of the interpolation `IFS.exists_noCoincidence_near`, with `h_j(p) ≠ p` and small
`t > 0`. A common fixed point of the new system is fixed by some `f_k`, `k ≠ j`, so it is `p`, which
`f_j^t` moves. -/
theorem exists_not_fixed_d2Sys_lt (hN : 2 ≤ N) {f : Fin N → CMap} (hf : InUnionClass f) (hr : 0 < r) :
    ∃ g, InUnionClass g ∧ (¬∃ x ∈ I, ∀ i, (g i x).re = x) ∧ Challenge.d2 f g < r :=
  by
  by_cases hfix : ∃ x ∈ I, ∀ i, (f i x).re = x
  swap
  · exact ⟨f, hf, hfix, by simpa [Challenge.d2] using hr⟩
  obtain ⟨p, hp, hfp⟩ := hfix
  obtain ⟨ε, hε, hfε⟩ := hf
  let Φ : IFS N ε :=
    ⟨f, hε, hfε⟩
      -- a map `f_j` with `h_j(p) ≠ p`, and a second map `f_k`
      
  obtain ⟨j⟩ : ∃ j : Fin N, IFS.Coincidences.slope N * p + IFS.Coincidences.offset j ≠ p :=
    by
    by_contra! h
    have h01 : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩ := Fin.mk_lt_mk.2 one_pos
    linarith [IFS.Coincidences.offset_add_slope_lt_offset h01, h ⟨0, by omega⟩, h ⟨1, by omega⟩,
      IFS.Coincidences.slope_pos (N := N)]
  have := Fin.nontrivial_iff_two_le.2 hN
  obtain ⟨k, hk⟩ := exists_ne j
  set c := Φ.cmin
  have hc := Φ.cmin_pos
  obtain ⟨K, hK, hK'⟩ := IFS.Coincidences.exists_deriv_deriv_bound Φ
  set t := min (c / (c + 1)) (r / (4 + K)) / 2
  have htt : t < min (c / (c + 1)) (r / (4 + K)) := half_lt_self (lt_min (by positivity) (by positivity))
  have := (lt_div_iff₀ (by positivity)).1 (htt.trans_le (min_le_left _ _))
  set g := Function.update f j (IFS.Coincidences.homotopy Φ t j) with hg
  refine ⟨g, ⟨ε, hε, fun i => ?_⟩, ?_, ?_⟩
  · grind [AnalyticESC.IFS.Coincidences.inClass_homotopy]
  · rintro ⟨x, hx, hgx⟩
    have := by
      simpa [Φ, by simpa [g, Function.update_of_ne hk] using hgx k, hfp] using Φ.abs_re_comp_sub_le_mul [k] hx hp
    have hc := Φ.cmax_lt_one
    obtain rfl : x = p := sub_eq_zero.1 (abs_eq_zero.1 (by nlinarith [abs_nonneg (x - p)]))
    have h := hgx j
    rw [hg, Function.update_self] at h
    rw [IFS.Coincidences.re_homotopy_ofReal] at h
    grind
  · have h : ∀ i, d2Map (f i) (g i) ≤ t * (4 + K) := by
      intro i
      by_cases hi : i = j
      · rw [hi, hg, Function.update_self]
        exact IFS.Coincidences.d2Map_homotopy_le Φ j (hK' j) ⟨by positivity, by nlinarith⟩
      · simp [hg, Function.update_of_ne hi, d2Map]
        positivity
    exact (Real.iSup_le h (by positivity)).trans_lt ((lt_div_iff₀ (by positivity)).1 (htt.trans_le (min_le_right _ _)))

end OpenDense

/-- Corollary 1.7. For `N ≥ 2`, the systems of `𝔖_N` with equality in (1.6) contain a subset `U` of
`𝔖_N` that is open and dense in the `𝒞²` metric. -/
theorem corollary_1_7 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, InUnionClass f ∧ Challenge.DimEquality f) ∧
        (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → Challenge.d2 f g < r → g ∈ U) ∧
          ∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, Challenge.d2 f g < r :=
  by
  have hN0 : 0 < N := by omega
  obtain ⟨U₁, hU₁, hU₁o, hU₁d⟩ := theorem_1_4 N
  refine ⟨U₁ ∩ {f | InUnionClass f ∧ ¬∃ x ∈ I, ∀ i, (f i x).re = x}, ?_, ?_, ?_⟩
  · -- Theorem 1.6, with the remark after it
    
    rintro f ⟨hf₁, -, hfix⟩
    obtain ⟨⟨ε, hε, hf⟩, hΦ⟩ := hU₁ f hf₁
    let Φ : IFS N ε := ⟨f, hε, hf⟩
    refine ⟨⟨ε, hε, hf⟩, Φ.theorem_1_6 hM hS hN0 (fun h => hfix ?_) (Φ.esc_of_sesc hΦ)⟩
    exact (Φ.exists_attractor_eq_singleton_iff hN0).1 h
  · -- openness
    grind [AnalyticESC.OpenDense.exists_forall_d2Sys_lt_not_fixed]
  · -- density: perturb to remove a common fixed point, then apply Theorem 1.4
    
    intro f hf r hr
    obtain ⟨g, hg, hgfix, hfg⟩ := OpenDense.exists_not_fixed_d2Sys_lt hN hf (half_pos hr)
    obtain ⟨ρ, hρ, hgρ⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hg hgfix
    obtain ⟨h, hh₁, hgh⟩ := hU₁d g hg (min ρ (r / 2)) (lt_min hρ (half_pos hr))
    have hh := (hU₁ h hh₁).1
    refine ⟨h, ⟨hh₁, hh, hgρ h hh (hgh.trans_le (min_le_left _ _))⟩, ?_⟩
    obtain ⟨ε, hε, hf⟩ := hf
    obtain ⟨ε', hε', hg⟩ := hg
    obtain ⟨ε'', hε'', hh⟩ := hh
    have htri := OpenDense.d2_le_add ⟨f, hε, hf⟩ ⟨g, hε', hg⟩ ⟨h, hε'', hh⟩
    change Challenge.d2 f h ≤ Challenge.d2 f g + Challenge.d2 g h at htri
    linarith [htri, hfg, hgh.trans_le (min_le_right ρ (r / 2))]

end AnalyticESC

end
