module

public import Mathlib

@[expose] public section

namespace Challenge

open Set Metric

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
noncomputable def supDist (f : Fin N → ℂ → ℂ) (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖comp f i x - comp f j x‖

/-- The strong exponential separation condition (Definition 1.2): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n` and all `n`. -/
def SESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- Nonvanishing of the derivatives at every finite orbit of a point of `I`. -/
def NonzeroDerivatives (f : Fin N → ℂ → ℂ) : Prop :=
  ∀ (i : Fin N) (w : List (Fin N)) (x : I), deriv (f i) (comp f w x) ≠ 0

/-- The distortion `f''/f'`. -/
noncomputable def nonlin (g : ℂ → ℂ) (z : ℂ) (_h : deriv g z ≠ 0) : ℂ :=
  deriv (deriv g) z / deriv g z

/-- The dual natural projection `H_w` of (1.4) for a finite word `w`. The term with index `n`
(from `0`) is `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where `v` is the prefix of the first `n`
letters, `i` the next letter and `f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}`. -/
noncomputable def dualProjFin (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : List (Fin N)) (x : I) : ℂ :=
  ∑ n : Fin w.length,
    nonlin (f (w.get n)) (comp f (w.take n).reverse x) (hd (w.get n) (w.take n).reverse x) *
      deriv (comp f (w.take n).reverse) x

/-- The dual natural projection `H_w` of (1.4) for an infinite word `w`. -/
noncomputable def dualProjInf (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : ℕ → Fin N) (x : I) : ℂ :=
  ∑' n, nonlin (f (w n)) (comp f (List.ofFn fun k : Fin n => w k).reverse x)
    (hd (w n) (List.ofFn fun k : Fin n => w k).reverse x) *
      deriv (comp f (List.ofFn fun k : Fin n => w k).reverse) x

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax (ε : ℝ) (f : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (f i) z‖

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f) : ℝ :=
  ⨆ (x : I) (i : Fin N), ‖nonlin (f i) x (hd i [] x)‖

/-- The maps `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` of the example in
Section 1.2.2. -/
noncomputable def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable def natProj (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) : ℝ :=
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
noncomputable def d2 (f g : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ i, (⨆ x : I, ‖f i x - g i x‖) +
    (⨆ x : I, ‖deriv (f i) x - deriv (g i) x‖) +
    (⨆ x : I, ‖deriv (deriv (f i)) x - deriv (deriv (g i)) x‖)

/-- The space `𝔖_N` of Section 1.1: IFSs whose maps lie in `S^ω_ε(I)` for some `ε > 0`, which may
depend on the system. -/
def InUnionClass (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

section Dimension

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

/-! ### Dimension theory (Sections 1.2.1 and 1.2.2) -/

/-- The exponential separation condition (ESC): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n`, for infinitely many
`n`. -/
def ESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- The sum `∑_{w ∈ Σ_n} (sup_{x ∈ I} |f_w'(x)|)^t`. The pressure is
`P(t) = lim_n log(pressureSum f t n) / n`; its zero is `s(Φ)` (Section 1.2.1). -/
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

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1, for the measure
`μ`, with the derivatives of the real maps `x ↦ f_i(x)`. -/
noncomputable def lyapunov (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : ℝ :=
  -∑ i, p i * ∫ x, Real.log |deriv (fun y : ℝ => (f i y).re) x| ∂μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2): a Borel probability measure on
`[0,1]` with `μ = ∑_i p_i μ ∘ f_i⁻¹`. -/
def IsSelfConformal (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Iᶜ = 0 ∧
    μ = ∑ i, ENNReal.ofReal (p i) • μ.map (fun x : ℝ => (f i x).re)

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

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2, where
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`. -/
noncomputable def lqDim (μ : Measure ℝ) (q : ℝ) (hq : q - 1 ≠ 0) : ℝ :=
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
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ p : Fin N → ℝ, (∀ i, 0 < p i) → ∑ i, p i = 1 →
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ Iᶜ = 0 →
      μ = ∑ i, ENNReal.ofReal (p i) • μ.map (φ i) →
      ∀ hχ : (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) ≠ 0,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (-∑ i, p i * Real.log (p i))
          (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) hχ)))

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

end Dimension

end Challenge

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

export Challenge (I nbhd InClass exampleMaps IsAnalyticCoord ConjSelfSimilar periodic InUnionClass
  divide Scale scaleZero logRatio entropy IsProbVec IsGibbsMeasure realComp RapaportHyp
  BowenGibbsStatement RapaportMeasureStatement RapaportSetStatement)

structure IFS (N : ℕ) (ε : ℝ) where
  f : Fin N → ℂ → ℂ
  ε_pos : 0 < ε
  inClass : ∀ i, InClass ε (f i)

inductive Word (N : ℕ) where
  | fin : List (Fin N) → Word N
  | inf : (ℕ → Fin N) → Word N

namespace Word

variable {N : ℕ}

def get? : Word N → ℕ → Option (Fin N)
  | fin w, n => w[n]?
  | inf w, n => some (w n)

def take : Word N → ℕ → List (Fin N)
  | fin w, n => w.take n
  | inf w, n => List.ofFn fun k : Fin n => w k

def prepend (a : List (Fin N)) : Word N → Word N
  | fin w => fin (a ++ w)
  | inf w => inf fun n => if h : n < a.length then a[n] else w (n - a.length)

end Word

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

abbrev comp : List (Fin N) → ℂ → ℂ := Challenge.comp Φ.f
noncomputable abbrev supDist : List (Fin N) → List (Fin N) → ℝ := Challenge.supDist Φ.f
abbrev ESC : Prop := Challenge.ESC Φ.f
abbrev SESC : Prop := Challenge.SESC Φ.f
noncomputable abbrev natProj : (ℕ → Fin N) → ℝ := Challenge.natProj Φ.f
abbrev attractor : Set ℝ := Challenge.attractor Φ.f
noncomputable abbrev cmax : ℝ := Challenge.cmax ε Φ.f
noncomputable abbrev lyapunov : (Fin N → ℝ) → Measure ℝ → ℝ := Challenge.lyapunov Φ.f
abbrev IsSelfConformal : (Fin N → ℝ) → Measure ℝ → Prop := Challenge.IsSelfConformal Φ.f
noncomputable abbrev potential : ℝ → (ℕ → Fin N) → ℝ := Challenge.potential Φ.f

def NoCoincidence : Prop :=
  ∀ i j : List (Fin N), i ≠ j → ∃ x ∈ I, Φ.comp i (x : ℂ) ≠ Φ.comp j (x : ℂ)

noncomputable def cmin : ℝ := ⨅ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (Φ.f i) z‖

noncomputable def nonlin (i : Fin N) (z : ℂ) : ℂ := deriv (deriv (Φ.f i)) z / deriv (Φ.f i) z

noncomputable def dualTerm (w : Word N) (n : ℕ) (z : ℂ) : ℂ :=
  match w.get? n with
  | none => 0
  | some i => Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z

noncomputable def dualProj (w : Word N) (z : ℂ) : ℂ := ∑' n, Φ.dualTerm w n z

noncomputable def dualComp (w : List (Fin N)) (h : ℂ → ℂ) : ℂ → ℂ :=
  w.foldr (fun i G z => deriv (Φ.f i) z * G (Φ.f i z) + Φ.nonlin i z) h

def DualSSC : Prop :=
  ∀ i j : ℕ → Fin N, i 0 ≠ j 0 → ∃ x ∈ I, Φ.dualProj (.inf i) x ≠ Φ.dualProj (.inf j) x

noncomputable def dualCylAt (k K : ℝ) (i : List (Fin N)) (x : ℝ) : Set ℝ :=
  uIcc (Φ.dualComp i (fun _ => (k : ℂ)) x).re (Φ.dualComp i (fun _ => (K : ℂ)) x).re

def DualCylDisjoint (k K : ℝ) (i j : List (Fin N)) : Prop :=
  ∃ x ∈ I, Disjoint (Φ.dualCylAt k K i x) (Φ.dualCylAt k K j x)

noncomputable def orbit (i : List (Fin N)) (x : ℝ) : List ℝ :=
  (List.range (i.length + 1)).map fun l => (Φ.comp (i.take l).reverse x).re

noncomputable def realMaps : Fin N → ℝ → ℝ := fun i x => (Φ.f i x).re

end IFS

noncomputable def d2Map (f g : ℂ → ℂ) : ℝ :=
  (⨆ x : I, ‖f ((x : ℝ) : ℂ) - g ((x : ℝ) : ℂ)‖) +
    (⨆ x : I, ‖deriv f ((x : ℝ) : ℂ) - deriv g ((x : ℝ) : ℂ)‖) +
    (⨆ x : I, ‖deriv (deriv f) ((x : ℝ) : ℂ) - deriv (deriv g) ((x : ℝ) : ℂ)‖)

noncomputable abbrev d2Sys {N : ℕ} (f g : Fin N → ℂ → ℂ) : ℝ := Challenge.d2 f g

noncomputable abbrev d2 {N : ℕ} {ε ε' : ℝ} (Φ : IFS N ε) (Ψ : IFS N ε') : ℝ := Challenge.d2 Φ.f Ψ.f

namespace Word

variable {N : ℕ}

@[simp] theorem get?_fin (w : List (Fin N)) (n : ℕ) : (fin w).get? n = w[n]? := rfl
@[simp] theorem get?_inf (w : ℕ → Fin N) (n : ℕ) : (inf w).get? n = some (w n) := rfl
@[simp] theorem take_fin (w : List (Fin N)) (n : ℕ) : (fin w).take n = w.take n := rfl
@[simp] theorem take_inf (w : ℕ → Fin N) (n : ℕ) :
    (inf w).take n = List.ofFn fun k : Fin n => w k := rfl

theorem isSome_get?_of_lt {w : Word N} {k m : ℕ} (h : k < m) :
    (w.get? m).isSome → (w.get? k).isSome := by
  cases w with | fin _ => simp [Option.isSome_iff_ne_none]; omega | inf _ => simp

private theorem getElem?_take_word (w : Word N) (n k : ℕ) :
    (w.take n)[k]? = if k < n then w.get? k else none := by
  cases w with
  | fin w => simp [List.getElem?_take]
  | inf w => simp only [take_inf, List.getElem?_ofFn, get?_inf]; split_ifs <;> rfl

theorem ext_get? {v w : Word N} (h : ∀ n, v.get? n = w.get? n) : v = w := by
  cases v with
  | fin v => cases w with
    | fin w => exact congrArg fin (List.ext_getElem? h)
    | inf w => exact absurd (h v.length) (by simp)
  | inf v => cases w with
    | fin w => exact absurd (h w.length) (by simp)
    | inf w => exact congrArg inf (funext fun n => Option.some_injective _ (h n))

private theorem get?_prepend (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).get? n = if n < a.length then a[n]? else w.get? (n - a.length) := by
  cases w with
  | fin w => simp [prepend, List.getElem?_append]
  | inf w => simp only [prepend, get?_inf]; split_ifs with hn <;> simp [hn]

theorem get?_prepend_of_lt (a : List (Fin N)) (w : Word N) {n : ℕ} (hn : n < a.length) :
    (w.prepend a).get? n = a[n]? := by simp [get?_prepend, hn]

theorem get?_prepend_add (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).get? (a.length + n) = w.get? n := by simp [get?_prepend]

theorem take_prepend_of_le (a : List (Fin N)) (w : Word N) {n : ℕ} (hn : n ≤ a.length) :
    (w.prepend a).take n = a.take n :=
  List.ext_getElem? fun k => by
    rw [getElem?_take_word, get?_prepend, List.getElem?_take]; split_ifs <;> first | rfl | omega

theorem take_prepend_add (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).take (a.length + n) = a ++ w.take n :=
  List.ext_getElem? fun k => by
    rw [getElem?_take_word, get?_prepend, List.getElem?_append, getElem?_take_word]
    split_ifs <;> first | rfl | omega

theorem exists_eq_prepend {i j : Word N} {n : ℕ}
    (hP : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k) :
    ∃ (a : List (Fin N)) (i' j' : Word N), a.length = n ∧ i = i'.prepend a ∧ j = j'.prepend a := by
  have hlen_le : ∀ w : Word N, (∀ k < n, (w.get? k).isSome) →
      ∃ w' : Word N, w = w'.prepend (w.take n) ∧ (w.take n).length = n := fun w hw => by
    cases w with
    | fin v =>
      have hnv : n ≤ v.length := by
        by_contra hlt; have := hw v.length (not_le.1 hlt); simp at this
      exact ⟨fin (v.drop n), by simp [prepend, List.take_append_drop], List.length_take_of_le hnv⟩
    | inf v =>
      refine ⟨inf fun k => v (n + k), ?_, by simp⟩
      simp only [prepend, take_inf, List.length_ofFn, List.getElem_ofFn]
      congr 1; funext k
      split_ifs with hk <;> [rfl; exact congrArg v (Nat.add_sub_of_le (not_lt.1 hk)).symm]
  obtain ⟨i', hi', hilen⟩ := hlen_le i fun k hk => (hP k hk).1
  obtain ⟨j', hj', -⟩ := hlen_le j fun k hk => (hP k hk).2 ▸ (hP k hk).1
  have htake : i.take n = j.take n := List.ext_getElem? fun k => by
    rw [getElem?_take_word, getElem?_take_word]
    split_ifs with hk <;> [exact (hP k hk).2; rfl]
  exact ⟨i.take n, i', j', hilen, hi', htake ▸ hj'⟩

end Word

theorem List.exists_decomp_of_ne {N : ℕ} {i j : List (Fin N)} (hlen : i.length = j.length)
    (hne : i ≠ j) :
    ∃ a b u : List (Fin N), i = a ++ u ∧ j = b ++ u ∧ a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? := by
  induction i using _root_.List.reverseRecOn generalizing j with
  | nil => exact absurd (_root_.List.eq_nil_of_length_eq_zero hlen.symm).symm hne
  | append_singleton i x ih =>
    have hj : j ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨j', y, rfl⟩ : ∃ j' y, j = j' ++ [y] :=
      ⟨j.dropLast, j.getLast hj, (_root_.List.dropLast_append_getLast hj).symm⟩
    simp only [_root_.List.length_append, _root_.List.length_singleton, Nat.add_right_cancel_iff] at hlen
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨a, b, u, rfl, rfl, hab, ha, hlast⟩ := ih hlen fun h => hne (h ▸ rfl)
      exact ⟨a, b, u ++ [x], by simp, by simp, hab, ha, hlast⟩
    · exact ⟨i ++ [x], j' ++ [y], [], by simp, by simp, by simp [hlen], by simp, by simp [hxy]⟩

theorem isCompact_image_I : IsCompact (((↑) : ℝ → ℂ) '' I) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem convex_image_I : Convex ℝ (((↑) : ℝ → ℂ) '' I) :=
  (convex_Icc (0 : ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap

theorem nbhd_eq_thickening (δ : ℝ) : nbhd δ = thickening δ (((↑) : ℝ → ℂ) '' I) := by
  ext; simp [nbhd, mem_thickening_iff, dist_eq_norm]

theorem isOpen_nbhd (δ : ℝ) : IsOpen (nbhd δ) := nbhd_eq_thickening δ ▸ isOpen_thickening

theorem convex_nbhd (δ : ℝ) : Convex ℝ (nbhd δ) := nbhd_eq_thickening δ ▸ convex_image_I.thickening δ

theorem isPreconnected_nbhd (δ : ℝ) : IsPreconnected (nbhd δ) := (convex_nbhd δ).isPreconnected

theorem isCompact_closure_nbhd (δ : ℝ) : IsCompact (closure (nbhd δ)) :=
  nbhd_eq_thickening δ ▸ isCompact_image_I.isBounded.thickening.isCompact_closure

theorem ofReal_mem_nbhd {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  nbhd_eq_thickening δ ▸ self_subset_thickening hδ _ (mem_image_of_mem _ hx)

theorem ball_subset_nbhd {δ x : ℝ} (hx : x ∈ I) : ball (x : ℂ) δ ⊆ nbhd δ :=
  nbhd_eq_thickening δ ▸ ball_subset_thickening (mem_image_of_mem _ hx) δ

theorem nbhd_mono {δ δ' : ℝ} (h : δ ≤ δ') : nbhd δ ⊆ nbhd δ' := by rw [nbhd_eq_thickening, nbhd_eq_thickening]; exact thickening_mono h _

theorem zero_mem_closure_nbhd {δ : ℝ} (hδ : 0 < δ) : (0 : ℂ) ∈ closure (nbhd δ) := by
  simpa using subset_closure (ofReal_mem_nbhd hδ (x := 0) ⟨le_rfl, zero_le_one⟩)

theorem closure_nbhd_subset {δ δ' : ℝ} (h : δ < δ') : closure (nbhd δ) ⊆ nbhd δ' := by
  rw [nbhd_eq_thickening, nbhd_eq_thickening]
  rcases le_or_gt δ' 0 with h' | h'
  · simp [thickening_of_nonpos (h.le.trans h')]
  · exact (closure_thickening_subset_cthickening δ _).trans (cthickening_subset_thickening' h' h _)

theorem hasDerivAt_re_ofReal {g : ℂ → ℂ} {x : ℝ} (hg : DifferentiableAt ℂ g x) :
    HasDerivAt (fun t : ℝ => (g t).re) (deriv g x).re x := hg.hasDerivAt.real_of_complex

theorem isOpen_setOf_ofReal_mem {U : Set ℂ} (hU : IsOpen U) : IsOpen {t : ℝ | (t : ℂ) ∈ U} :=
  hU.preimage Complex.continuous_ofReal

theorem im_deriv_eq_zero {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    (deriv g x).im = 0 :=
  (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (hg.differentiableAt (hU.mem_nhds hx)).hasDerivAt.comp_ofReal).unique <|
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem ((isOpen_setOf_ofReal_mem hU).mem_nhds hx) fun t ht => hreal t ht)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem nbhd_subset_two : nbhd ε ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_eq_thickening, thickening_of_nonpos h]
  · exact nbhd_mono (by linarith)

theorem closure_nbhd_subset_two : closure (nbhd ε) ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_eq_thickening, thickening_of_nonpos h]
  · exact closure_nbhd_subset (by linarith)

theorem differentiableOn_f (i : Fin N) : DifferentiableOn ℂ (Φ.f i) (nbhd (2 * ε)) :=
  (Φ.inClass i).differentiableOn

theorem differentiableAt_f (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.f i) z :=
  (Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds (closure_nbhd_subset_two hz))

theorem mapsTo_f (i : Fin N) : MapsTo (Φ.f i) (nbhd ε) (nbhd ε) :=
  fun z hz => (Φ.inClass i).mapsTo z (subset_closure hz)

theorem im_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) : (Φ.f i t).im = 0 :=
  (Φ.inClass i).im_eq_zero t ht

private theorem continuousOn_norm_deriv_f (i : Fin N) :
    ContinuousOn (fun z => ‖deriv (Φ.f i) z‖) (closure (nbhd ε)) :=
  (((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).continuousOn.mono closure_nbhd_subset_two).norm

theorem cmax_nonneg : 0 ≤ Φ.cmax :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cmin_nonneg : 0 ≤ Φ.cmin :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => norm_nonneg _

theorem cmax_lt_one : Φ.cmax < 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cmax, Challenge.cmax]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (closure (nbhd ε)) := ⟨⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩⟩
  obtain ⟨i, hi'⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin N => ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
  obtain ⟨z, hz, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ (Φ.continuousOn_norm_deriv_f i)
  rw [cmax, Challenge.cmax, ← hi']
  exact (ciSup_le fun w => hmax w.2).trans_lt ((Φ.inClass i).norm_deriv_lt_one z hz)

theorem norm_deriv_le_cmax (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (Φ.f i) z‖ ≤ Φ.cmax := by
  have hb : BddAbove (range fun w : closure (nbhd ε) => ‖deriv (Φ.f i) w‖) := by
    rw [← image_eq_range (fun w => ‖deriv (Φ.f i) w‖)]
    exact (isCompact_closure_nbhd ε).bddAbove_image (Φ.continuousOn_norm_deriv_f i)
  exact (le_ciSup hb ⟨z, hz⟩).trans
    (le_ciSup (f := fun i => ⨆ w : closure (nbhd ε), ‖deriv (Φ.f i) w‖) (finite_range _).bddAbove i)

theorem cmin_pos (hN : 0 < N) : 0 < Φ.cmin := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (closure (nbhd ε)) := ⟨⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩⟩
  obtain ⟨i, hi'⟩ := (range_nonempty
    (fun i : Fin N => ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)).csInf_mem (finite_range _)
  obtain ⟨z, hz, hmin⟩ := (isCompact_closure_nbhd ε).exists_isMinOn
    ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ (Φ.continuousOn_norm_deriv_f i)
  rw [cmin, iInf, ← hi']
  exact (norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero z hz)).trans_le (le_ciInf fun w => hmin w.2)

theorem cmin_le_norm_deriv (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.cmin ≤ ‖deriv (Φ.f i) z‖ :=
  (ciInf_le (f := fun i => ⨅ w : closure (nbhd ε), ‖deriv (Φ.f i) w‖) (finite_range _).bddBelow i).trans
    (ciInf_le (f := fun w : closure (nbhd ε) => ‖deriv (Φ.f i) w‖)
      ⟨0, by rintro _ ⟨_, rfl⟩; exact norm_nonneg _⟩ ⟨z, hz⟩)

theorem cmin_le_cmax (hN : 0 < N) : Φ.cmin ≤ Φ.cmax :=
  (Φ.cmin_le_norm_deriv ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos)).trans
    (Φ.norm_deriv_le_cmax ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos))

theorem exists_differentiableOn_nonlin (i : Fin N) :
    ∃ U : Set ℂ, IsOpen U ∧ closure (nbhd ε) ⊆ U ∧ DifferentiableOn ℂ (Φ.nonlin i) U := by
  have h1 := (Φ.differentiableOn_f i).deriv (isOpen_nbhd _)
  exact ⟨nbhd (2 * ε) ∩ deriv (Φ.f i) ⁻¹' {0}ᶜ,
    h1.continuousOn.isOpen_inter_preimage (isOpen_nbhd _) isOpen_compl_singleton,
    fun z hz => ⟨closure_nbhd_subset_two hz, (Φ.inClass i).deriv_ne_zero z hz⟩,
    ((h1.deriv (isOpen_nbhd _)).mono inter_subset_left).div
      (h1.mono inter_subset_left) fun _ hz => hz.2⟩

theorem exists_nonlin_bound :
    ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ M := by
  have h : ∀ i, ∃ C, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ C := fun i => by
    obtain ⟨U, -, hU, hd⟩ := Φ.exists_differentiableOn_nonlin i
    exact (isCompact_closure_nbhd ε).exists_bound_of_continuousOn (hd.continuousOn.mono hU)
  choose C hC using h
  exact ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i z hz =>
    (hC i z hz).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))⟩

theorem im_deriv_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) :
    (deriv (Φ.f i) t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd _) (Φ.differentiableOn_f i) (fun _ hs => Φ.im_f_ofReal i hs) ht

theorem im_nonlin_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.nonlin i t).im = 0 := by
  have ht2 := nbhd_subset_two ht
  simp [nonlin, Complex.div_im, Φ.im_deriv_f_ofReal i ht2,
    im_deriv_eq_zero (isOpen_nbhd _) ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _))
      (fun _ hs => Φ.im_deriv_f_ofReal i hs) ht2]

@[simp] theorem comp_nil : Φ.comp [] = id := rfl
@[simp] theorem comp_cons (i : Fin N) (w : List (Fin N)) : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w := rfl

theorem comp_append (u v : List (Fin N)) : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u with | nil => rfl | cons i u ih => rw [List.cons_append, comp_cons, ih, comp_cons]; rfl

theorem mapsTo_comp (w : List (Fin N)) : MapsTo (Φ.comp w) (nbhd ε) (nbhd ε) := by
  induction w with | nil => exact mapsTo_id _ | cons i w ih => exact (Φ.mapsTo_f i).comp ih

theorem mapsTo_comp_closure (w : List (Fin N)) :
    MapsTo (Φ.comp w) (closure (nbhd ε)) (closure (nbhd ε)) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => exact fun z hz => subset_closure ((Φ.inClass i).mapsTo _ (ih hz))

theorem differentiableAt_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.comp w) z := by
  induction w with
  | nil => exact differentiableAt_id
  | cons i w ih => exact (Φ.differentiableAt_f i (Φ.mapsTo_comp_closure w hz)).comp z ih

theorem differentiableOn_comp (w : List (Fin N)) : DifferentiableOn ℂ (Φ.comp w) (nbhd ε) :=
  fun _ hz => (Φ.differentiableAt_comp w (subset_closure hz)).differentiableWithinAt

theorem exists_differentiableOn_comp (w : List (Fin N)) :
    ∃ U : Set ℂ, IsOpen U ∧ closure (nbhd ε) ⊆ U ∧ DifferentiableOn ℂ (Φ.comp w) U := by
  induction w with
  | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_id⟩
  | cons i w ih =>
    obtain ⟨U, hU, hcl, hd⟩ := ih
    exact ⟨U ∩ Φ.comp w ⁻¹' nbhd (2 * ε),
      hd.continuousOn.isOpen_inter_preimage hU (isOpen_nbhd _),
      fun z hz => ⟨hcl hz, closure_nbhd_subset_two (Φ.mapsTo_comp_closure w hz)⟩,
      (Φ.differentiableOn_f i).comp (hd.mono inter_subset_left) fun _ hz => hz.2⟩

theorem deriv_comp_cons (i : Fin N) (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp (i :: w)) z = deriv (Φ.f i) (Φ.comp w z) * deriv (Φ.comp w) z :=
  deriv_comp z (Φ.differentiableAt_f i (Φ.mapsTo_comp_closure w hz)) (Φ.differentiableAt_comp w hz)

theorem deriv_comp_append (u v : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp (u ++ v)) z = deriv (Φ.comp u) (Φ.comp v z) * deriv (Φ.comp v) z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem norm_deriv_comp_le (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (Φ.comp w) z‖ ≤ Φ.cmax ^ w.length := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.norm_deriv_le_cmax i (Φ.mapsTo_comp_closure w hz)) ih (norm_nonneg _) Φ.cmax_nonneg

theorem cmin_pow_le_norm_deriv_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.cmin ^ w.length ≤ ‖deriv (Φ.comp w) z‖ := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.cmin_le_norm_deriv i (Φ.mapsTo_comp_closure w hz)) ih
      (pow_nonneg Φ.cmin_nonneg _) (norm_nonneg _)

theorem deriv_comp_ne_zero (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp w) z ≠ 0 := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz]
    exact mul_ne_zero ((Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure w hz)) ih

theorem exists_comp_bound : ∃ R, 0 ≤ R ∧ ∀ w, ∀ z ∈ closure (nbhd ε), ‖Φ.comp w z‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_closure_nbhd ε).isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _, fun w z hz => (hR _ (Φ.mapsTo_comp_closure w hz)).trans (le_max_left _ _)⟩

theorem norm_comp_sub_le (w : List (Fin N)) {z z' : ℂ} (hz : z ∈ nbhd ε) (hz' : z' ∈ nbhd ε) :
    ‖Φ.comp w z - Φ.comp w z'‖ ≤ Φ.cmax ^ w.length * ‖z - z'‖ :=
  (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun _ hx => Φ.differentiableAt_comp w (subset_closure hx))
    (fun _ hx => Φ.norm_deriv_comp_le w (subset_closure hx)) hz' hz

theorem im_comp_ofReal (w : List (Fin N)) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.comp w t).im = 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have h1 : Φ.comp w t = ((Φ.comp w t).re : ℂ) := Complex.ext rfl (by simp [ih])
    rw [comp_cons, Function.comp_apply, h1]
    exact Φ.im_f_ofReal i (h1 ▸ nbhd_subset_two (Φ.mapsTo_comp w ht))

theorem comp_ofReal (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.comp w x = ((Φ.comp w x).re : ℂ) :=
  Complex.ext rfl (by simp [Φ.im_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hx)])

theorem re_comp_mem_I (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) : (Φ.comp w x).re ∈ I := by
  induction w with
  | nil => simpa using hx
  | cons i w ih => rw [comp_cons, Function.comp_apply, Φ.comp_ofReal w hx]; exact (Φ.inClass i).re_mem_I _ ih

theorem im_deriv_comp_ofReal (w : List (Fin N)) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (deriv (Φ.comp w) t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd ε) (Φ.differentiableOn_comp w) (fun _ hs => Φ.im_comp_ofReal w hs) ht

theorem injOn_re_comp (w : List (Fin N)) : InjOn (fun t : ℝ => (Φ.comp w t).re) I := by
  have hd : ∀ t ∈ I, HasDerivAt (fun t : ℝ => (Φ.comp w t).re) (deriv (Φ.comp w) t).re t := fun t ht =>
    hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure (ofReal_mem_nbhd Φ.ε_pos ht)))
  have key : ∀ {a b}, a ∈ I → b ∈ I → a < b → (Φ.comp w a).re ≠ (Φ.comp w b).re :=
    fun {a b} ha hb hab heq => by
      have hsub : Icc a b ⊆ I := Icc_subset_Icc ha.1 hb.2
      obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
        (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt) heq
        (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht)))
      have hcI := hsub (Ioo_subset_Icc_self hc)
      exact Φ.deriv_comp_ne_zero w (subset_closure (ofReal_mem_nbhd Φ.ε_pos hcI))
        (Complex.ext hc0 (Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hcI)))
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (key ha hb h)
  · exact h
  · exact absurd hab.symm (key hb ha h)

noncomputable def compInf (w : List (Fin N)) : ℝ := sInf ((fun x : ℝ => (Φ.comp w x).re) '' I)
noncomputable def compSup (w : List (Fin N)) : ℝ := sSup ((fun x : ℝ => (Φ.comp w x).re) '' I)

theorem image_comp_eq_Icc (w : List (Fin N)) :
    0 ≤ Φ.compInf w ∧ Φ.compInf w ≤ Φ.compSup w ∧ Φ.compSup w ≤ 1 ∧
      Φ.cmin ^ w.length ≤ Φ.compSup w - Φ.compInf w ∧
      Φ.compSup w - Φ.compInf w ≤ Φ.cmax ^ w.length ∧
      (fun x : ℝ => (Φ.comp w x).re) '' I = Icc (Φ.compInf w) (Φ.compSup w) := by
  set h : ℝ → ℝ := fun x => (Φ.comp w x).re with h_def
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd Φ.ε_pos hx
  have hderiv : ∀ x ∈ I, HasDerivAt h (deriv (Φ.comp w) x).re x := fun x hx =>
    hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure (hmem hx)))
  have hcont : ContinuousOn h I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have himage : h '' I = Icc (Φ.compInf w) (Φ.compSup w) := hcont.image_Icc zero_le_one
  have h0 : h 0 ∈ Icc (Φ.compInf w) (Φ.compSup w) := himage ▸ mem_image_of_mem h ⟨le_rfl, zero_le_one⟩
  have h1 : h 1 ∈ Icc (Φ.compInf w) (Φ.compSup w) := himage ▸ mem_image_of_mem h ⟨zero_le_one, le_rfl⟩
  have hpq : Φ.compInf w ≤ Φ.compSup w := h0.1.trans h0.2
  obtain ⟨a, ha, hpa⟩ : Φ.compInf w ∈ h '' I := himage ▸ left_mem_Icc.2 hpq
  obtain ⟨b, hb, hqb⟩ : Φ.compSup w ∈ h '' I := himage ▸ right_mem_Icc.2 hpq
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h (fun x => (deriv (Φ.comp w) x).re)
    zero_lt_one hcont (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
  have hcI : c ∈ I := Ioo_subset_Icc_self hc
  have hlow : Φ.cmin ^ w.length ≤ |h 1 - h 0| := by
    have := Φ.cmin_pow_le_norm_deriv_comp w (subset_closure (hmem hcI))
    rw [← Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w (hmem hcI)), hslope] at this
    simpa using this
  refine ⟨hpa ▸ (Φ.re_comp_mem_I w ha).1, hpq, hqb ▸ (Φ.re_comp_mem_I w hb).2, ?_, ?_, himage⟩
  · have : |h 1 - h 0| ≤ Φ.compSup w - Φ.compInf w :=
      abs_sub_le_iff.2 ⟨by linarith [h0.1, h1.2], by linarith [h1.1, h0.2]⟩
    linarith
  · have hre : Φ.compSup w - Φ.compInf w ≤ ‖Φ.comp w b - Φ.comp w a‖ := by
      rw [← hpa, ← hqb]
      exact (le_abs_self _).trans ((by simp [h_def] : |h b - h a| = |(Φ.comp w b - Φ.comp w a).re|).trans_le
        (Complex.abs_re_le_norm _))
    have hba : ‖(b : ℂ) - a‖ ≤ 1 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_sub_le_iff.2 ⟨by linarith [ha.1, hb.2], by linarith [hb.1, ha.2]⟩
    exact hre.trans ((Φ.norm_comp_sub_le w (hmem hb) (hmem ha)).trans
      (mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg _) hba))

end IFS

theorem exists_mem_I_norm_sub_le {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1
    ((isCompact_image_I.cthickening_eq_biUnion_closedBall hε) ▸
      closure_thickening_subset_cthickening ε _ (by rwa [← nbhd_eq_thickening]))
  exact ⟨x, hx, mem_closedBall_iff_norm.1 hzx⟩

/-- A map complex analytic on `B_{2ε}`, real at the real points of `B_{2ε}`, with
`f(I) ⊆ I` and `0 < |f'| < 1` on `cl B_ε`, lies in `S^ω_ε(I)`. -/
theorem inClass_of_deriv {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (nbhd (2 * ε)))
    (him : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I)
    (hne : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0)
    (hlt : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1) : InClass ε f := by
  refine ⟨hd, him, hI, ?_, hne, hlt⟩
  have hsub : closure (nbhd ε) ⊆ nbhd (2 * ε) := closure_nbhd_subset (by linarith)
  -- `|f'|` attains its maximum `c < 1` on the compact set `cl B_ε`
  have hcont : ContinuousOn (fun z => ‖deriv f z‖) (closure (nbhd ε)) :=
    ((hd.deriv (isOpen_nbhd _)).continuousOn.mono hsub).norm
  obtain ⟨w, hw, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd hε⟩ hcont
  have hc : ‖deriv f w‖ < 1 := hlt w hw
  intro z hz
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hε.le hz
  have hxcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
  -- the mean value inequality on the convex set `cl B_ε`
  have hmv : ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ :=
    (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
      (fun y hy => hd.differentiableAt ((isOpen_nbhd _).mem_nhds (hsub hy)))
      (fun y hy => hmax hy) hxcl hz
  -- `f(x)` is the real point `(f x).re` of `I`
  have hfx : f x = ((f x).re : ℂ) :=
    Complex.ext rfl (by simp [him x (ofReal_mem_nbhd (by linarith) hx)])
  refine ball_subset_nbhd (hI x hx) (mem_ball_iff_norm.2 ?_)
  rw [← hfx]
  calc ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ := hmv
    _ ≤ ‖deriv f w‖ * ε := mul_le_mul_of_nonneg_left hzx (norm_nonneg _)
    _ < 1 * ε := mul_lt_mul_of_pos_right hc hε
    _ = ε := one_mul ε

theorem exists_inClass {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (nbhd (2 * ε))) (him : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I) (hne : ∀ x ∈ I, deriv f x ≠ 0)
    (hlt : ∀ x ∈ I, ‖deriv f x‖ < 1) : ∃ ε' > 0, InClass ε' f := by
  set V := nbhd (2 * ε) ∩ deriv f ⁻¹' ({0}ᶜ ∩ ball 0 1)
  have hV : IsOpen V := (hd.deriv (isOpen_nbhd _)).continuousOn.isOpen_inter_preimage (isOpen_nbhd _)
    (isOpen_compl_singleton.inter isOpen_ball)
  have hIV : ((↑) : ℝ → ℂ) '' I ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ofReal_mem_nbhd (by linarith) hx, hne x hx, mem_ball_zero_iff.2 (hlt x hx)⟩
  obtain ⟨δ, hδ, hδV⟩ := isCompact_image_I.exists_cthickening_subset_open hV hIV
  set ε' := min δ ε
  have hε' : 0 < ε' := lt_min hδ hε
  have h2 : nbhd (2 * ε') ⊆ nbhd (2 * ε) := nbhd_mono (by linarith [min_le_right δ ε])
  have hcl : closure (nbhd ε') ⊆ V := fun z hz =>
    hδV (cthickening_mono (min_le_left _ _) _ (closure_thickening_subset_cthickening ε' _ (by rwa [← nbhd_eq_thickening])))
  exact ⟨ε', hε', inClass_of_deriv hε' (hd.mono h2) (fun x hx => him x (h2 hx)) hI
    (fun z hz => (hcl hz).2.1) (fun z hz => mem_ball_zero_iff.1 (hcl hz).2.2)⟩

theorem exists_inClass_forall {N : ℕ} {f : Fin N → ℂ → ℂ}
    (h : ∀ i, ∃ ε > 0, InClass ε (f i)) : ∃ ε > 0, ∀ i, InClass ε (f i) := by
  choose ε hε hf using h
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨j, hj⟩ := Finite.exists_min ε
    refine ⟨ε j, hε j, fun i => ?_⟩
    have h2 : nbhd (2 * ε j) ⊆ nbhd (2 * ε i) := nbhd_mono (by linarith [hj i])
    have hcl : closure (nbhd (ε j)) ⊆ closure (nbhd (ε i)) := closure_mono (nbhd_mono (hj i))
    exact inClass_of_deriv (hε j) ((hf i).differentiableOn.mono h2)
      (fun x hx => (hf i).im_eq_zero x (h2 hx)) (hf i).re_mem_I
      (fun z hz => (hf i).deriv_ne_zero z (hcl hz))
      (fun z hz => (hf i).norm_deriv_lt_one z (hcl hz))

private theorem tendsto_ofReal_nhdsNE (c : ℝ) :
    Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with _ hx; simpa using hx

theorem eqOn_nbhd_of_eqOn_Icc {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ I) (heq : ∀ x ∈ Icc a b, g x = h x) : EqOn g h (nbhd ε) := by
  have hfreq : ∃ᶠ x in 𝓝[≠] ((a + b) / 2), x ∈ Icc a b :=
    (eventually_nhdsWithin_of_eventually_nhds (Icc_mem_nhds (by linarith) (by linarith))).frequently
  have hfreq' : ∃ᶠ z : ℂ in 𝓝[≠] (((a + b) / 2 : ℝ) : ℂ), ∃ x ∈ Icc a b, z = (x : ℂ) :=
    (tendsto_ofReal_nhdsNE _).frequently (hfreq.mono fun x hx => ⟨x, hx, rfl⟩)
  exact (hg.analyticOnNhd (isOpen_nbhd ε)).eqOn_of_preconnected_of_frequently_eq
    (hh.analyticOnNhd (isOpen_nbhd ε)) (isPreconnected_nbhd ε)
    (ofReal_mem_nbhd hε (hI ⟨by linarith, by linarith⟩))
    (hfreq'.mono fun _ ⟨x, hx, hz⟩ => hz ▸ heq x hx)

theorem eqOn_nbhd_of_iteratedDeriv_eq {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {x : ℝ} (hx : x ∈ I)
    (heq : ∀ k, iteratedDeriv k g x = iteratedDeriv k h x) : EqOn g h (nbhd ε) := by
  have hball : ball (x : ℂ) ε ⊆ nbhd ε := ball_subset_nbhd hx
  refine (hg.analyticOnNhd (isOpen_nbhd ε)).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd (isOpen_nbhd ε)) (isPreconnected_nbhd ε) (ofReal_mem_nbhd hε hx) ?_
  filter_upwards [ball_mem_nhds (x : ℂ) hε] with z hz
  rw [← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball),
    ← Complex.taylorSeries_eq_on_ball' hz (hh.mono hball)]
  simp_rw [heq]

theorem finite_zeros {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (nbhd ε))
    (hne : ∃ x ∈ I, g x ≠ 0) : {x : ℝ | x ∈ I ∧ g x = 0}.Finite := by
  by_contra hinf
  obtain ⟨c, hcI, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc fun _ hx => hx.1
  have hzero := (hg.analyticOnNhd (isOpen_nbhd ε)).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_nbhd ε) (ofReal_mem_nbhd hε hcI)
    ((tendsto_ofReal_nhdsNE c).frequently ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun _ hx => hx.2))
  obtain ⟨x, hx, hgx⟩ := hne
  exact hgx (hzero (ofReal_mem_nbhd hε hx))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem norm_comp_ofReal_le_one (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp w x‖ ≤ 1 := by
  rw [Φ.comp_ofReal w hx, Complex.norm_real, Real.norm_eq_abs]
  have := Φ.re_comp_mem_I w hx
  exact abs_le.2 ⟨by linarith [this.1], this.2⟩

theorem tendsto_natProj (w : ℕ → Fin N) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re) atTop (𝓝 (Φ.natProj w)) := by
  have hz0 : (0 : ℂ) ∈ nbhd ε := by simpa using ofReal_mem_nbhd Φ.ε_pos (x := 0) ⟨le_rfl, zero_le_one⟩
  have hu : ∀ n, dist (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re
      (Φ.comp (List.ofFn fun k : Fin (n + 1) => w k) 0).re ≤ 1 * Φ.cmax ^ n := fun n => by
    rw [show (List.ofFn fun k : Fin (n + 1) => w k) = (List.ofFn fun k : Fin n => w k) ++ [w n] by
        rw [List.ofFn_succ', List.concat_eq_append]; simp,
      Φ.comp_append, Function.comp_apply, Real.dist_eq, one_mul, ← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ((Φ.norm_comp_sub_le _ hz0 (Φ.mapsTo_comp [w n] hz0)).trans ?_)
    rw [List.length_ofFn, zero_sub, norm_neg]
    exact mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg n)
      (by simpa using Φ.norm_comp_ofReal_le_one [w n] ⟨le_rfl, zero_le_one⟩)
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric Φ.cmax 1 Φ.cmax_lt_one hu))

theorem attractor_subset_I : Φ.attractor ⊆ I := by
  rintro _ ⟨w, rfl⟩
  exact isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj w)
    (Eventually.of_forall fun _ => by simpa using Φ.re_comp_mem_I _ ⟨le_rfl, zero_le_one⟩)

theorem abs_re_comp_sub_le_mul (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |(Φ.comp w x).re - (Φ.comp w y).re| ≤ Φ.cmax ^ w.length * |x - y| := by
  have h := Φ.norm_comp_sub_le w (ofReal_mem_nbhd Φ.ε_pos hx) (ofReal_mem_nbhd Φ.ε_pos hy)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans h

theorem abs_re_comp_sub_le (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |(Φ.comp w x).re - (Φ.comp w y).re| ≤ Φ.cmax ^ w.length :=
  (Φ.abs_re_comp_sub_le_mul w hx hy).trans (mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg _)
    (abs_le.2 ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩))

theorem re_comp_natProj (a : List (Fin N)) (w : ℕ → Fin N) :
    (Φ.comp a (Φ.natProj w)).re =
      Φ.natProj (fun n => if h : n < a.length then a[n] else w (n - a.length)) := by
  have hπ : Φ.natProj w ∈ I := Φ.attractor_subset_I ⟨w, rfl⟩
  have hc : ContinuousAt (fun t : ℝ => (Φ.comp a t).re) (Φ.natProj w) :=
    Complex.continuous_re.continuousAt.comp ((Φ.differentiableAt_comp a
      (subset_closure (ofReal_mem_nbhd Φ.ε_pos hπ))).continuousAt.comp Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique (hc.tendsto.comp (Φ.tendsto_natProj w))
    (((tendsto_add_atTop_iff_nat a.length).2 (Φ.tendsto_natProj _)).congr fun n => ?_)
  have hlist : (List.ofFn fun k : Fin (n + a.length) =>
      if h : (k : ℕ) < a.length then a[(k : ℕ)] else w ((k : ℕ) - a.length)) =
      a ++ List.ofFn fun k : Fin n => w k :=
    List.ext_getElem (by simp [Nat.add_comm]) fun l _ _ => by simp [List.getElem_append]
  rw [Function.comp_apply, hlist, ← Complex.ofReal_zero, Φ.comp_append,
    Function.comp_apply, ← Φ.comp_ofReal _ ⟨le_rfl, zero_le_one⟩]

theorem natProj_eq_comp_prefix (ω : ℕ → Fin N) (k : ℕ) :
    Φ.natProj ω = (Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω (j + k))).re := by
  rw [Φ.re_comp_natProj]; congr 1; funext n
  simp only [List.length_ofFn, List.getElem_ofFn]
  split_ifs with h <;> [rfl; exact congrArg ω (Nat.sub_add_cancel (not_lt.1 h)).symm]

theorem continuous_natProj : Continuous Φ.natProj :=
  TendstoUniformly.continuous (F := fun n ω => (Φ.comp (List.ofFn fun k : Fin n => ω k) 0).re) (p := atTop)
    (Metric.tendstoUniformly_iff.2 fun δ hδ =>
      ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).eventually (gt_mem_nhds hδ)).mono
        fun n hn ω => by
          have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin n => ω k)
            (Φ.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩) ⟨le_rfl, zero_le_one⟩
          rw [List.length_ofFn, Complex.ofReal_zero, ← Φ.natProj_eq_comp_prefix] at h
          rw [Real.dist_eq]; exact h.trans_lt hn)
    (Frequently.of_forall fun n => (continuous_of_discreteTopology
      (f := fun v : Fin n → Fin N => (Φ.comp (List.ofFn v) 0).re)).comp
      (continuous_pi fun k => continuous_apply (k : ℕ)))

theorem norm_le_supDist (i j : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp i x - Φ.comp j x‖ ≤ Φ.supDist i j :=
  le_ciSup (f := fun x : I => ‖Φ.comp i ((x : ℝ) : ℂ) - Φ.comp j ((x : ℝ) : ℂ)‖)
    ⟨2, by
      rintro _ ⟨y, rfl⟩
      linarith [norm_sub_le (Φ.comp i ((y : ℝ) : ℂ)) (Φ.comp j ((y : ℝ) : ℂ)),
        Φ.norm_comp_ofReal_le_one i y.2, Φ.norm_comp_ofReal_le_one j y.2]⟩
    ⟨x, hx⟩

theorem exists_close_pair_ge (h : ¬ Φ.SESC) {c : ℝ} (hc : 0 < c) (B : ℕ) :
    ∃ n, B ≤ n ∧ ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < c ^ n := by
  by_contra! hcon
  apply h
  set c₀ := min c 1
  have hc₀ : 0 < c₀ := lt_min hc one_pos
  refine ⟨c₀ ^ (B + 1), pow_pos hc₀ _, fun n i j hij => ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hij (by subst h0; exact Subsingleton.elim i j)
  let u : Fin B → Fin N := fun _ => i ⟨0, hn⟩
  have h1 := hcon (n + B) (Nat.le_add_left B n) (Fin.append i u) (Fin.append j u) fun he => hij <| by
    have := congrArg List.ofFn he
    rw [List.ofFn_fin_append, List.ofFn_fin_append] at this
    exact List.ofFn_injective (List.append_cancel_right this)
  rw [List.ofFn_fin_append, List.ofFn_fin_append] at h1
  have hsup : Φ.supDist (List.ofFn i ++ List.ofFn u) (List.ofFn j ++ List.ofFn u) ≤
      Φ.supDist (List.ofFn i) (List.ofFn j) := by
    have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    refine ciSup_le fun x => ?_
    change ‖Φ.comp (List.ofFn i ++ List.ofFn u) x - Φ.comp (List.ofFn j ++ List.ofFn u) x‖ ≤ _
    rw [Φ.comp_append, Φ.comp_append, Function.comp_apply, Function.comp_apply, Φ.comp_ofReal _ x.2]
    exact Φ.norm_le_supDist _ _ (Φ.re_comp_mem_I _ x.2)
  calc (c₀ ^ (B + 1)) ^ n = c₀ ^ ((B + 1) * n) := (pow_mul _ _ _).symm
    _ ≤ c₀ ^ (n + B) := pow_le_pow_of_le_one hc₀.le (min_le_right _ _) (by nlinarith)
    _ ≤ c ^ (n + B) := pow_le_pow_left₀ hc₀.le (min_le_left _ _) _
    _ ≤ _ := h1.trans hsup

theorem esc_of_sesc (h : Φ.SESC) : Φ.ESC := by
  obtain ⟨c, hc, h⟩ := h; exact ⟨c, hc, Frequently.of_forall h⟩

end IFS

end AnalyticESC
