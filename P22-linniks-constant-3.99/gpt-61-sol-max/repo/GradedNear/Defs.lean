
import Mathlib
set_option quotPrecheck false

/-!
# Definitions: the graded near lemma, its zero form, and the leaf-LP certificates

All definitions that the compared theorems use are in this one module, so that the Palomar
Challenge (`scripts/make_challenge.py`) is a verbatim copy that Lean elaborates identically
(including the auxiliary proof constants it abstracts from definitions).

References:
* [HB] D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime
  in an arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338.
* [X] T. Xylouris, *Über die Nullstellen der Dirichletschen L-Funktionen und die kleinste
  Primzahl in einer arithmetischen Progression*, Bonner Math. Schriften 404 (2011).
* [G] S. W. Graham, *An asymptotic estimate related to Selberg's sieve*, J. Number Theory 10
  (1978) 83–94.
* [B] D. A. Burgess, *On character sums and L-series. II*, Proc. London Math. Soc. (3) 13
  (1963) 524–536.

Throughout, `q` is the modulus and `Real.log q` plays the role of Heath-Brown's `𝓛`.
The four printed results used as hypotheses are stated as `Prop`s below
(`XylourisLemma31`, `XylourisLemma32`, `BurgessPrimitive`, `GrahamEstimate`). Each is implied by its
source; see the individual docstrings.

**Significance.** The graded near lemma is a weighted, Selberg-sieve-majorized version of
Heath-Brown's Lemma 12.1 [HB, §12]: every entry carries its own anchor, so crowds of zeros at
different distances from `σ = 1` are charged at their own rates. Heath-Brown writes [HB, §16,
item 9] that it "would be nice to have a weighted version of Lemma 12.1 ... Unfortunately, no neat
way of achieving this seems available". The lemma is the new analytic ingredient of a proposed
proof that Linnik's constant is at most 3.99 (Theorem 8.4 of the paper `paper/linnik399.pdf` in
this repository); that application is not formalized here.

**Differences from the paper's Theorem 8.4** (each harmless for the application):
* the pair excess `e_j` is defined from the exact Gram values `Re G(-σ_jk + i y_jk)` of all
  same-character partners; the paper bounds it by constants `c^hi` (§9.4), which this implies;
* entry heights satisfy `|γ_j| ≤ T ≤ (log q)/3`;
* the safe-anchor case hypothesis is the zero-free statement `SafeAnchor q s₁ (2T + 1)` for all
  zeros; with `T = l(q)` it follows from the paper's safe-anchor hypothesis (Definition 8.3) and [X, Lemma 3.3] = [HB, Lemma 6.1];
* `NearData.Valid` requires a uniform lower bound for `ω` where `f ≠ 0`, and `I_B > 0`.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

namespace GradedNear

/-- Real exponents used in the character and sieve estimates. -/
scoped notation "⅓" => ((1 : ℝ) / 3)
scoped notation "⅔" => ((2 : ℝ) / 3)
scoped notation "⅑" => ((1 : ℝ) / 9)

open Classical in
/-- The set of indices `k ≠ j` of the same character as `j` (used for pair excesses). -/
def sameCharOthers {ι : Type*} [Fintype ι] {α : Type*} (χ : ι → α) (j : ι) : Finset ι :=
  Finset.univ.filter fun k => k ≠ j ∧ χ k = χ j

/-! ## Test functions -/

/-- [HB, Condition 1, p. 280] = [X, Bedingung 1, p. 17]. The function `f` is continuous on
`[0, ∞)`, vanishes on `[x₀, ∞)`, and is twice continuously differentiable on `(0, x₀)` with
`|f''| ≤ B` there. -/
structure Condition1 (f : ℝ → ℝ) (x₀ B : ℝ) : Prop where
  pos : 0 < x₀
  cont : ContinuousOn f (Set.Ici 0)
  vanish : ∀ t, x₀ ≤ t → f t = 0
  smooth : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)
  bound : ∀ t ∈ Set.Ioo 0 x₀, |deriv (deriv f) t| ≤ B

/-- The Laplace transform `F(z) = ∫₀^∞ f(t) e^{-zt} dt`. -/
def laplace (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), ↑(f t) * cexp (-(z * t))

/-- [HB, Condition 2, p. 286] = [X, Bedingung 2, p. 18]: `f ≥ 0` on `[0, ∞)` and
`Re F(z) ≥ 0` whenever `Re z ≥ 0`. -/
structure Condition2 (f : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  re_nonneg : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (laplace f z).re

/-! ## Prime sums and zero sums -/

/-- The smoothed prime sum `Σ_{n ≥ 1} Λ(n) χ(n) n^{-s} f(log n / log q)` of [X, Lemmas 3.1–3.2]
(Heath-Brown's `K(s, χ)` is its real part). -/
def primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ↑(Λ n) * χ n * ↑n ^ (-s) * ↑(f (Real.log n / Real.log q))

/-- The sum, over the zeros `ρ` of `L(s, χ)` with `|1 + i Im(s) - ρ| ≤ δ`, counted with
multiplicity, of `Re F((s - ρ) log q)`: the zero sum of [X, Lemma 3.2]. For `δ < 1` the disc lies
in `Re ρ > 0`, so only nontrivial zeros enter; there Mathlib's `LFunction χ` (the `L`-function of
`χ` as a character mod `q`) has the same zeros and multiplicities as that of the primitive
character inducing `χ`. For `χ ≠ 1` it is entire and not identically zero, so the zero set in the
disc is finite and the `finsum` is a genuine finite sum. -/
def zeroSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (s : ℂ) (δ : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ‖ 1 + ↑s.im * I - ρ‖ ≤ δ ∧ DirichletCharacter.LFunction χ ρ = 0},
    ↑(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) *
      (laplace f ((s - ρ) * ↑(Real.log q))).re

/-- The region of [X, Lemmas 3.1–3.2]: `|Re s - 1| ≤ (log 𝓛)^{1/2} / 𝓛` and `|Im s| ≤ 𝓛`,
where `𝓛 = log q`. -/
def LemmaRegion (q : ℕ) (s : ℂ) : Prop :=
  |s.re - 1| ≤ Real.sqrt (Real.log (Real.log q)) / Real.log q ∧ |s.im| ≤ Real.log q

/-! ## The literature inputs -/

/-- [X, Lemma 3.1, p. 18] = [HB, Lemma 5.3]: for `f` satisfying Condition 1 and `s` in the
region, `Σ Λ(n) χ₀(n) n^{-s} f(𝓛⁻¹ log n) = 𝓛 F((s - 1)𝓛) + O(𝓛 / log 𝓛)`, with the implied
constant depending only on `f`. Here `χ₀ = 1` is the principal character mod `q`. -/
def XylourisLemma31 : Prop :=
  ∀ (f : ℝ → ℝ) (x₀ B : ℝ), Condition1 f x₀ B →
    ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ s : ℂ, LemmaRegion q s →
      ‖primeSum (1 : DirichletCharacter ℂ q) f s - ↑(Real.log q) *
          laplace f ((s - 1) * ↑(Real.log q))‖ ≤
        C * Real.log q / Real.log (Real.log q)

/-- [X, Lemma 3.2, p. 18]; cf. [HB, Lemma 5.2, p. 24] (whose printed statement omits the factor
`Λ(n)`, a misprint, and has the conductor term `f(0)(φ/2 + ε)𝓛`, which gives the form below after
rescaling `ε`): for `f` satisfying Condition 1 with `f(0) ≥ 0`
and every `ε > 0` there are `δ ∈ (0, 1)` and `q₀` such that for `q ≥ q₀`, every non-principal
`χ` mod `q` and every `s` in the region,
`Σ Λ(n) Re(χ(n) n^{-s}) f(𝓛⁻¹ log n) ≤ -𝓛 Σ_{|1+it-ρ| ≤ δ} Re F((s-ρ)𝓛) + (φ/2) f(0) 𝓛 + ε 𝓛`.
The printed conductor coefficient is `φ(χ) ∈ {1/4, 1/3}` ([X, p. 17]); since `f(0) ≥ 0`, the
statement below with `φ = 1/3` is implied by the printed one. -/
def XylourisLemma32 : Prop :=
  ∀ (f : ℝ → ℝ) (x₀ B : ℝ), Condition1 f x₀ B → 0 ≤ f 0 →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ s : ℂ, LemmaRegion q s →
        (primeSum χ f s).re ≤
          -(Real.log q * zeroSum χ f s δ) + f 0 / 6 * Real.log q + ε * Real.log q

/-- A character sum over an interval of given start and length. -/
scoped notation "charSum " χ:arg N:arg H:arg =>
  (∑ n ∈ Finset.Ioc N (N + H), χ n)

/-- Burgess's bound with `r = 3`: for every `ε > 0`, every non-principal character `χ` mod `q`,
every `N ≥ 0` and every `1 ≤ H ≤ q`, `|Σ_{N < n ≤ N + H} χ(n)| ≪_ε q^{1/9 + ε} H^{2/3}`.
[HB, Lemma 2.1, k = 3, p. 7] states this for primitive `χ` and `N ≥ 1`; the remark after it notes
that Burgess's own formulation [B] covers non-principal characters that are not necessarily
primitive. The form below also follows from [HB, Lemma 2.1] by Möbius inversion over the primes of
`q` not dividing the conductor (a factor `τ(q) ≪ q^ε`), removing complete periods, and shifting
`N` by `q`. ([B] and [G] are cited here as secondary citations taken from [HB].) -/
def BurgessBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
    ∀ N H : ℕ, 1 ≤ H → H ≤ q →
      ‖charSum χ N H‖ ≤
        C * ↑q ^ (⅑ + ε) * ↑H ^ ⅔

/-- [HB, Lemma 2.1, p. 7], the case `k = 3`, as printed: "Let `q ≥ 1` and let `χ` be a primitive
character modulo `q`. Let `N ≥ 1` and `1 ≤ H ≤ q`. Then for any `ε > 0` we have
`Σ_{N < n ≤ N + H} χ(n) ≪_{ε,k} q^{(k+1)/(4k²) + ε} H^{1 - 1/k}` (2.1) for `k = 2` or `3`.
Moreover if `q` is cube-free the estimate (2.1) holds for any `k ∈ ℕ`."
For `k = 3` the exponents are `(k + 1)/(4k²) = 1/9` and `1 - 1/k = 2/3`, and the implied constant
depends on `ε` only. Here `N` and `H` are natural numbers (a special case if the print allows real
`N`, `H`); all hypotheses of the print (`q ≥ 1`, `χ` primitive, `N ≥ 1`, `1 ≤ H ≤ q`) are kept.
The remark after the lemma reads: "Actually Burgess's formulation refers to characters which are
non-principal, but not necessarily primitive. Of course (2.1) holds trivially when `1 ≤ H ≤ q` and
`χ` is identically 1." The non-principal form with `N ≥ 0` is `BurgessBound`, derived from this
statement in `burgessBound_of_primitive`. -/
def BurgessPrimitive : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ N H : ℕ, 1 ≤ N → 1 ≤ H → H ≤ q →
      ‖charSum χ N H‖ ≤
        C * ↑q ^ (⅑ + ε) * ↑H ^ ⅔

/-- The Selberg weights `ψ_d = μ(d) log(V/d) / log V` for `d ≤ V`, and `0` otherwise
([HB, (11.6)] with `U = 1`). -/
def grahamWeight (V : ℝ) (d : ℕ) : ℝ :=
  if ↑d ≤ V then ↑(μ d) * Real.log (V / d) / Real.log V else 0

/-- Graham's estimate ([G, p. 84]; [HB, (11.13)] with `U = 1`, in the range `N ≥ V`):
`Σ_{n ≤ N} (Σ_{d ∣ n} ψ_d)² = N / log V + O(N / log² V)`. -/
def GrahamEstimate : Prop :=
  ∃ C V₀ : ℝ, ∀ V N : ℝ, V₀ ≤ V → V ≤ N →
    |∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (∑ d ∈ n.divisors, grahamWeight V d) ^ 2 - N / Real.log V| ≤
      C * N / Real.log V ^ 2

/-! ## The data of the graded near lemma -/

/-- The fixed data of the graded near lemma: a detector `f`, a Gram test `g` (the Gram test
of the paper's Definition 8.1; Heath-Brown's Lemma 12.1 corresponds to the limiting case `g = f`,
`s = s₁`, no sieve cells), a safe anchor `s₁`, a reference anchor `s`, sieve cells
`[t k, t (k+1))` for `k < m` with weights `h k`, a sieve margin `ε'`, and a finite set `Δ` of
anchor offsets. -/
structure NearData where
  f : ℝ → ℝ
  (xf Bf : ℝ)
  g : ℝ → ℝ
  (xg Bg s₁ s : ℝ)
  m : ℕ
  (t h : ℕ → ℝ)
  ε' : ℝ
  Δ : Finset ℝ

namespace NearData

variable (D : NearData)

/-- The sieve weight `H(u) = Σ_{k < m} h_k 1_{[t_k, t_{k+1})}(u)`. -/
def sieveH (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D.m, if D.t k ≤ u ∧ u < D.t (k + 1) then D.h k else 0

/-- The Cauchy–Schwarz weight `ω(u) = g(u) e^{s₁ u} + H(u)`. -/
def omega (u : ℝ) : ℝ := D.g u * Real.exp (D.s₁ * u) + D.sieveH u

/-- `I_B(s) = ∫ e^{2su} f(u)² / ω(u) du`. -/
def IB : ℝ := ∫ u in Set.Ioi (0 : ℝ), Real.exp (2 * D.s * u) * D.f u ^ 2 / D.omega u

/-- The sieve level exponent `δ_k = (t_k - 1/3)/2 - ε'` (the level is `q^{δ_k}`). -/
def level (k : ℕ) : ℝ := (D.t k - ⅓) / 2 - D.ε'

/-- Shared diagonal components of the near form. -/
scoped[GradedNear] notation "gramDiag " D:arg δ:arg =>
  (∫ u in Set.Ioi (0 : ℝ), NearData.g D u * Real.exp ((NearData.s₁ D - 2 * δ) * u))
scoped[GradedNear] notation "sieveDiag " D:arg δ:arg =>
  (∑ k ∈ Finset.range (NearData.m D),
    NearData.h D k * Real.exp (-2 * δ * NearData.t D k) *
      (NearData.t D (k + 1) ^ 2 - NearData.t D k ^ 2) / (2 * NearData.level D k))
/-- The full diagonal is the sum of its Gram and sieve parts. -/
def Dδ (δ : ℝ) : ℝ := gramDiag D δ + sieveDiag D δ

/-- `d₁ = g(0)/6`, the conductor charge of an off-diagonal Gram entry. -/
def d₁ : ℝ := D.g 0 / 6

/-- The standing hypotheses on the data. -/
structure Valid : Prop where
  f_cond : Condition1 D.f D.xf D.Bf
  g_cond1 : Condition1 D.g D.xg D.Bg
  g_cond2 : Condition2 D.g
  ε'_pos : 0 < D.ε'
  t_lt : ∀ k < D.m, D.t k < D.t (k + 1)
  t_zero : ⅓ + 2 * D.ε' < D.t 0
  h_nonneg : ∀ k < D.m, 0 ≤ D.h k
  Δ_nonneg : ∀ δ ∈ D.Δ, 0 ≤ δ
  omega_lb : ∃ c : ℝ, 0 < c ∧ ∀ u, 0 ≤ u → D.f u ≠ 0 → c ≤ D.omega u
  IB_pos : 0 < D.IB

end NearData

/-! ## Entries, responses and the safe anchor -/

/-- A finite family of entries `(χ_j, γ_j, δ_j)`: characters mod `q`, heights, and anchor
offsets; the response anchor of entry `j` is `s_j = s - δ_j`. -/
structure Entries (q : ℕ) (ι : Type*) where
  χ : ι → DirichletCharacter ℂ q
  (γ δ : ι → ℝ)

variable {q : ℕ} {ι : Type*}

/-- Complex test point at normalized horizontal offset `σ` and height `γ`. -/
scoped[GradedNear] notation "testPoint " q:arg σ:arg γ:arg =>
  (((1 - σ / Real.log q : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I)

/-- The response `R_j = -𝓛⁻¹ Σ Λ(n) Re(χ_j(n) n^{-(1 - s_j/𝓛 + iγ_j)}) f(log n / 𝓛)`. -/
def response (D : NearData) (E : Entries q ι) (j : ι) : ℝ :=
  -(primeSum (E.χ j) D.f
      (testPoint q (D.s - E.δ j) (E.γ j))).re / Real.log q

/-- The common same-character Gram transform. -/
scoped notation "pairValue " q:arg D:arg E:arg j:arg k:arg =>
  (laplace (NearData.g D)
    (↑(-(NearData.s₁ D - Entries.δ E j - Entries.δ E k)) +
      ↑((Entries.γ E j - Entries.γ E k) * Real.log q) * I)).re

/-- The pair excess `e_j = Σ_{k ≠ j, χ_k = χ_j} (Re G(-σ_{jk} + i y_{jk}) - d₁)_+`, where
`G` is the Laplace transform of `g`, `σ_{jk} = s₁ - δ_j - δ_k` and `y_{jk} = (γ_j - γ_k) log q`. -/
def pairExcess [Fintype ι] (D : NearData) (E : Entries q ι) (j : ι) : ℝ :=
  ∑ k ∈ sameCharOthers E.χ j, max 0 (pairValue q D E j k - D.d₁)

/-- The safe-anchor hypothesis at height `T'`: no non-principal `L(s, ψ)` mod `q` vanishes
at a point `ρ` with `|Im ρ| ≤ T'` and `Re ρ > 1 - s₁ / log q`. -/
def SafeAnchor (q : ℕ) [NeZero q] (s₁ T' : ℝ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ ρ : ℂ, DirichletCharacter.LFunction ψ ρ = 0 →
    |ρ.im| ≤ T' → ρ.re ≤ 1 - s₁ / Real.log q


/-!
## The zero form: responses, zero terms, multiplicities, kept bounds

* `responseAt χ f σ γ`: the response of an entry `(χ, γ, σ)`;
* `zeroTerm f q σ γ ρ`: the term of a zero `ρ` in that response;
* `zmult χ ρ`: the multiplicity of `ρ` as a zero of `L(s, χ)`;
* `keptBound D E S η j`: the lower bound for the response of entry `j` from its kept zeros.
-/

/-- The response of an entry `(χ, γ, σ)`: `-𝓛⁻¹ Re primeSum(χ, f, (1 - σ/𝓛) + iγ)`. -/
def responseAt {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (σ γ : ℝ) : ℝ :=
  -(primeSum χ f (testPoint q σ γ)).re / Real.log q

/-- The term of a zero `ρ` in the response of `(σ, γ)`:
`Re F((1 - Re ρ) 𝓛 - σ + i (γ - Im ρ) 𝓛)`. -/
def zeroTerm (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) : ℝ :=
  (laplace f (((1 - ρ.re) * Real.log q - σ : ℝ) +
    ↑((γ - ρ.im) * Real.log q) * I)).re

/-- The multiplicity of `ρ` as a zero of `L(s, χ)`, as a real number. -/
abbrev zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℝ :=
  ↑(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)


/-- The lower bound for the response of entry `j` given by its kept zeros `S_j`:
`Σ_{ρ ∈ S_j} m_ρ Re F((λ_ρ - s_j) + i(γ_j - Im ρ)𝓛) - f(0)/6 - η`. -/
def keptBound [NeZero q] (D : NearData) (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ)
    (j : ι) : ℝ :=
  ∑ ρ ∈ Sz j, zmult (E.χ j) ρ * zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ - D.f 0 / 6 - η


/-!
## Exact certificates for the leaf LPs (paper §10): the checker and its semantics

A leaf LP has columns (ordinary bins, hidden columns and reserved-second-family columns alike),
each with an objective coefficient `G`, far weight `W`, count cost `C`, hidden-count cost `NH`
and second-family indicator `E`. For every near row `k` a column has a feature `v k` and a
diagonal `D k`, and the row has a radius `d`, and fixed family terms `(n, v, D)`. All data are
integers scaled by `S = 10¹⁶`.

The constraints on real column values `x ≥ 0` and real thresholds `τ_k` are (`Feasible`):
* far: `Σ W x ≤ F`; count: `Σ C x ≤ 2S`; hidden count: `Σ NH x ≤ ng S`;
  second family: `Σ E x = n₂ S`;
* near row `k`: `0 ≤ τ_k`, `τ_k² ≤ d_k/S` and
  `Σ_j x_j (v_jk/S - τ_k)₊² / (D_jk/S) + Σ_fam n (v/S - τ_k)₊² / (D/S) ≤ 1 - τ_k² / (d_k/S)`.

The objective is `first + final + Σ G x` (scaled by `S`).

A certificate is a bisection tree over the threshold box (ticks of `10⁻⁶`). At each tree node
each row uses the first-order relaxation (order 2) or the tangent pair (order 1: cases 0 and 1),
and every resulting case is either excluded (some row with all costs `≥ 0` and a negative budget)
or carries nonnegative integer duals satisfying every column inequality; weak duality then
bounds the objective. The checker transliterates the acceptance test of
`computations/graded/graded_cert.py` in the research repository (`Leaf._row_case`, `tangent_cost`, `tangent_exact`,
`check_case`, `excludable`, `check_box`, `verify_tree` and the root box). It omits the Python
input assertions that soundness does not need (`W > 0`, `v ≥ 0`, `C ∈ {0, S}`, and `U = 0` or
`P = M = 0` when a leaf has no hidden or second-family columns), so it accepts a superset of
what `graded_cert` accepts; `checkLeaf_sound` holds for everything it accepts.
-/

namespace Cert

/-- Input scale. -/
def S : ℤ := 10 ^ 16

/-- Real units of an integer certificate feature; expands in the public interface. -/
scoped notation:max "unscale " v:arg => ((v : ℝ) / S)
/-- The positive feature remaining above a threshold. -/
scoped notation:max "rowSlack " v:arg τ:arg => max 0 (unscale v - τ)

/-- Threshold ticks per unit. -/
def TS : ℤ := 10 ^ 6
/-- Dual scale. -/
def DS : ℤ := 10 ^ 12
/-- Half a threshold tick in input units, `S / TS / 2`. -/
def HS : ℤ := 5 * 10 ^ 9

/-- A column: objective, far weight, count cost, hidden-count cost, second-family indicator,
and per-row feature and diagonal. -/
structure Col where
  (G W C NH E : ℤ)
  (v D : List ℤ)

/-- A near row: its radius `d` and its fixed family terms `(n, v, D)`. -/
structure RowHead where
  d : ℤ
  fam : List (ℤ × ℤ × ℤ)

/-- The integer data of a leaf. -/
structure Leaf where
  cols : List Col
  rows : List RowHead
  (F ng n2 first final : ℤ)

/-- Row lookup, including the checker's out-of-range default. -/
abbrev Leaf.row (L : Leaf) (k : ℕ) : RowHead := L.rows.getD k ⟨1, []⟩
/-- Column lookup at a bounded index. -/
abbrev Leaf.col (L : Leaf) (j : Fin L.cols.length) : Col := L.cols.get j

/-- The stored integer feature of a column in a near row. -/
abbrev Leaf.feature (L : Leaf) (j : Fin L.cols.length) (k : ℕ) : ℤ :=
  (L.col j).v.getD k 0
/-- The corresponding positive diagonal, with the checker's safe default. -/
abbrev Leaf.diagonal (L : Leaf) (j : Fin L.cols.length) (k : ℕ) : ℤ :=
  (L.col j).D.getD k 1

variable (L : Leaf)

/-! ## The checker -/

/-- `⌈√n⌉`. -/
def isqrtUp (n : ℕ) : ℕ := if Nat.sqrt n * Nat.sqrt n = n then Nat.sqrt n else Nat.sqrt n + 1

/-- The end (in ticks) of the root threshold box of a row of radius `d`. -/
def rootEnd (d : ℤ) : ℤ := (isqrtUp ((d * TS * TS / S).toNat + 1) : ℤ)

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : ℤ) : ℤ := -(-a / b)

/-- The tangent-case cost of a feature `v` on a box of midpoint `m2/2` and half-width `h2/2`
ticks: `((v - m)₊ ± h)² - h²`, floored at scale `S`. -/
def tangentCost (v m2 h2 : ℤ) (c : ℕ) : ℤ :=
  let x := v - m2 * HS
  if x ≤ 0 then 0 else
    let hS := h2 * HS
    (if c = 0 then x * (x + 2 * hS) else x * (x - 2 * hS)) / S

/-- The exact tangent-case family term `((v - m)₊ ± h)² - h²`. -/
def tangentExact (v m h : ℚ) (c : ℕ) : ℚ :=
  let x := max (v - m) 0
  if c = 0 then (x + h) ^ 2 - h ^ 2 else if 0 < x then (x - h) ^ 2 - h ^ 2 else 0

/-- The cost of a column in a row on the box interval `[a, b]` (ticks), for case `c`
(`2` first-order; `0`, `1` tangent). -/
def colCost (v D a b : ℤ) (c : ℕ) : ℤ :=
  if c = 2 then max (v - b * (S / TS)) 0 ^ 2 / D
  else tangentCost v (a + b) (b - a) c * S / D

/-- The budget of a row on the box interval `[a, b]` for case `c`. -/
def rowBudget (r : RowHead) (a b : ℤ) (c : ℕ) : ℤ :=
  if c = 2 then
    S - S * S * a * a / (TS * TS * r.d) -
      (r.fam.map fun t => t.1 * max (t.2.1 - b * (S / TS)) 0 ^ 2 / t.2.2).sum
  else
    let p : ℚ := (if c = 0 then ↑a else ↑b) / TS
    let hq : ℚ := ↑(b - a) / (2 * TS)
    let bq : ℚ := 1 - (p ^ 2 - hq ^ 2) / (↑r.d / S) -
      (r.fam.map fun t => (t.1 : ℚ) * tangentExact ((t.2.1 : ℚ) / S)
        (↑(a + b) / (2 * TS)) hq c / ((t.2.2 : ℚ) / S)).sum
    ⌈bq * S⌉

/-- The costs of a column in every row, for a box and a case vector. -/
def colCosts (col : Col) (box : List (ℤ × ℤ)) (cs : List ℕ) : List ℤ :=
  List.zipWith3 (fun ab vD c => colCost vD.1 vD.2 ab.1 ab.2 c) box (col.v.zip col.D) cs

/-- The budgets of every row, for a box and a case vector. -/
def budgets (box : List (ℤ × ℤ)) (cs : List ℕ) : List ℤ :=
  List.zipWith3 (fun r ab c => rowBudget r ab.1 ab.2 c) L.rows box cs

/-- Nonnegative integer duals: far `Y`, count `V`, hidden count `U`, the free dual `P - M` of the
second-family equality, and one multiplier per near row. -/
structure Duals where
  (Y V U P M : ℕ)
  Z : List ℕ

/-- The certificate of one case. -/
inductive CaseCert where
  | excluded
  | duals (du : Duals)

/-- The value certified by duals for one case (`none` if a column inequality fails). -/
def caseValue (box : List (ℤ × ℤ)) (cs : List ℕ) (du : Duals) : Option ℤ :=
  if du.Z.length = L.rows.length ∧
      L.cols.all fun col => decide (DS * col.G ≤
        ↑du.Y * col.W + ↑du.V * col.C + ↑du.U * col.NH +
          (↑du.P - du.M) * col.E +
          (List.zipWith (fun z c => (z : ℤ) * c) du.Z (colCosts col box cs)).sum) then
    some (ceilDiv (↑du.Y * L.F + ↑du.V * (2 * S) + ↑du.U * (L.ng * S) +
      (↑du.P - du.M) * (L.n2 * S) +
      (List.zipWith (fun z b => (z : ℤ) * b) du.Z (budgets L box cs)).sum) DS + L.first + L.final)
  else none

/-- A case may be excluded if some row has all column costs `≥ 0` and a negative budget. -/
def excludable (box : List (ℤ × ℤ)) (cs : List ℕ) : Bool :=
  (List.range L.rows.length).any fun k =>
    decide ((budgets L box cs).getD k 0 < 0) &&
      L.cols.all fun col => decide (0 ≤ (colCosts col box cs).getD k 0)

/-- All case vectors for the given orders: `{0, 1}` for order 1, `{2}` otherwise. -/
def caseVectors : List ℕ → List (List ℕ)
  | [] => [[]]
  | o :: os =>
    let rest := caseVectors os
    if o = 1 then rest.map (0 :: ·) ++ rest.map (1 :: ·) else rest.map (2 :: ·)

/-- The value of a tree node's box: the maximum over its cases (`-1` if all are excluded). -/
def checkBox (box : List (ℤ × ℤ)) (orders : List ℕ) (certs : List CaseCert) :
    Option ℤ :=
  let cvs := caseVectors orders
  if orders.length = L.rows.length ∧ certs.length = cvs.length ∧
      orders.all fun o => o = 1 ∨ o = 2 then
    (List.zip cvs certs).foldl (fun acc cc =>
      acc.bind fun m =>
        match cc.2 with
        | .excluded => if excludable L box cc.1 then some m else none
        | .duals du => (caseValue L box cc.1 du).map (max m)) (some (-1))
  else none

/-- A certificate tree: a bisection of dimension `k` at tick `mid`, or a node with its orders
and case certificates. -/
inductive Tree where
  | split (k : ℕ) (mid : ℤ) (left right : Tree)
  | node (orders : List ℕ) (certs : List CaseCert)

/-- Checks a tree on a box; returns the maximum certified value, each node's value `< S`. -/
def verifyTree : Tree → List (ℤ × ℤ) → Option ℤ
  | .split k mid l r, box =>
    match box[k]? with
    | some (a, b) =>
      if a < mid ∧ mid < b then
        (verifyTree l (box.set k (a, mid))).bind fun m₁ =>
          (verifyTree r (box.set k (mid, b))).map (max m₁)
      else none
    | none => none
  | .node orders certs, box =>
    (checkBox L box orders certs).bind fun v => if v < S then some v else none

/-- Well-formedness: every column has one feature and one diagonal per row, all diagonals,
radii and family diagonals are positive, and family counts are nonnegative. -/
def wellFormed : Bool :=
  L.cols.all (fun col => col.v.length = L.rows.length && col.D.length = L.rows.length &&
    col.D.all fun x => decide (0 < x)) &&
  L.rows.all fun r => decide (0 < r.d) &&
    r.fam.all fun t => decide (0 ≤ t.1) && decide (0 < t.2.2)

/-- The root box `∏_k [0, end_k]`. -/
def rootBox : List (ℤ × ℤ) := L.rows.map fun r => (0, rootEnd r.d)

/-- The checker: `some v` certifies that the leaf LP's objective is at most `v` (scaled by `S`)
at every feasible point. -/
def checkLeaf (T : Tree) : Option ℤ :=
  if wellFormed L then verifyTree L T (rootBox L) else none

/-! ## Semantics -/

/-- The left side of near row `k` at real column values `x` and threshold `τ`. -/
def rowLHS (x : Fin L.cols.length → ℝ) (k : ℕ) (τ : ℝ) : ℝ :=
   ∑ j, x j * rowSlack ((L.cols.get j).v.getD k 0) τ ^ 2 /
       unscale ((L.cols.get j).D.getD k 1) +
    (((L.rows.getD k ⟨1, []⟩).fam).map fun t =>
      (t.1 : ℝ) * rowSlack t.2.1 τ ^ 2 / unscale t.2.2 ).sum

variable (x : Fin L.cols.length → ℝ)
local notation "colSum " f:arg => (∑ j, (f (L.cols.get j) : ℝ) * x j)

/-- The constraints of the leaf LP at real column values `x` and real thresholds `τ`. -/
def Feasible (τ : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧
   colSum Col.W ≤ L.F ∧
   colSum Col.C ≤ 2 * S ∧
   colSum Col.NH ≤ L.ng * S ∧
   colSum Col.E = L.n2 * S ∧
  ∀ k < L.rows.length, 0 ≤ τ k ∧ τ k ^ 2 ≤ unscale (L.rows.getD k ⟨1, []⟩).d ∧
    rowLHS L x k (τ k) ≤ 1 - τ k ^ 2 / unscale (L.rows.getD k ⟨1, []⟩).d

/-- The objective (scaled by `S`). -/
def objective : ℝ :=
  L.first + L.final + colSum Col.G

end Cert
/-- A zero's normalized distance from the line `Re s = 1`. -/
scoped notation "zeroLambda " q:arg ρ:arg => (1 - Complex.re ρ) * Real.log q
/-- The local disc at height `γ`. -/
scoped notation "InDisc " γ:arg δ:arg ρ:arg => ‖(1 + (γ : ℂ) * Complex.I) - ρ‖ ≤ δ
/-- The diagonal numerator in the graded quadratic form. -/
scoped notation "diagNum " D:arg E:arg j:arg =>
  NearData.Dδ D (Entries.δ E j) - NearData.d₁ D + pairExcess D E j

/-- The non-principal, height and offset conditions on an entry family. -/
scoped notation "Nonprincipal " E:arg => (∀ j, Entries.χ E j ≠ 1)
scoped notation "HeightBound " E:arg T:arg => (∀ j, |Entries.γ E j| ≤ T)
scoped notation "Offsets " E:arg D:arg => (∀ j, Entries.δ E j ∈ NearData.Δ D)
/-- Nonzero sieve heights require distinct characters. -/
scoped notation "SieveDistinct " E:arg D:arg =>
  ((∃ k < NearData.m D, NearData.h D k ≠ 0) → Function.Injective (Entries.χ E))
/-- Adverse zeros not among those kept in a response. -/
scoped notation "discardedZeros " q:arg χ:arg σ:arg γ:arg δ:arg Sz:arg =>
  {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ InDisc γ δ ρ ∧ ρ ∉ Sz ∧ zeroLambda q ρ < σ}
/-- Separation of the other adverse zeros from the entry's height. -/
scoped notation "DistantZeros " q:arg χ:arg σ:arg γ:arg δ:arg Sz:arg M:arg =>
  (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → InDisc γ δ ρ → ρ ∉ Sz →
    zeroLambda q ρ < σ → M ≤ |γ - Complex.im ρ| * Real.log q)
/-- The real-valued Laplace transform on the real axis. -/
scoped notation "realLaplace " f:arg x:arg => (laplace f (((x : ℝ) : ℂ))).re
/-- The common large-modulus entry context of the near lemmas. -/
scoped macro "ForLargeNear " D:term:arg " (" q:ident ", " ι:ident ", " E:ident " => " P:term ")" : term =>
  `(∃ q₀ : ℕ, ∀ $q:ident : ℕ, [NeZero $q] → q₀ ≤ $q →
    ∀ T : ℝ, 0 ≤ T → T ≤ Real.log $q / 3 → SafeAnchor $q (NearData.s₁ $D) (2 * T + 1) →
    ∀ ($ι:ident : Type) [Fintype $ι] ($E:ident : Entries $q $ι),
      Nonprincipal $E → HeightBound $E T → Offsets $E $D → SieveDistinct $E $D → $P)

/-- The common normalized threshold conclusion, with its entry terms written under one binder. -/
scoped macro "NearThreshold " d:term:arg " (" j:ident " => " v:term ", " D:term ")" : term =>
  `(∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt $d ∧
      Finset.sum Finset.univ (fun $j => (max 0 ($v - τ)) ^ 2 / $D) ≤ 1 - τ ^ 2 / $d)
end GradedNear
