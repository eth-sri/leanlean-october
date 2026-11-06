module

public import Mathlib
set_option hygiene false
local notation "𝖂" => f i

@[expose] public section

/-!
# Definitions

The vocabulary of B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation of
analytic self-conformal sets on the real line*.

Maps are given by their holomorphic extension `f : ℂ → ℂ`. Statements about `[0,1]` evaluate at
real points `x`, `x ∈ I`; there `f`, `f'` and `f''` are real, and the complex derivatives
agree with the derivatives of the real restriction. Finite words are lists, read from the left:
`f_{i₁ ⋯ iₙ} = f_{i₁} ∘ ⋯ ∘ f_{iₙ}`.
-/

namespace AnalyticESC


open Set Metric Filter


notation:max "𝔇" f:max => deriv (deriv f)

/-- The unit interval `I = [0,1]`. -/
abbrev I : Set ℝ := Icc 0 1

-- `Ɐ P` is `∀ x ∈ I, P`.
notation "Ɐ " b => ∀ x ∈ AnalyticESC.I, b

theorem zero_mem_I : 0 ∈ I := by grind

theorem one_mem_I : 1 ∈ I := by grind

instance : Nonempty I := ⟨⟨0, zero_mem_I⟩⟩

notation "Iℂ" => ((↑) : ℝ → ℂ) '' I

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := thickening δ Iℂ

notation:max "𝔹" δ:max => closure (nbhd δ)
notation:max "𝔑" δ:max => nbhd (2 * δ)

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (𝔑 ε)
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ 𝔑 ε → (f x).im = 0
  re_mem_I : Ɐ (f x).re ∈ I
  mapsTo : MapsTo f (𝔹 ε) (nbhd ε)
  deriv_ne_zero : ∀ z ∈ 𝔹 ε, deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ 𝔹 ε, ‖deriv f z‖ < 1

/-- An analytic IFS `Φ = (f_i)_{i ∈ Fin N}` in `𝔖_N`, for a fixed `ε > 0`. -/
structure IFS (N : ℕ) (ε : ℝ) where
  /-- The maps of the system. -/
  f : Fin N → ℂ → ℂ
  ε_pos : 0 < ε
  inClass : ∀ i, InClass ε 𝖂

notation:max "𝔚" N:max => List (Fin N)
notation:max "𝔖" N:max => ℕ → Fin N
notation:max "𝔡" Φ:max i:max => deriv (IFS.f Φ i)

/-- A finite or infinite word over the alphabet `Fin N`, an element of `Σ_* ∪ Σ`. -/
inductive Word (N : ℕ) where
  | fin (w : 𝔚 N)
  | inf (w : 𝔖 N)

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
def take : Word N → ℕ → 𝔚 N
  | fin w, n => w.take n
  | inf w, n => List.ofFn fun k : Fin n => w k

-- `𝔱` is `(w.take n).reverse`.
notation "𝔱" => (w.take n).reverse

/-- The word `a w` obtained by placing the finite word `a` in front of `w`. -/
def prepend (a : 𝔚 N) : Word N → Word N
  | fin w => fin (a ++ w)
  | inf w => inf fun n => if h : n < a.length then a[n] else w (n - a.length)

/-- `|i ∧ j|`: the length of the longest common prefix of `i` and `j` (`⊤` if `i = j` is
infinite). -/
noncomputable def commonPrefixLength (i j : Word N) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k), (n : ℕ∞)

end Word

namespace IFS

variable (Φ : IFS N ε) (i : Fin N) (w : Word N) (k K : ℝ)

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (w : 𝔚 N) : ℂ → ℂ := w.foldr (fun i g => Φ.f i ∘ g) id

notation:max "𝔡ᶜ" Φ:max w:max => deriv (IFS.comp Φ w)

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable def supDist (i j : 𝔚 N) : ℝ :=
  ⨆ x : I, ‖Φ.comp i x - Φ.comp j x‖

/-- The exponential separation condition (ESC): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n`, for infinitely many
`n`. -/
def ESC : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ Φ.supDist (List.ofFn i) (List.ofFn j)

/-- The strong exponential separation condition (SESC, Definition 1.2). -/
def SESC : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ Φ.supDist (List.ofFn i) (List.ofFn j)

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable def natProj (w : 𝔖 N) : ℝ :=
  limUnder atTop fun n => (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re

/-- The attractor `Λ = π(Σ)`. -/
def attractor : Set ℝ := range Φ.natProj

/-- Compositions along distinct finite words differ somewhere on `[0,1]`: `f_i ≢ f_j` on `[0,1]`
for all distinct `i, j ∈ Σ_*` (the hypothesis of Lemma 4.1). -/
def NoCoincidence : Prop :=
  ∀ i j, i ≠ j → ∃ x ∈ I, Φ.comp i x ≠ Φ.comp j x

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax : ℝ := ⨆ (i : Fin N) (z : 𝔹 ε), ‖𝔡 Φ i z‖

/-- The constant `c_min` of (1.7): the infimum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmin : ℝ := ⨅ (i : Fin N) (z : 𝔹 ε), ‖𝔡 Φ i z‖

/-- The distortion `f_i''/f_i'`. -/
noncomputable def nonlin (z : ℂ) : ℂ := 𝔇 (Φ.f i) z / 𝔡 Φ i z

/-- The term with index `n` (from `0`) of the series (1.4) for `H_w`: with `v` the first `n`
letters of `w` and `i` the next one, `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where
`f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}` is the composition in reverse order. Zero if `|w| ≤ n`. -/
noncomputable def dualTerm (n : ℕ) (z : ℂ) : ℂ :=
  match w.get? n with
  | none => 0
  | some i => Φ.nonlin i (Φ.comp 𝔱 z) * 𝔡ᶜ Φ 𝔱 z

/-- The dual natural projection `H_w` of (1.4), for finite and infinite words. -/
noncomputable def dualProj (z : ℂ) : ℂ := ∑' n, Φ.dualTerm w n z

/-- The dual operator `(F_i h)(z) = f_i'(z) · h(f_i(z)) + (f_i''/f_i')(z)` of (2.1). -/
noncomputable def dualOp (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  𝔡 Φ i z * h (Φ.f i z) + Φ.nonlin i z

/-- `F_w = F_{w₁} ∘ ⋯ ∘ F_{w_k}` for a finite word `w`. -/
noncomputable def dualComp (w : 𝔚 N) : (ℂ → ℂ) → ℂ → ℂ :=
  w.foldr (fun i G => Φ.dualOp i ∘ G) id

/-- The dual IFS `Φ*` satisfies the strong separation condition, in its coding form
(Lemmas 2.5 and 2.6): `H_i ≠ H_j` on `I` whenever `i₁ ≠ j₁`. -/
def DualSSC : Prop :=
  ∀ i j, i 0 ≠ j 0 → ∃ x ∈ I, Φ.dualProj (.inf i) x ≠ Φ.dualProj (.inf j) x

/-- `conv((F_i k)(x), (F_i K)(x))` for a finite word `i` and constants `k`, `K`. -/
noncomputable def dualCylAt (i : 𝔚 N) (x : ℝ) : Set ℝ :=
  uIcc (Φ.dualComp i (fun _ => k) x).re (Φ.dualComp i (fun _ => K) x).re

/-- The cylinders `F_i(k,K)` and `F_j(k,K)` are disjoint in the sense of (2.2). -/
def DualCylDisjoint (i j : 𝔚 N) : Prop :=
  ∃ x ∈ I, Disjoint (Φ.dualCylAt k K i x) (Φ.dualCylAt k K j x)

end IFS

/-- The `𝒞²` distance on `I` between two maps (Section 1.1), with derivatives at real points. -/
noncomputable def d2Map (f g : ℂ → ℂ) : ℝ :=
  (⨆ x : I, ‖f x - g x‖) +
    (⨆ x : I, ‖deriv f x - deriv g x‖) +
    (⨆ x : I, ‖𝔇 f x - 𝔇 g x‖)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` between two families of maps. -/
noncomputable def d2Sys (f g : Fin N → ℂ → ℂ) : ℝ := ⨆ i, d2Map 𝖂 (g i)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` on `𝔖_N`. The two systems may lie in
`𝔖_N(ε)` for different `ε`. -/
noncomputable def d2 (Φ : IFS N ε) (Ψ : IFS N ε') : ℝ :=
  ⨆ i, d2Map (Φ.f i) (Ψ.f i)

/-- The space `𝔖_N` of Section 1.1: families of maps that all lie in `S^ω_ε(I)` for some
`ε > 0`, that is, in `S^ω(I) = ⋃_{ε > 0} S^ω_ε(I)`. -/
def InUnionClass (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε 𝖂

end AnalyticESC
