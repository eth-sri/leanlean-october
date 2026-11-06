module

public import Mathlib

@[expose] public section

/-!
# Definitions

The vocabulary of B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation of
analytic self-conformal sets on the real line*.

Maps are given by their holomorphic extension `f : ℂ → ℂ`. Statements about `[0,1]` evaluate at
real points `(x : ℂ)`, `x ∈ I`; there `f`, `f'` and `f''` are real, and the complex derivatives
agree with the derivatives of the real restriction. Finite words are lists, read from the left:
`f_{i₁ ⋯ iₙ} = f_{i₁} ∘ ⋯ ∘ f_{iₙ}`.
-/

namespace Challenge

open Set Metric

/-- The unit interval `I = [0,1]`. -/
abbrev I : Set ℝ := Icc 0 1

variable {N : ℕ}

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (f : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℂ → ℂ := w.foldr (fun i g => f i ∘ g) id

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable def supDist (f : Fin N → ℂ → ℂ) (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖comp f i x - comp f j x‖

/-- The strong exponential separation condition (Definition 1.2). -/
def SESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable def natProj (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) : ℝ :=
  Filter.limUnder Filter.atTop fun n => (comp f (List.ofFn fun k : Fin n => w k) 0).re

/-- The attractor `Λ = π(Σ)`. -/
def attractor (f : Fin N → ℂ → ℂ) : Set ℝ := range (natProj f)

/-- The `𝒞²` distance on `[0,1]` (Section 1.1). -/
noncomputable def d2 (f g : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ i, (⨆ x : I, ‖f i x - g i x‖) +
    (⨆ x : I, ‖deriv (f i) x - deriv (g i) x‖) +
    (⨆ x : I, ‖deriv (deriv (f i)) x - deriv (deriv (g i)) x‖)

section Dimension

open MeasureTheory Filter Topology

/-- The exponential separation condition (ESC). -/
def ESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

end Dimension

end Challenge

namespace AnalyticESC

open Set Metric Filter Topology Challenge
open scoped UniformConvergence

export Challenge (I)

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := thickening δ (((↑) : ℝ → ℂ) '' I)

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (nbhd (2 * ε))
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0
  re_mem_I : ∀ x ∈ I, (f x).re ∈ I
  mapsTo : MapsTo f (closure (nbhd ε)) (nbhd ε)
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1

/-- An analytic IFS `Φ = (f_i)_{i ∈ Fin N}` in `𝔖_N`, for a fixed `ε > 0`. -/
structure IFS (N : ℕ) (ε : ℝ) where
  /-- The maps of the system. -/
  f : Fin N → ℂ → ℂ
  ε_pos : 0 < ε
  inClass : ∀ i, InClass ε (f i)

/-- A finite or infinite word over the alphabet `Fin N`, an element of `Σ_* ∪ Σ`. -/
inductive Word (N : ℕ) where
  | fin (w : List (Fin N))
  | inf (w : ℕ → Fin N)

namespace Word

variable {N : ℕ}

/-- The length `|w| ∈ ℕ ∪ {∞}`. -/
def length : Word N → ℕ∞
  | fin w => w.length
  | inf _ => ⊤

/-- The letter in position `n` (counted from `0`), if `n < |w|`. -/
def get? : Word N → ℕ → Option (Fin N)
  | fin w, n => w[n]?
  | inf w, n => some (w n)

/-- The prefix of the first `n` letters (the whole word if `|w| ≤ n`). -/
def take : Word N → ℕ → List (Fin N)
  | fin w, n => w.take n
  | inf w, n => List.ofFn fun k : Fin n => w k

/-- The word `a w` obtained by placing the finite word `a` in front of `w`. -/
def prepend (a : List (Fin N)) : Word N → Word N
  | fin w => fin (a ++ w)
  | inf w => inf fun n => if h : n < a.length then a[n] else w (n - a.length)

/-- `|i ∧ j|`: the length of the longest common prefix of `i` and `j` (`⊤` if `i = j` is
infinite). -/
noncomputable def commonPrefixLength (i j : Word N) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k), (n : ℕ∞)

end Word

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
abbrev comp (w : List (Fin N)) : ℂ → ℂ := Challenge.comp Φ.f w

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable abbrev supDist (i j : List (Fin N)) : ℝ := Challenge.supDist Φ.f i j

/-- The exponential separation condition (ESC). -/
abbrev ESC : Prop := Challenge.ESC Φ.f

/-- The strong exponential separation condition (SESC, Definition 1.2). -/
abbrev SESC : Prop := Challenge.SESC Φ.f

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable abbrev natProj (w : ℕ → Fin N) : ℝ := Challenge.natProj Φ.f w

/-- The attractor `Λ = π(Σ)`. -/
abbrev attractor : Set ℝ := Challenge.attractor Φ.f

/-- Compositions along distinct finite words differ somewhere on `[0,1]`: `f_i ≢ f_j` on `[0,1]`
for all distinct `i, j ∈ Σ_*` (the hypothesis of Lemma 4.1). -/
def NoCoincidence : Prop :=
  ∀ i j : List (Fin N), i ≠ j → ∃ x ∈ I, Φ.comp i (x : ℂ) ≠ Φ.comp j (x : ℂ)

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax : ℝ := ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (Φ.f i) z‖

/-- The constant `c_min` of (1.7): the infimum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmin : ℝ := ⨅ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (Φ.f i) z‖

/-- The distortion `f_i''/f_i'`. -/
noncomputable def nonlin (i : Fin N) (z : ℂ) : ℂ := deriv (deriv (Φ.f i)) z / deriv (Φ.f i) z

/-- The term with index `n` (from `0`) of the series (1.4) for `H_w`: with `v` the first `n`
letters of `w` and `i` the next one, `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where
`f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}` is the composition in reverse order. Zero if `|w| ≤ n`. -/
noncomputable def dualTerm (w : Word N) (n : ℕ) (z : ℂ) : ℂ :=
  match w.get? n with
  | none => 0
  | some i => Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z

/-- The dual natural projection `H_w` of (1.4), for finite and infinite words. -/
noncomputable def dualProj (w : Word N) (z : ℂ) : ℂ := ∑' n, Φ.dualTerm w n z

/-- The dual operator `(F_i h)(z) = f_i'(z) · h(f_i(z)) + (f_i''/f_i')(z)` of (2.1). -/
noncomputable def dualOp (i : Fin N) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (Φ.f i) z * h (Φ.f i z) + Φ.nonlin i z

/-- `F_w = F_{w₁} ∘ ⋯ ∘ F_{w_k}` for a finite word `w`. -/
noncomputable def dualComp (w : List (Fin N)) : (ℂ → ℂ) → ℂ → ℂ :=
  w.foldr (fun i G => Φ.dualOp i ∘ G) id

/-- The dual IFS `Φ*` satisfies the strong separation condition: `H_i` and `H_j` differ on `I`
whenever `i₁ ≠ j₁`. -/
def DualSSC : Prop :=
  ∀ i j : ℕ → Fin N, i 0 ≠ j 0 → ∃ x ∈ I, Φ.dualProj (.inf i) x ≠ Φ.dualProj (.inf j) x

/-- `conv((F_i k)(x), (F_i K)(x))` for a finite word `i` and constants `k`, `K`. -/
noncomputable def dualCylAt (k K : ℝ) (i : List (Fin N)) (x : ℝ) : Set ℝ :=
  uIcc (Φ.dualComp i (fun _ => (k : ℂ)) x).re (Φ.dualComp i (fun _ => (K : ℂ)) x).re

/-- The cylinders `F_i(k,K)` and `F_j(k,K)` are disjoint in the sense of (2.2). -/
def DualCylDisjoint (k K : ℝ) (i j : List (Fin N)) : Prop :=
  ∃ x ∈ I, Disjoint (Φ.dualCylAt k K i x) (Φ.dualCylAt k K j x)

/-- The orbit `𝒪_i(x) = (x, f_{i₁}(x), f_{i₂ i₁}(x), …, f_{i_{|i|} ⋯ i₁}(x))` of Section 4.1, as
a list of real points. -/
noncomputable def orbit (i : List (Fin N)) (x : ℝ) : List ℝ :=
  (List.range (i.length + 1)).map fun l => (Φ.comp (i.take l).reverse x).re

/-- The real map `x ↦ f_i(x)` of the system. -/
def realMap (i : Fin N) (x : ℝ) : ℝ := (Φ.f i x).re

end IFS

/-- The `𝒞²` distance on `I` between two maps (Section 1.1), with derivatives at real points. -/
noncomputable def d2Map (f g : ℂ → ℂ) : ℝ :=
  (⨆ x : I, ‖f x - g x‖) + (⨆ x : I, ‖deriv f x - deriv g x‖) +
    (⨆ x : I, ‖deriv (deriv f) x - deriv (deriv g) x‖)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` between two families of maps. -/
noncomputable abbrev d2Sys {N : ℕ} (f g : Fin N → ℂ → ℂ) : ℝ := ⨆ i, d2Map (f i) (g i)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` on `𝔖_N`. The two systems may lie in
`𝔖_N(ε)` for different `ε`. -/
noncomputable abbrev d2 {N : ℕ} {ε ε' : ℝ} (Φ : IFS N ε) (Ψ : IFS N ε') : ℝ := d2Sys Φ.f Ψ.f

/-- The space `𝔖_N` of Section 1.1: families of maps that all lie in `S^ω_ε(I)` for some
`ε > 0`, that is, in `S^ω(I) = ⋃_{ε > 0} S^ω_ε(I)`. -/
def InUnionClass {N : ℕ} (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

end AnalyticESC
