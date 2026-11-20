module

public import AnalyticESC.Statements

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

namespace AnalyticESC

open Set Metric Filter Topology
open scoped UniformConvergence

export Challenge (I nbhd InClass InUnionClass IsAnalyticCoord ConjSelfSimilar periodic)

/-- The closure of the open complex neighbourhood of `I`. -/
abbrev closedNbhd (ε : ℝ) := closure (nbhd ε)

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

/-- The letter in position `n` (counted from `0`), if `n < |w|`. -/
def get? : Word N → ℕ → Option (Fin N)
  | fin w, n => w[n]?
  | inf w, n => some (w n)

/-- The prefix and shift of a stream. -/
abbrev pref {α : Type*} (w : ℕ → α) (n : ℕ) := List.ofFn fun k : Fin n => w k

abbrev shift {α : Type*} (w : ℕ → α) (n : ℕ) := fun k => w (k + n)

/-- The prefix of the first `n` letters (the whole word if `|w| ≤ n`). -/
def take : Word N → ℕ → List (Fin N)
  | fin w, n => w.take n
  | inf w, n => pref w n

/-- Two words have equal length when letters are defined at the same positions. -/
def SameLength (v w : Word N) : Prop := ∀ n, (v.get? n).isSome = (w.get? n).isSome

end Word

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The maps of the IFS restricted to the real line. -/
def realMaps (i : Fin N) (x : ℝ) : ℝ := (Φ.f i x).re

abbrev comp := Challenge.comp Φ.f

/-- A finite composition restricted to the real line. -/
abbrev reComp (w : List (Fin N)) (x : ℝ) : ℝ := (Φ.comp w x).re

noncomputable abbrev supDist := Challenge.supDist Φ.f

abbrev ESC := Challenge.ESC Φ.f

abbrev SESC := Challenge.SESC Φ.f

noncomputable abbrev natProj := Challenge.natProj Φ.f

abbrev attractor := Challenge.attractor Φ.f

noncomputable abbrev cmax := Challenge.cmax ε Φ.f

/-- The constant `c_min` of (1.7): the infimum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmin : ℝ := ⨅ p : Fin N × closedNbhd ε, ‖deriv (Φ.f p.1) p.2‖

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

/-- Different first-letter pieces of the dual attractor are disjoint. We express this
using the parametrization by infinite words: projections from different pieces differ
at some real point. -/
def DualSSC : Prop :=
  ∀ i j : ℕ → Fin N, i 0 ≠ j 0 → ∃ x ∈ I, Φ.dualProj (.inf i) x ≠ Φ.dualProj (.inf j) x

end IFS

/-- Uniform distance between the order-`j` derivatives on `[0,1]`. -/
noncomputable def jetDist (f g : ℂ → ℂ) (j : ℕ) : ℝ :=
  ⨆ x : I, ‖iteratedDeriv j f (x : ℝ) - iteratedDeriv j g (x : ℝ)‖

/-- The `𝒞²` distance on `I` is the sum of the first three jet distances. -/
noncomputable def d2Map (f g : ℂ → ℂ) : ℝ := ∑ j : Fin 3, jetDist f g j

noncomputable abbrev d2Sys {N : ℕ} := Challenge.d2 (N := N)

theorem d2Sys_eq {N : ℕ} (f g : Fin N → ℂ → ℂ) :
    d2Sys f g = ⨆ i, d2Map (f i) (g i) := by
  simp [Challenge.d2, d2Map, jetDist, iteratedDeriv_succ, Fin.sum_univ_three]

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` on `𝔖_N`. The two systems may lie in
`𝔖_N(ε)` for different `ε`. -/
noncomputable def d2 {N : ℕ} {ε ε' : ℝ} (Φ : IFS N ε) (Ψ : IFS N ε') : ℝ :=
  d2Sys Φ.f Ψ.f

end AnalyticESC
