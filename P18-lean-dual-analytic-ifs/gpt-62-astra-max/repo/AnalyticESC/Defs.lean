module

public import AnalyticESC.Vocabulary

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

export Challenge (I nbhd d2 InClass InUnionClass IsAnalyticCoord ConjSelfSimilar periodic exampleMaps)

noncomputable abbrev dev (f g : ℂ → ℂ) := ⨆ x : I, ‖f x - g x‖

/-- An analytic IFS `Φ = (f_i)_{i ∈ Fin N}` in `𝔖_N`, for a fixed `ε > 0`. -/
structure IFS (N : ℕ) where
  /-- The maps of the system. -/
  f : Fin N → ℂ → ℂ
  {ε : ℝ}
  ε_pos : 0 < ε
  inClass : ∀ i, InClass ε (f i)

/-- Logarithmic derivative of the first derivative, over either scalar field. -/
noncomputable abbrev logDer {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜 → 𝕜) (x : 𝕜) := deriv (deriv f) x / deriv f x

namespace IFS

variable {N : ℕ} (Φ : IFS N)

abbrev tube := nbhd Φ.ε
abbrev box := closure Φ.tube
abbrev realMap (i : Fin N) (x : ℝ) := (Φ.f i x).re
def comp := Challenge.comp Φ.f
noncomputable abbrev supDist := Challenge.supDist Φ.f
abbrev ESC := Challenge.ESC Φ.f
abbrev SESC := Challenge.SESC Φ.f
noncomputable abbrev natProj := Challenge.natProj Φ.f
abbrev attractor := Challenge.attractor Φ.f
noncomputable abbrev cmax := Challenge.cmax Φ.ε Φ.f

/-- The distortion `f_i''/f_i'`. -/
noncomputable abbrev nonlin (i : Fin N) := logDer (Φ.f i)

/-- An address with a cutoff `l : ℕ∞` represents either its first `l` letters
or the whole address. This keeps the same shift and prefix operations for both. -/
noncomputable def dualTerm (l : ℕ∞) (w : Address N) (n : ℕ) : ℂ → ℂ :=
  if (n:ℕ∞) < l then fun z => Φ.nonlin (w n) (Φ.comp (block n w).reverse z) * deriv (Φ.comp (block n w).reverse) z else 0

noncomputable def dualProj (l : ℕ∞) (w : Address N) (z : ℂ) : ℂ := ∑' n, Φ.dualTerm l w n z
noncomputable abbrev P (w : Address N) (x : ℝ) := Φ.dualProj ⊤ w x

end IFS


end AnalyticESC
