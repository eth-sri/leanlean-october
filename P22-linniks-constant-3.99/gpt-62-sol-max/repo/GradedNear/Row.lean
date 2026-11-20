module

public import GradedNear.Parabolic

/-!
# The near rows of the leaves: a concrete instance of the graded near lemma

A near row of a leaf (paper §§9.1–9.4; `computations/sieve_near/sieve_inputs.py` in the research repository,
`SieveNearTest`) fixes rational parameters: the detector `f = f_{2γ}` and the short Gram test
`g = f_{2g₁}` (the parabolic tests of `Parabolic.lean`, normalized so that `f(0) = g(0) = 1`), the
anchors `s ≥ s₁ ≥ 0`, and a Selberg-sieve weight with heights `h_k ≥ 0` on the `m` cells
`[t_k, t_{k+1})`, `t_k = t₀ + (2γ - t₀) k/m`, with level margin `ε' = 1/2000`. `Params.near` is
the corresponding `NearData`.

* `Params.valid`: the standing hypotheses `NearData.Valid` follow from checkable conditions on the
  rationals (`Params.Good`) and positive lower bounds `L_k` of `ω` on the cells;
* `Params.IB_le`: `I_B ≤ Σ_{j<n} (t₀/n) e^{(2s-s₁)b_j} f(a_j)²/g(b_j) +
  Σ_{k<m} (t_{k+1}-t_k) e^{2s t_{k+1}} f(t_k)²/L_k`, the upper Riemann sum of the builders
  (`n` short cells `[a_j, b_j)` of `[0, t₀)`, where the sieve weight vanishes);
* `Params.Dδ_eq`, `Params.Dδ_anti`: `D(δ) = 2g₁ Φ(2g₁(2δ - s₁)) + Σ_k c_k e^{-2δ t_k}` with
  `c_k = h_k (t_{k+1}² - t_k²)/(2δ_k)`, and `D` decreases in `δ ≥ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace GradedNear

namespace Row

open Parabolic

/-- The rational parameters of a near row. -/
structure Params where
  /-- The detector is `f_{2γ}`. -/
  γ : ℚ
  /-- The short Gram test is `f_{2g₁}`. -/
  g1 : ℚ
  /-- The first sieve cell starts at `t₀`. -/
  t0 : ℚ
  /-- The reference anchor. -/
  s : ℚ
  /-- The safe anchor. -/
  s1 : ℚ
  /-- The sieve heights `h_k`, one per cell. -/
  h : List ℚ

/-- The level margin `ε' = 1/2000` (`EPS_LEVEL`). -/
def epsLev : ℚ := 1 / 2000

namespace Params

variable (p : Params)

/-- The number of sieve cells. -/
def m : ℕ := p.h.length

/-- The cell ends `t_k = t₀ + (2γ - t₀) k / m`. -/
def tk (k : ℕ) : ℚ := p.t0 + (2 * p.γ - p.t0) * k / p.m

/-- The sieve height of cell `k` (`0` beyond the list). -/
def hk (k : ℕ) : ℚ := p.h.getD k 0

/-- The `NearData` of the row, with the finite set `Δ` of anchor offsets of its entries. -/
def near (Δ : Finset ℝ) : NearData where
  f := fpar (2 * (p.γ : ℝ))
  xf := 2 * (p.γ : ℝ)
  Bf := 10 / (2 * (p.γ : ℝ)) ^ 2
  g := fpar (2 * (p.g1 : ℝ))
  xg := 2 * (p.g1 : ℝ)
  Bg := 10 / (2 * (p.g1 : ℝ)) ^ 2
  s₁ := p.s1
  s := p.s
  m := p.m
  t := fun k => (p.tk k : ℝ)
  h := fun k => (p.hk k : ℝ)
  ε' := (epsLev : ℝ)
  Δ := Δ

@[simp] lemma near_f (Δ : Finset ℝ) : (p.near Δ).f = fpar (2 * (p.γ : ℝ)) := rfl
@[simp] lemma near_g (Δ : Finset ℝ) : (p.near Δ).g = fpar (2 * (p.g1 : ℝ)) := rfl
@[simp] lemma near_s (Δ : Finset ℝ) : (p.near Δ).s = p.s := rfl
@[simp] lemma near_s₁ (Δ : Finset ℝ) : (p.near Δ).s₁ = p.s1 := rfl
@[simp] lemma near_m (Δ : Finset ℝ) : (p.near Δ).m = p.m := rfl
@[simp] lemma near_t (Δ : Finset ℝ) (k : ℕ) : (p.near Δ).t k = (p.tk k : ℝ) := rfl
@[simp] lemma near_h (Δ : Finset ℝ) (k : ℕ) : (p.near Δ).h k = (p.hk k : ℝ) := rfl
@[simp] lemma near_ε' (Δ : Finset ℝ) : (p.near Δ).ε' = (epsLev : ℝ) := rfl

variable {p}

/-! ## The weight `ω` -/

/-! ## The integral `I_B` -/

/-! ## The diagonal `D(δ)` -/

/-! ## Validity -/

end Params

end Row

end GradedNear

end
