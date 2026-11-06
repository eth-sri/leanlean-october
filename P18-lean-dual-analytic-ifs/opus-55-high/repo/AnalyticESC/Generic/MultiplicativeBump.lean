module

public import AnalyticESC.Generic.Class
public import AnalyticESC.Analysis

public section

set_option hygiene false
local notation "𝔛" => 2 * B₂ + 9
local notation "𝔙" => f1 + f0 * h1
local notation "𝔘" => ht0 k
local notation "𝔔" => Y.erase y
local notation "𝔓" => hU.mem_nhds hz
local notation "𝔒" => 1 / ρ / 2
local notation "𝔐" => hY y hy
local notation "𝔏" => 20 * (δ / m)
local notation "𝔈" => Finset.mem_erase.2 ⟨Ne.symm hil, hl⟩
local notation "𝔷" => hasDerivAt_P 2 Z z
local notation "𝔶" => hY k hk
local notation "𝔵" => pow_pos hρ 3
local notation "𝔬" => hasDerivAt_A Y a η z
local notation "𝔫" => z - k
local notation "𝔩" => -(1 / ρ)
local notation "𝔦" => Complex.exp h - 1
local notation "𝕮" => Y.erase i
local notation "𝕭" => 2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2
local notation "𝕬" => hW i hi
local notation "𝖟" => z - i
local notation "𝖞" => f2 + 2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2
local notation "𝖝" => Y.erase k
local notation "𝖜" => -t
local notation "𝖛" => P2 0 Y x - 2 * ∑ i ∈ Y, P 0 𝕮 x

local notation "𝖚" => Y.card * ν

local notation "𝖙" => -𝔒

local notation "𝖘" => erase_le hW i

local notation "𝖗" => W.erase i

local notation "𝖖" => ∑ k ∈ Y, a k

local notation "𝔲" => -(t / 2)

local notation "𝔨" => norm_nonneg _

local notation "𝔧" => ha k hk

local notation "𝔤" => m + 1

local notation "𝔣" => ρ ^ 3

local notation "𝔟" => m + 2

/-!
# Proposition 4.2

The proof of Proposition 4.2 of the paper: a perturbation `g` of a map `f ∈ S^ω(I)` with
`f([0,1]) ⊆ (0,1)` that is small in `𝒞¹` on `[0,1]`, agrees with `f` to first order on a finite
set `𝒴 ∪ 𝒵` and to second order on `𝒵`, and changes `f''/f'` by at least `δ` at the points of
`𝒴`, at a cost of `C δ` in the second derivative.

## Construction

As in (4.2), `g = f e^{φ ψ A}` with
`φ(z) = ∏_{y ∈ 𝒴} (z - y)²`, `ψ(z) = ∏_{w ∈ 𝒵} (z - w)⁴` and
`A(z) = ∑_{y ∈ 𝒴} a_y e^{-(z - y)²/η}`. The same formulas define `g` on `ℂ`; it is holomorphic
wherever `f` is, and real on `ℝ`. Write `h = φ ψ A`. Then `g' = (f' + f h') e^h`,
`g'' = (f'' + 2 f' h' + f h'² + f h'') e^h`, `h' = φ' ψ A + φ ψ' A + φ ψ A'` and
`h'' = φ'' ψ A + φ ψ'' A + φ ψ A'' + 2 φ' ψ' A + 2 φ' ψ A' + 2 φ ψ' A'`, with the derivatives of
`φ`, `ψ` and `A` given by the formulas of the paper (`P1`, `P2`, `A1`, `A2`). Since `φ` vanishes
to second order on `𝒴` and `ψ` to fourth order on `𝒵`, `g = f` and `g' = f'` on `𝒴 ∪ 𝒵`,
`g'' = f''` on `𝒵`, and `g''(y) = f''(y) + 2 f(y) ∏_{y' ≠ y} (y - y')² ψ(y) A(y)` for `y ∈ 𝒴`.
The amplitudes `a_y` of (4.4) give the lower bound in (iii), since `A(y) ≥ a_y`.

## Estimates

The norms are bounded at the points of `[0,1]` term by term, as in the paper, with the trivial
bounds on `φ`, `ψ` and their derivatives and the bound (4.3) (`gaussian_bound`). The norms
`‖φ ψ A‖`, `‖φ' ψ A‖`, `‖φ ψ' A‖`, `‖φ ψ'' A‖`, `‖φ' ψ' A‖` are handled by `(C1)` and the norms
`‖φ ψ A'‖`, `‖φ ψ' A'‖` by `(C2)`. In the three remaining norms the paper's bound on `φ''`,
`(C3)`, `(C4)` and `(C2)` split off a sum `∑_y a_y ψ(x) ∏_{y' ≠ y} (x - y')² F((x - y)²/η)`: for
`‖φ'' ψ A‖` it is the paper's `I(x)` with `F(t) = 2 e^{-t}`, for `‖φ ψ A''‖` it is the whole term
with `F(t) = |4t² - 2t| e^{-t}`, and for `‖φ' ψ A'‖` it is the diagonal part with
`F(t) = 4t e^{-t}`. Such a sum is split as in the paper: far from `𝒴` (at distance at least
`η^{1/3}` from every point) `F` is exponentially small by (4.6) and its analogue, and near a
point `y` of `𝒴`, which by (4.5) is far from the others, the choice (4.4) of `a_y` bounds the
summand by `F_max δ |f'(y)|/|f(y)|`. The paper's "Hence `g ∈ S^ω([0,1])`" is `exists_inClass`.

## Choices and details

* All widths are equal, `η_y = ρ³`, and `(C1)`-`(C4)`, (4.5), (4.6) and the comparison near `𝒴`
  are conditions on `ρ`, which is taken small last. The conditions from (4.3) are imposed with
  `c = a_y` and a common right-hand side `ν`, which absorbs the fixed factors.
* An empty `𝒵` is padded by a point outside `𝒴`, a case the paper does not treat. Thus `Q ≥ 1`,
  and the factors `16Q² + 12Q` and `8Q` in `(C1)` and `(C2)` apply without changing them.
* The paper writes out the near/far split for `‖φ'' ψ A‖` and leaves `‖φ ψ A''‖` and
  `‖φ' ψ A'‖` to the reader. These two norms are not small: near `y` they are of order
  `a_y ψ(y) ∏_{y' ≠ y} (y - y')² = δ |f'(y)|/(2 |f(y)|)`, so they contribute to `C δ`. Their
  profiles `|4t² - 2t| e^{-t}` and
  `4t e^{-t}` need the analogue of (4.6) with `e^{-η^{-1/3}/2}` in place of `e^{-η^{-1/3}}` far
  from `𝒴`, and the off-diagonal part of `φ' ψ A'` needs (4.3) with `p = 3`, `q = -1` as in
  `(C2)`, with `c = 4 M a_y`.
* The paper bounds the ratio of `ψ(x) ∏_{y' ≠ y} (x - y')²` to its value at `y` by explicit
  products and makes it at most `2` for small `η`; we use continuity at `y`.
* The three norms contribute `2 δ/m`, `10 δ/m` and `2 · 4 δ/m` to `|h''|` on `[0,1]`, where
  `m ≤ f ≤ 1 - m` (`MultiplicativeBump.exists_margin`). With `|f| ≤ 1` and `|e^h| ≤ 2` this gives
  `C = 40/m`, which depends on `f` only.
-/

namespace AnalyticESC

variable {B c k l t w x y ε ν ρ : ℝ} {W Y : Finset ℝ} {a v : ℝ → ℝ} {f : ℂ → ℂ} {u z : ℂ}

open Set Filter Topology

namespace MultiplicativeBump

/-- A margin `m > 0` with `m ≤ f ≤ 1 - m` and `m ≤ |f'| ≤ 1 - m` on `I`. -/
theorem exists_margin (hε : 0 < ε) (hf : InClass ε f)
    (hI : Ɐ (f x).re ∈ Ioo 0 1) :
    ∃ m > 0, Ɐ
      m ≤ (f x).re ∧ (f x).re ≤ 1 - m ∧ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 - m := by
  have hf0 : ContinuousOn (fun x : ℝ => (f x).re) I :=
    Complex.continuous_re.comp_continuousOn
      (hf.differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun _ => ofReal_mem_nbhd (by positivity)))
  have hf1 : ContinuousOn (fun x : ℝ => ‖deriv f x‖) I :=
    ((hf.differentiableOn.deriv isOpen_nbhd).continuousOn.comp
      Complex.continuous_ofReal.continuousOn (fun _ => ofReal_mem_nbhd (by positivity))).norm
  set h : ℝ → ℝ := fun x =>
    min (min (f x).re (1 - (f x).re)) (min ‖deriv f x‖ (1 - ‖deriv f x‖)) with hh
  have hcont : ContinuousOn h I := by fun_prop
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩ hcont
  have hpos : Ɐ 0 < h x := by
    intro x hx
    have hcl := ofReal_mem_closure hε hx
    have h1 := hI x hx
    have h2 := norm_pos_iff.2 (hf.deriv_ne_zero x hcl)
    have h3 := hf.norm_deriv_lt_one x hcl
    simp_all
  refine ⟨h x₀, hpos x₀ hx₀, fun x hx => ?_⟩
  have h1 : h x₀ ≤ h x := by tauto
  grind

/-! ## The polynomial factors `φ` and `ψ` -/

/-- The product `P_{m,W}(z) = ∏_{w ∈ W} (z - w)^{m+2}`; `φ = P_{0,𝒴}` and `ψ = P_{2,𝒵}`. -/
noncomputable def P (m : ℕ) (W : Finset ℝ) (z : ℂ) : ℂ := ∏ w ∈ W, (z - w) ^ 𝔟

/-- The derivative `P'_{m,W}(z) = ∑_{i ∈ W} (m+2) (z - i)^{m+1} P_{m,W∖{i}}(z)`. -/
noncomputable def P1 (m : ℕ) (W : Finset ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ W, ((m + 2 : ℕ) : ℂ) * 𝖟 ^ 𝔤 * P m 𝖗 z

/-- The second derivative `P''_{m,W}(z) = ∑_{i ∈ W} ((m+2)(m+1) (z - i)^m P_{m,W∖{i}}(z) +
(m+2) (z - i)^{m+1} P'_{m,W∖{i}}(z))`. -/
noncomputable def P2 (m : ℕ) (W : Finset ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ W, (((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * 𝖟 ^ m * P m 𝖗 z +
    ((m + 2 : ℕ) : ℂ) * 𝖟 ^ 𝔤 * P1 m 𝖗 z)

theorem hasDerivAt_P m W z : HasDerivAt (P m W) (P1 m W z) z := by
  refine (HasDerivAt.fun_finsetProd (u := W) (f := fun w z => (z - (w : ℂ)) ^ 𝔟) fun w _ =>
    ((hasDerivAt_id' z).sub_const (w : ℂ)).fun_pow 𝔟).congr_deriv
    (Finset.sum_congr rfl fun i _ => ?_)
  simp [P]; ring

theorem hasDerivAt_P1 m W z : HasDerivAt (P1 m W) (P2 m W z) z := by
  refine (HasDerivAt.fun_sum (u := W) fun i _ => ((((hasDerivAt_id' z).sub_const (i : ℂ)).fun_pow
    𝔤).const_mul _).mul (hasDerivAt_P m 𝖗 z)).congr_deriv
    (Finset.sum_congr rfl fun i _ => ?_)
  grind

theorem differentiable_P m W : Differentiable ℂ (P m W) :=
  fun z => (hasDerivAt_P m W z).differentiableAt

theorem P_ne_zero m (hy : y ∉ W) : P m W y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (sub_ne_zero.2 fun h =>
    hy (by simp_all))

theorem P_of_mem m (hw : w ∈ W) : P m W w = 0 :=
  Finset.prod_eq_zero hw (by simp)

theorem P1_of_mem m (hw : w ∈ W) : P1 m W w = 0 :=
  Finset.sum_eq_zero fun i hi => by
    by_cases hiw : i = w
    · grind
    · rw [P_of_mem m (Finset.mem_erase.2 ⟨Ne.symm hiw, hw⟩), mul_zero]

theorem P2_of_mem m (hw : w ∈ W) :
    P2 m W w = ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * 0 ^ m * P m (W.erase w) w := by
  rw [P2, Finset.sum_eq_single w (fun i _ hiw => ?_) (absurd hw)]
  · simp
  · have hw' := Finset.mem_erase.2 ⟨Ne.symm hiw, hw⟩
    simp [P_of_mem m hw', P1_of_mem m hw']

local notation "ℌ" => H Y Z a η
local notation "𝔍" => H1 Y Z a η
local notation "𝔎" => H2 Y Z a η
local notation "𝔊" => G f Y Z a η
local notation "𝔄" => A Y a η
local notation "𝔅" => A1 Y a η
local notation "𝔴" => ∀ w ∈ W, ‖z - w‖ ≤ 1
local notation "𝔪" => ((m : ℝ) + 2)
section Bounds

variable {m : ℕ} {W : Finset ℝ} {z : ℂ}

theorem P_eq_mul (hl : l ∈ W) z :
    P m W z = (z - l) ^ 𝔟 * P m (W.erase l) z :=
  (Finset.mul_prod_erase W (fun w => (z - w) ^ 𝔟) hl).symm

variable (hW : 𝔴)
include hW

theorem norm_P_le_one : ‖P m W z‖ ≤ 1 := by
  simpa [P] using Finset.prod_le_one₀ (fun _ _ => by positivity) fun w hw => pow_le_one₀ 𝔨 (hW w hw)

theorem erase_le i : ∀ w ∈ W.erase i, ‖z - w‖ ≤ 1 := by simp_all

theorem norm_P_le (hl : l ∈ W) :
    ‖P m W z‖ ≤ ‖z - l‖ ^ 𝔟 := by
  rw [P_eq_mul hl, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (norm_P_le_one (erase_le hW l))

theorem norm_P1_le : ‖P1 m W z‖ ≤ 𝔟 * W.card := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 𝔪 fun i hi => ?_).trans_eq (by grind))
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  push_cast
  have := norm_P_le_one (m := m) 𝖘
  have := pow_le_one₀ (n := m + 1) 𝔨 𝕬
  calc _ ≤ 𝔪 * 1 * 1 := by gcongr
    _ = _ := by ring

theorem norm_P1_le_of_mem (hl : l ∈ W) :
    ‖P1 m W z‖ ≤ 𝔟 * W.card * ‖z - l‖ ^ 𝔤 := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (𝔪 * ‖z - l‖ ^ 𝔤) fun i hi => ?_).trans_eq (by grind))
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  push_cast
  by_cases hil : i = l
  · subst hil
    have := norm_P_le_one (m := m) 𝖘
    calc _ ≤ 𝔪 * ‖z - i‖ ^ 𝔤 * 1 := by gcongr
      _ = _ := by ring
  · have := pow_le_one₀ (n := m + 1) 𝔨 𝕬
    have := (norm_P_le (m := m) 𝖘 𝔈).trans
      (pow_le_pow_of_le_one 𝔨 (hW l hl) (Nat.le_succ _))
    bound

theorem norm_P2_le :
    ‖P2 m W z‖ ≤ 𝔟 * 𝔤 * W.card + 𝔟 ^ 2 * W.card ^ 2 := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (𝔪 * 𝔤 + 𝔟 ^ 2 * W.card) fun i hi => ?_).trans_eq (by grind))
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  push_cast
  have := pow_le_one₀ (n := m) 𝔨 𝕬
  have := pow_le_one₀ (n := m + 1) 𝔨 𝕬
  have := norm_P_le_one (m := m) 𝖘
  have : ‖P1 m 𝖗 z‖ ≤ 𝔟 * W.card := (norm_P1_le 𝖘).trans (by gcongr; apply Finset.erase_subset)
  calc _ ≤ 𝔪 * 𝔤 * 1 * 1 + 𝔪 * 1 * (𝔟 * W.card) := by gcongr
    _ = _ := by ring

theorem norm_P2_sub_le (hl : l ∈ W) :
    ‖P2 m W z - ∑ i ∈ W, ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * 𝖟 ^ m * P m 𝖗 z‖
      ≤ 𝔟 ^ 2 * W.card ^ 2 * ‖z - l‖ ^ 𝔤 := by
  rw [P2, ← Finset.sum_sub_distrib]
  simp only [add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (𝔪 ^ 2 * W.card * ‖z - l‖ ^ 𝔤) fun i hi => ?_).trans_eq (by grind))
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  push_cast
  by_cases hil : i = l
  · subst hil
    have : ‖P1 m 𝖗 z‖ ≤ 𝔟 * W.card := (norm_P1_le 𝖘).trans (by gcongr; apply Finset.erase_subset)
    calc _ ≤ 𝔪 * ‖z - i‖ ^ 𝔤 * (𝔟 * W.card) := by gcongr
      _ = _ := by ring
  · have := pow_le_one₀ (n := m + 1) 𝔨 𝕬
    have : ‖P1 m 𝖗 z‖ ≤ 𝔟 * W.card * ‖z - l‖ ^ 𝔤 := (norm_P1_le_of_mem 𝖘 𝔈).trans (by gcongr; apply Finset.erase_subset)
    calc _ ≤ 𝔪 * 1 * (𝔟 * W.card * ‖z - l‖ ^ 𝔤) := by gcongr
      _ = _ := by ring

end Bounds

/-! ## The Gaussian sum `A` -/

local notation:max "𝔯" x:max => Real.exp (-(x - k) ^ 2 / η)
local notation:max "𝔠" x:max => Complex.exp (-(x - k) ^ 2 / η)

section
variable (f : ℂ → ℂ) (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ)

/-- `A(z) = ∑_{y ∈ 𝒴} a_y e^{-(z - y)²/η}`. -/
noncomputable def A : ℂ :=
  ∑ k ∈ Y, (a k : ℂ) * 𝔠 z

/-- `A'(z) = ∑_{y ∈ 𝒴} a_y (-2 (z - y)/η) e^{-(z - y)²/η}`. -/
noncomputable def A1 : ℂ :=
  ∑ k ∈ Y, (a k : ℂ) * (-2 * 𝔫 / η) * 𝔠 z

/-- `A''(z) = ∑_{y ∈ 𝒴} a_y · 2 (2 (z - y)²/η² - 1/η) e^{-(z - y)²/η}`. -/
noncomputable def A2 : ℂ :=
  ∑ k ∈ Y, (a k : ℂ) * (2 * (2 * 𝔫 ^ 2 / η ^ 2 - 1 / η)) * 𝔠 z

/-- The derivative of the Gaussian `e^{-(z - y)²/η}`. -/
theorem hasDerivAt_gaussian k η z :
    HasDerivAt (fun z => 𝔠 z)
      (-2 * 𝔫 / η * 𝔠 z) z := by
  refine (((((hasDerivAt_id' z).sub_const k).fun_pow 2).neg.div_const (η : ℂ)).cexp).congr_deriv ?_
  norm_num
  ring

/-- `A'` is the derivative of `A`. -/
theorem hasDerivAt_A :
    HasDerivAt 𝔄 (𝔅 z) z := by
  refine (HasDerivAt.fun_sum (A := fun k z => (a k : ℂ) * 𝔠 z) fun k _ => (hasDerivAt_gaussian k η z).const_mul (a k : ℂ)).congr_deriv (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- `A''` is the derivative of `A'`. -/
theorem hasDerivAt_A1 :
    HasDerivAt 𝔅 (A2 Y a η z) z := by
  have h := HasDerivAt.fun_sum (u := Y)
    (A := fun k z => (a k : ℂ) * (-2 * 𝔫 / η) * 𝔠 z)
    fun k _ =>
      ((((hasDerivAt_id' z).sub_const (k : ℂ)).const_mul (-2 : ℂ)).div_const (η : ℂ)
        |>.const_mul (a k : ℂ)).mul (hasDerivAt_gaussian k η z)
  refine h.congr_deriv (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-! ## The exponent `h = φ ψ A` and its derivatives -/

/-- The exponent `h = φ ψ A` with `φ = P_{0,𝒴}` and `ψ = P_{2,𝒵}`. -/
noncomputable def H : ℂ :=
  P 0 Y z * P 2 Z z * 𝔄 z

/-- `h' = φ' ψ A + φ ψ' A + φ ψ A'`. -/
noncomputable def H1 : ℂ :=
  P1 0 Y z * P 2 Z z * 𝔄 z + P 0 Y z * P1 2 Z z * 𝔄 z +
    P 0 Y z * P 2 Z z * 𝔅 z

/-- `h'' = φ'' ψ A + φ ψ'' A + φ ψ A'' + 2 φ' ψ' A + 2 φ' ψ A' + 2 φ ψ' A'`. -/
noncomputable def H2 : ℂ :=
  P2 0 Y z * P 2 Z z * 𝔄 z + P 0 Y z * P2 2 Z z * 𝔄 z +
    P 0 Y z * P 2 Z z * A2 Y a η z + 2 * (P1 0 Y z * P1 2 Z z * 𝔄 z) +
    2 * (P1 0 Y z * P 2 Z z * 𝔅 z) + 2 * (P 0 Y z * P1 2 Z z * 𝔅 z)

/-- `h'` is the derivative of `h`. -/
theorem hasDerivAt_H :
    HasDerivAt ℌ (𝔍 z) z := by
  refine (((hasDerivAt_P 0 Y z).fun_mul 𝔷).fun_mul 𝔬).congr_deriv ?_
  simp [H1]
  ring

/-- `h''` is the derivative of `h'`. -/
theorem hasDerivAt_H1 :
    HasDerivAt 𝔍 (𝔎 z) z := by
  refine (((((hasDerivAt_P1 0 Y z).fun_mul 𝔷).fun_mul 𝔬).fun_add (((hasDerivAt_P 0 Y z).fun_mul (hasDerivAt_P1 2 Z z)).fun_mul 𝔬)).fun_add (((hasDerivAt_P 0 Y z).fun_mul 𝔷).fun_mul (hasDerivAt_A1 Y a η z))).congr_deriv ?_
  simp [H2]
  ring

/-- `h` is entire. -/
theorem differentiable_H : Differentiable ℂ ℌ :=
  fun z => (hasDerivAt_H Y Z a η z).differentiableAt

/-! ## Values at real points -/

/-- `P_{m,W}` is real at real points. -/
theorem P_ofReal m W (x : ℝ) :
    P m W x = ((∏ w ∈ W, (x - w) ^ 𝔟 : ℝ) : ℂ) := by aesop

/-- `A` is real at real points. -/
theorem A_ofReal (x : ℝ) :
    𝔄 x = ((∑ k ∈ Y, a k * 𝔯 x : ℝ) : ℂ) := by aesop

/-- `h` is real at real points. -/
theorem im_H_ofReal (x : ℝ) : (ℌ x).im = 0 := by
  rw [H, P_ofReal, P_ofReal, A_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_im]

/-- `|x - w|` for real `x` and `w`. -/
theorem norm_ofReal_sub (x w : ℝ) : ‖(x : ℂ) - w‖ = |x - w| := by norm_cast

/-- `|e^{-(x - y)²/η}| = e^{-(x - y)²/η}` at real points. -/
theorem norm_gaussian (x k η : ℝ) :
    ‖𝔠 x‖ = 𝔯 x := by
  rw [show -(x - k) ^ 2 / η = ((-(x - k) ^ 2 / η : ℝ) : ℂ) by simp_all,
    Complex.norm_exp_ofReal]

/-! ## The map `g = f e^{φ ψ A}` -/

/-- The perturbed map `g = f e^{φ ψ A}` of (4.2). -/
noncomputable def G : ℂ :=
  f z * Complex.exp (ℌ z)

end

section Map

variable {f : ℂ → ℂ} {Y Z : Finset ℝ} {a : ℝ → ℝ} {η : ℝ}

/-- `g' = (f' + f h') e^h` where `f` is differentiable. -/
theorem hasDerivAt_G (hf : DifferentiableAt ℂ f z) :
    HasDerivAt 𝔊 ((deriv f z + f z * 𝔍 z) * Complex.exp (ℌ z)) z := by
  refine (hf.hasDerivAt.fun_mul (hasDerivAt_H Y Z a η z).cexp).congr_deriv ?_
  ring

/-- On an open set on which `f` is holomorphic, `g' = (f' + f h') e^h` and
`g'' = (f'' + 2 f' h' + f h'² + f h'') e^h`. -/
theorem deriv_G (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hz : z ∈ U) :
    deriv 𝔊 z = (deriv f z + f z * 𝔍 z) * Complex.exp (ℌ z) ∧
      𝔇 𝔊 z = (𝔇 f z + 2 * deriv f z * 𝔍 z +
        f z * 𝔍 z ^ 2 + f z * 𝔎 z) * Complex.exp (ℌ z) := by
  have h1 : ∀ w ∈ U, deriv 𝔊 w =
      (deriv f w + f w * 𝔍 w) * Complex.exp (ℌ w) :=
    fun w hw => (hasDerivAt_G (hf.differentiableAt (hU.mem_nhds hw))).deriv
  refine ⟨h1 z hz, ?_⟩
  have heq : deriv 𝔊 =ᶠ[𝓝 z]
      fun w => (deriv f w + f w * 𝔍 w) * Complex.exp (ℌ w) :=
    Filter.eventually_of_mem 𝔓 h1
  rw [heq.deriv_eq]
  have h := (((hf.deriv hU).differentiableAt 𝔓).hasDerivAt.fun_add ((hf.differentiableAt 𝔓).hasDerivAt.fun_mul (hasDerivAt_H1 Y Z a η z))).fun_mul
    (hasDerivAt_H Y Z a η z).cexp
  rw [h.deriv]
  ring

/-- `h = h' = 0` on `𝒴`. -/
theorem H_of_mem_Y (hy : y ∈ Y) : ℌ y = 0 ∧ 𝔍 y = 0 := by
  simp [H, H1, P_of_mem 0 hy, P1_of_mem 0 hy]

/-- `h''(y) = 2 ∏_{y' ≠ y} (y - y')² ψ(y) A(y)` for `y ∈ 𝒴`. -/
theorem H2_of_mem_Y (hy : y ∈ Y) :
    𝔎 y = 2 * P 0 𝔔 y * P 2 Z y * 𝔄 y := by
  simp [H2, P_of_mem 0 hy, P1_of_mem 0 hy, P2_of_mem 0 hy]

/-- `h = h' = h'' = 0` on `𝒵`. -/
theorem H_of_mem_Z (hw : w ∈ Z) :
    ℌ w = 0 ∧ 𝔍 w = 0 ∧ 𝔎 w = 0 := by
  simp [H, H1, H2, P_of_mem 2 hw, P1_of_mem 2 hw, P2_of_mem 2 hw]

end Map

/-! ## Elementary bounds -/

/-- `t e^{-t} ≤ 1`. -/
theorem mul_exp_neg_le_one t : t * Real.exp 𝖜 ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
  linarith [Real.add_one_le_exp t]

/-- `t² e^{-t} ≤ 2` for `t ≥ 0`. -/
theorem sq_mul_exp_neg_le_two (ht : 0 ≤ t) : t ^ 2 * Real.exp 𝖜 ≤ 2 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos t)]
  linarith [Real.quadratic_le_exp_of_nonneg ht]

/-- `e^{-t} = e^{-t/2} e^{-t/2}`. -/
theorem exp_neg_eq_sq_half t : Real.exp 𝖜 = Real.exp 𝔲 * Real.exp 𝔲 := by
  rw [← Real.exp_add]
  ring_nf

/-- `t e^{-t} ≤ 2 e^{-t/2}`. -/
theorem mul_exp_neg_le_half t : t * Real.exp 𝖜 ≤ 2 * Real.exp 𝔲 := by
  rw [exp_neg_eq_sq_half]
  nlinarith [mul_exp_neg_le_one (t / 2), Real.exp_pos 𝔲]

/-- The profile `|4t² - 2t| e^{-t}` of the term `φ ψ A''` near a point of `𝒴`. -/
theorem abs_mul_exp_neg_le (ht : 0 ≤ t) :
    |4 * t ^ 2 - 2 * t| * Real.exp 𝖜 ≤ 10 ∧
      |4 * t ^ 2 - 2 * t| * Real.exp 𝖜 ≤ 36 * Real.exp 𝔲 := by
  have := mul_le_mul_of_nonneg_right (abs_le.2 ⟨by nlinarith, by nlinarith⟩ :
    |4 * t ^ 2 - 2 * t| ≤ 4 * t ^ 2 + 2 * t) (Real.exp_pos 𝖜).le
  have h := exp_neg_eq_sq_half t
  have := sq_mul_exp_neg_le_two (t := t / 2) (by positivity)
  constructor <;> nlinarith [mul_exp_neg_le_one t, sq_mul_exp_neg_le_two ht, mul_exp_neg_le_half t,
    Real.exp_pos 𝔲]

local notation "𝔭" => P 2 Z x * P 0 𝖝 x
local notation "𝔞" => |x - k|
local notation "𝔮" => ((x - k) ^ 2 / η)
local notation "𝔰" => ((x - k) ^ 2 / ρ ^ 3)
local notation "𝔢" => Real.exp (-(x - k) ^ 2 / ρ ^ 3)
local notation "𝔗" T:max => ∑ k ∈ Y, a k * ‖𝔭‖ * T
local notation "𝔳" => (-2 * ((x : ℂ) - k) / η)
local notation "𝔉" P => ∀ k ∈ Y, P
local notation "𝔸" => 𝔉 0 ≤ a k
local notation "𝔥" => ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'|
/-! ## Splitting a sum near and far from the points of `𝒴` -/

/-- The near/far split. Let the points of `𝒴` be `2ρ`-separated, and let `w_y ≤ a_y` and
`0 ≤ F_y ≤ K` for every `y`, `w_y ≤ B` if `|x - y| < ρ`, and `F_y ≤ b` if
`|x - y| ≥ ρ`. Then `∑_y w_y F_y ≤ K B + b ∑_y a_y`: at most one point of `𝒴` is near `x`. -/
theorem sum_le_near_far {w F : ℝ → ℝ}
    (hsep : 𝔥) (hB : 0 ≤ B) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (ha : 𝔸) (hwa : 𝔉 w k ≤ a k)
    (hwB : 𝔉 𝔞 < ρ → w k ≤ B) (hF0 : 𝔉 0 ≤ F k) (hFK : 𝔉 F k ≤ K)
    (hFb : 𝔉 ρ ≤ 𝔞 → F k ≤ b) :
    ∑ k ∈ Y, w k * F k ≤ K * B + 𝖖 * b := by
  rw [← Finset.sum_filter_add_sum_filter_not Y fun k => 𝔞 < ρ, Finset.sum_mul]
  gcongr ?_ + ?_
  · refine (Finset.sum_le_card_nsmul _ _ (K * B) fun k hk => ?_).trans
      ((nsmul_le_nsmul_left (by positivity) (Finset.card_le_one.2 fun k hk k' hk' => ?_)).trans
        (one_nsmul _).le)
    · simp at hk
      nlinarith [hwB k hk.1 hk.2, hFK k hk.1, hF0 k hk.1]
    · grind
  · refine (Finset.sum_le_sum fun k hk => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun k hk _ => mul_nonneg 𝔧 hb)
    simp at hk
    bound

/-! ## Small widths -/

/-- The bound (4.3) for small `ρ`, with `σ = ρ³`: `c σ^q |u|^p e^{-u²/σ} ≤ ν` for every `u`. -/
theorem eventually_gauss {p q : ℝ} (hc : 0 < c) (hp : 0 < p) (hν : 0 < ν) (hq : -(p / 2) < q) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ u, c * 𝔣 ^ q * |u| ^ p * Real.exp (-u ^ 2 / ρ ^ 3) ≤ ν := by
  have : ∀ᶠ ρ in 𝓝 0, ρ ^ 3 < (2 * Real.exp 1 / p) ^ (p / (2 * q + p)) *
      (ν / c) ^ (1 / (q + p / 2)) :=
    ((continuous_pow 3).tendsto 0).eventually (gt_mem_nhds (by simp; positivity))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with ρ hρ h u using
    gaussian_bound hc hp hν hq 𝔵 h.le u

/-- The far terms: `K e^{-c/ρ} ≤ ν` for small `ρ`. -/
theorem eventually_exp_neg_div_le K (hc : 0 < c) (hν : 0 < ν) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), K * Real.exp (-(c / ρ)) ≤ ν := by
  filter_upwards [(((Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_inv_nhdsGT_zero.const_mul_atTop hc)).const_mul K).eventually
      (gt_mem_nhds (by simpa using hν)))] with ρ h
  exact h.le

/-- Small radii separate the points of a finite set: `2ρ < |y - y'|` for `y ≠ y'`. -/
theorem eventually_sep (Y : Finset ℝ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 𝔥 := by
  refine (eventually_all_finset Y).2 fun k _ => (eventually_all_finset Y).2 fun k' _ => ?_
  rcases eq_or_ne k k' with rfl | hkk
  · simp
  · filter_upwards [Ioo_mem_nhdsGT (half_pos (abs_pos.2 (sub_ne_zero.2 hkk)))] with ρ hρ
    grind

/-- Near a point `y` with `F(y) ≠ 0`, `|F| ≤ 2 |F(y)|` for a continuous `F`. -/
theorem eventually_near {F : ℂ → ℂ} (hF : Continuous F) (hy : F y ≠ 0) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ x, |x - y| < ρ → ‖F x‖ ≤ 2 * ‖F y‖ := by
  obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.1 hF.continuousAt (‖F y‖) (norm_pos_iff.2 hy)
  filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ x hx
  have := h (by rw [dist_eq_norm, norm_ofReal_sub]; linarith [hρ.2] : dist (x : ℂ) y < r)
  rw [dist_eq_norm] at this
  linarith [norm_sub_norm_le (F x) (F y)]

/-! ## The estimates on `[0,1]` -/

section Estimates

variable {Y Z : Finset ℝ} {a : ℝ → ℝ} {η x : ℝ}

/-- `|x - w| ≤ 1` for `x, w ∈ [0,1]`. -/
theorem norm_ofReal_sub_le_one (hx : x ∈ I) (hY : ∀ y ∈ Y, y ∈ I) : ∀ w ∈ Y, ‖(x : ℂ) - w‖ ≤ 1 := by
  intro w hw
  rw [norm_ofReal_sub, abs_le]
  grind

/-- `φ' = ∑_{y ∈ 𝒴} 2 (z - y) ∏_{y' ≠ y} (z - y')²`. -/
theorem P1_zero W z : P1 0 W z = ∑ i ∈ W, 2 * 𝖟 * P 0 𝖗 z := by
  simp [P1]

/-- The bound on `φ''` of the paper:
`|φ'' - 2 ∑_{y ∈ 𝒴} ∏_{y' ≠ y} (z - y')²| ≤ 4 M² |z - l|` for `l ∈ 𝒴`. -/
theorem norm_P2_zero_sub_le (hW : 𝔴)
    (hl : l ∈ W) : ‖P2 0 W z - 2 * ∑ i ∈ W, P 0 𝖗 z‖ ≤ 4 * W.card ^ 2 * ‖z - l‖ := by
  convert norm_P2_sub_le (m := 0) hW hl using 2 <;> norm_num [Finset.mul_sum]

/-- The products `∏_{y' ≠ y} (z - y')²` with `y ≠ k` contain the factor `(z - k)²`. -/
theorem sum_norm_P_erase_le (hW : 𝔴)
    (hk : k ∈ W) : ∑ i ∈ W.erase k, ‖P 0 𝖗 z‖ ≤ W.card * ‖z - k‖ ^ 2 := by
  refine (Finset.sum_le_card_nsmul _ _ (‖z - k‖ ^ 2) fun i hi => ?_).trans ?_
  · simpa using norm_P_le 𝖘
      (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hi).symm, hk⟩)
  · rw [nsmul_eq_mul]
    gcongr
    grind

/-- `|-2 (x - y)/η| = 2 |x - y|/η` at real points. -/
theorem norm_A1_coeff (hη : 0 < η) (x k : ℝ) :
    ‖𝔳‖ = 2 * 𝔞 / η := by
  rw [show 𝔳 = ((-2 * (x - k) / η : ℝ) : ℂ) by simp_all,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hη]
  norm_num

/-- Points at distance at least `ρ` from `y` have `t = (x - y)²/ρ³ ≥ 1/ρ`. -/
theorem one_div_le_of_le_abs (hρ : 0 < ρ) (h : ρ ≤ 𝔞) :
    1 / ρ ≤ 𝔰 := by
  rw [div_le_div_iff₀ hρ 𝔵]
  nlinarith [sq_abs (x - k), mul_le_mul h h hρ.le (hρ.le.trans h)]

/-- The factor `Λ(M, Q) = M (4M² + 10M + 3 L₀ + 16Q)` with `L₀ = 2M(16Q² + 12Q)`,
collecting the small terms of `h`, `h'` and `h''`. -/
noncomputable def coef (M Q : ℝ) : ℝ :=
  M * (4 * M ^ 2 + 10 * M + 3 * (2 * M * (16 * Q ^ 2 + 12 * Q)) + 4 * (4 * Q))

variable (ha : 𝔸)
include ha

/-- `|u A(x)| ≤ ∑_y a_y e^{-(x-y)²/η} v_y` if `|u| ≤ v_y` for every `y ∈ 𝒴`. -/
theorem norm_mul_A_le (hu : 𝔉 ‖u‖ ≤ v k) :
    ‖u * 𝔄 x‖ ≤ ∑ k ∈ Y, a k * 𝔯 x * v k := by
  rw [A, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg 𝔧, norm_gaussian]
  nlinarith [hu k hk, mul_nonneg 𝔧 (Real.exp_pos (-(x - k) ^ 2 / η)).le]

/-- `|u A'(x)| ≤ ∑_y a_y (2|x - y|/η) e^{-(x-y)²/η} v_y` if `|u| ≤ v_y` for every `y ∈ 𝒴`. -/
theorem norm_mul_A1_le (hη : 0 < η)
    (hu : 𝔉 ‖u‖ ≤ v k) :
    ‖u * 𝔅 x‖ ≤
      ∑ k ∈ Y, a k * (2 * 𝔞 / η) * 𝔯 x * v k := by
  rw [A1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg 𝔧,
    norm_gaussian, norm_A1_coeff hη]
  nlinarith [hu k hk, mul_nonneg (mul_nonneg 𝔧 (by positivity : 0 ≤ 2 * 𝔞 / η))
    (Real.exp_pos (-(x - k) ^ 2 / η)).le]

/-- A term `u A` with `|u| ≤ c |x - y|^p` for every `y ∈ 𝒴`, given the bound (4.3) in the form
`a_y |x - y|^p e^{-(x-y)²/η} ≤ ν`. -/
theorem norm_mul_A_le_of (hc : 0 ≤ c)
    (hu : 𝔉 ‖u‖ ≤ c * 𝔞 ^ p)
    (hν : 𝔉 a k * 𝔞 ^ p * 𝔯 x ≤ ν) :
    ‖u * 𝔄 x‖ ≤ c * 𝖚 := by
  refine (norm_mul_A_le ha hu).trans ((Finset.sum_le_card_nsmul _ _ (c * ν) fun k hk => ?_).trans_eq
    (by grind))
  linarith [mul_le_mul_of_nonneg_left (hν k hk) hc]

/-- A term `u A'` with `|u| ≤ c |x - y|²` for every `y ∈ 𝒴`, given the bound (4.3) in the form
`a_y |x - y|³ η⁻¹ e^{-(x-y)²/η} ≤ ν`. -/
theorem norm_mul_A1_le_of (hη : 0 < η) (hc : 0 ≤ c)
    (hu : 𝔉 ‖u‖ ≤ c * 𝔞 ^ 2)
    (hν : 𝔉 a k * 𝔞 ^ 3 / η * 𝔯 x ≤ ν) :
    ‖u * 𝔅 x‖ ≤ 2 * c * 𝖚 := by
  refine (norm_mul_A1_le ha hη hu).trans ((Finset.sum_le_card_nsmul _ _ (2 * c * ν)
    fun k hk => ?_).trans_eq (by grind))
  have := mul_le_mul_of_nonneg_left (hν k hk) (by positivity : 0 ≤ 2 * c)
  convert this using 1
  ring

/-- The term `φ ψ A''`: with `t = (x - y)²/η`, the summand of `y` is
`a_y ψ(x) ∏_{y' ≠ y} (x - y')² (4t² - 2t) e^{-t}`. -/
theorem norm_P_mul_A2_le :
    ‖P 0 Y x * P 2 Z x * A2 Y a η x‖ ≤
      𝔗
        (|4 * 𝔮 ^ 2 - 2 * 𝔮| * Real.exp (-𝔮)) := by
  rw [A2, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
  rw [P_eq_mul hk, show (x - k : ℂ) ^ (0 + 2) * P 0 𝖝 x * P 2 Z x *
    ((a k : ℂ) * (2 * (2 * (x - k) ^ 2 / η ^ 2 - 1 / η)) * 𝔠 x) =
    (a k : ℂ) * 𝔭 *
      ((4 * 𝔮 ^ 2 - 2 * 𝔮 : ℝ) : ℂ) *
      𝔠 x by push_cast; ring]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg 𝔧, Real.norm_eq_abs, norm_gaussian, neg_div]
  ring

variable (hY : ∀ y ∈ Y, y ∈ I) (hx : x ∈ I)
include hY hx

/-- The near/far split for the three norms `‖φ'' ψ A‖`, `‖φ ψ A''‖` and `‖φ' ψ A'‖`: with
`t = (x - y)²/ρ³`, the summand of `y` carries the weight `a_y |ψ(x) ∏_{y' ≠ y} (x - y')²|`, which
is at most `B` near `y`, and the profiles `2 e^{-t}`, `|4t² - 2t| e^{-t}` and `4t e^{-t}`, which
are bounded by `2`, `10` and `4` and are exponentially small far from `y`. -/
theorem sum_near_far_le (hρ : 0 < ρ)
    (hB : 0 ≤ B) (hψ : ‖P 2 Z x‖ ≤ 1)
    (hsep : 𝔥)
    (hnear : 𝔉 𝔞 < ρ → a k * ‖𝔭‖ ≤ B) :
    𝔗 (2 * 𝔢) +
      𝔗
        (|4 * 𝔰 ^ 2 - 2 * 𝔰| *
          Real.exp (-𝔰)) +
      2 * 𝔗
        (4 * 𝔰 * Real.exp (-𝔰)) ≤
      20 * B + 𝖖 * (2 * Real.exp 𝔩 + 52 * Real.exp 𝖙) := by
  have hwa : 𝔉 a k * ‖𝔭‖ ≤ a k := by
    intro k hk
    rw [norm_mul]
    exact mul_le_of_le_one_right 𝔧 (mul_le_one₀ hψ 𝔨 (norm_P_le_one
      fun w hw => norm_ofReal_sub_le_one hx hY w (Finset.mem_of_mem_erase hw)))
  have ht0 : ∀ k, 0 ≤ 𝔰 := fun k => by positivity
  have hf := fun k => one_div_le_of_le_abs (x := x) (k := k) hρ
  refine (add_le_add_three
    (sum_le_near_far (K := 2) (b := 2 * Real.exp 𝔩) hsep hB (by norm_num) (by positivity)
      ha hwa hnear (fun k _ => by positivity) (fun k _ => ?_) fun k _ h => ?_)
    (sum_le_near_far (b := 36 * Real.exp 𝖙) hsep hB (by norm_num)
      (by positivity) ha hwa hnear (fun k _ => by positivity) (fun k _ => (abs_mul_exp_neg_le
        𝔘).1) fun k _ h => (abs_mul_exp_neg_le 𝔘).2.trans ?_)
    (mul_le_mul_of_nonneg_left (sum_le_near_far (K := 4) (b := 8 * Real.exp 𝖙) hsep
      hB (by norm_num) (by positivity) ha hwa hnear (fun k _ => by positivity)
      (fun k _ => ?_) fun k _ h => ?_) two_pos.le)).trans_eq (by ring)
  · have := Real.exp_le_one_iff.2 (neg_nonpos.2 𝔘)
    grind
  · gcongr
    grind
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by grind)) (by norm_num)
  · linarith [mul_exp_neg_le_one 𝔰]
  · linarith [Real.exp_le_exp.2 (by linarith [hf k h] : -(𝔰 / 2) ≤ -𝔒),
      mul_exp_neg_le_half 𝔰]

variable (hZ : ∀ w ∈ Z, w ∈ I)
include hZ

/-- The term `φ'' ψ A`: the bound on `φ''`, `(C3)` and `(C4)` reduce it to
`I(x) = 2 ψ(x) ∑_y a_y e^{-(x-y)²/η} ∏_{y' ≠ y} (x - y')²`. -/
theorem norm_P2_mul_A_le
    (h1 : 𝔉 a k * 𝔞 ^ 1 * 𝔯 x ≤ ν)
    (h2 : 𝔉 a k * 𝔞 ^ 2 * 𝔯 x ≤ ν) :
    ‖P2 0 Y x * P 2 Z x * 𝔄 x‖ ≤ 4 * Y.card ^ 2 * 𝖚 + 2 * Y.card * 𝖚 +
      𝔗 (2 * 𝔯 x) := by
  have hYx := norm_ofReal_sub_le_one hx hY
  have hψ := norm_P_le_one (m := 2) (norm_ofReal_sub_le_one hx hZ)
  refine (norm_mul_A_le ha (v := fun k => 4 * Y.card ^ 2 * 𝔞 +
    2 * ‖𝔭‖ + 2 * Y.card * 𝔞 ^ 2) fun k hk => ?_).trans
    ((Finset.sum_le_sum fun k hk => (?_ : _ ≤ 4 * Y.card ^ 2 * ν + 2 * Y.card * ν +
      a k * ‖𝔭‖ * (2 * 𝔯 x))).trans_eq
      (by simp [Finset.sum_add_distrib]; ring))
  · have h3 := norm_P2_zero_sub_le hYx hk
    have h4 := (norm_sum_le _ _).trans (sum_norm_P_erase_le hYx hk)
    rw [norm_ofReal_sub] at h3 h4
    rw [show P2 0 Y x * P 2 Z x = 𝖛 * P 2 Z x +
      2 * (𝔭) + P 2 Z x * (2 * ∑ i ∈ Y.erase k, P 0 𝕮 x) by
      rw [← Finset.add_sum_erase Y _ hk]; ring]
    refine norm_add₃_le.trans (add_le_add_three ?_ (by simp) ?_) <;>
      simp only [norm_mul, Complex.norm_two]
    · nlinarith [norm_nonneg 𝖛]
    · nlinarith [norm_nonneg (∑ i ∈ Y.erase k, P 0 𝕮 (x : ℂ))]
  · have := ha k hk
    have := mul_le_mul_of_nonneg_left (h1 k hk) (by positivity : (0 : ℝ) ≤ 4 * Y.card ^ 2)
    have := mul_le_mul_of_nonneg_left (h2 k hk) (by positivity : (0 : ℝ) ≤ 2 * Y.card)
    nlinarith

/-- The term `φ' ψ A'`: the diagonal part is `-4 a_y ψ(x) ∏_{y' ≠ y} (x - y')² t e^{-t}` with
`t = (x - y)²/η`, the rest is bounded by (4.3) with `p = 3`, `q = -1`, as in `(C2)`. -/
theorem norm_P1_mul_A1_le (hη : 0 < η)
    (h3 : 𝔉 a k * 𝔞 ^ 3 / η * 𝔯 x ≤ ν) :
    ‖P1 0 Y x * P 2 Z x * 𝔅 x‖ ≤ 4 * Y.card * 𝖚 +
      𝔗
        (4 * 𝔮 * Real.exp (-𝔮)) := by
  have hYx := norm_ofReal_sub_le_one hx hY
  rw [A1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => (?_ : _ ≤ a k *
    ‖𝔭‖ * (4 * 𝔮 * Real.exp (-𝔮)) +
      4 * Y.card * ν)).trans_eq (by simp [Finset.sum_add_distrib]; ring))
  have hak := ha k hk
  have h4 := sum_norm_P_erase_le hYx hk
  rw [norm_ofReal_sub] at h4
  have hR : ‖P 2 Z x * ∑ i ∈ Y.erase k, 2 * ((x : ℂ) - i) * P 0 𝕮 x‖ ≤
      2 * Y.card * 𝔞 ^ 2 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left 𝔨 (norm_P_le_one (norm_ofReal_sub_le_one hx hZ))).trans ((norm_sum_le _ _).trans
      ((Finset.sum_le_sum fun i hi => ?_).trans (by rw [← Finset.mul_sum]; linarith :
        ∑ i ∈ Y.erase k, 2 * ‖P 0 𝕮 x‖ ≤ _)))
    rw [norm_mul, norm_mul, Complex.norm_two]
    nlinarith [hYx i (Finset.mem_of_mem_erase hi), norm_nonneg (P 0 𝕮 x)]
  rw [P1_zero, ← Finset.add_sum_erase Y _ hk, add_mul, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · rw [show 2 * (x - k) * P 0 𝖝 x * P 2 Z x *
      ((a k : ℂ) * 𝔳 * 𝔠 x) =
      (a k : ℂ) * 𝔭 * ((-4 * 𝔮 : ℝ) : ℂ) *
        𝔠 x by push_cast; ring,
      norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hak, Real.norm_eq_abs, norm_gaussian, neg_div,
      abs_of_nonpos (by have : 0 ≤ 𝔮 := by positivity
                        linarith)]
    ring
  · rw [show ∀ S, S * P 2 Z x *
      ((a k : ℂ) * 𝔳 * 𝔠 x) =
      ((a k : ℂ) * 𝔳 * 𝔠 x) *
        (P 2 Z x * S) from fun S => by ring, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hak, norm_gaussian, norm_A1_coeff hη]
    have := mul_le_mul_of_nonneg_left hR (by positivity :
      0 ≤ a k * (2 * 𝔞 / η) * 𝔯 x)
    have := mul_le_mul_of_nonneg_left (h3 k hk) (by positivity : (0 : ℝ) ≤ 4 * Y.card)
    linarith [show a k * (2 * 𝔞 / η) * 𝔯 x * (2 * Y.card * 𝔞 ^ 2)
      = 4 * Y.card * (a k * 𝔞 ^ 3 / η * 𝔯 x) by ring]

/-- The estimates for `h`, `h'` and `h''` at a point of `[0,1]`, for `η = ρ³`. The hypotheses
`h1`, `h2`, `h3` are the conclusions of (4.3) under `(C1)`-`(C4)`, `hsep` is (4.5), and `hnear`
is the comparison of `ψ ∏_{y' ≠ y} (x - y')²` with its value at `y`, used with the choice (4.4)
of the `a_y`. The terms `φ'' ψ A`, `φ ψ A''` and `φ' ψ A'` contribute `20 B` and the far terms of
the near/far split. -/
theorem norm_H_le (hZne : Z.Nonempty)
    (hρ : 0 < ρ) (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (h1 : 𝔉 a k * 𝔞 ^ 1 * 𝔢 ≤ ν)
    (h2 : 𝔉 a k * 𝔞 ^ 2 * 𝔢 ≤ ν)
    (h3 : 𝔉 a k * 𝔞 ^ 3 / ρ ^ 3 * 𝔢 ≤ ν)
    (hsep : 𝔥)
    (hnear : 𝔉 𝔞 < ρ → a k * ‖𝔭‖ ≤ B) :
    ‖H Y Z a 𝔣 x‖ ≤ coef Y.card Z.card * ν ∧
      ‖H1 Y Z a 𝔣 x‖ ≤ coef Y.card Z.card * ν ∧
      ‖H2 Y Z a 𝔣 x‖ ≤ coef Y.card Z.card * ν + 20 * B +
        𝖖 * (2 * Real.exp 𝔩 + 52 * Real.exp 𝖙) := by
  have hYx := norm_ofReal_sub_le_one hx hY
  have hZx := norm_ofReal_sub_le_one hx hZ
  have hψ0 := norm_P_le_one (m := 2) hZx
  have hψ1 := norm_P1_le (m := 2) hZx
  have hψ2 := norm_P2_le (m := 2) hZx
  have hφ0 : 𝔉 ‖P 0 Y x‖ ≤ 𝔞 ^ 2 := by
    intro k hk
    simpa [norm_ofReal_sub] using norm_P_le (m := 0) hYx hk
  have hφ1 : 𝔉 ‖P1 0 Y x‖ ≤ 2 * Y.card * 𝔞 := by
    intro k hk
    simpa [norm_ofReal_sub] using norm_P1_le_of_mem (m := 0) hYx hk
  norm_num at hψ1 hψ2
  have hQ1 : (1 : ℝ) ≤ Z.card := by exact_mod_cast hZne.card_pos
  have hψ0' : ‖P 2 Z x‖ ≤ 16 * Z.card ^ 2 + 12 * Z.card := by nlinarith
  have hψ1' : ‖P1 2 Z x‖ ≤ 16 * Z.card ^ 2 + 12 * Z.card := by nlinarith
  have hψ2' : ‖P2 2 Z x‖ ≤ 16 * Z.card ^ 2 + 12 * Z.card := by linarith
  have hψ0'' : ‖P 2 Z x‖ ≤ 4 * Z.card := by linarith
  have hφ0' : 𝔉 ‖P 0 Y x‖ ≤ 2 * Y.card * 𝔞 := by
    intro k hk
    have : (1 : ℝ) ≤ Y.card := by exact_mod_cast Finset.card_pos.2 ⟨k, hk⟩
    have : 𝔞 ≤ 1 := by grind
    nlinarith [hφ0 k hk, abs_nonneg (x - k)]
  have G : ∀ Φ Ψ, (𝔉 ‖Φ‖ ≤ 2 * Y.card * 𝔞) → ‖Ψ‖ ≤ 16 * Z.card ^ 2 + 12 * Z.card →
      ‖Φ * Ψ * A Y a 𝔣 x‖ ≤ 2 * Y.card * (16 * Z.card ^ 2 + 12 * Z.card) * 𝖚 :=
    fun Φ Ψ hΦ hΨ => norm_mul_A_le_of ha (by positivity) (fun k hk => by
      rw [norm_mul]
      exact (mul_le_mul (hΦ k hk) hΨ 𝔨 (by positivity)).trans_eq (by ring)) h1
  have G' : ∀ Ψ, ‖Ψ‖ ≤ 4 * Z.card → ‖P 0 Y x * Ψ * A1 Y a 𝔣 x‖ ≤
      2 * (4 * Z.card) * 𝖚 := fun Ψ hΨ =>
    norm_mul_A1_le_of ha 𝔵 (by positivity) (fun k hk => by
      rw [norm_mul]
      exact (mul_le_mul (hφ0 k hk) hΨ 𝔨 (by positivity)).trans_eq (by ring)) h3
  have d1 := norm_P2_mul_A_le ha hY hx hZ h1 h2
  have d2 := norm_P_mul_A2_le (Z := Z) (η := ρ ^ 3) (x := x) ha
  have d3 := norm_P1_mul_A1_le ha hY hx hZ 𝔵 h3
  have n := sum_near_far_le ha hY hx hρ hB hψ0 hsep hnear
  have : 0 ≤ (Y.card : ℝ) ^ 3 * ν := by positivity
  have : 0 ≤ (Y.card : ℝ) ^ 2 * ν := by positivity
  have : 0 ≤ (Y.card : ℝ) ^ 2 * Z.card ^ 2 * ν := by positivity
  have : 0 ≤ (Y.card : ℝ) ^ 2 * Z.card * ν := by positivity
  have : 0 ≤ (Y.card : ℝ) * Z.card * ν := by positivity
  simp only [H, coef]
  refine ⟨by linarith [G _ _ hφ0' hψ0'], norm_add₃_le.trans ?_,
    (norm_add₃_le.trans (add_le_add_three ((norm_add_le _ _).trans
      (add_le_add_left norm_add₃_le _)) le_rfl le_rfl)).trans ?_⟩
  · linarith [G _ _ hφ1 hψ0', G _ _ hφ0' hψ1', G' _ hψ0'']
  · simp only [norm_mul (2 : ℂ), Complex.norm_two]
    linarith [G _ _ hφ0' hψ2', G _ _ hφ1 hψ1', G' _ hψ1]

end Estimates

/-- From the bounds on `h`, `h'`, `h''` to the bounds on `g - f`, `g' - f'`, `g'' - f''`, using
`g - f = f (e^h - 1)`, `g' - f' = f' (e^h - 1) + f h' e^h` and
`g'' - f'' = f'' (e^h - 1) + (2 f' h' + f h'² + f h'') e^h`. -/
theorem norm_sub_le_of_norm_H_le (hs : s ≤ 1 / 2)
    (hf0 : ‖f0‖ ≤ 1) (hf1 : ‖f1‖ ≤ 1) (hf2 : ‖f2‖ ≤ B2)
    (hh : ‖h‖ ≤ s) (hh1 : ‖h1‖ ≤ s) (hh2 : ‖h2‖ ≤ D + s) :
    ‖f0 * Complex.exp h - f0‖ ≤ 2 * s ∧
      ‖𝔙 * Complex.exp h - f1‖ ≤ 4 * s ∧
      ‖𝖞 * Complex.exp h - f2‖ ≤
        2 * B2 * s + 8 * s + 2 * D := by
  have he1 : ‖Complex.exp h - 1‖ ≤ 2 * s :=
    (Complex.norm_exp_sub_one_le (by linarith)).trans (by linarith)
  have he : ‖Complex.exp h‖ ≤ 2 := by linarith [norm_sub_norm_le (Complex.exp h) 1, norm_one (α := ℂ)]
  have := norm_nonneg h1
  have := norm_nonneg 𝔦
  have := mul_le_mul hf0 hh1 𝔨 zero_le_one
  have := mul_le_mul hf0 hh2 𝔨 zero_le_one
  refine ⟨?_, ?_, ?_⟩
  · rw [show f0 * Complex.exp h - f0 = f0 * 𝔦 by ring, norm_mul]
    nlinarith
  · rw [show 𝔙 * Complex.exp h - f1 =
        f1 * 𝔦 + f0 * h1 * Complex.exp h by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    nlinarith [norm_nonneg (Complex.exp h)]
  · rw [show 𝖞 * Complex.exp h - f2 =
        f2 * 𝔦 + 𝕭 * Complex.exp h by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have : ‖2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2‖ ≤ 2 * s + s / 2 + (D + s) := by
      refine norm_add₃_le.trans ?_
      simp
      nlinarith
    nlinarith [norm_nonneg f2, norm_nonneg 𝕭]

/-- `|A(y)| ≥ a_y` at `y ∈ 𝒴` for positive amplitudes. -/
theorem le_norm_A (ha : 𝔸) (hy : y ∈ Y) :
    a y ≤ ‖𝔄 y‖ := by
  rw [A_ofReal, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have h := Finset.single_le_sum (f := fun k => a k * 𝔯 y)
    (fun k hk => mul_nonneg 𝔧 (Real.exp_pos _).le) hy
  simp_all

end MultiplicativeBump

local notation "𝔉" P => ∀ k ∈ Y, P

open MultiplicativeBump in
/-- Proposition 4.2, by the construction of the paper. Let `f ∈ S^ω(I)` with `f([0,1]) ⊆ (0,1)`.
There is `C > 0` such that for all finite disjoint `𝒴, 𝒵 ⊆ [0,1]`, `η > 0` and `δ > 0` there is
`g ∈ S^ω(I)` with `g = f` and `g' = f'` on `𝒴 ∪ 𝒵`, `g'' = f''` on `𝒵`,
`|g''/g' - f''/f'| ≥ δ` on `𝒴`, `|g - f| < η` and `|g' - f'| < η` on `[0,1]`, and
`|g'' - f''| < C δ + η` on `[0,1]`. The paper writes `ε` for `η`. Here `g = f e^{φ ψ A}` with the
amplitudes (4.4) and all widths equal to `ρ³` for a small `ρ > 0`, and `C = 40/m` for a margin
`m` with `m ≤ f ≤ 1 - m` on `[0,1]`. -/
theorem proposition_4_2 (hε : 0 < ε) (hf : InClass ε f)
    (hI : Ɐ (f x).re ∈ Ioo 0 1) :
    ∃ C > 0, ∀ Y Z : Finset ℝ, (∀ y ∈ Y, y ∈ I) → (∀ z ∈ Z, z ∈ I) → Disjoint Y Z →
      ∀ η > 0, ∀ δ > 0, ∃ g, (∃ ε' > 0, InClass ε' g) ∧
        (∀ y ∈ Y ∪ Z, g y = f y ∧ deriv g y = deriv f y) ∧
        (∀ z ∈ Z, 𝔇 g z = 𝔇 f z) ∧
        (∀ y ∈ Y, δ ≤ ‖𝔇 g y / deriv g y - 𝔇 f y / deriv f y‖) ∧
        (Ɐ ‖g x - f x‖ < η) ∧ (Ɐ ‖deriv g x - deriv f x‖ < η) ∧
        (Ɐ ‖𝔇 g x - 𝔇 f x‖ < C * δ + η) := by
  obtain ⟨m, hm, hmar⟩ := exists_margin hε hf hI
  have h2ε : 0 < 2 * ε := by positivity
  -- a bound `B₂` for `f''` on `[0,1]`
  obtain ⟨B₂, hB₂⟩ := isCompact_image_I.exists_bound_of_continuousOn
    ((((hf.differentiableOn).deriv isOpen_nbhd).deriv isOpen_nbhd).continuousOn.mono (image_I_subset_nbhd h2ε))
  replace hB₂ : Ɐ ‖𝔇 f x‖ ≤ B₂ := fun x hx => hB₂ _ (mem_image_of_mem _ hx)
  have hB₂0 := (norm_nonneg _).trans (hB₂ 0 zero_mem_I)
  -- `f` and `f'` on `[0,1]`
  have hfreal : Ɐ f x = ((f x).re : ℂ) := fun x hx =>
    Complex.ext rfl (by simp [hf.im_eq_zero x (ofReal_mem_nbhd h2ε hx)])
  have hf0 : Ɐ m ≤ ‖f x‖ ∧ ‖f x‖ ≤ 1 := by
    intro x hx
    obtain ⟨h1, h2, -, -⟩ := hmar x hx
    rw [hfreal x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    grind
  have hf1 : Ɐ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 := by grind
  refine ⟨40 / m, by positivity, fun Y Z hY hZ hYZ η hη δ hδ => ?_⟩
  wlog hZne : Z.Nonempty generalizing Z
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.1 hZne
    obtain ⟨z, hzI, hzY⟩ := ((Set.Icc_infinite zero_lt_one).sdiff Y.finite_toSet).nonempty
    obtain ⟨g, hg, hagree, -, hrest⟩ := this {z} (by grind)
      (Finset.disjoint_singleton_right.2 hzY) (Finset.singleton_nonempty z)
    grind
  -- the amplitudes (4.4)
  set N : ℝ → ℝ := fun k => ‖P 2 Z k * P 0 𝖝 k‖
  have hN0 : 𝔉 P 2 Z k * P 0 𝖝 k ≠ 0 := fun k hk =>
    mul_ne_zero (P_ne_zero 2 (Finset.disjoint_left.1 hYZ hk))
      (P_ne_zero 0 (Finset.notMem_erase k Y))
  have hN : 𝔉 0 < N k := fun k hk => norm_pos_iff.2 (hN0 k hk)
  set a : ℝ → ℝ := fun k => δ * ‖deriv f k‖ / (2 * ‖f k‖ * N k) with ha_def
  have hfk := fun k hk => hm.trans_le (hf0 k 𝔶).1
  have ha : 𝔉 0 < a k := by
    intro k hk
    have := hm.trans_le (hf1 k 𝔶).1
    have := hfk k hk
    have := hN k hk
    positivity
  have haN : 𝔉 2 * a k * N k * ‖f k‖ = δ * ‖deriv f k‖ := by
    intro k hk
    have := hfk k hk
    have := hN k hk
    simp [ha_def]
    field_simp
  -- the size `s` of `h`, `h'` and of `h''` up to `20 δ/m` on `[0,1]`; the paper's `ε`
  set s := min (1 / 2) (min (η / 𝔛) (m / 5))
  have hs : 0 < s := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hsη : (2 * B₂ + 8) * s < η := by
    have h1 : s ≤ η / 𝔛 := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hsm : s ≤ m / 5 := (min_le_right _ _).trans (min_le_right _ _)
  set Λ := coef Y.card Z.card with hΛ
  have hΛ0 : 0 ≤ Λ := by
    simp [hΛ, coef]
    positivity
  set ν := s / (2 * (Λ + 1)) with hν_def
  have hν : 0 < ν := by positivity
  have hΛν : Λ * ν ≤ s / 2 := by
    rw [hν_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the width `η_y = ρ³`: (4.3) under `(C1)`-`(C4)`, (4.5), (4.6) and its analogue, and the
  -- comparison near `𝒴`
  have hcont : ∀ k, Continuous fun z => P 2 Z z * P 0 𝖝 z := fun k =>
    ((differentiable_P 2 Z).mul (differentiable_P 0 _)).continuous
  have hs4 : 0 < s / 4 := by positivity
  obtain ⟨ρ, ⟨⟨⟨⟨⟨⟨⟨E1, E2⟩, E3⟩, Esep⟩, Enear⟩, F1⟩, F2⟩, hρ⟩⟩ :=
    (((((((((eventually_all_finset Y).2 fun k hk => eventually_gauss (q := 0) 𝔧 one_pos hν (by norm_num)).and
      ((eventually_all_finset Y).2 fun k hk => eventually_gauss (q := 0) 𝔧 two_pos hν (by norm_num))).and
      ((eventually_all_finset Y).2 fun k hk => eventually_gauss (q := -1) 𝔧 three_pos hν (by norm_num))).and
      (eventually_sep Y)).and
      ((eventually_all_finset Y).2 fun k hk => eventually_near (hcont k) (hN0 k hk))).and
      (eventually_exp_neg_div_le (𝖖 * 2) one_pos hs4)).and
      (eventually_exp_neg_div_le (𝖖 * 52) (by norm_num : (0 : ℝ) < 1 / 2) hs4)).and
      self_mem_nhdsWithin).exists
  set g := G f Y Z a 𝔣
  have hderiv := fun x (hx : x ∈ I) => deriv_G (Y := Y) (Z := Z) (a := a) (η := ρ ^ 3) isOpen_nbhd
    hf.differentiableOn (ofReal_mem_nbhd h2ε hx)
  -- the estimates on `[0,1]`
  have hest : Ɐ ‖g x - f x‖ ≤ 2 * s ∧ ‖deriv g x - deriv f x‖ ≤ 4 * s ∧
      ‖𝔇 g x - 𝔇 f x‖ ≤ 2 * B₂ * s + 8 * s + 2 * 𝔏 := by
    intro x hx
    have hnear : 𝔉 |x - k| < ρ → a k * ‖P 2 Z x * P 0 𝖝 x‖ ≤ δ / m := by
      intro k hk hxk
      rw [le_div_iff₀ hm]
      linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Enear k hk x hxk) (ha k hk).le)
        hm.le, mul_le_mul_of_nonneg_left (hf0 k 𝔶).1 (by positivity :
          0 ≤ 2 * a k * N k), mul_le_mul_of_nonneg_left (hf1 k 𝔶).2 hδ.le, haN k hk]
    obtain ⟨n0, n1, n2⟩ := norm_H_le (fun k hk => (ha k hk).le) hY hx hZ hZne hρ hν.le
      (by positivity) (fun k hk => by simpa using E1 k hk (x - k)) (fun k hk => by simpa using E2 k hk (x - k))
      (fun k hk => by simpa [Real.rpow_neg_one, div_eq_mul_inv, mul_right_comm] using E3 k hk (x - k)) Esep hnear
    rw [(hderiv x hx).1, (hderiv x hx).2]
    rw [div_right_comm] at F2
    exact norm_sub_le_of_norm_H_le (min_le_left _ _) (hf0 x hx).2 (hf1 x hx).2 (hB₂ x hx) (by linarith)
      (by linarith) (by linarith)
  refine ⟨g, ?_, fun w hw => ?_, fun w hw => ?_, fun y hy => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · -- "Hence `g ∈ S^ω([0,1])`", by `exists_inClass`
    refine exists_inClass isOpen_nbhd ?_ ((hf.differentiableOn).fun_mul (differentiable_H Y Z a 𝔣).cexp.differentiableOn)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · exact image_I_subset_nbhd h2ε
    · have hH : H Y Z a 𝔣 x = ((H Y Z a 𝔣 x).re : ℂ) :=
        Complex.ext rfl (by simp [im_H_ofReal])
      show (f x * Complex.exp (H Y Z a 𝔣 x)).im = 0
      rw [hH, Complex.mul_im, Complex.exp_ofReal_im, hf.im_eq_zero x hx]
      ring
    · obtain ⟨h1, h2, -, -⟩ := hmar x hx
      have h3 := (Complex.abs_re_le_norm (g x - f x)).trans (hest x hx).1
      rw [abs_le, Complex.sub_re] at h3
      show (g x).re ∈ I
      constructor <;> linarith
    · obtain ⟨-, -, h1, -⟩ := hmar x hx
      have h2 := (hest x hx).2.1
      intro h
      rw [h, zero_sub, norm_neg] at h2
      linarith
    · obtain ⟨-, -, -, h1⟩ := hmar x hx
      have h2 := (hest x hx).2.1
      have h3 := norm_sub_norm_le (deriv g x) (deriv f x)
      linarith
  · -- agreement to first order on `𝒴 ∪ 𝒵`
    have hH : H Y Z a 𝔣 w = 0 ∧ H1 Y Z a 𝔣 w = 0 := by
      rcases Finset.mem_union.1 hw with hw | hw
      · exact H_of_mem_Y hw
      · exact ⟨(H_of_mem_Z hw).1, (H_of_mem_Z hw).2.1⟩
    rw [(hderiv w ((fun w hw => (Finset.mem_union.1 hw).elim (hY w) (hZ w)) w hw)).1, hH.1, hH.2]
    refine ⟨?_, by simp⟩
    show f w * Complex.exp (H Y Z a 𝔣 w) = f w
    rw [hH.1, Complex.exp_zero, mul_one]
  · -- agreement to second order on `𝒵`
    obtain ⟨h0, h1, h2⟩ := H_of_mem_Z hw
    rw [(hderiv w (hZ w hw)).2, h0, h1, h2]
    simp
  · -- the lower bound in (iii)
    obtain ⟨h0, h1⟩ := H_of_mem_Y hy
    rw [(hderiv y 𝔐).2, (hderiv y 𝔐).1, h0, h1, H2_of_mem_Y hy]
    simp only [Complex.exp_zero, mul_zero, add_zero, mul_one, zero_pow two_ne_zero, add_div,
      add_sub_cancel_left]
    rw [norm_div, le_div_iff₀ (hm.trans_le (hf1 y 𝔐).1), show f y * (2 * P 0 𝔔 y *
      P 2 Z y * A Y a 𝔣 y) = f y * 2 * (P 2 Z y * P 0 𝔔 y) * A Y a 𝔣 y by ring,
      norm_mul, norm_mul, norm_mul, Complex.norm_two]
    linarith [haN y hy, mul_le_mul_of_nonneg_left (le_norm_A (η := ρ ^ 3) (fun k hk => (ha k hk).le)
      hy) (by positivity : 0 ≤ ‖f y‖ * 2 * N y)]
  · linarith [(hest x hx).1, mul_nonneg hB₂0 hs.le]
  · linarith [(hest x hx).2.1, mul_nonneg hB₂0 hs.le]
  · linarith [(hest x hx).2.2, show 2 * 𝔏 = 40 / m * δ by ring]

end AnalyticESC
