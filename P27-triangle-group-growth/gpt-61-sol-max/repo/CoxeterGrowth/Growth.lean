module
public import Mathlib

public section
/-!
# Growth of the triangle Coxeter groups `(p, q, ∞)`

The amalgam normal forms, their evaluation in a Coxeter system, and their generating function
are followed by the Padovan instance and the growth-rate analysis for the whole family.
A normal form is `c^ε x₁ ⋯ xₖ`, where nonempty alternating `a,c` and `b,c` blocks alternate.
The head coordinate is a dihedral element, and tail entries encode block length minus one.
The generator actions preserve these forms and lift through `CoxeterSystem.lift`; evaluation
and the orbit map are inverse and preserve length. Counting the forms gives the series identity.
All compared statements expand to standard Mathlib vocabulary.
-/

namespace TriangleGrowth

open Finset PowerSeries Filter Topology



local notation "Gen" => Fin 3

variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix Gen}
  (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {p q p' q' : ℕ}

local notation:max "A" n:arg => Nat.card {w // cs.length w = n}
local notation:max "B" n:arg => Nat.card {w // cs'.length w = n}
local notation "sphereRoots" => fun n => (A n : ℝ) ^ (n : ℝ)⁻¹
local notation "G" => PowerSeries.mk fun n => (A n : ℤ)
local notation:max "S" m:arg x:arg => ∑ i ∈ Finset.Ico 1 m, x ^ i
local notation:max "F" p:arg q:arg x:arg => S p x⁻¹ * S q x⁻¹

/-! ## Dihedral heads -/

abbrev Head := Bool × ℕ

/-! ## Raw normal forms -/

/-- Raw normal forms `((ε, j), r)`. -/
abbrev Raw := Head × List ℕ

abbrev origin : Raw := ((false, 0), [])

/-- Validity of a list of successor-encoded block lengths, bounded alternately by `m₁`, the next by `m₂`, … -/
def VT := fun
  | _, _, [] => True
  | m₁, m₂, k :: r => k + 1 < m₁ ∧ VT m₂ m₁ r

attribute [local grind] Function.Injective Function.Involutive Prod.map Sigma.uncurry Bool.toNat VT

/- Validity of a `p`-head followed by `q, p, …` blocks. -/
set_option quotPrecheck false in
local notation "Valid" => fun v : Raw => v.1.2 < p ∧ VT q p v.2

/-- Length (number of letters) of a normal form. -/
abbrev len (v : Raw) := v.1.1.toNat + v.1.2 + v.2.sum + v.2.length

/-- Re-read a normal form with a head of the other type. -/
abbrev swap (v : Raw) :=
  if v.1.2 = 0 then match v.2 with
    | [] => v
    | k :: r => ((v.1.1, k + 1), r)
  else ((v.1.1, 0), (v.1.2 - 1) :: v.2)

theorem swap_swap : Function.Involutive swap := by
  grind

/-- `a`/`b` (head generator) acting on the head. -/
abbrev actH m (v : Raw) :=
  (if v.1.1 then
    if v.1.2 + 2 < m then (false, v.1.2 + 2) else (true, 2 * m - v.1.2 - 3)
  else
    if v.1.2 < 2 then (false, 1 - v.1.2) else (true, v.1.2 - 2), v.2)
/-- `c` acting on the head. -/
abbrev actC : Raw → Raw := Prod.map (Prod.map Bool.not id) id
/-- The left action of the three generators on raw normal forms. -/
abbrev act p q (i : Gen) v := match i with
  | 0 => actH p v
  | 1 => swap (actH q (swap v))
  | 2 => actC v

local notation "actPQ" => act p q



/-! ### The Coxeter relations on raw normal forms -/

theorem rel_HC (hm : 2 ≤ m) (h : v.1.2 < m) :
    (actH m ∘ actC)^[m] v = v := by
  let sig (x : Head) := if x.1 then Int.negSucc x.2 else x.2
  -- Up to one period, the orbit coordinate wraps at most once; the tail is unchanged.
  have ht n (hn : n ≤ m) : let y := (actH m ∘ actC)^[n] v
      y.1.2 < m ∧ (sig y.1 = sig v.1 + 2 * n ∨
        sig y.1 + 2 * m = sig v.1 + 2 * n) ∧ y.2 = v.2 := by
    induction n with
    | zero => simp_all
    | succ n ih =>
      grind [Function.iterate_succ_apply']
  specialize ht m le_rfl
  grind

/-! ## Counting normal forms -/

/-- Successor-encoded block lists of total length `n`, bounded alternately by `m₁, m₂, m₁, …`. -/
def tails m₁ m₂ n :=
  if n = 0 then {[]} else
    ((range n).sigma fun k =>
      if k + 1 < m₁ then tails m₂ m₁ (n - (k + 1)) else ∅).map
        ⟨Sigma.uncurry List.cons, by grind⟩

theorem mem_tails :
    r ∈ tails m₁ m₂ n ↔ VT m₁ m₂ r ∧ r.sum + r.length = n := by
  induction r generalizing m₁ m₂ n <;> unfold tails <;> split_ifs <;>
    simp_all [Sigma.uncurry] <;> grind

/-- `X + X² + ⋯ + X^{m-1}`. -/
local notation:max "Pm" m:arg => S m X
/-- `1 + X + ⋯ + X^{m-1}`. -/
local notation:max "Rm" m:arg => ∑ i ∈ range m, X ^ i

/-- The generating function of a counting sequence. -/
local notation "ser" f:arg => PowerSeries.mk fun n => (Finset.card (f n) : ℤ)

/-- All raw normal forms of length `n`. -/
def NFs p q n :=
  ((univ.filter (fun e : Bool => e.toNat ≤ n)).sigma fun e =>
    ((range (n - e.toNat + 1)).filter (· < p)).sigma fun j => tails q p (n - e.toNat - j)).map
      (Equiv.sigmaAssocProd.symm.trans (Equiv.sigmaEquivProd _ _)).toEmbedding

local notation "forms" => NFs p q

@[grind] theorem mem_NFs : v ∈ forms n ↔ Valid v ∧ len v = n := by
  simp [NFs, mem_tails, Equiv.sigmaAssoc]
  grind

/-! ### Generating functions -/

theorem tails_series :
    ser (tails m₁ m₂) = 1 + Pm m₁ * ser (tails m₂ m₁) := by
  ext n
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [tails]
  split_ifs <;> simp_all [sum_range_succ', apply_ite Finset.card]

/-- **The series identity for normal forms**:
`(Σ #NF_n Xⁿ) · (1 − P_p P_q) = (1 + X) [p] [q]`. -/
theorem nf_series (hq : 1 ≤ q) :
    ser (forms) * (1 - Pm p * Pm q) = Rm 2 * Rm p * Rm q := by
  have hF :
      ser (forms) = Rm 2 * (Rm p * ser (tails q p)) := by
    ext n
    simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      map_sum]
    cases n <;> simp [NFs, sum_filter, sum_range_succ']
  rw [hF, sum_range_eq_add_Ico _ hq]
  linear_combination Rm 2 * Rm p * (@tails_series q p + Pm q * @tails_series p q)

/-! ## Evaluation in a Coxeter system -/

/-- The tail: successor-encoded blocks alternating between `s_i` and `s_{i'}`. -/
abbrev tailP := fun
  | _, _, [] => 1
  | i, i', k :: r => (cs.wordProd (CoxeterSystem.alternatingWord 2 i (k + 1)))⁻¹ * tailP i' i r

/-- A normal form with an `s_i`-head, followed by blocks starting with `s_{i'}`. -/
def piH i i' (v : Raw) :=
  cs.simple 2 ^ v.1.1.toNat * (cs.wordProd (CoxeterSystem.alternatingWord 2 i v.1.2))⁻¹ * tailP cs i' i v.2

/-- Evaluation of a raw normal form in `W`. -/
local notation "piA" => piH cs 0 1

/-- The hypotheses: `M` is the Coxeter matrix of type `(p, q, ∞)`. -/
class IsTri (M : CoxeterMatrix Gen) (p q : outParam ℕ) : Prop where
  h01 : M 1 0 = 0
  h02 : M 0 2 = p
  h12 : M 1 2 = q
  hp : 2 ≤ p
  hq : 2 ≤ q

attribute [local simp] piH CoxeterSystem.alternatingWord IsTri.h01 IsTri.h02 IsTri.h12 CoxeterMatrix.symmetric

theorem piH_swap : piH cs i' i (swap v) = piH cs i i' v := by
  rcases v with ⟨⟨e, _ | j⟩, _ | _⟩ <;> simp [swap, mul_assoc]

/-- **Head identity**: `actH` is left multiplication by `s_i`. -/
theorem piH_actH (hm : 2 ≤ m) (hM : M i 2 = m) :
    ∀ {v : Raw}, v.1.2 < m → piH cs i i' (actH m v) = cs.simple i * piH cs i i' v := by
  rintro ⟨⟨e, j⟩, r⟩ hj
  cases e <;> simp_all [← mul_assoc]
  all_goals
    split_ifs with h
    all_goals solve
      | rcases j with _ | _ | j <;>
          simp_all [CoxeterSystem.wordProd, ← mul_assoc]
      | have H := congrArg Inv.inv
          (cs.prod_alternatingWord_eq_prod_alternatingWord_sub 2 i (j + 2)
            (by grind [M.symmetric]))
        rw [M.symmetric, hM,
          show m * 2 - (j + 2) = (2 * m - j - 3) + 1 by omega] at H
        simpa [CoxeterSystem.wordProd] using H.symm

/-! ## The triangle Coxeter group -/

attribute [local grind →] IsTri.hp IsTri.hq

variable [hT : IsTri M p q]



include hT
theorem piA_act (hv : Valid v) :
    piA (actPQ i v) = cs.simple i * piA v := by
  fin_cases i
  · exact piH_actH cs hT.hp hT.h02 hv.1
  · simpa only [Fin.reduceFinMk, piH_swap] using
      piH_actH cs hT.hq hT.h12 (v := swap v) (by grind)
  · cases h : v.1.1 <;> simp [h, ← mul_assoc]

/-- The normal form of `w`. -/
noncomputable def ev w :=
  let g i :=
    Function.Involutive.toPerm (fun v : {v // Valid v} => ⟨actPQ i v.1, by grind⟩)
      (by fin_cases i <;> grind)
  cs.lift ⟨g, by
    have hr i : (g (Fin.castSucc i) * g 2) ^ (if i = 0 then p else q) = 1 := by
      ext1 v
      apply Subtype.ext
      refine ((show Function.Semiconj Subtype.val _
        (actPQ i.castSucc ∘ actPQ 2) from fun _ => rfl).iterate_right _ v).trans ?_
      fin_cases i
      · exact rel_HC hT.hp v.2.1
      · have hh : Function.Semiconj swap (actPQ 1 ∘ actPQ 2)
            (actH q ∘ actC) := by
          grind [Function.Semiconj, swap_swap _]
        apply swap_swap.injective
        exact (hh.iterate_right q v.1).trans (rel_HC hT.hq (by grind))
    intro i j
    fin_cases i, j <;> simp_all
    all_goals first
      | exact inv_mul_cancel (g _)
      | apply mul_right_cancel (b := g 2)
        simp_all [mul_pow_mul]⟩ w ⟨origin, by grind⟩

@[grind] theorem ev_simple_mul :
    (ev cs (cs.simple i * w) : Raw) = actPQ i (ev cs w) := by
  erw [ev, map_mul, CoxeterSystem.lift_apply_simple]
  rfl

/-- Every element is the value of its normal form. -/
@[grind! =>] theorem piA_ev : piA (ev cs w) = w := by
  induction w using cs.simple_induction_left
  · simp [ev]
  · grind [piA_act]

@[grind! .] theorem normal_form (hv : Valid v) :
    cs.length (piA v) ≤ len v ∧ (ev cs (piA v) : Raw) = v := by
  induction v using (measure len).wf.induction
  next v ih =>
    rcases eq_or_ne v origin with rfl | h0
    · simp [ev]
    obtain ⟨i, hi⟩ : ∃ i : Gen, len (actPQ i v) + 1 = len v := by
      simp [Fin.exists_fin_succ]
      grind
    specialize ih _ (Nat.lt_of_succ_le hi.le) (by grind)
    have : actPQ i (actPQ i v) = v := by fin_cases i <;> grind
    grind [piA_act, CoxeterSystem.length_mul_le, CoxeterSystem.length_simple]

/-- **Length additivity**: the Coxeter length is the length of the normal form. -/
@[grind] theorem length_eq_len_ev : cs.length w = len (ev cs w) := by
  apply le_antisymm
  · grind
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    rw [hω.eq]
    clear hω
    induction ω <;> first | grind [CoxeterSystem.wordProd_cons] | simp [ev]

omit hT

/-- Spheres of `W` are in bijection with normal forms of the same length. -/
theorem sphere_eq_card (hT : IsTri M p q := by constructor <;> first | omega | simp_all) :
    A n = (forms n).card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    ⟨fun w => ⟨ev cs w, by grind⟩,
      fun v => ⟨piA v, by grind⟩, ?_, ?_⟩ <;>
    grind

variable (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2))
  (h01 : M 0 1 = 0) (h02g : M 0 2 = p) (h12g : M 1 2 = q)

variable (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
variable (τ : ℝ) (hτ : 1 < τ) (heq : F p q τ = 1)
variable {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1)

local notation "Q2" => 1 + X
local notation "Q3" => Q2 + X ^ 2

local notation "D2" => 1 - X ^ 2

abbrev le23 := Nat.le_succ 2


section

attribute [local simp] Finset.sum_Ico_eq_sum_range Finset.sum_range_succ

include hp hq h01 h02g h12g in
/-- **Growth series of the triangle Coxeter group `(p, q, ∞)`** (coefficient form in `ℤ⟦X⟧`). -/
theorem growth_series :
    G * (1 - Pm p * Pm q) = Q2 * Rm p * Rm q := by
  simpa [sphere_eq_card cs]
    using @nf_series p q (by omega)

/-- The `(2, 3)` rate equation is the plastic cubic. -/
theorem rate23_iff {τ : ℝ} :
    F 2 3 τ = 1 ↔ τ ^ 3 = τ + 1 := by
  norm_num
  grind

variable (p q)

include hp hq in
/-- Non-vacuity: the hypotheses of `growth_series` are satisfiable for all `p, q ≥ 2`. -/
theorem triangle_matrix_exists :
    ∃ M : CoxeterMatrix Gen, M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q  := by
  refine ⟨⟨!![1, 0, p; 0, 1, q; p, q, 1], ?_, ?_, ?_⟩, rfl, rfl, rfl⟩ <;>
    simp_all [Matrix.IsSymm, ← Matrix.ext_iff, Fin.forall_fin_succ]
  omega

include h01

set_option hygiene false in
macro "growth_instance" : tactic =>
  `(tactic| linear_combination (norm := norm_num) growth_series cs (by norm_num) (by norm_num) h01 h02 h12 <;> ring)

include h02 in
/-- `(2,4,∞)`: `Σ a(n) tⁿ · (1 − t² − t³ − t⁴) = (1+t)²(1+t+t²+t³)`. -/
theorem growth_series_24 (h12 : M 1 2 = 4) :
    G *
        (D2 - X ^ 3 - X ^ 4) = Q2 ^ 2 * (Q3 + X ^ 3) := by
  growth_instance

/-- `(3,3,∞)`: `Σ a(n) tⁿ · (1 − t² − 2t³ − t⁴) = (1+t)(1+t+t²)²`. -/
theorem growth_series_33 (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    G *
        (D2 - 2 * X ^ 3 - X ^ 4) = Q2 * Q3 ^ 2 := by
  growth_instance

include h02 h12

/-- `(2,3,∞)`: `Σ a(n) tⁿ · (1 − t² − t³) = (1+t)²(1+t+t²)`. -/
theorem growth_series_23 :
    G * (D2 - X ^ 3) =
      Q2 ^ 2 * Q3 := by
  growth_instance

/-- Coefficient extraction for `(2,3,∞)`. -/
theorem sphere23_values :
    A 0 = 1 ∧ A 1 = 3 ∧ A 2 = 5 ∧ A 3 = 7 ∧ A 4 = 9 ∧
      ∀ n, A (n + 5) = A (n + 3) + A (n + 2) := by
  have H := growth_series_23 cs h01 h02 h12
  ring_nf at H
  have c n := congrArg (coeff n) H
  simp [coeff_mul_X_pow', coeff_X] at c
  repeat' constructor
  any_goals grind [c 0, c 1, c 2, c 3, c 4]
  intro n
  grind [c (n + 5)]

theorem sphere23_rec_fails_at_4 :
    A 4 ≠ A 2 + A 1 := by
  have := sphere23_values cs h01 h02 h12
  omega

/-! ## Padovan -/

/-- Any Padovan sequence agrees with the sphere counts after the initial offset. -/
theorem sphere23_padovan
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) n (hn : 2 ≤ n) :
    A n = pad (n + 5) := by
  have := sphere23_values cs h01 h02 h12
  induction n using Nat.stepInduction 5 with
  | base n h => interval_cases n <;> grind
  | step n ih => simp_all

/-! ## Exponential growth rate -/

include h1 h3 in
/-- `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for `n ≥ 2`, for every real `ρ > 1` with `ρ³ = ρ + 1`. -/
theorem sphere23_growth_bounds n :
    2 * ρ ^ (n + 2) ≤ A (n + 2) ∧ ↑(A (n + 2)) ≤ 4 * ρ ^ (n + 2) := by
  have := sphere23_values cs h01 h02 h12
  induction n using Nat.stepInduction 3 with
  | base n hn =>
    interval_cases n <;> simp_all
    all_goals constructor <;> nlinarith [sq_nonneg (ρ - 1)]
  | step m ih =>
    simp_all only [Nat.forall_lt_succ_right, pow_add]
    grind

end

/-! ## Monotonicity and symmetry of the normal-form counts -/

theorem VT_mono (hp : p ≤ p') (hq : q ≤ q') :
    VT q p r → VT q' p' r := by
  induction r generalizing p q p' q' <;> grind

grind_pattern VT_mono => VT q p r, VT q' p' r

theorem card_NFs_swap (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (forms n).card = (NFs q p n).card := by
  apply card_bijective swap swap_swap.bijective
  grind

/-! ## Exponential bounds from the recursion -/

theorem sumIco_lt_of_lt (hm : 2 ≤ m) (h : m < m') {x : ℝ} (hx : 0 < x) :
    S m x < S m' x :=
by
  apply sum_lt_sum_of_subset (Ico_subset_Ico_right h.le) (i := m) <;> first | grind | bound

theorem sumIco_half_lt (hm : 2 ≤ m) : S m (2⁻¹ : ℝ) < 1 := by
  rw [geom_sum_Ico' (by norm_num) (by omega)]
  bound

section

include hp hq

/-- The reciprocal rate polynomial is strictly decreasing on `(1, ∞)`. -/
theorem rateFn_strictAnti :
    StrictAntiOn (fun x : ℝ => F p q x) (Set.Ioi 1) := by
  intro
  intros
  simp_all
  gcongr <;> aesop

/-- **Existence and uniqueness of the rate**: for `(p, q) ≠ (2, 2)` exactly one `τ > 1` solves
`S_p(τ⁻¹) S_q(τ⁻¹) = 1`. -/
theorem rate_exists_unique (hne : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ F p q τ = 1 := by
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo (f := fun x : ℝ => S p x * S q x) zero_le_one (by fun_prop)
    (show 1 ∈ _ from ⟨by simp [zero_pow_eq], by
      norm_num
      norm_cast
      rw [Nat.one_lt_mul_iff]
      grind⟩)
  have hx1 := one_lt_inv_iff₀.mpr hx
  refine ⟨x⁻¹, ⟨hx1, by simpa using hgx⟩, fun τ hτ => ?_⟩
  apply (rateFn_strictAnti hp hq).injOn hτ.1 hx1
  grind

/-! ## The growth rate of every member -/

/-! ## The rates as a function of `(p, q)` -/

/-- **Strict monotonicity of the rate** in `(p, q)`. -/
theorem rate_lt_rate (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) {τ τ' : ℝ} (hτ : 1 < τ) (hτ' : 1 < τ')
    (heq : F p q τ = 1)
    (heq' : F p' q' τ' = 1) : τ < τ' := by
  have hx := inv_pos.2 (zero_lt_one.trans hτ)
  apply ((rateFn_strictAnti (hp.trans hpp) (hq.trans hqq)).lt_iff_gt hτ' hτ).1
  rw [heq', ← heq]
  rcases hpp.lt_or_eq with h | rfl
  · apply mul_lt_mul (sumIco_lt_of_lt hp h hx) (by gcongr) <;> positivity
  · gcongr
    apply sumIco_lt_of_lt hq ?_ hx
    grind

section

variable {τ}
include hτ heq

include h1 h3 in
/-- **The plastic number is the minimal rate** of the hyperbolic `(p, q, ∞)`, attained only at
`(2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate : ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  wlog h : p ≤ q generalizing p q
  · grind
  have hq3 : 3 ≤ q := by
    by_contra! hq3
    interval_cases q
    interval_cases p
    norm_num at heq
    field_simp at heq
    nlinarith
  have hr := rate23_iff.mpr h3
  by_cases hh : p = 2 ∧ q = 3
  · obtain ⟨rfl, rfl⟩ := hh
    have := (rateFn_strictAnti hp hq).injOn hτ h1
    grind
  · have := rate_lt_rate le_rfl le23 hp hq3
      (by grind) h1 hτ
    grind

/-- **Every rate is below 2.** -/
theorem rate_lt_two : τ < 2 := by
  apply ((rateFn_strictAnti hp hq).lt_iff_gt one_lt_two hτ).1
  simpa only [heq] using mul_lt_one_of_nonneg_of_lt_one_left
    (by positivity) (sumIco_half_lt hp) (sumIco_half_lt hq).le

end

/-- **(12) Monotonicity** in `(p, q)`: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono (hpp : p ≤ p') (hqq : q ≤ q') (h01 : M 0 1 = 0) (h02 : M 0 2 = p)
    (h12 : M 1 2 = q) (h01' : M' 0 1 = 0) (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') n :
    A n ≤ B n := by
  rw [sphere_eq_card cs,
    sphere_eq_card cs']
  gcongr
  grind

include h01 h02g h12g

include hτ heq in
/-- **The growth rate of `(p, q, ∞)`**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate :
    Tendsto sphereRoots atTop
      (𝓝 τ) := by
  have hpos n : (1 : ℝ) ≤ A n := by
    norm_cast
    rw [sphere_eq_card cs]
    simp_all
    use ((false, 0), List.replicate n 0)
    clear h02g h12g
    induction n generalizing p q <;> grind
  let a n : ℝ := A n
  let N := p + q
  let R (f : ℕ → ℝ) :=
    ∀ n, N ≤ n → f n = ∑ j ∈ Ico 1 q, ∑ i ∈ Ico 1 p, f (n - (i + j))
  have hrec : R a := by
    intro n hn
    dsimp [a]
    have h := congrArg (coeff n) (growth_series cs hp hq h01 h02g h12g)
    simp (disch := (simp_all only [mem_Ico, mem_range]; omega))
      [mul_sub, sum_mul, mul_sum, ← pow_add,
        coeff_mul_X_pow', coeff_X, ite_eq_left, ite_eq_right] at h
    exact_mod_cast sub_eq_zero.mp h
  have hτ0 := zero_lt_one.trans hτ
  have hr c : R (c * τ ^ ·) := by
    intro n hn
    simp (disch := (simp_all; omega)) only
      [pow_sub₀ τ hτ0.ne', pow_add, mul_inv, ← inv_pow]
    simp_rw [← mul_sum, ← sum_mul, ← mul_sum]
    grind
  let C := 1 + ∑ m ∈ range N, a m
  have hb n : (τ ^ N)⁻¹ * τ ^ n ≤ a n ∧ a n ≤ C * τ ^ n := by
    induction n using Nat.strong_induction_on
    next n ih =>
      rcases lt_or_ge n N with hn | hn
      · constructor
        · exact le_trans (by bound) (hpos n)
        · nlinarith [hpos n, single_le_sum (f := a) (by bound) (mem_range.2 hn),
            one_le_pow₀ hτ.le (n := n)]
      · simp_all [R]
        constructor <;> gcongr <;> grind
  have hlim c (hc : 0 < c := by positivity) :
      Tendsto (fun n : ℕ => Real.rpow (c * τ ^ n) n⁻¹) atTop (𝓝 τ) := by
    simpa using ((tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat
      (Or.inl hc.ne')).mul_const τ).congr' (by
        filter_upwards [eventually_ne_atTop 0] with n hn
        simp (disch := positivity)  [Real.mul_rpow, Real.pow_rpow_inv_natCast])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim (τ ^ N)⁻¹) (hlim C) ?_ ?_
  all_goals
    intro n
    dsimp
    bound [hb n]

/-- **(13) Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm (h01' : M' 0 1 = 0)
    (h02g' : M' 0 2 = q) (h12g' : M' 1 2 = p) n :
    A n = B n := by
  rw [sphere_eq_card cs,
    sphere_eq_card cs']
  exact card_NFs_swap hp hq

variable (ρ)

include hpq h1 h3 in
/-- **(14) The plastic number bounds the whole family from below**: for every hyperbolic
`(p, q, ∞)`, `2ρⁿ ≤ a(n)` for `n ≥ 2`. -/
theorem sphere_ge_plastic n :
    2 * ρ ^ (n + 2) ≤ A (n + 2) := by
  rw [sphere_eq_card cs]
  obtain ⟨M₀, h₀, h₂, h₃⟩ := triangle_matrix_exists 2 3 le_rfl le23
  have h := (sphere23_growth_bounds M₀.toCoxeterSystem h₀ h₂ h₃ h1 h3 n).1
  rw [sphere_eq_card M₀.toCoxeterSystem] at h
  refine h.trans ?_
  norm_cast
  rcases lt_or_ge q 3 with h | h
  case' inl => rw [card_NFs_swap le_rfl le23]
  all_goals
    gcongr
    grind

end

/-- **The rates tend to 2**: for every `σ < 2`, all `(p, q)` with `p, q ≥ N` have rate `> σ`. -/
theorem rate_tendsto_two σ (hσ : σ < 2) : ∃ N, ∀ p q, N ≤ p → N ≤ q →
    ∀ τ : ℝ, 1 < τ → F p q τ = 1 → σ < τ := by
  rcases le_or_gt σ 1 with h1 | h1
  · exact ⟨0, by grind⟩
  let x := σ⁻¹
  have hσ0 := zero_lt_one.trans h1
  have hy0 := inv_pos.2 hσ0
  have hy1 := inv_lt_one_of_one_lt₀ h1
  have hy2 : 0 < 2 * x - 1 := by
    nlinarith [mul_inv_cancel₀ hσ0.ne']
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hy2 hy1
  refine ⟨max N 2, fun p q hp hq τ hτ heq => ?_⟩
  have hS m (hm : max N 2 ≤ m) : 1 < S m x := by
    nlinarith [geom_sum_Ico_mul_neg x (show 1 ≤ m by omega),
      pow_le_pow_of_le_one hy0.le hy1.le (show N ≤ m by omega)]
  apply ((rateFn_strictAnti (by omega : 2 ≤ p) (by omega : 2 ≤ q)).lt_iff_gt hτ h1).1
  grind [one_lt_mul]

include h01 h02 h12 h1 h3 in
/-- The `(2,3)` limit is an instance of the general rate theorem. -/
theorem sphere23_root_tendsto :
    Tendsto sphereRoots atTop (𝓝 ρ) :=
  sphere_root_tendsto_rate cs le_rfl le23 h01 h02 h12 ρ h1
    (rate23_iff.mpr h3)

/-- **(9)** The plastic number exists and is unique. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  simpa only [rate23_iff] using
    rate_exists_unique (p := 2) (q := 3) le_rfl le23 (by decide)

end TriangleGrowth
