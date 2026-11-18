module

public import Mathlib

@[expose] public noncomputable section

namespace HK

open Filter Topology Real Finset Digraph Function

local notation "Vec" n => Fin n → ℝ
local notation "S" s => (s : Finset _)

/-! ### Definitions -/

inductive Model
  | sbc
  | sbi

def Model.bound m {n} (r : Vec n) (i j : Fin n) :=
  match m with
  | Model.sbc => r i
  | .sbi => r j

def neighbors m {n} (r y : Vec n) i :=
  univ.filter fun j => |y i - y j| ≤ Model.bound m r i j

def proximityDigraph m {n} (r y : Vec n) :=
  { Adj := fun i j => j ∈ neighbors m r y i : Digraph _ }

def adjMatrix m {n} (r y : Vec n) :=
  Matrix.of fun i j => if j ∈ neighbors m r y i then (1 : ℝ) / (neighbors m r y i).card else 0

def step m {n} (r y : Vec n) :=
  (adjMatrix m r y).mulVec y

def traj m {n} (r x₀ : Vec n) t :=
  (step m r)^[t] x₀

def FixedFrom {n} (x : ℕ → Vec n) τ :=
  ∀ t, τ ≤ t → x t = x τ

def PseudoStableAfter {n} x (xinf : Vec n) τ :=
  Tendsto x atTop (𝓝 xinf) ∧
    ∃ F C, F.Nonempty ∧ C.Nonempty ∧ Disjoint F C ∧ F ∪ C = univ ∧
      ∀ t, τ ≤ t →
        (∀ i ∈ F, x t i = xinf i) ∧
        ∀ i ∈ C, x t i < x (t + 1) i ∧ x (t + 1) i < xinf i ∨
          x t i > x (t + 1) i ∧ x (t + 1) i > xinf i

def Conjecture22ForAgents m n :=
  ∀ r x₀ : Vec n, (∀ i, 0 < r i) →
    ∃ τ, ∀ t, τ ≤ t →
      proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r (traj m r x₀ τ)

def Conjecture22For m := ∀ n, Conjecture22ForAgents m n
def Conjecture22 := ∀ m, Conjecture22For m

def Conjecture23ForAgents m n :=
  ∀ r x₀ : Vec n, (∀ i, 0 < r i) →
    ∃ τ, FixedFrom (traj m r x₀) τ ∨ ∃ xinf, PseudoStableAfter (traj m r x₀) xinf τ

def Conjecture23For m := ∀ n, Conjecture23ForAgents m n
def Conjecture23 := ∀ m, Conjecture23For m

def Theorem64ivLiteralForAgents m n :=
  ∀ r x₀ : Vec n, (∀ i, 0 < r i) →
    ∀ τ, (∀ t, τ ≤ t →
        proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r (traj m r x₀ τ)) →
      ∃ t₂, τ ≤ t₂ ∧ ∃ xinf, PseudoStableAfter (traj m r x₀) xinf t₂

def Theorem64ivLiteralFor m := ∀ n, Theorem64ivLiteralForAgents m n

def Theorem64ivForAgents m n :=
  ∀ r x₀ : Vec n, (∀ i, 0 < r i) →
    ∀ τ, (∀ t, τ ≤ t →
        proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r (traj m r x₀ τ)) →
      ∃ t₂, τ ≤ t₂ ∧
        (FixedFrom (traj m r x₀) t₂ ∨ ∃ xinf, PseudoStableAfter (traj m r x₀) xinf t₂)

def Theorem64ivFor m := ∀ n, Theorem64ivForAgents m n
def Theorem64ivLiteral := ∀ m, Theorem64ivLiteralFor m
def Theorem64iv := ∀ m, Theorem64ivFor m

def fvct m {n} (r y : Vec n) :=
  limUnder atTop fun t => (adjMatrix m r y ^ t).mulVec y

def perStepFactor m {n} r (x : _ → Vec n) i t :=
  (x (t + 1) i - fvct m r (x t) i) / (x t i - fvct m r (x t) i)

def equiTopologyDistance {n} (r z : Vec n) i :=
  1 / 2 * sInf {d | ∃ j ≠ i, d = abs (|z i - z j| - r i) ∨ d = abs (|z i - z j| - r j)}

def EquiTopologyNbhd {n} (r z y : Vec n) :=
  ∀ i, (0 < equiTopologyDistance r z i → |y i - z i| < equiTopologyDistance r z i) ∧
    (equiTopologyDistance r z i = 0 → |y i - z i| = equiTopologyDistance r z i)

def sbc7_x0 : Vec 7 := ![0, 38, 69, 84, 99, 130, 168]
def sbc7_r : Vec 7 := ![18, 42, 48, 12, 48, 42, 18]
def sbc7_lim : Vec 7 := ![0, 36, 72, 84, 96, 132, 168]
def sbc7_v : Vec 7 := ![0, 2, -3, 0, 3, -2, 0]

def sbiRate := (1 - √5) / 8

def sbi7_x0 : Vec 7 :=
  ![0, 15 / 2, 10 - goldenRatio / 2, 11, 12 + goldenRatio / 2, 29 / 2, 22]
def sbi7_r : Vec 7 := ![8, 4, 4, 8, 4, 4, 8]
def sbi7_lim : Vec 7 := ![0, 7, 10, 11, 12, 15, 22]
def sbi_v : Vec 7 := ![0, 1, -goldenRatio, 0, goldenRatio, -1, 0]

def sbc6_x0 : Vec 6 := ![0, 22, 37, 103, 118, 140]
def sbc6_r : Vec 6 := ![10, 70, 70, 70, 70, 10]
def sbc6_lim : Vec 6 := ![0, 20, 40, 100, 120, 140]
def sbc6_v : Vec 6 := ![0, 2, -3, 3, -2, 0]

def sbi7b_x0 : Vec 7 :=
  ![0, 71, 100 - goldenRatio, 110, 120 + goldenRatio, 149, 220]
def sbi7b_r : Vec 7 := ![85, 35, 35, 75, 35, 35, 85]
def sbi7b_lim : Vec 7 := ![0, 70, 100, 110, 120, 150, 220]

def sbc5Rate := (1 - √2) / 3
def sbc5_x0 : Vec 5 := ![0, 7, 12 - √2, 19, 24]
def sbc5_r : Vec 5 := ![3, 9, 9, 9, 3]
def sbc5_lim : Vec 5 := ![0, 6, 12, 18, 24]
def sbc5_v : Vec 5 := ![0, 1, -√2, 1, 0]

def sbi6Rate := (13 - √249) / 40
def sbi6_x0 : Vec 6 :=
  ![0, 25 + 10 / 16, 31 + (-5 - √249) / 16, 44 + 8 / 16, 55 + 10 / 16, 90]
def sbi6_r : Vec 6 := ![45, 18, 27, 45 / 2, 27, 54]
def sbi6_lim : Vec 6 := ![0, 25, 31, 44, 55, 90]
def sbi6_v : Vec 6 := ![0, 10 / 16, (-5 - √249) / 16, 8 / 16, 10 / 16, 0]

def sbc9_x0 : Vec 9 := ![0, 22, 37, 103, 118, 140, 210, 280, 300]
def sbc9_r : Vec 9 := ![10, 70, 70, 70, 70, 10, 100, 10, 10]
def sbi8_x0 : Vec 8 :=
  ![0, 60, 71, 100 - goldenRatio, 110, 120 + goldenRatio, 149, 220]
def sbi8_r : Vec 8 := ![85, 1, 35, 35, 75, 35, 35, 85]

def sbi5_r : Vec 5 := ![31, 9, 5, 15, 28]
def sbi5_lim : Vec 5 := ![0, 10, 18, 20, 42]

def sbi5LinearStep (z : Vec 3) : Vec 3 :=
  ![(z 0 + z 2) / 3, (z 0 + z 1 + z 2) / 5, (z 1 + z 2) / 4]

def sbi5Offset ρ t :=
  sbi5LinearStep^[t] ![1 / 3 - ρ, 1 / 5, 0]

def sbi5Lift (z : Vec 3) : Vec 5 := ![0, z 0, z 1, z 2, 0]

def sbi5_x0 ρ := sbi5_lim + sbi5Lift (sbi5Offset ρ 0)

def sbc5Family_r (δ : ℝ) : Vec 5 :=
  ![6 - 3 * δ, 6 + 3 * δ, 6 + 3 * δ, 6 + 3 * δ, 6 - 3 * δ]

def sbc5Family_x0 δ i := sbc5_lim i + δ * sbc5_v i

/-! ### Shared infrastructure -/

set_option maxHeartbeats 3000000

local infixr:35 " & " => And.intro

theorem adj_filter_apply {m} {r y z : Vec n} {i} :
    (adjMatrix m r y).mulVec z i =
      (∑ j, if j ∈ neighbors m r y i then z j else 0) /
      ∑ j, if j ∈ neighbors m r y i then 1 else 0 := by
  simp [-sum_boole, -sum_const, adjMatrix, Matrix.mulVec, dotProduct,
    card_eq_sum_ones, div_eq_inv_mul, mul_sum, ite_mul]

attribute [local simp] Fin.sum_univ_succ sbc7_x0 sbc7_r sbc7_lim sbc7_v sbi7_x0 sbi7_r sbi7_lim sbi_v
  sbc6_x0 sbc6_r sbc6_lim sbc6_v sbi7b_x0 sbi7b_r sbi7b_lim sbc5_x0 sbc5_r sbc5_lim sbc5_v
  sbi6_x0 sbi6_r sbi6_lim sbi6_v sbc9_x0 sbc9_r sbi8_x0 sbi8_r sbi5_r sbi5_lim
  sbi5LinearStep sbi5Lift sbc5Family_r sbc5Family_x0

section
variable {m : Model} {q c : ℝ} {r x₀ y z L v w : Vec n} {x : ℕ → Vec n}

theorem traj_succ : traj m r x₀ (t + 1) = step m r (traj m r x₀ t) :=
  iterate_succ_apply' ..

macro "r_pos" : term => `(fun i => by fin_cases i <;> simp)

set_option hygiene false in
macro "hk_ind" : tactic =>
  `(tactic| (induction t; { funext i; fin_cases i <;> simp [traj] <;> ring }
             rename_i t ih; rw [traj_succ, ih]))

macro "hk_table" ds:Lean.Parser.Tactic.simpLemma* : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [-one_div, neighbors, Model.bound, abs_le, div_mul_eq_mul_div, mul_comm goldenRatio, $ds,*] <;>
    (try constructor) <;> (try intro) <;> nlinarith))

macro "hk_step" : tactic =>
  `(tactic| (
    try simp only [neg_div] at *
    funext i; (try rw [step]); rw [adj_filter_apply]; fin_cases i <;> (
      simp [-sum_boole, -one_div, -div_eq_zero_iff, neighbors, Model.bound, abs_le,
        div_mul_eq_mul_div, mul_comm goldenRatio]
      repeat (first
        | (erw [ite_eq_left]; rotate_right; (try constructor) <;> nlinarith)
        | (erw [ite_eq_right]; rotate_right; intro; nlinarith))
      ring_nf <;> norm_num <;> try ring)))

theorem pow_bounds_of_neg (hq : -1 < q ∧ q < 0) (t : ℕ) : q ≤ q ^ t ∧ q ^ t ≤ 1 := by
  induction t with
  | zero => simp; linarith
  | succ t ih => rw [pow_succ]; constructor <;> nlinarith

def unit_pow (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) t := pow_nonneg h0 t & pow_le_one₀ (n := t) h0 h1

def pow_lt_of_bounds (a b : ℝ) (h : -b < a ∧ a < 0) (ht : 1 ≤ t) :=
  (le_abs_self (a ^ t)).trans_lt (abs_pow a t ▸
    pow_lt_pow_left₀ (abs_lt.2 ⟨h.1, by linarith⟩) (by positivity) (by omega))

@[irreducible] def pow_bounds := pow_bounds_of_neg (q := -1 / 6) (by norm_num)

theorem sbiRate_eq : sbiRate = (1 - goldenRatio) / 4 := by
  unfold sbiRate goldenRatio; ring

def pow_succ_sbi t := (pow_succ sbiRate t).trans (congrArg _ sbiRate_eq)

theorem sbiRate_bounds : -1 < sbiRate ∧ sbiRate < 0 := by
  constructor <;> linarith [sbiRate_eq, one_lt_goldenRatio, goldenRatio_lt_two]

@[irreducible] def phi_bds t :=
  one_lt_goldenRatio & goldenRatio_lt_two & goldenRatio_sq & sbiRate_eq & pow_bounds_of_neg sbiRate_bounds t

def geom_tendsto {L v : Vec n} (hq : -1 < q ∧ q < 0) :=
  show Tendsto (fun t => L + q ^ t • v) atTop (𝓝 L) by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (abs_lt.2 ⟨hq.1, by linarith⟩)).smul_const v).const_add L

theorem nf_nps_of_osc {i} (hc : Tendsto x atTop (𝓝 L)) τ k l
    (hk : τ ≤ k) (hl : τ ≤ l) (h1 : x k i < L i) (h2 : L i < x l i) :
    ¬ FixedFrom x τ ∧ ∀ w, ¬ PseudoStableAfter x w τ := by
  refine ⟨fun hf => by grind [hf k hk, hf l hl], fun _ ⟨hlim, F, C, _, _, _, hFC, h⟩ => ?_⟩
  cases tendsto_nhds_unique hlim hc
  rcases mem_union.1 (hFC ▸ mem_univ i) with hi | hi
  · grind [(h k hk).1 i hi]
  · have hiff : ∀ t ≥ τ, x t i < L i ↔ x τ i < L i :=
      Nat.le_induction .rfl fun t ht _ => by have := (h t ht).2 i hi; grind
    grind [hiff k hk, hiff l hl]

def geom_dyn {x : ℕ → Vec (n + 2)} {L v : Vec (n + 2)}
    (hq : -1 < q ∧ q < 0) (hx : ∀ t, x t = fun i => L i + q ^ t * v i)
    (hv : 0 < v 1 := by simp <;> positivity) :=
  have hc := (geom_tendsto hq).congr fun t => (hx t).symm
  have ho τ := nf_nps_of_osc (i := 1) hc τ (2 * τ + 1) (2 * τ) (by omega) (by omega)
    (by simp only [hx]; nlinarith [Odd.pow_neg ⟨τ, rfl⟩ hq.2])
    (by simp only [hx]; nlinarith [(even_two_mul τ).pow_pos hq.2.ne])
  hc & (fun τ => (ho τ).1) & fun w τ => (ho τ).2 w

theorem adj_eq_of_digraph (hd : proximityDigraph m r y = proximityDigraph m r z) :
    adjMatrix m r y = adjMatrix m r z := by
  simp only [adjMatrix, show neighbors m r y = _ from by
    ext i j; exact .of_eq (congrFun₂ (congrArg Adj hd) i j)]

theorem digraph_const (h : ∀ t, neighbors m r (traj m r x₀ t) = N) t :
    proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r x₀ := by
  unfold proximityDigraph; rw [(h t).trans (h 0).symm]; rfl

def fvct_eq {f : ℕ → Vec n} (h0 : f 0 = y)
    (hs : ∀ k, (adjMatrix m r y).mulVec (f k) = f (k + 1)) (hc : Tendsto f atTop (𝓝 L)) :=
  show fvct m r y = L from (hc.congr fun k => by
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, hs]).limUnder_eq

theorem fvct_from {t : ℕ}
    (hd : ∀ s ≥ t, proximityDigraph m r (traj m r x₀ s) = proximityDigraph m r z)
    (hc : Tendsto (traj m r x₀) atTop (𝓝 L)) : fvct m r (traj m r x₀ t) = L :=
  fvct_eq (by simp) (fun k => by
    dsimp; rw [adj_eq_of_digraph (hd t le_rfl), ← adj_eq_of_digraph (hd (k + t) le_add_self),
      Nat.succ_add, traj_succ, step]) (hc.comp <| tendsto_add_atTop_nat t)

def fvct_of_eigen (hq : -1 < q ∧ q < 0)
    (hs : ∀ u, (adjMatrix m r y).mulVec (fun i => L i + u * v i) = fun i => L i + q * u * v i)
    (hy : y = fun i => L i + c * v i := by rfl) :=
  show fvct m r y = L from fvct_eq (f := fun k i => L i + q ^ k * (c * v i)) (by ext; simp [hy])
    (fun k => by simpa only [← mul_assoc, pow_succ'] using hs (q ^ k * c)) (geom_tendsto hq)

set_option hygiene false in
def perStepFactor_eq {i t} (hx : ∀ t, x t = fun j => L j + q ^ t * v j)
    (hf : ∀ t, fvct m r (x t) = _) (hq : q < 0)
    (hv : v i ≠ 0 := by have := goldenRatio_pos.ne'; fin_cases i <;> simp_all <;> linarith [sqrt_nonneg 249]) :=
  show perStepFactor m r x i t = q by
    have := hq.ne; rw [perStepFactor, hf, hx, hx]; simp only [pow_succ']; field_simp; ring

def refute_t64 (hd : ∀ _s, _ = _) (hn : (∀ _t, ¬ _) ∧ ∀ _w _t, ¬ _)
    (hr : ∀ i, 0 < r i := by exact r_pos) (h : Theorem64ivForAgents m n) :=
  let ⟨t, _, h'⟩ := h r x₀ hr 0 fun s _ => hd s
  h'.elim (hn.1 t) fun ⟨w, hw⟩ => hn.2 w t hw

theorem c23_imp_t64 (h : Conjecture23ForAgents m n) : Theorem64ivForAgents m n :=
  fun r x₀ hr τ _ => let ⟨τ', _⟩ := h r x₀ hr
    ⟨max τ τ', le_max_left .., by unfold FixedFrom PseudoStableAfter at *; grind⟩

theorem lit_imp (h : Theorem64ivLiteralFor m) : Theorem64ivFor m :=
  fun n r x₀ hr τ hτ => (h n r x₀ hr τ hτ).imp fun _ => And.imp_right .inr

def neg_par (hq : q < 0) t := (em (Even t)).imp
  (fun h => h & h.pow_pos hq.ne)
  fun h => h & (Nat.not_even_iff_odd.1 h).pow_neg hq

end

/-! ### SBC-7 and SBI-7 -/

def sbc7_par := neg_par (q := -1 / 6) (by norm_num)
def sbi7_par := neg_par sbiRate_bounds.2

theorem sbc7_closed_form t :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6) ^ t * sbc7_v i := by
  hk_ind; have := pow_bounds t; rw [pow_succ]
  rcases sbc7_par t with ⟨_, _⟩ | ⟨_, _⟩ <;> hk_step

theorem sbc7_neighbors t :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] := by
  have := pow_bounds t; rw [sbc7_closed_form]
  rcases sbc7_par t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> hk_table ht

theorem sbi7_closed_form t :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i := by
  hk_ind; have := phi_bds t; rw [pow_succ_sbi]
  rcases sbi7_par t with ⟨_, _⟩ | ⟨_, _⟩ <;> hk_step

theorem sbi7_neighbors t :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have := phi_bds t; rw [sbi7_closed_form]
  rcases sbi7_par t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> hk_table ht

/-! ### SBC-6 and SBI-7b -/

theorem sbc6_closed_form t :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6) ^ t * sbc6_v i := by
  hk_ind; have := pow_bounds t; rw [pow_succ]; hk_step

theorem sbc6_neighbors t :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := by
  have := pow_bounds t; rw [sbc6_closed_form]; hk_table

theorem sbi7b_closed_form t :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i := by
  hk_ind; have := phi_bds t; rw [pow_succ_sbi]; hk_step

theorem sbi7b_neighbors t :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  have := phi_bds t; rw [sbi7b_closed_form]; hk_table

def d7c := geom_dyn (by norm_num) sbc7_closed_form
def d7i := geom_dyn sbiRate_bounds
  (fun t => (sbi7_closed_form t).trans <| funext fun _ =>
    congrArg (_ + ·) ((div_mul_eq_mul_div ..).trans (mul_div_assoc ..)))
def d6 := geom_dyn (by norm_num) sbc6_closed_form
def d7b := geom_dyn sbiRate_bounds sbi7b_closed_form

theorem tendsto_limits :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) :=
  ⟨d7c.1, d7i.1, d6.1, d7b.1⟩

set_option hygiene false in
macro "alt_nc" j:num n:Lean.Parser.Tactic.simpLemma : term =>
  `(⟨τ + 1, le_self_add, fun h => by
    have := congrFun₂ (congrArg Adj h) 3 $j
    simp only [proximityDigraph, $n] at this
    split_ifs at this <;> simp_all [Nat.even_add_one]⟩)

theorem sbc7_digraph_not_eventually_constant τ :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) :=
  alt_nc 2 sbc7_neighbors

theorem sbi7_digraph_not_eventually_constant τ :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) :=
  alt_nc 1 sbi7_neighbors

theorem sbc6_digraph_constant t :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 :=
  digraph_const sbc6_neighbors t

theorem sbi7b_digraph_constant t :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 :=
  digraph_const sbi7b_neighbors t

theorem not_fixedFrom τ :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  ⟨d7c.2.1 τ, d7i.2.1 τ, d6.2.1 τ, d7b.2.1 τ⟩

theorem not_pseudoStableAfter xinf yinf τ :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ :=
  ⟨d7c.2.2 xinf τ, d7i.2.2 xinf τ, d6.2.2 yinf τ, d7b.2.2 xinf τ⟩

theorem sbc6_fvct t : fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim :=
  fvct_from (fun s _ => sbc6_digraph_constant s) d6.1

theorem sbc6_perStepFactor t i (hi : i ∈ S {1, 2, 3, 4}) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 :=
  perStepFactor_eq sbc6_closed_form sbc6_fvct (by norm_num)

theorem sbc6_perStepFactor_not_tendsto i (hi : i ∈ S {1, 2, 3, 4})
    ρ (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) :=
  fun h => by simp only [sbc6_perStepFactor _ i hi, tendsto_const_nhds_iff] at h; linarith

theorem sbi7b_fvct t : fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim :=
  fvct_from (fun s _ => sbi7b_digraph_constant s) d7b.1

theorem sbi7b_perStepFactor t i (hi : i ∈ S {1, 2, 4, 5}) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate :=
  perStepFactor_eq sbi7b_closed_form sbi7b_fvct sbiRate_bounds.2

theorem sbi7b_perStepFactor_not_tendsto i (hi : i ∈ S {1, 2, 4, 5})
    ρ (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop (𝓝 ρ) :=
  fun h => by simp only [sbi7b_perStepFactor _ i hi, tendsto_const_nhds_iff] at h; linarith [sbiRate_bounds.2]

theorem alternating_fvct t :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim := by
  constructor
  · have := pow_bounds t; rw [sbc7_closed_form]
    refine fvct_of_eigen (q := -1 / 6) (by norm_num) fun u => ?_
    rcases sbc7_par t with ⟨_, _⟩ | ⟨_, _⟩ <;> hk_step
  · have := phi_bds t; rw [sbi7_closed_form]
    refine fvct_of_eigen sbiRate_bounds fun u => ?_
    conv_rhs => rw [sbiRate_eq]
    rcases sbi7_par t with ⟨_, _⟩ | ⟨_, _⟩ <;> hk_step

/-! ### SBC-5 family, SBC-5, and SBI-6 -/

def sbc_sqrt_two_bounds :=
  one_lt_sqrt_two & (by rw [sqrt_lt'] <;> norm_num : √2 < 1.5)

theorem sbc5Rate_bounds : -1 < sbc5Rate ∧ sbc5Rate < 0 := by
  have := sbc_sqrt_two_bounds; unfold sbc5Rate; constructor <;> linarith

@[irreducible] def sbc5_bds {δ} (hδ : (0 : ℝ) ≤ δ) t :=
  let ⟨p0, p1⟩ := pow_bounds_of_neg sbc5Rate_bounds t
  sbc_sqrt_two_bounds & mul_le_mul_of_nonneg_right (sbc5Rate_bounds.1.le.trans p0) hδ &
    mul_le_of_le_one_left hδ p1

theorem sbc5Family_closed_form δ (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) t :
    traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t =
      fun i => sbc5_lim i + (sbc5Rate ^ t * δ) * sbc5_v i := by
  hk_ind; have := sbc5_bds hδ0.le t; rw [pow_succ', mul_assoc]
  generalize sbc5Rate ^ t * δ = w at *; rw [sbc5Rate]; hk_step

theorem sbc5Family_neighbors δ (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) t :
    neighbors .sbc (sbc5Family_r δ) (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  have := sbc5_bds hδ0.le t; rw [sbc5Family_closed_form δ hδ0 hδ1]
  generalize sbc5Rate ^ t * δ = w at *; hk_table

theorem sbc5_near_homogeneous ε (hε : 0 < ε) :
    ∃ r x₀ : Vec 5,
      (∀ i, 0 < r i) ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, proximityDigraph .sbc r (traj .sbc r x₀ t) =
        proximityDigraph .sbc r x₀) ∧
      Tendsto (traj .sbc r x₀) atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom (traj .sbc r x₀) τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter (traj .sbc r x₀) xinf τ) := by
  let δ := min 1 (ε / 4)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left ..; have : δ ≤ ε / 4 := min_le_right ..
  exact ⟨_, _, fun i => by fin_cases i <;> simp <;> linarith,
    fun i j => by fin_cases i <;> fin_cases j <;> simp <;> nlinarith,
    by simp; linarith, digraph_const (sbc5Family_neighbors δ hδ0 hδ1),
    geom_dyn sbc5Rate_bounds
      fun t => (sbc5Family_closed_form δ hδ0 hδ1 t).trans <| funext fun _ => congrArg (_ + ·) (mul_assoc ..)⟩

theorem sbc5_closed_form t :
    traj .sbc sbc5_r sbc5_x0 t = fun i => sbc5_lim i + sbc5Rate ^ t * sbc5_v i := by
  hk_ind; have := sbc5_bds zero_le_one t; simp at this
  rw [pow_succ]; generalize sbc5Rate ^ t = u at *; rw [sbc5Rate]; hk_step

theorem sbc5_neighbors t :
    neighbors .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  have := sbc5_bds zero_le_one t; simp at this; rw [sbc5_closed_form]; hk_table

theorem sbi_sqrt249_bounds : 15 < √249 ∧ √249 < 16 := by
  constructor <;> [rw [lt_sqrt]; rw [sqrt_lt']] <;> norm_num

theorem sbi6Rate_bounds : -1 < sbi6Rate ∧ sbi6Rate < 0 := by
  have := sbi_sqrt249_bounds; unfold sbi6Rate; constructor <;> linarith

@[irreducible] def sbi6_bds t :=
  sbi_sqrt249_bounds & (by unfold sbi6Rate; linarith [sbi_sqrt249_bounds.2] : -3 / 40 < sbi6Rate) &
    pow_bounds_of_neg sbi6Rate_bounds t

theorem sbi6_closed_form t :
    traj .sbi sbi6_r sbi6_x0 t = fun i => sbi6_lim i + sbi6Rate ^ t * sbi6_v i := by
  hk_ind; have := sbi6_bds t; rw [pow_succ]
  generalize sbi6Rate ^ t = u at *; rw [sbi6Rate]; hk_step

theorem sbi6_neighbors t :
    neighbors .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := by
  have := sbi6_bds t; rw [sbi6_closed_form]; hk_table

def d5 := geom_dyn sbc5Rate_bounds sbc5_closed_form
def d6i := geom_dyn sbi6Rate_bounds sbi6_closed_form

theorem small_tendsto :
    Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) ∧
    Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) :=
  ⟨d5.1, d6i.1⟩

theorem small_digraph_constant t :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 ∧
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 :=
  ⟨digraph_const sbc5_neighbors t, digraph_const sbi6_neighbors t⟩

theorem small_not_fixedFrom τ :
    ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ :=
  ⟨d5.2.1 τ, d6i.2.1 τ⟩

theorem small_not_pseudoStableAfter xinf yinf τ :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ :=
  ⟨d5.2.2 xinf τ, d6i.2.2 yinf τ⟩

theorem sbc5_fvct t : fvct .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) = sbc5_lim :=
  fvct_from (fun s _ => digraph_const sbc5_neighbors s) d5.1

theorem sbc5_perStepFactor t i (hi : i ∈ S {1, 2, 3}) :
    perStepFactor .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0) i t = sbc5Rate :=
  perStepFactor_eq sbc5_closed_form sbc5_fvct sbc5Rate_bounds.2

theorem sbi6_fvct t : fvct .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) = sbi6_lim :=
  fvct_from (fun s _ => digraph_const sbi6_neighbors s) d6i.1

theorem sbi6_perStepFactor t i (hi : i ∈ S {1, 2, 3, 4}) :
    perStepFactor .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0) i t = sbi6Rate :=
  perStepFactor_eq sbi6_closed_form sbi6_fvct sbi6Rate_bounds.2

/-! ### Refutations -/

theorem not_conjecture22_sbc_seven : ¬ Conjecture22ForAgents .sbc 7 := fun h => by
  obtain ⟨τ, _⟩ := h sbc7_r sbc7_x0 r_pos; grind [sbc7_digraph_not_eventually_constant τ]

theorem not_conjecture22_sbi_seven : ¬ Conjecture22ForAgents .sbi 7 := fun h => by
  obtain ⟨τ, _⟩ := h sbi7_r sbi7_x0 r_pos; grind [sbi7_digraph_not_eventually_constant τ]

theorem not_theorem64iv_sbc_five : ¬ Theorem64ivForAgents .sbc 5 :=
  refute_t64 (digraph_const sbc5_neighbors) d5.2

theorem not_conjecture23_sbc_five : ¬ Conjecture23ForAgents .sbc 5 :=
  mt c23_imp_t64 not_theorem64iv_sbc_five

theorem not_theorem64iv_sbi_six : ¬ Theorem64ivForAgents .sbi 6 :=
  refute_t64 (digraph_const sbi6_neighbors) d6i.2

theorem not_conjecture23_sbi_six : ¬ Conjecture23ForAgents .sbi 6 :=
  mt c23_imp_t64 not_theorem64iv_sbi_six

theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc := (not_conjecture22_sbc_seven <| · 7)
theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi := (not_conjecture22_sbi_seven <| · 7)
theorem not_conjecture22 : ¬ Conjecture22 := (not_conjecture22_sbc <| · .sbc)

theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc := (not_conjecture23_sbc_five <| · 5)
theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi := (not_conjecture23_sbi_six <| · 6)
theorem not_conjecture23 : ¬ Conjecture23 := (not_conjecture23_sbc <| · .sbc)

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc := (not_theorem64iv_sbc_five <| · 5)
theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi := (not_theorem64iv_sbi_six <| · 6)
theorem not_theorem64iv : ¬ Theorem64iv := (not_theorem64iv_sbc <| · .sbc)

theorem not_theorem64iv_literal_sbc : ¬ Theorem64ivLiteralFor .sbc := mt lit_imp not_theorem64iv_sbc
theorem not_theorem64iv_literal_sbi : ¬ Theorem64ivLiteralFor .sbi := mt lit_imp not_theorem64iv_sbi
theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral := (not_theorem64iv_literal_sbc <| · .sbc)

/-! ### Spectator systems -/

@[irreducible] def sbc9_bds t := pow_bounds t & unit_pow (1 / 5) (by norm_num) (by norm_num) t

theorem sbc9_closed_form t :
    traj .sbc sbc9_r sbc9_x0 t =
      ![0, 20 + 2 * (-1 / 6) ^ t, 40 - 3 * (-1 / 6) ^ t, 100 + 3 * (-1 / 6) ^ t,
        120 - 2 * (-1 / 6) ^ t, 140, 210 + 12 / 11 * ((-1 / 6) ^ t - (1 / 5) ^ t),
        280, 300] := by
  hk_ind; have := sbc9_bds t; rw [pow_succ, pow_succ]; hk_step

theorem sbc9_neighbors t :
    neighbors .sbc sbc9_r (traj .sbc sbc9_r sbc9_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}] := by
  have := sbc9_bds t; rw [sbc9_closed_form]; hk_table

theorem sbc9_spectator_lt t (ht : 1 ≤ t) : traj .sbc sbc9_r sbc9_x0 t 6 < 210 := by
  simp only [sbc9_closed_form, Matrix.cons_val]
  linarith [pow_lt_of_bounds (-1 / 6) (1 / 5) (by norm_num) ht]

theorem spe_inv : goldenRatio⁻¹ = goldenRatio - 1 :=
  inv_eq_of_mul_eq_one_right (by linear_combination goldenRatio_sq)

@[irreducible] def sbi8_bds t := phi_bds t & unit_pow (1 / 4) (by norm_num) (by norm_num) t

theorem sbi8_closed_form t :
    traj .sbi sbi8_r sbi8_x0 t =
      ![0, 60 + goldenRatio⁻¹ * ((1 / 4) ^ t - sbiRate ^ t), 70 + sbiRate ^ t,
        100 - goldenRatio * sbiRate ^ t, 110, 120 + goldenRatio * sbiRate ^ t,
        150 - sbiRate ^ t, 220] := by
  hk_ind; have := sbi8_bds t; rw [spe_inv, pow_succ, pow_succ_sbi]; hk_step

theorem sbi8_neighbors t :
    neighbors .sbi sbi8_r (traj .sbi sbi8_r sbi8_x0 t) =
      ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}] := by
  have := sbi8_bds t; rw [sbi8_closed_form, spe_inv]; hk_table

theorem sbi8_spectator_gt t (ht : 1 ≤ t) : 60 < traj .sbi sbi8_r sbi8_x0 t 1 := by
  simp only [sbi8_closed_form, Matrix.cons_val_one, Matrix.cons_val_zero]
  nlinarith [pow_lt_of_bounds sbiRate (1 / 4) ⟨by linarith [sbiRate_eq, goldenRatio_lt_two], sbiRate_bounds.2⟩ ht,
    inv_pos.2 goldenRatio_pos]

/-! ### Lemmas 4.2 and 4.8 and equi-topology distances -/

theorem proximityDigraph_eq_of_equiTopologyNbhd m {n} (r z y : Vec n)
    (h : EquiTopologyNbhd r z y) : proximityDigraph m r y = proximityDigraph m r z := by
  unfold proximityDigraph; congr; ext i j; simp [neighbors]
  set R := m.bound r i j
  have hd a b (hR : R = r a ∨ R = r b) (hab : b ≠ a) :
      2 * |y a - z a| < abs (|z a - z b| - R) ∨ y a = z a := by
    have ha := h a; rw [equiTopologyDistance] at ha
    generalize hS : Set.ofPred _ = s at ha
    have hb : ∀ d ∈ s, 0 ≤ d := hS ▸ by simp; grind
    have := sInf_nonneg hb
    have := csInf_le ⟨0, hb⟩ (a := abs (|z a - z b| - R)) (hS ▸ ⟨b, hab, by grind⟩)
    grind
  have hR : R = r i ∨ R = r j := by cases m <;> simp [R, Model.bound]
  have := hd i j hR; have := hd j i hR.symm; grind

theorem eventually_constant_of_tendsto m {n} (r x₀ xinf : Vec n)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    ∃ T, ∀ t, T ≤ t → proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r xinf := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 <| eventually_all.2 fun i =>
    Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hconv i) _ (hε i)
  exact ⟨T, fun t ht => proximityDigraph_eq_of_equiTopologyNbhd m r xinf _
    fun i => ⟨fun _ => by simpa [dist_eq] using hT t ht i, by grind [hε i]⟩⟩

theorem fvct_eq_and_equilibrium_of_tendsto m {n} (r x₀ xinf : Vec n)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    (∃ T, ∀ t, T ≤ t → fvct m r (traj m r x₀ t) = xinf) ∧ step m r xinf = xinf := by
  obtain ⟨T, hT⟩ := eventually_constant_of_tendsto m r x₀ xinf hconv hε
  rw [step]; exact ⟨⟨T, fun t ht => fvct_from (fun s hs => hT s (ht.trans hs)) hconv⟩,
    tendsto_nhds_unique (((Continuous.tendsto (by fun_prop) _).comp hconv).congr'
      (eventually_atTop.2 ⟨T, fun t ht => by simp [traj_succ, step, adj_eq_of_digraph (hT t ht)]⟩))
      (hconv.comp <| tendsto_add_atTop_nat 1)⟩

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := by
  constructor <;> intro i <;> (
    rw [equiTopologyDistance]; obtain ⟨j, hj⟩ := exists_ne i
    refine mul_pos (by norm_num) (one_pos.trans_le <| le_csInf ⟨_, j, hj, .inl rfl⟩ ?_)
    rintro _ ⟨k, hk, rfl | rfl⟩ <;> fin_cases i <;> fin_cases k <;> simp_all <;> norm_num)

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ S {2, 3, 4}, equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ S {1, 3, 5}, equiTopologyDistance sbi7_r sbi7_lim i = 0) := by
  constructor <;> intro i hi <;> (
    simp [equiTopologyDistance]; apply IsLeast.csInf_eq
    refine ⟨?_, by rintro _ ⟨_, -, rfl | rfl⟩ <;> positivity⟩
    fin_cases i <;> simp_all) <;>
    [use 3; use 2; use 3; use 3; use 1; use 3] <;> simp <;> norm_num

/-! ### SBI-5 complex modes -/

theorem sbi5Offset_succ : sbi5Offset ρ (t + 1) = sbi5LinearStep (sbi5Offset ρ t) :=
  iterate_succ_apply' ..

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧
    60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0 := by
  simp only [← and_assoc]
  exact intermediate_value_Ioo (by norm_num) (by fun_prop) (by norm_num)

theorem sbi5_offset_bound {ρ} (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) t i :
    |sbi5Offset ρ t i| ≤ (2 / 3) ^ t / 3 := by
  induction t generalizing i with
  | zero => fin_cases i <;> simp [sbi5Offset] <;> grind
  | succ t ih =>
    rw [sbi5Offset_succ, pow_succ]
    fin_cases i <;> simp <;> grind [ih 0, ih 1, ih 2]

@[irreducible] def sbi5_le {ρ} hlo hhi t :=
  have f i := abs_le.1 (sbi5_offset_bound (ρ := ρ) hlo hhi t i)
  pow_le_one₀ (n := t) (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num) & f 0 & f 1 & f 2

theorem sbi5_trajectory ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) t :
    traj .sbi sbi5_r (sbi5_x0 ρ) t = sbi5_lim + sbi5Lift (sbi5Offset ρ t) := by
  induction t with
  | zero => rfl
  | succ t ih => have := sbi5_le hlo hhi t; rw [traj_succ, ih, sbi5Offset_succ]; hk_step

theorem sbi5_neighbors ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) t :
    neighbors .sbi sbi5_r (traj .sbi sbi5_r (sbi5_x0 ρ) t) =
      ![{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}] := by
  have := sbi5_le hlo hhi t; rw [sbi5_trajectory ρ hlo hhi]; hk_table

theorem sbi5_tendsto ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) :
    Tendsto (traj .sbi sbi5_r (sbi5_x0 ρ)) atTop (𝓝 sbi5_lim) :=
  tendsto_pi_nhds.2 fun i => by
    have h j := squeeze_zero_norm (fun t => (norm_eq_abs _).trans_le (sbi5_offset_bound hlo hhi t j)) <| by
      rw [← zero_div 3]; exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)).div_const 3
    simp only [sbi5_trajectory ρ hlo hhi]
    fin_cases i <;> simp <;> first | exact tendsto_const_nhds | simpa using (h _).const_add _

theorem sbi5_digraph_constant ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) t :
    proximityDigraph .sbi sbi5_r (traj .sbi sbi5_r (sbi5_x0 ρ) t) =
      proximityDigraph .sbi sbi5_r (sbi5_x0 ρ) :=
  digraph_const (sbi5_neighbors ρ hlo hhi) t

theorem sbi5_oscillates_every_five ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) t i
    (hi : i ∈ S {1, 2, 3}) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ traj .sbi sbi5_r (sbi5_x0 ρ) k i < sbi5_lim i) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ sbi5_lim i < traj .sbi sbi5_r (sbi5_x0 ρ) k i) := by
  set B := ρ ^ 2 - 47 / 60 * ρ + 3 / 20 with hB
  have hrec s k : sbi5Offset ρ (s + 2) k = (47 / 60 - ρ) * sbi5Offset ρ (s + 1) k - B * sbi5Offset ρ s k := by
    induction s generalizing k with
    | zero => fin_cases k <;> simp [sbi5Offset] <;> nlinarith
    | succ s ih =>
      conv_lhs => erw [sbi5Offset_succ]; rw [funext ih]
      fin_cases k <;> simp [sbi5Offset_succ] <;> ring
  have : 1 / 36 < B := by nlinarith
  have hnz s j : sbi5Offset ρ s j = 0 → sbi5Offset ρ (s + 1) j ≠ 0 := by
    induction s generalizing j with
    | zero => fin_cases j <;> simp [sbi5Offset]; linarith
    | succ s ih => intro h1 h2; have := hrec s j; exact ih _ (by nlinarith) h1
  let j : Fin 3 := ![0, 0, 1, 2, 0] i
  simp only [sbi5_trajectory ρ hlo hhi]
  fin_cases i <;> simp at hi ⊢ <;> constructor <;> (
    by_contra! h
    have : ∀ d : Fin 5, _ := fun d => h (t + d) le_self_add (by omega) & hrec (t + d) j
    simp [Fin.forall_fin_succ, ← add_assoc, j] at this
    apply hnz t j <;> simp [j] <;> nlinarith)

def sbi5_nf_nps {ρ} hlo hhi hp τ :=
  let ⟨⟨k, hk, _, h1⟩, ⟨l, hl, _, h2⟩⟩ := sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by decide)
  nf_nps_of_osc (sbi5_tendsto ρ hlo hhi) τ k l hk hl h1 h2

theorem sbi5_not_fixedFrom ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) τ :
    ¬ FixedFrom (traj .sbi sbi5_r (sbi5_x0 ρ)) τ :=
  (sbi5_nf_nps hlo hhi hp τ).1

theorem sbi5_not_pseudoStableAfter ρ (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) xinf τ :
    ¬ PseudoStableAfter (traj .sbi sbi5_r (sbi5_x0 ρ)) xinf τ :=
  (sbi5_nf_nps hlo hhi hp τ).2 xinf

theorem not_theorem64iv_sbi_five : ¬ Theorem64ivForAgents .sbi 5 :=
  let ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  refute_t64 (sbi5_digraph_constant ρ hlo hhi)
    ⟨sbi5_not_fixedFrom ρ hlo hhi hp, sbi5_not_pseudoStableAfter ρ hlo hhi hp⟩

theorem not_conjecture23_sbi_five : ¬ Conjecture23ForAgents .sbi 5 :=
  mt c23_imp_t64 not_theorem64iv_sbi_five

end HK
