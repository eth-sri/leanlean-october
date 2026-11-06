module
public import Mathlib
@[expose] public section
open PowerSeries Finset Filter Topology
namespace TriangleGrowth
set_option hygiene false
local notation "F" m:max x:max => ∑ i ∈ Ico 1 m, x ^ i
local notation "E" p:max q:max x:max => F p x⁻¹ * F q x⁻¹ = 1
local notation "Ψ" x => x ^ 3 = x + 1
local notation "ν" n:max => #(NF p q n)
local macro "χ" : tactic => `(tactic| rcases v with ⟨e, _ | j, _ | ⟨_ | k, r⟩⟩)
local notation "𝔬" => (0, 0, [])
local notation "G" m:max x:max => ∑ i ∈ range m, x ^ i
local notation "S" c:max n:max => Nat.card {w // CoxeterSystem.length c w = n}
local macro "ω" : term => `(by first | omega | positivity | (simp_all <;> omega) | nlinarith)
local macro "κ" : term => `(key cs ω ω h01 h02 h12)
local macro "γ" : tactic => `(tactic| (have := growth_series cs ω ω h01 h02 h12; simp [sum_range_succ, sum_Ico_eq_sum_range] at this; linear_combination this))
local notation "D" c:max t:max => Tendsto (fun n : ℕ => (S c n : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 t)
local notation "P" c:max => (PowerSeries.mk fun n => (S c n : ℤ))
abbrev R := ℕ × ℕ × List ℕ
def VT : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | a, b, k :: r => 0 < k ∧ k < a ∧ VT b a r
def V (p q) (v : R) := v.1 ≤ 1 ∧ v.2.1 < p ∧ VT q p v.2.2
def len (v : R) := v.1 + v.2.1 + v.2.2.sum
def A (m : ℕ) : R → R
  | (0, 0, r) => (0, 1, r)
  | (0, 1, r) => (0, 0, r)
  | (0, j + 2, r) => (1, j, r)
  | (_ + 1, j, r) => if j + 2 < m then (0, j + 2, r) else (1, 2 * m - j - 3, r)
def C (v : R) := (1 - v.1, v.2)
def sw : R → R
  | (e, 0, (k + 1) :: r) => (e, k + 1, r)
  | (e, j + 1, r) => (e, 0, (j + 1) :: r)
  | v => v
def act (p q : ℕ) : Fin 3 → R → R
  | 0 => A p
  | 1 => sw ∘ A q ∘ sw
  | 2 => C
theorem sw_sw : sw (sw v) = v ∧ sw (C v) = C (sw v) ∧ len (sw v) = len v := by
  χ <;> simp [sw, C, len] <;> omega
def sg m (v : R) := if v.1 = 0 then v.2.1 else 2 * m - 1 - v.2.1
theorem Tpow {f : α → R} {g : Function.End α} (hm : 2 ≤ m) (hi : Function.Injective f) (hf : Function.Semiconj f g (A m ∘ C))
    (h : ∀ x, V m n (f x)) : g ^ m = 1 := by
  funext x
  apply hi
  erw [hf.iterate_right]
  show _ = f x
  obtain ⟨h0, h1, -⟩ := h x
  generalize f x = v at h0 h1 ⊢
  have : ∀ n ≤ m, ∃ w, (A m ∘ C)^[n] v = w ∧ w.1 ≤ 1 ∧ w.2.1 < m ∧ w.2.2 = v.2.2 ∧
      (sg m w = sg m v + 2 * n ∨ sg m w + 2 * m = sg m v + 2 * n) := by
    intro n hn
    induction n with
    | zero => simp [*]
    | succ n ih =>
      obtain ⟨⟨_ | _ | e, _ | _ | j, r⟩, hw, h⟩ := ih ω
      all_goals simp [Function.iterate_succ_apply', hw]
      all_goals grind [A, C, sg]
  have := this m le_rfl
  unfold sg at this; grind
def alt : Fin 3 → Fin 3 → ℕ → List (Fin 3)
  | _, _, 0 => []
  | x, y, n + 1 => x :: alt y x n
theorem alt_rev (n) : ∀ x y, alt x y n = (CoxeterSystem.alternatingWord y x n).reverse := by
  induction n <;> simp_all [alt, CoxeterSystem.alternatingWord]
def tw : Fin 3 → Fin 3 → List ℕ → List (Fin 3)
  | _, _, [] => []
  | a, b, k :: r => alt a 2 k ++ tw b a r
def wd (a b : Fin 3) : R → List (Fin 3)
  | (e, j, r) => List.replicate e 2 ++ alt a 2 j ++ tw b a r
theorem wd_len (a b) : ∀ v, (wd a b v).length = len v
  | (e, j, r) => by
    induction r generalizing e j a b <;> simp_all [wd, tw, len, alt_rev]
    grind
section
variable (h : V p q v)
include h
theorem sw_V (hq : 0 < q) : V q p (sw v) := by
  χ <;> simp_all [sw, V, VT]
theorem wd_sw : wd a b (sw v) = wd b a v := by
  χ <;> simp_all [sw, wd, tw, V, VT, alt]
theorem hA (hm : 2 ≤ p) :
    V p q (A p v) ∧ A p (A p v) = v ∧ len (A p v) ≤ len v + 1 := by
  rcases v with ⟨_ | _ | e, _ | _ | j, r⟩ <;> grind [A, V, len]
theorem act_spec (hp : 2 ≤ p) (hq : 2 ≤ q) (i) :
    V p q (act p q i v) ∧ act p q i (act p q i v) = v ∧ len (act p q i v) ≤ len v + 1 := by
  have := hA (sw_V h ω) hq; have := hA h hp
  fin_cases i <;> unfold act <;> grind [C, V, len, sw_V, sw_sw]

theorem desc : v = 𝔬 ∨ ∃ i, len (act p q i v) < len v := by
  rcases v with ⟨_ | e, _ | _ | j, _ | ⟨_ | _ | k, r⟩⟩ <;>
    simp [Fin.exists_fin_succ, act, sw_sw] <;> grind [V, VT, A, C, sw.eq_1, len]
end
def tl (a b n : ℕ) : Finset (List ℕ) := (if n = 0 then {[]} else ∅) ∪
  ((Ico 1 a).filter (· ≤ n)).attach.biUnion fun i => (tl b a (n - i)).image (List.cons i)
termination_by n
decreasing_by grind
theorem mem_tl (r) : ∀ a b n, r ∈ tl a b n ↔ VT a b r ∧ r.sum = n := by
  induction r <;> intro a b n <;> rw [tl] <;> simp_all [VT] <;> grind
def NF (p q n) := ((range 2 ×ˢ range p).filter fun x => x.1 + x.2 ≤ n).biUnion
  fun x => (tl q p (n - (x.1 + x.2))).map ⟨fun r => (x.1, x.2, r), fun _ _ => by simp⟩
theorem mem_NF : v ∈ NF p q n ↔ V p q v ∧ len v = n := by
  simp [NF, V, len, mem_tl, DFunLike.coe]; grind
def T (a b) := mk fun n => (#(tl a b n) : ℤ)
theorem hTs (a b) : T a b = 1 + F a X * T b a := by
  ext n; rw [T, coeff_mk, tl, card_union_of_disjoint, card_biUnion]
  · simp [card_image_of_injective _ List.cons_injective, ← sum_filter, T, sum_mul, coeff_X_pow_mul']
    grind [sum_attach]
  · grind [disjoint_left, Set.PairwiseDisjoint, Set.Pairwise]
  · split_ifs <;> simp
theorem hN : mk (fun n => (ν n : ℤ)) = (1 + X) * G p X * T q p := by
  ext n; rw [coeff_mk, NF, card_biUnion, sum_filter]
  · simp [T, sum_product, add_mul, sum_mul, mul_sum, coeff_X_pow_mul', ← pow_succ', sum_range_succ, sum_add_distrib, add_comm 1]
  · grind [disjoint_left, Set.PairwiseDisjoint, Set.Pairwise, Function.Embedding.coeFn_mk]
theorem series (hq : 0 < q) : mk (fun n => (ν n : ℤ)) *
    (1 - F p X * F q X) =
      (1 + X) * G p X * G q X := by
  rw [hN, sum_range_eq_add_Ico _ hq]
  linear_combination (1 + X) * G p X * (hTs q p + F q X * hTs p q)
theorem recN (hq : 0 < q) (h : p + q ≤ n) : ν n =
    ∑ j ∈ Ico 1 q, ∑ i ∈ Ico 1 p, ν (n - (i + j)) := by
  have := congrArg (coeff n) (series (p := p) hq)
  simp [mul_sub, sum_mul, mul_sum, ← pow_add, coeff_mul_X_pow', add_mul, ← pow_succ'] at this

  rw [sum_eq_zero (s := range q) fun x hx => sum_eq_zero fun y hy => by grind, sum_congr rfl fun j hj => sum_congr rfl fun i hi => ite_eq_left ω] at this
  zify; linarith
theorem Fle (hm : m ≤ m') {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : F m x ≤ F m' y :=
  (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hm) fun i _ _ => by positivity).trans
    (by gcongr)
theorem Fpos (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) : 0 < F m x :=
  sum_pos (fun i _ => by positivity) ⟨1, ω⟩
theorem Fgeo (hm : 1 ≤ m) (x : ℝ) : F m x * (1 - x) = x - x ^ m := by
  rw [geom_sum_Ico_mul_neg x hm, pow_one]
theorem e23 {τ : ℝ} (h : 0 < τ) : E 2 3 τ ↔ Ψ τ := by
  simp [sum_Ico_eq_sum_range, sum_range_succ]
  field_simp
  grind
section
variable {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
include hp hq
theorem core (hpp : p ≤ p') (hqq : q ≤ q') {τ τ' : ℝ}
    (hτ : 1 < τ) (hτ' : 1 < τ') (e : E p q τ) (e' : E p' q' τ')
    (h : τ' ≤ τ) : p = p' ∧ q = q' ∧ τ = τ' := by
  have hx : 0 < τ⁻¹ := ω
  have hxx : τ⁻¹ ≤ τ'⁻¹ := inv_anti₀ ω h
  have st {m m'} (hm : 2 ≤ m) (hmm : m ≤ m') (he : F m' τ'⁻¹ ≤ F m τ⁻¹) : m = m' ∧ τ = τ' := by
    constructor <;> by_contra hne
    · have := Fle (ω : m + 1 ≤ m') hx.le hxx
      rw [sum_Ico_succ_top ω] at this
      linarith [pow_pos hx m]
    · have : F m τ⁻¹ < F m τ'⁻¹ := by gcongr <;> grind [nonempty_Ico]
      linarith [Fle hmm (hx.le.trans hxx) le_rfl]
  have := Fle hpp hx.le hxx; have := Fle hqq hx.le hxx; have := Fpos hp hx; have := Fpos hq hx
  exact ⟨(st hp hpp ω).1, (st hq hqq ω).1, (st hp hpp ω).2⟩

theorem rate_exists_unique (hpq : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ E p q τ := by
  obtain ⟨x, ⟨x0, x1⟩, hx⟩ := intermediate_value_Ioo zero_le_one
    (by fun_prop : Continuous fun x : ℝ => F p x * F q x).continuousOn ⟨by simp [zero_pow_eq], show 1 < _ by simp; norm_cast; exact Nat.one_lt_mul_iff.2 ⟨ω, ω, ω⟩⟩
  have := (one_lt_inv₀ x0).2 x1
  have e' : E p q x⁻¹ := by simpa
  exact ⟨x⁻¹, ⟨this, e'⟩, fun τ ⟨hτ, e⟩ => by grind [core hp hq le_rfl le_rfl this hτ e', core hp hq le_rfl le_rfl hτ this e]⟩
theorem rate_lt_rate (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) (τ τ' : ℝ) (hτ : 1 < τ) (hτ' : 1 < τ')
    (hτeq : E p q τ)
    (hτeq' : E p' q' τ') : τ < τ' :=
  lt_of_not_ge fun h => by simp_all [core hp hq hpp hqq hτ hτ' hτeq hτeq' h]
variable (τ : ℝ) (hτ : 1 < τ) (hτeq : E p q τ)
include hτ hτeq
theorem plastic_le_rate (ρ) (hρ : 1 < ρ) (hρ3 : Ψ ρ) :
    ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have e := (e23 ω).2 hρ3
  have hne : ¬(p = 2 ∧ q = 2) := by
    rintro ⟨rfl, rfl⟩; simp at hτeq; field_simp at hτeq; nlinarith
  wlog h' : 3 ≤ q generalizing p q
  · grind
  have c := core le_rfl ω hp h' hρ hτ e hτeq
  have : ρ ≤ τ := by grind
  refine ⟨this, fun h => by grind, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); exacts [(core hp hq le_rfl le_rfl hτ hρ hτeq e this).2.2, ω]
theorem rate_lt_two : τ < 2 := by
  by_contra! h
  have (m) (hm : 1 ≤ m) : F m τ⁻¹ < 1 := by
    linarith [Fle (le_refl m) ω (inv_anti₀ ω h), Fgeo hm 2⁻¹, (ω : (0:ℝ) < 2⁻¹ ^ m)]
  nlinarith [this p ω, this q ω, Fpos (x := τ⁻¹) hp ω
]
end
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ Ψ ρ :=
  (existsUnique_congr fun _ => and_congr_right fun h => e23 ω).1
    (rate_exists_unique le_rfl ω ω)
theorem rate_tendsto_two (σ) (hσ : σ < 2) :
    ∃ N : ℕ, ∀ p q, N ≤ p → N ≤ q → ∀ τ : ℝ, 1 < τ →
      E p q τ → σ < τ := by
  wlog h1 : 1 < σ
  · exact ⟨0, by grind⟩
  have hy : σ⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith [inv_strictAnti₀ ω hσ] : 0 < 2 * σ⁻¹ - 1) hy
  refine ⟨N + 1, fun p q hp hq τ hτ e => ?_⟩
  by_contra! h
  have (m) (hm : N + 1 ≤ m) : 1 < F m τ⁻¹ := by
    nlinarith [Fgeo (m := m) ω σ⁻¹, pow_le_pow_of_le_one ω hy.le (ω : N ≤ m), Fle (le_refl m) ω (inv_anti₀ ω h)]
  nlinarith [this p hp, this q hq]
theorem VT_mono (ha : a ≤ a') (hb : b ≤ b') (r) : VT a b r → VT a' b' r := by
  induction r generalizing a b a' b' <;> grind [VT]
theorem NF_mono (hp : p ≤ p') (hq : q ≤ q') : ν n ≤ #(NF p' q' n) :=
  card_le_card fun v => by grind [mem_NF, V, VT_mono]
theorem NF_symm (hp : 0 < p) (hq : 0 < q) : ν n = #(NF q p n) := by
  apply card_nbij' sw sw <;> intro v h <;> simp_all [mem_NF, sw_V, sw_sw]
theorem VT_rep (ha : 2 ≤ a) (hb : 2 ≤ b) (n) : VT a b (List.replicate n 1) := by
  induction n generalizing a b <;> grind [VT]
local notation "B" p:max q:max c:max d:max t:max m:max => (#(NF p q m) : ℝ) ∈ Set.Icc (c * t ^ m) (d * t ^ m)
theorem bnds (hK : p + q ≤ K) (hq : 0 < q) {τ : ℝ} (hτ : 0 < τ)
    (e : E p q τ)
    (h0 : ∀ n, 2 ≤ n → n < K → B p q c d τ n) (n) (hn : 2 ≤ n) : B p q c d τ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn' : n < K
    · grind
    have g (c : ℝ) : c * τ ^ n = ∑ j ∈ Ico 1 q, ∑ i ∈ Ico 1 p, c * τ ^ (n - (i + j)) := by
      rw [← mul_one (c * _), ← e, sum_mul_sum, sum_comm, mul_sum]; simp_rw [mul_sum]
      refine sum_congr rfl fun j hj => sum_congr rfl fun i hi => ?_
      rw [pow_sub₀ _ hτ.ne' ω]; ring
    rw [recN hq ω, g c, g d]; simp_all
    constructor <;> gcongr <;> grind
theorem b23 {ρ : ℝ} (hρ : 1 < ρ) (h3 : Ψ ρ) (n) :
    B 2 3 2 4 ρ (n + 2) := by
  have : #(NF 2 3 2) = 5 ∧ #(NF 2 3 3) = 7 ∧ #(NF 2 3 4) = 9 := by decide +kernel
  refine bnds (K := 5) ω ω ω ((e23 ω).2 h3) (fun n h hn => ?_) _ ω
  interval_cases n <;> simp [this] <;> constructor <;> nlinarith [sq_nonneg (ρ - 1)]
theorem triangle_matrix_exists (p q) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q :=
  by refine ⟨⟨!![1, 0, p; 0, 1, q; p, q, 1], ?_, ?_, ?_⟩, rfl, rfl, rfl⟩ <;> simp [Matrix.IsSymm.ext_iff, Fin.forall_fin_succ] <;> omega
attribute [local simp] CoxeterSystem.wordProd_append CoxeterSystem.wordProd_cons
section
variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
theorem piH (hm : 2 ≤ m)
    (hM : M a 2 = m) (h : V m n v) :
    cs.wordProd (wd a b (A m v)) = cs.simple a * cs.wordProd (wd a b v) := by
  have hb : cs.wordProd (alt a 2 m) = cs.wordProd (alt 2 a m) := by
    simpa [CoxeterSystem.braidWord, M.symmetric 2 a, hM, alt_rev] using cs.wordProd_braidWord_eq 2 a
  rcases v with ⟨_ | _ | e, j, r⟩ <;> simp [V] at h
  · rcases j with _ | _ | j <;> simp [A, wd, alt]
  · rw [A]; split_ifs
    · simp [wd, alt]
    · obtain rfl | rfl : m = j + 2 ∨ m = j + 1 := ω
      · simpa [show 2 * (j + 2) - j - 3 = j + 1 by omega, wd, alt, ← mul_assoc] using hb.symm
      · rcases j with _ | j; · omega
        simpa [show 2 * (j + 2) - (j + 1) - 3 = j by omega, wd, alt, ← mul_assoc] using
          congrArg (cs.simple a * ·) hb
section
variable {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
include hp hq h01 h02 h12
theorem piA (h : V p q v) : ∀ i, cs.wordProd (wd 0 1 (act p q i v)) = cs.simple i * cs.wordProd (wd 0 1 v)
  | 0 => piH cs hp h02 h
  | 1 => by
    have h1 := sw_V h ω
    erw [act, wd_sw (hA h1 hq).1, piH cs hq h12 h1, wd_sw h]
  | 2 => by rcases v with ⟨_ | _ | e, j, r⟩ <;> simp_all [V, act, C, wd]
theorem key : S cs n = ν n := by
  simp_rw [← Nat.card_eq_finsetCard, mem_NF]
  let g : Fin 3 → Function.End {v // V p q v} := fun i v => ⟨act p q i v.1, (act_spec v.2 hp hq i).1⟩
  have inv (i) : g i * g i = 1 := funext fun v => Subtype.ext (act_spec v.2 hp hq i).2.1
  have rev (i j n) (h : (g i * g j) ^ n = 1) : (g j * g i) ^ n = 1 := by
    simpa [h, mul_assoc, inv] using congrArg (· * g j) (mul_pow_mul (g j) (g i) n)
  have h02' := Tpow (g := g 0 * g 2) hp Subtype.val_injective (fun _ => rfl) Subtype.property
  have h12' := Tpow (g := g 1 * g 2) hq
    ((Function.LeftInverse.injective fun _ => sw_sw.1).comp Subtype.val_injective)
    (fun u => by simp [g, act, sw_sw, (· * ·), Mul.mul]) fun v => sw_V v.2 ω
  have hl : M.IsLiftable g := fun i j => by
    fin_cases i <;> fin_cases j <;> simp [inv, h01, h02, h12, M.symmetric _ 0, M.symmetric 2, h02', h12', rev]
  let ev w := cs.lift ⟨g, hl⟩ w ⟨𝔬, ω, ω, trivial⟩

  have ev1 : (ev 1).1 = 𝔬 ∧ ∀ i w, (ev (cs.simple i * w)).1 = act p q i (ev w) := by
    and_intros <;> intros <;> simp [ev] <;> rfl
  have piev (w) : cs.wordProd (wd 0 1 (ev w)) = w := by
    induction w using cs.simple_induction_left with
    | one => simp [ev1.1, wd, alt, tw]
    | mul_simple_left w i h => rw [ev1.2, piA cs hp hq h01 h02 h12 (ev w).2, h]
  have hlen (w) : cs.length w = len (ev w) := le_antisymm
    (by grind [cs.length_wordProd_le (wd 0 1 (ev w)), wd_len])
    (by
      obtain ⟨L, hL, rfl⟩ := cs.exists_isReduced w; rw [hL.eq]; clear hL
      induction L with
      | nil => simp [ev1.1, len]
      | cons i L ih => simp_all; grind [act_spec (ev (cs.wordProd L)).2 hp hq i])
  have sur (v) (hv : V p q v) : ∃ w, (ev w).1 = v := by
    induction v using (measure len).wf.induction with | _ v ih =>
    rcases desc hv with rfl | ⟨i, hi⟩
    · grind
    have := act_spec hv hp hq i
    obtain ⟨w, hw⟩ := ih _ hi this.1
    grind
  refine Nat.card_eq_of_bijective (fun w => ⟨ev w.1, (ev w.1).2, by grind⟩)
    ⟨fun a b h => by grind, fun v => ?_⟩
  obtain ⟨w, hw⟩ := sur _ v.2.1
  exact ⟨⟨w, by grind⟩, by grind⟩
theorem sphere_symm (h01' : M' 0 1 = 0)
    (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n) :
    S cs n = S cs' n := by
  rw [κ, key cs' ω ω h01' h02' h12', NF_symm ω ω]
theorem growth_series :
    P cs *
        (1 - F p X * F q X) =
      (1 + X) * G p X * G q X := by
  simpa [κ] using series ω

theorem sphere_root_tendsto_rate (τ) (hτ : 1 < τ)
    (hτeq : E p q τ) :
    D cs τ := by
  simp only [κ]
  have h1 (n) : (1 : ℝ) ≤ ν n := by
    exact_mod_cast card_pos.2 ⟨(0, 0, List.replicate n 1), (mem_NF ..).2 ⟨⟨ω, ω, VT_rep hq hp n⟩, by simp [len]⟩⟩
  obtain ⟨d, hd⟩ := Finite.exists_le fun n : Fin (p + q + 2) => (ν n : ℝ) ⊔ τ ^ n.1
  have := (h1 0).trans (le_sup_left.trans (hd ⟨0, ω⟩))
  have : 0 < d⁻¹ := ω
  have lim (c) (hc : 0 < c) : Tendsto (fun n : ℕ => c ^ (n : ℝ)⁻¹ * τ) atTop (𝓝 τ) := by
    simpa using ((Real.continuousAt_const_rpow hc.ne').tendsto.comp tendsto_inv_atTop_nhds_zero_nat).mul_const τ
  have h := bnds ω ω ω hτeq fun n _ hn => have := sup_le_iff.1 (hd ⟨n, hn⟩)
    ⟨((inv_mul_le_one₀ ω).2 this.2).trans (h1 n), this.1.trans (le_mul_of_one_le_right ω (one_le_pow₀ hτ.le))⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (lim _ this) (lim d ω) <;>
  filter_upwards [eventually_gt_atTop 1] with n hn <;>
  rw [← Real.pow_rpow_inv_natCast (ω : 0 ≤ τ) (ω : n ≠ 0), ← Real.mul_rpow ω ω] <;> gcongr <;> grind

end
theorem sphere_mono (hp : 2 ≤ p)
    (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q') (h01 : M 0 1 = 0) (h02 : M 0 2 = p)
    (h12 : M 1 2 = q) (h01' : M' 0 1 = 0) (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n) :
    S cs n ≤ S cs' n := by
  simp [κ, key cs' ω ω h01' h02' h12', NF_mono hpp hqq]
theorem sphere_ge_plastic (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2))
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (ρ) (hρ : 1 < ρ) (hρ3 : Ψ ρ) (n) :
    2 * ρ ^ (n + 2) ≤ (S cs (n + 2) : ℝ) := by
  rw [κ]
  apply (b23 hρ hρ3 n).1.trans

  norm_cast
  obtain rfl | h : p = 2 ∨ 3 ≤ p := ω
  · exact NF_mono le_rfl ω
  · rw [NF_symm ω ω]; exact NF_mono h hq
variable (h01 : M 0 1 = 0)
include h01
theorem growth_series_24 (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    P cs *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  γ
theorem growth_series_33 (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    P cs *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  γ
variable (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
include h02 h12
theorem growth_series_23 :
    P cs * (1 - X ^ 2 - X ^ 3) =
      (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  γ
theorem sphere23_values :
    S cs 0 = 1 ∧ S cs 1 = 3 ∧
      S cs 2 = 5 ∧ S cs 3 = 7 ∧
      S cs 4 = 9 ∧
      ∀ n, S cs (n + 5) =
        S cs (n + 3) + S cs (n + 2) := by
  simp only [κ]
  and_intros <;> try decide +kernel
  simp [recN, sum_Ico_eq_sum_range, sum_range_succ]

theorem sphere23_rec_fails_at_4 :
    S cs 4 ≠
      S cs 2 + S cs 1 := by
  simp [sphere23_values cs h01 h02 h12]
theorem sphere23_padovan
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n) (hn : 2 ≤ n) :
    S cs n = pad (n + 5) := by
  have := sphere23_values cs h01 h02 h12
  induction n using Nat.strong_induction_on with | _ n ih =>
  rcases n with _ | _ | _ | _ | _ | n <;> simp_all
variable (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : Ψ ρ)
include hρ hρ3
theorem sphere23_growth_bounds (n) :
    2 * ρ ^ (n + 2) ≤ (S cs (n + 2) : ℝ) ∧
      (S cs (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) :=
  κ ▸ b23 hρ hρ3 n
theorem sphere23_root_tendsto :
    D cs ρ :=
  sphere_root_tendsto_rate cs le_rfl ω h01 h02 h12 ρ hρ ((e23 ω).2 hρ3)
