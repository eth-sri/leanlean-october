module
public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr

@[expose] public section
/-!
# Growth series and growth rates of the triangle Coxeter groups `(p, q, ∞)`

Proofs of the twenty challenge statements for the `(p, q, ∞)` Coxeter family: normal-form
combinatorics and group bijection, generating-function identity, instances `(2,3,∞)`, `(2,4,∞)`,
`(3,3,∞)`, Padovan identification and bounds for `(2,3,∞)`, monotonicity and symmetry in `(p, q)`,
and existence, uniqueness, monotonicity, plastic-number minimality, and limit `2` of the hyperbolic
growth rates.
-/

open PowerSeries Finset Filter Topology CoxeterSystem

namespace TriangleGrowth

/-! ## Normal-form combinatorics and group bijection -/

private abbrev Raw := (Bool × ℕ) × List ℕ

private def dc (v : Raw) := ((!v.1.1, v.1.2), v.2)

private def da (m : ℕ) : Raw → Raw
  | ((b, j), r) =>
    (if b then if j + 2 < m then (false, j + 2) else (true, 2 * m - j - 3)
     else if j = 0 then (false, 1) else if j = 1 then (false, 0) else (true, j - 2), r)

private theorem da_lt {m} (hm : 2 ≤ m) {v} (hv : v.1.2 < m) : (da m v).1.2 < m := by
  rcases v with ⟨⟨_, _⟩, _⟩; grind [da]

private theorem da_da {m} (hm : 2 ≤ m) {v} (hv : v.1.2 < m) : da m (da m v) = v := by
  rcases v with ⟨⟨_ | _, _⟩, _⟩ <;> grind [da]

private theorem T_pow {m} (hm : 2 ≤ m) {u} (hx : u.1.2 < m) : (da m ∘ dc)^[m] u = u := by
  let g (a) : Raw :=
    (let b := if a < 2 * m then a else a - 2 * m
     if b < m then (false, b) else (true, 2 * m - 1 - b), u.2)
  let z := if u.1.1 then 2 * m - 1 - u.1.2 else u.1.2
  have hg (a) (h : a = 0 ∨ a = 2 * m) : g (z + a) = u := by rcases u with ⟨⟨_ | _, _⟩, _⟩ <;> grind
  suffices ∀ k ≤ m, (da m ∘ dc)^[k] u = g (z + 2 * k) from (this m le_rfl).trans (hg _ (.inr rfl))
  intro k hk; induction k with
  | zero => exact (hg 0 (.inl rfl)).symm
  | succ k ih => rw [Function.iterate_succ_apply', ih (by omega)]; clear ih; grind [da, dc]

private def VT : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | m₁, m₂, k :: r => k + 1 < m₁ ∧ VT m₂ m₁ r

private abbrev V (m₁ m₂ : ℕ) (v : Raw) := v.1.2 < m₁ ∧ VT m₂ m₁ v.2
private def len (v : Raw) := v.1.1.toNat + v.1.2 + v.2.sum + v.2.length

private def swap : Raw → Raw
  | ((b, 0), []) => ((b, 0), [])
  | ((b, 0), k :: r) => ((b, k + 1), r)
  | ((b, j + 1), r) => ((b, 0), j :: r)

private theorem swap_swap : Function.Involutive swap := fun v => by
  rcases v with ⟨⟨_, _ | _⟩, _ | _⟩ <;> rfl

private theorem swap_V {m₁ m₂} (hm : 2 ≤ m₂) : ∀ {v}, V m₁ m₂ v → V m₂ m₁ (swap v)
  | ((_, 0), []), _ => ⟨Nat.zero_lt_of_lt hm, trivial⟩
  | ((_, 0), _ :: _), h => h.2
  | ((_, _ + 1), _), h => ⟨Nat.zero_lt_of_lt hm, h.1, h.2⟩

private theorem len_swap (v) : len (swap v) = len v := by
  rcases v with ⟨⟨_, _ | _⟩, _ | _⟩ <;> grind [swap, len]

private def act (p q : ℕ) : Fin 3 → Raw → Raw
  | 0 => da p
  | 1 => swap ∘ da q ∘ swap
  | 2 => dc

private abbrev TSub (m₁ m₂ n : ℕ) := {r : List ℕ // VT m₁ m₂ r ∧ r.sum + r.length = n}
private abbrev NFSub (p q n : ℕ) := {v : Raw // V p q v ∧ len v = n}

private instance (m₁ m₂) : Unique (TSub m₁ m₂ 0) :=
  ⟨⟨⟨[], trivial, rfl⟩⟩, fun ⟨r, _, h⟩ => by cases r <;> grind⟩

private def tailSuccEquiv (m₁ m₂ n : ℕ) :
    TSub m₁ m₂ (n + 1) ≃ (k : {k ∈ range (m₁ - 1) | k ≤ n}) × TSub m₂ m₁ (n - k) :=
  ⟨fun | ⟨[], _, h⟩ => nomatch h
       | ⟨k :: r, ⟨_, hv⟩, _⟩ => ⟨⟨k, by grind⟩, ⟨r, hv, by grind⟩⟩,
    fun ⟨k, r, hv, _⟩ => ⟨k :: r, ⟨by grind, hv⟩, by grind⟩,
    fun | ⟨[], _, h⟩ => nomatch h | ⟨_ :: _, _, _⟩ => rfl, fun _ => rfl⟩

private instance tail_finite (n : ℕ) : ∀ {m₁ m₂}, Finite (TSub m₁ m₂ n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m₁ m₂; rcases n with _ | n
    · infer_instance
    · have := fun k : {k ∈ range (m₁ - 1) | k ≤ n} => ih (n - k) (by grind) (m₁ := m₂) (m₂ := m₁)
      exact (tailSuccEquiv _ _ _).finite_iff.2 inferInstance

private def nfEquiv (p q n : ℕ) :
    NFSub p q n ≃
      (x : {x ∈ (univ : Finset Bool) ×ˢ range p | x.1.toNat + x.2 ≤ n}) ×
        TSub q p (n - (x.1.1.toNat + x.1.2)) :=
  ⟨fun ⟨⟨x, r⟩, _, _⟩ => ⟨⟨x, by grind [len]⟩, ⟨r, ‹_ ∧ _›.2, by grind [len]⟩⟩,
    fun ⟨⟨x, _⟩, r, hv, _⟩ => ⟨(x, r), ⟨by grind, hv⟩, by grind [len]⟩,
    fun _ => rfl, fun _ => rfl⟩

private instance (p q n) : Finite (NFSub p q n) :=
  (nfEquiv p q n).finite_iff.2 inferInstance

section
variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

private def altW (a b : Fin 3) (k : ℕ) := (cs.wordProd (alternatingWord b a k))⁻¹

@[simp] private theorem altW_zero (a b) : altW cs a b 0 = 1 := by simp [altW, alternatingWord]
@[simp] private theorem altW_succ (a b k) : altW cs a b (k + 1) = cs.simple a * altW cs b a k := by
  simp [altW, alternatingWord, wordProd_append, cs.inv_simple]

private def tailP : Fin 3 → Fin 3 → List ℕ → W
  | _, _, [] => 1
  | i, i', k :: r => altW cs i 2 (k + 1) * tailP i' i r

private def piH (i i') (v : Raw) :=
  (if v.1.1 then altW cs 2 i (v.1.2 + 1) else altW cs i 2 v.1.2) * tailP cs i' i v.2

private theorem piH_swap (i i' v) : piH cs i' i (swap v) = piH cs i i' v := by
  rcases v with ⟨⟨_ | _, _ | _⟩, _ | _⟩ <;> simp [swap, piH, tailP, mul_assoc]

private theorem piH_da (i i') {m} (hm : 2 ≤ m) (hM : M i 2 = m) :
    ∀ {v}, v.1.2 < m → piH cs i i' (da m v) = cs.simple i * piH cs i i' v
  | ((false, j), _), _ => by
    rcases j with _ | _ | _ <;> simp [da, piH, ← mul_assoc, cs.simple_mul_simple_self]
  | ((true, j), _), hx => by
    dsimp at hx; by_cases h : j + 2 < m
    · simp [da, h, piH, mul_assoc]
    · simp only [da, ↓reduceIte, h, piH, ← mul_assoc]; congr 1
      rw [← altW_succ]; simp only [altW, inv_inj]
      have hM' := (M.symmetric 2 i).trans hM
      have := cs.prod_alternatingWord_eq_prod_alternatingWord_sub 2 i (j + 2) (by omega)
      rw [hM', show m * 2 - (j + 2) = 2 * m - j - 3 + 1 by omega] at this
      exact this.symm

private theorem sphere_card {p q} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (n) :
    Nat.card {w : W // cs.length w = n} = Nat.card (NFSub p q n) := by
  let NF := {v : Raw // V p q v}
  let g (i) : Function.End NF := fun v => ⟨act p q i v.1,
    match i with
    | 0 => ⟨da_lt hp v.2.1, v.2.2⟩
    | 1 => swap_V hp ⟨da_lt hq (swap_V hq v.2).1, (swap_V hq v.2).2⟩
    | 2 => v.2⟩
  have hg2 (i) (v : NF) : g i (g i v) = v := Subtype.ext <|
    match i with
    | 0 => da_da hp v.2.1
    | 1 => by dsimp [g, act]; rw [swap_swap, da_da hq (swap_V hq v.2).1, swap_swap]
    | 2 => by simp [g, act, dc]
  have hsq (i) : g i * g i = 1 := funext (hg2 i)
  suffices hle : ∀ i j, i ≤ j → (g i * g j) ^ M i j = 1 by
    have hlift : M.IsLiftable g := fun i j => by
      rcases le_total i j with h | h
      · exact hle i j h
      · rw [M.symmetric, ← one_mul ((g i * g j) ^ _), ← hsq j, mul_assoc,
          (show SemiconjBy _ _ _ from (mul_assoc _ _ _).symm).pow_right, hle j i h, one_mul, hsq]
    let nf0 : NF := ⟨((false, 0), []), Nat.zero_lt_of_lt hp, trivial⟩
    let ev (w) : NF := cs.lift ⟨g, hlift⟩ w nf0
    have hev (i w) : ev (cs.simple i * w) = g i (ev w) := by simp [ev]; rfl
    have hev1 : ev 1 = nf0 := by simp [ev]; rfl
    let piA := piH cs 0 1
    have hpiA_act (i) (v : NF) : piA (g i v).1 = cs.simple i * piA v.1 :=
      match i with
      | 0 => piH_da cs 0 1 hp h02 v.2.1
      | 1 => by dsimp [piA, g, act]; rw [piH_swap cs 1 0, piH_da cs 1 0 hq h12 (swap_V hq v.2).1, piH_swap]
      | 2 => by
        cases h : v.1.1.1 <;>
          simp [piA, piH, g, act, dc, h, ← mul_assoc, cs.simple_mul_simple_self]
    have hpiA_ev (w) : piA (ev w).1 = w := by
      induction w using cs.simple_induction_left with
      | one => simp [hev1, nf0, piA, piH, tailP]
      | mul_simple_left w i ih => rw [hev, hpiA_act, ih]
    have hprops (v : NF) : cs.length (piA v.1) ≤ len v.1 ∧ ev (piA v.1) = v := by
      induction hl : len v.1 generalizing v with
      | zero =>
        rcases v with ⟨⟨⟨_ | _, _ | _⟩, _ | _⟩, _⟩ <;>
          simp [len, piA, piH, tailP, hev1, nf0] at hl ⊢
      | succ k ih =>
        have hdec (m a) (r : List ℕ) : len (da m ((false, a + 1), r)) + 1 = len ((false, a + 1), r) := by
          grind [da, len]
        have ⟨i, hi⟩ : ∃ i, len (g i v).1 + 1 = len v.1 :=
          match v with
          | ⟨((false, 0), []), _⟩ => by simp [len] at hl
          | ⟨((false, 0), a :: r), _⟩ =>
            ⟨1, by dsimp [g, act]; rw [len_swap]; exact (hdec q a r).trans (by grind [len])⟩
          | ⟨((false, j + 1), r), _⟩ => ⟨0, hdec p j r⟩
          | ⟨((true, _), _), _⟩ => ⟨2, by simp [g, act, dc, len]; omega⟩
        obtain ⟨ih1, ih2⟩ := ih (g i v) (by omega)
        have hpi : piA v.1 = cs.simple i * piA (g i v).1 := by rw [← hpiA_act, hg2]
        exact ⟨hpi ▸ (cs.length_mul_le _ _).trans (by rw [cs.length_simple]; omega),
          by rw [hpi, hev, ih2, hg2]⟩
    have hlen_ev (w) : cs.length w = len (ev w).1 := by
      refine le_antisymm (by have := (hprops (ev w)).1; rwa [hpiA_ev] at this) ?_
      obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
      rw [hω.eq]; clear hω
      have h0 (m u) : len (da m u) ≤ len u + 1 := by rcases u with ⟨⟨_, _⟩, _⟩; grind [da, len]
      have hg (i) (v : NF) : len (g i v).1 ≤ len v.1 + 1 :=
        match i with
        | 0 => h0 p v.1
        | 1 => by dsimp [g, act]; rw [len_swap, ← len_swap v.1]; exact h0 q _
        | 2 => by cases h : v.1.1.1 <;> simp [g, act, dc, len, h] <;> omega
      induction ω with
      | nil => rw [wordProd_nil, hev1]; rfl
      | cons i ω ih => rw [wordProd_cons, hev, List.length_cons]; exact (hg i (ev _)).trans (by omega)
    exact Nat.card_congr
      ⟨fun w => ⟨_, (ev w.1).2, (hlen_ev w.1).symm.trans w.2⟩,
        fun v => ⟨piA v.1, by rw [hlen_ev, (hprops ⟨_, v.2.1⟩).2]; exact v.2.2⟩,
        fun w => Subtype.ext (hpiA_ev w.1),
        fun v => Subtype.ext (congrArg (·.1) (hprops ⟨_, v.2.1⟩).2)⟩
  intro i j hij; match i, j with
  | 0, 0 | 1, 1 | 2, 2 => rw [M.diagonal, pow_one]; exact hsq _
  | 0, 1 => rw [h01, pow_zero]
  | 0, 2 =>
    rw [h02]; exact funext fun v => Subtype.ext <|
      (Function.Semiconj.iterate_right (f := Subtype.val) (fun _ => rfl) p v).trans (T_pow hp v.2.1)
  | 1, 2 =>
    rw [h12]; exact funext fun v => Subtype.ext <| swap_swap.injective <|
      (Function.Semiconj.iterate_right (f := swap ∘ Subtype.val) (ga := g 1 * g 2) (gb := da q ∘ dc)
        (by rintro ⟨⟨⟨_, _ | _⟩, _ | _⟩, _⟩ <;> exact swap_swap _) q v).trans
        (T_pow hq (swap_V hq v.2).1)
  | 1, 0 | 2, 0 | 2, 1 => omega

end

/-! ## Rate equation helpers -/

private abbrev S (m : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Ico 1 m, x ^ i
private abbrev F (p q : ℕ) (x : ℝ) : ℝ := S p x * S q x

private theorem F_anti {p q} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StrictAntiOn (fun x => F p q x⁻¹) {x | 0 < x} := fun x (hx : 0 < x) y (hy : 0 < y) hxy => by
  have := (inv_lt_inv₀ hy hx).2 hxy
  have hS {m} (hm : 2 ≤ m) : S m y⁻¹ < S m x⁻¹ :=
    sum_lt_sum (fun _ _ => by gcongr) ⟨1, by grind, by simpa⟩
  exact mul_lt_mul'' (hS hp) (hS hq) (by positivity) (by positivity)

private theorem F_two_lt {p q} (hp : 2 ≤ p) (hq : 2 ≤ q) : F p q 2⁻¹ < 1 := by
  have hS {m} (hm : 2 ≤ m) : S m 2⁻¹ < 1 := by
    nlinarith [geom_sum_Ico_mul_neg (2⁻¹ : ℝ) (by omega : 1 ≤ m),
      (by positivity : 0 < (2⁻¹ : ℝ) ^ m), pow_one (2⁻¹ : ℝ)]
  nlinarith [hS hp, hS hq, (by positivity : 0 ≤ S p 2⁻¹)]

private theorem rate23_iff {τ : ℝ} (hτ : 0 < τ) : F 2 3 τ⁻¹ = 1 ↔ τ ^ 3 = τ + 1 := by
  have := hτ.ne'; simp [F, S, sum_Ico_eq_sum_range, sum_range_succ]; field_simp; grind

/-! ## The twenty challenge statements -/

private def triM (p q) (hp : 2 ≤ p) (hq : 2 ≤ q) : CoxeterMatrix (Fin 3) :=
  ⟨!![1, 0, p; 0, 1, q; p, q, 1],
    Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl,
    fun i => by fin_cases i <;> rfl,
    fun i j h => by fin_cases i <;> fin_cases j <;> simp_all <;> omega⟩

/-- **(2) Non-vacuity**: the Coxeter matrix of type `(p, q, ∞)` exists for all `p, q ≥ 2`. -/
theorem triangle_matrix_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q :=
  ⟨triM p q hp hq, rfl, rfl, rfl⟩

section
variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
  (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

/-- **(12) Monotonicity** in `(p, q)`: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (h01' : M' 0 1 = 0) (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n : ℕ) :
    Nat.card {w : W // cs.length w = n} ≤ Nat.card {w : W' // cs'.length w = n} := by
  let rec hvt {a b a' b'} (ha : a ≤ a') (hb : b ≤ b') : ∀ {r}, VT a b r → VT a' b' r
    | [], _ => trivial
    | _ :: _, ⟨h1, hr⟩ => ⟨h1.trans_le ha, hvt hb ha hr⟩
  rw [sphere_card cs hp hq h01 h02 h12 n,
    sphere_card cs' (hp.trans hpp) (hq.trans hqq) h01' h02' h12' n]
  exact Nat.card_le_card_of_injective
    (fun v => ⟨v.1, ⟨v.2.1.1.trans_le hpp, hvt hqq hpp v.2.1.2⟩, v.2.2⟩)
    fun _ _ h => Subtype.ext (congrArg (·.1) h)

/-- **(13) Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (h01' : M' 0 1 = 0) (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n : ℕ) :
    Nat.card {w : W // cs.length w = n} = Nat.card {w : W' // cs'.length w = n} := by
  rw [sphere_card cs hp hq h01 h02 h12 n, sphere_card cs' hq hp h01' h02' h12' n]
  let f {a b} (hb : 2 ≤ b) (v : NFSub a b n) : NFSub b a n :=
    ⟨swap v.1, swap_V hb v.2.1, (len_swap _).trans v.2.2⟩
  exact Nat.card_congr ⟨f hq, f hp,
    fun _ => Subtype.ext (swap_swap _), fun _ => Subtype.ext (swap_swap _)⟩

end

section
variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

section
variable {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
include hp hq h01 h02 h12

/-- **(1) The growth series of the triangle Coxeter group `(p, q, ∞)`.** -/
theorem growth_series :
    (mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - (∑ i ∈ Ico 1 p, X ^ i) * ∑ i ∈ Ico 1 q, X ^ i) =
      (1 + X) * (∑ i ∈ range p, X ^ i) * ∑ i ∈ range q, X ^ i := by
  simp_rw [sphere_card cs hp hq h01 h02 h12]
  let TS (m₁ m₂) : ℤ⟦X⟧ := mk fun n => (Nat.card (TSub m₁ m₂ n) : ℤ)
  have hT (m₁ m₂) : TS m₁ m₂ = 1 + (∑ k ∈ Ico 1 m₁, X ^ k) * TS m₂ m₁ := by
    ext n; rw [sum_Ico_eq_sum_range]
    simp only [TS, map_add, coeff_one, sum_mul, map_sum, coeff_X_pow_mul', coeff_mk]
    cases n with
    | zero => simp
    | succ n =>
      rw [ite_eq_right (Nat.succ_ne_zero _), zero_add, Nat.card_congr (tailSuccEquiv m₁ m₂ n),
        Nat.card_sigma, sum_coe_sort _ fun a => Nat.card (TSub _ _ (_ - a)),
        Nat.cast_sum, sum_filter]
      exact sum_congr rfl fun _ _ => by grind
  let A : ℤ⟦X⟧ := (1 + X) * ∑ j ∈ range p, X ^ j
  have hN : (mk fun n => (Nat.card (NFSub p q n) : ℤ)) = A * TS q p := by
    have h2 : (1 + X : ℤ⟦X⟧) = ∑ b : Bool, X ^ b.toNat := by simp [add_comm]
    ext n; dsimp only [A]
    rw [h2, sum_mul_sum, ← sum_product', sum_mul, map_sum, coeff_mk,
      Nat.card_congr (nfEquiv p q n), Nat.card_sigma,
      sum_coe_sort _ fun x : Bool × ℕ => Nat.card (TSub _ _ (_ - (x.1.toNat + x.2))),
      Nat.cast_sum, sum_filter]
    exact sum_congr rfl fun _ _ => by rw [← pow_add, coeff_X_pow_mul', coeff_mk]
  rw [hN, sum_range_eq_add_Ico (n := q) _ (by omega), pow_zero]
  linear_combination A * hT q p + A * (∑ i ∈ Ico 1 q, X ^ i) * hT p q

/-- **(16) Growth rate of every member**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * ∑ i ∈ Ico 1 q, τ⁻¹ ^ i = 1) :
    Tendsto (fun n => (Nat.card {w : W // cs.length w = n} : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 τ) := by
  let a (n) := Nat.card {w : W // cs.length w = n}
  have ha1 (n) : 1 ≤ a n := by
    let rec hv {x y} (hx : 2 ≤ x) (hy : 2 ≤ y) : ∀ m, VT x y (List.replicate m 0)
      | 0 => trivial
      | m + 1 => ⟨by omega, hv hy hx m⟩
    rw [show a n = _ from sphere_card cs hp hq h01 h02 h12 n]
    exact @Nat.card_pos _
      ⟨⟨((false, 0), List.replicate n 0), ⟨Nat.zero_lt_of_lt hp, hv hq hp n⟩, by simp [len]⟩⟩ _
  let P := Ico 1 p ×ˢ Ico 1 q
  have hrec (n) (hn : p + q ≤ n) : (a n : ℝ) = ∑ u ∈ P, (a (n - (u.1 + u.2)) : ℝ) := by
    have h := (congrArg (coeff n) (growth_series cs hp hq h01 h02 h12)).symm
    rw [show (1 + X : ℤ⟦X⟧) = ∑ e ∈ range 2, X ^ e by simp [sum_range_succ],
      mul_sub, mul_one, map_sub, coeff_mk] at h
    repeat' rw [sum_mul_sum, ← sum_product'] at h
    simp only [mul_sum, ← pow_add, map_sum, coeff_X_pow, coeff_mul_X_pow', coeff_mk] at h
    rw [sum_eq_zero fun _ _ => ite_eq_right (by grind), eq_comm, sub_eq_zero] at h
    exact_mod_cast h.trans (sum_congr rfl fun _ _ => ite_eq_left (by grind))
  have hτ0 : 0 < τ := by linarith
  let c := (τ ^ (p + q))⁻¹
  let C : ℝ := 1 + ∑ m ∈ range (p + q), (a m : ℝ)
  have hbnd (n) : c * τ ^ n ≤ a n ∧ (a n : ℝ) ≤ C * τ ^ n := by
    induction n using Nat.strongRecOn with
    | _ n ih =>
      rcases Nat.lt_or_ge n (p + q) with hn | hn
      · exact ⟨(inv_mul_le_one_of_le₀ (pow_le_pow_right₀ hτ.le hn.le) (by positivity)).trans
          (by exact_mod_cast ha1 n), by
          nlinarith [single_le_sum (f := fun m => (a m : ℝ)) (fun _ _ => by positivity)
            (mem_range.2 hn), one_le_pow₀ (n := n) hτ.le]⟩
      · have hsum : ∑ u ∈ P, τ ^ (n - (u.1 + u.2)) = τ ^ n := by
          rw [← mul_one (τ ^ n), ← hτeq, sum_mul_sum, ← sum_product', mul_sum]
          exact sum_congr rfl fun u hu => by
            rw [pow_sub₀ _ hτ0.ne' (by grind), pow_add, mul_inv, inv_pow, inv_pow]
        rw [hrec n hn, ← hsum, mul_sum, mul_sum]
        exact ⟨by gcongr with u hu; exact (ih _ (by grind)).1,
          by gcongr with u hu; exact (ih _ (by grind)).2⟩
  have htend (A) (hA : 0 < A) : Tendsto (fun n : ℕ => A ^ (n : ℝ)⁻¹ * τ) atTop (𝓝 τ) := by
    simpa using
      (tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat (Or.inl hA.ne')).mul_const τ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (htend c (by positivity))
    (htend C (by positivity)) ?_ ?_ <;> filter_upwards [eventually_ge_atTop 1] with n hn <;>
    rw [← Real.pow_rpow_inv_natCast hτ0.le (by omega : n ≠ 0),
      ← Real.mul_rpow (by positivity) (by positivity)]
  · have := (hbnd n).1; gcongr
  · have := (hbnd n).2; gcongr

end

section
variable (h01 : M 0 1 = 0)
include h01

/-- **(5) `(3,3,∞)`.** -/
theorem growth_series_33 (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    (mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  have h := growth_series cs (by decide) (by decide) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h; linear_combination h

section
variable (h02 : M 0 2 = 2)
include h02

/-- **(4) `(2,4,∞)`.** -/
theorem growth_series_24 (h12 : M 1 2 = 4) :
    (mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  have h := growth_series cs le_rfl (by decide) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h; linear_combination h

section
variable (h12 : M 1 2 = 3)
include h12

/-- **(3) `(2,3,∞)`.** -/
theorem growth_series_23 :
    (mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * (1 - X ^ 2 - X ^ 3) =
      (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  have h := growth_series cs le_rfl (by decide) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h; linear_combination h

/-- **(6) `(2,3,∞)` sphere sizes**: `1, 3, 5, 7, 9`, then `a(n+5) = a(n+3) + a(n+2)`. -/
theorem sphere23_values :
    Nat.card {w : W // cs.length w = 0} = 1 ∧ Nat.card {w : W // cs.length w = 1} = 3 ∧
      Nat.card {w : W // cs.length w = 2} = 5 ∧ Nat.card {w : W // cs.length w = 3} = 7 ∧
      Nat.card {w : W // cs.length w = 4} = 9 ∧
      ∀ n, Nat.card {w : W // cs.length w = n + 5} =
        Nat.card {w : W // cs.length w = n + 3} + Nat.card {w : W // cs.length w = n + 2} := by
  have H := growth_series_23 cs h01 h02 h12
  rw [show (1 + X : ℤ⟦X⟧) ^ 2 * (1 + X + X ^ 2) =
    1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 by ring] at H
  have hc (n) := congrArg (coeff n) H
  simp [mul_sub, coeff_mul_X_pow', coeff_X] at hc
  have := hc 1; have := hc 2; have := hc 3; have := hc 4; simp at *
  refine ⟨by omega, by omega, by omega, by omega, fun n => ?_⟩
  have := hc (n + 5); simp at this; omega

/-- **(7)** The recursion of (6) fails one step earlier: `a(4) ≠ a(2) + a(1)`. -/
theorem sphere23_rec_fails_at_4 :
    Nat.card {w : W // cs.length w = 4} ≠
      Nat.card {w : W // cs.length w = 2} + Nat.card {w : W // cs.length w = 1} := by
  have := sphere23_values cs h01 h02 h12; grind

/-- **(8) Padovan**: `a(n) = Pad(n + 5)` for `n ≥ 2`. -/
theorem sphere23_padovan
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {w : W // cs.length w = n} = pad (n + 5) := by
  have h := sphere23_values cs h01 h02 h12
  induction n using Nat.strongRecOn with
  | _ n _ =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => grind
    | m + 5 => rw [h.2.2.2.2.2 m]; grind

section
variable (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1)
include hρ hρ3

/-- **(10) Two-sided growth bound** for `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ`, `n ≥ 2`. -/
theorem sphere23_growth_bounds (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ Nat.card {w : W // cs.length w = n + 2} ∧
      ↑(Nat.card {w : W // cs.length w = n + 2}) ≤ 4 * ρ ^ (n + 2) := by
  obtain ⟨-, -, h2, h3', h4, hrec⟩ := sphere23_values cs h01 h02 h12
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 | 1 | 2 => simp [h2, h3', h4]; constructor <;> nlinarith [sq_nonneg ρ]
    | m + 3 =>
      have := ih (m + 1) (by omega); have := ih m (by omega)
      rw [hrec m, show ρ ^ (m + 5) = ρ ^ (m + 3) + ρ ^ (m + 2) by linear_combination ρ ^ (m + 2) * hρ3]
      push_cast; clear ih hrec; grind

/-- **(11) Growth rate** of `(2,3,∞)`: `a(n)^{1/n} → ρ`, the plastic number. -/
theorem sphere23_root_tendsto :
    Tendsto (fun n => (Nat.card {w : W // cs.length w = n} : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 ρ) :=
  sphere_root_tendsto_rate cs le_rfl (by decide) h01 h02 h12 ρ hρ
    ((rate23_iff (by linarith)).2 hρ3)

end
end
end
end

/-- **(14) The plastic number bounds the whole family from below**: for every hyperbolic
`(p, q, ∞)`, `2ρⁿ ≤ a(n)` for `n ≥ 2`. -/
theorem sphere_ge_plastic {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2))
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ Nat.card {w : W // cs.length w = n + 2} := by
  let cs23 := (triM 2 3 le_rfl (by decide)).toCoxeterSystem
  refine (sphere23_growth_bounds cs23 rfl rfl rfl ρ hρ hρ3 n).1.trans (Nat.cast_le.2 ?_)
  rcases Nat.lt_or_ge 2 p with hp3 | _
  · rw [sphere_symm cs23 (cs23.reindex (Equiv.swap 0 1)) le_rfl (by decide)
      rfl rfl rfl rfl rfl rfl]
    exact sphere_mono _ cs (by decide) le_rfl hp3 hq rfl rfl rfl h01 h02 h12 _
  · exact sphere_mono cs23 cs le_rfl (by decide) hp (by grind : 3 ≤ q) rfl rfl rfl h01 h02 h12 _

end

section
variable {p q : ℕ}

/-- **(17) The rate is strictly increasing** in `(p, q)`. -/
theorem rate_lt_rate {p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) (τ τ' : ℝ) (hτ : 1 < τ) (hτ' : 1 < τ')
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * ∑ i ∈ Ico 1 q, τ⁻¹ ^ i = 1)
    (hτeq' : (∑ i ∈ Ico 1 p', τ'⁻¹ ^ i) * ∑ i ∈ Ico 1 q', τ'⁻¹ ^ i = 1) : τ < τ' := by
  have h0 : 0 < τ := zero_lt_one.trans hτ
  have hSlt {m m'} (hm1 : 1 ≤ m) (hm : m < m') : S m τ⁻¹ < S m' τ⁻¹ :=
    sum_lt_sum_of_subset (i := m) (by grind) (by grind) (by simp)
      (by positivity) fun _ _ _ => by positivity
  have hSpos {m} (hm : 2 ≤ m) : 0 < S m τ⁻¹ := by simpa [S] using hSlt le_rfl hm
  refine ((F_anti (hp.trans hpp) (hq.trans hqq)).lt_iff_gt (zero_lt_one.trans hτ') h0).1
    ((hτeq'.trans hτeq.symm).trans_lt ?_)
  rcases hpp.lt_or_eq with hp' | rfl
  · nlinarith [hSlt (by omega) hp', show S q τ⁻¹ ≤ S q' τ⁻¹ by dsimp [S]; gcongr, hSpos hq, hSpos hp]
  · nlinarith [hSlt (by omega) (by grind : q < q'), hSpos hp]

section
variable (hp : 2 ≤ p) (hq : 2 ≤ q)
include hp hq

/-- **(15) The rate equation** has exactly one root `τ > 1` for every hyperbolic `(p, q)`. -/
theorem rate_exists_unique (hpq : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * ∑ i ∈ Ico 1 q, τ⁻¹ ^ i = 1 := by
  have g1 : 1 < F p q 1⁻¹ := by
    simp [F, S]
    exact_mod_cast (by
      rcases eq_or_ne p 2 with rfl | _
      · grind
      · nlinarith [show 2 ≤ p - 1 by omega, show 1 ≤ q - 1 by omega] : 1 < (p - 1) * (q - 1))
  obtain ⟨τ, hτ, hfx⟩ := intermediate_value_Icc' (f := fun τ => F p q τ⁻¹) (by norm_num)
    (by fun_prop (disch := intro _ hx; linarith [hx.1])) ⟨(F_two_lt hp hq).le, g1.le⟩
  exact ⟨τ, ⟨hτ.1.lt_of_ne fun h => by simp [← h] at hfx; linarith, hfx⟩,
    fun y ⟨hy1, hy2⟩ => (F_anti hp hq).injOn (zero_lt_one.trans hy1)
      (zero_lt_one.trans_le hτ.1) (hy2.trans hfx.symm)⟩

section
variable (τ : ℝ) (hτ : 1 < τ) (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * ∑ i ∈ Ico 1 q, τ⁻¹ ^ i = 1)
include hτ hτeq

/-- **(18) The plastic number is the minimal rate**: `ρ ≤ τ`, with equality exactly for
`(p, q) = (2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have hρ23 : F 2 3 ρ⁻¹ = 1 := (rate23_iff (zero_lt_one.trans hρ)).2 hρ3
  by_cases h : (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)
  · have h23 : F 2 3 τ⁻¹ = 1 := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hτeq, (mul_comm _ _).trans hτeq]
    have hτρ := (F_anti le_rfl (by decide)).injOn (zero_lt_one.trans hτ)
      (zero_lt_one.trans hρ) (h23.trans hρ23.symm)
    exact ⟨hτρ.ge, iff_of_true hτρ h⟩
  · have hlt : ρ < τ := by
      rcases (show 3 ≤ q ∨ 3 ≤ p by
        by_contra!; obtain ⟨rfl, rfl⟩ : p = 2 ∧ q = 2 := by omega
        simp [mul_self_eq_one_iff] at hτeq; grind) with h3 | h3
      · exact rate_lt_rate le_rfl (by decide) hp h3 (by grind) ρ τ hρ hτ hρ23 hτeq
      · exact rate_lt_rate (by decide) le_rfl h3 hq (by grind) ρ τ hρ hτ
          ((mul_comm _ _).trans hρ23) hτeq
    exact ⟨hlt.le, iff_of_false hlt.ne' h⟩

/-- **(19)** Every rate is below `2`. -/
theorem rate_lt_two : τ < 2 :=
  ((F_anti hp hq).lt_iff_gt (zero_lt_two (α := ℝ)) (zero_lt_one.trans hτ)).1
    ((F_two_lt hp hq).trans_eq hτeq.symm)

end
end
end

/-- **(9)** The plastic number exists and is unique. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  obtain ⟨ρ, ⟨h1, h2⟩, hu⟩ := rate_exists_unique (q := 3) le_rfl (by decide) (by decide)
  exact ⟨ρ, ⟨h1, (rate23_iff (zero_lt_one.trans h1)).1 h2⟩,
    fun y ⟨hy1, hy2⟩ => hu y ⟨hy1, (rate23_iff (zero_lt_one.trans hy1)).2 hy2⟩⟩

/-- **(20)** The rates tend to `2` as `p, q → ∞`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) :
    ∃ N, ∀ p q, N ≤ p → N ≤ q → ∀ τ : ℝ, 1 < τ →
      (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * ∑ i ∈ Ico 1 q, τ⁻¹ ^ i = 1 → σ < τ := by
  rcases le_or_gt σ 1 with h1 | h1
  · exact ⟨0, fun _ _ _ _ _ hτ _ => h1.trans_lt hτ⟩
  have hσ0 := zero_lt_one.trans h1
  have hy1 : σ⁻¹ < 1 := (inv_lt_one₀ hσ0).2 h1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < 2 * σ⁻¹ - 1 by linarith [(inv_lt_inv₀ zero_lt_two hσ0).2 hσ]) hy1
  refine ⟨N + 2, fun p q hp hq τ hτ heq => ?_⟩
  have hS {m} (hm : N + 2 ≤ m) : 1 < S m σ⁻¹ := by
    nlinarith [geom_sum_Ico_mul_neg σ⁻¹ (by omega : 1 ≤ m),
      pow_le_pow_of_le_one (by positivity) hy1.le (by omega : N ≤ m), pow_one σ⁻¹]
  refine ((F_anti (by omega) (by omega)).lt_iff_gt
    (zero_lt_one.trans hτ) hσ0).1 (heq.trans_lt ?_)
  nlinarith [hS hp, hS hq]

end TriangleGrowth
