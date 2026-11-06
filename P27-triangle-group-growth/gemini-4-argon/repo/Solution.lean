import CoxeterGrowth.TriangleNF

open PowerSeries Finset Filter Topology

namespace TriangleGrowth

local notation "S" cs:max n:max => Nat.card {w : _ // CoxeterSystem.length cs w = n}
local notation "GS" cs:max => PowerSeries.mk fun n => (S cs n : ℤ)
local notation "SI" m:max x:max => ∑ i ∈ Ico 1 m, x ^ i
local notation "SR" m:max x:max => ∑ i ∈ range m, x ^ i
local notation "RF" p:max q:max x:max => SI p x * SI q x
local notation "RE" p:max q:max τ:max => RF p q τ⁻¹ = 1

@[simp] def da (m : ℕ) : ℕ × ℕ → ℕ × ℕ
  | (0, 0) => (0, 1)
  | (0, 1) => (0, 0)
  | (0, j + 2) => (1, j)
  | (_ + 1, j) => if j + 2 < m then (0, j + 2) else (1, 2 * m - j - 3)

@[simp] def dc (x : ℕ × ℕ) : ℕ × ℕ := (1 - x.1, x.2)

@[simp] abbrev HV (m : ℕ) (x : ℕ × ℕ) : Prop := x.1 ≤ 1 ∧ x.2 < m

theorem da_HV {m : ℕ} (hm : 2 ≤ m) : ∀ {x : ℕ × ℕ}, HV m x → HV m (da m x)
  | (0, 0), _ | (0, 1), _ | (0, _ + 2), _ => by dsimp; omega
  | (_ + 1, j), hx => by have := hx.2; dsimp; split_ifs <;> dsimp <;> omega

theorem da_da {m : ℕ} : ∀ {x : ℕ × ℕ}, HV m x → da m (da m x) = x
  | (0, 0), _ | (0, 1), _ => rfl
  | (0, _ + 2), hx | (_ + 1, _), hx => by
    have := hx.1; have := hx.2; dsimp
    split_ifs <;> dsimp <;> (try split_ifs) <;> ext <;> dsimp <;> omega

abbrev sig (m : ℕ) (x : ℕ × ℕ) : ℕ := if x.1 = 0 then x.2 else 2 * m - 1 - x.2

theorem sig_T {m : ℕ} (hm : 2 ≤ m) : ∀ {x : ℕ × ℕ}, HV m x →
    sig m (da m (dc x)) = if sig m x + 2 < 2 * m then sig m x + 2 else sig m x + 2 - 2 * m
  | (0, _), hx => by dsimp at *; split_ifs <;> dsimp [sig] at * <;> omega
  | (e + 1, 0), hx | (e + 1, 1), hx | (e + 1, _ + 2), hx => by
    have := hx.1; have := hx.2; dsimp at *
    simp [sig, show 1 - (e + 1) = 0 by omega]; split_ifs <;> omega

theorem T_pow {m : ℕ} (hm : 2 ≤ m) {x : ℕ × ℕ} (hx : HV m x) :
    (fun y => da m (dc y))^[m] x = x := by
  have hT : ∀ n ≤ m, HV m ((fun y => da m (dc y))^[n] x) ∧
      sig m ((fun y => da m (dc y))^[n] x) =
        if sig m x + 2 * n < 2 * m then sig m x + 2 * n else sig m x + 2 * n - 2 * m := by
    intro n hn; induction n with
    | zero => exact ⟨hx, by have := hx.2; dsimp [sig]; split_ifs <;> omega⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨da_HV hm ⟨by dsimp; omega, h1.2⟩, (sig_T hm h1).trans ?_⟩
      rw [h2]; have := hx.2; dsimp [sig]; split_ifs <;> omega
  obtain ⟨h1, h2⟩ := hT m le_rfl
  have := h1.1; have := h1.2; have := hx.1; have := hx.2
  unfold sig at h2; split_ifs at h2 <;> ext <;> omega

abbrev Raw := (ℕ × ℕ) × List ℕ

@[simp] def VT : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | m₁, m₂, k :: r => 0 < k ∧ k < m₁ ∧ VT m₂ m₁ r

@[simp] abbrev V (m₁ m₂ : ℕ) (v : Raw) : Prop := HV m₁ v.1 ∧ VT m₂ m₁ v.2

@[simp] def len (v : Raw) : ℕ := v.1.1 + v.1.2 + v.2.sum

def swap : Raw → Raw
  | ((e, 0), []) => ((e, 0), [])
  | ((e, 0), k :: r) => ((e, k), r)
  | ((e, j + 1), r) => ((e, 0), (j + 1) :: r)

theorem swap_V {m₁ m₂ : ℕ} : ∀ {v : Raw}, V m₁ m₂ v → ∀ (_ : 0 < m₂ := by omega), V m₂ m₁ (swap v)
  | ((_, 0), []), h, hm => ⟨⟨h.1.1, hm⟩, trivial⟩
  | ((_, 0), _ :: _), h, _ => ⟨⟨h.1.1, h.2.2.1⟩, h.2.2.2⟩
  | ((_, _ + 1), _), h, hm => ⟨⟨h.1.1, hm⟩, Nat.succ_pos _, h.1.2, h.2⟩

theorem swap_swap {m₁ m₂ : ℕ} : ∀ v : Raw, VT m₁ m₂ v.2 → swap (swap v) = v
  | ((_, 0), []), _ | ((_, _ + 1), _), _ | ((_, 0), (_ + 1) :: _), _ => rfl
  | ((_, 0), 0 :: _), h => absurd h.1 (Nat.lt_irrefl 0)

theorem len_swap : ∀ v : Raw, len (swap v) = len v
  | ((_, 0), []) => rfl
  | ((_, 0), _ :: _) | ((_, _ + 1), _) => by simp [swap]; omega

abbrev actH (m : ℕ) (v : Raw) : Raw := (da m v.1, v.2)
abbrev actC (v : Raw) : Raw := (dc v.1, v.2)

@[simp] def act (p q : ℕ) : Fin 3 → Raw → Raw
  | 0, v => actH p v
  | 1, v => swap (actH q (swap v))
  | 2, v => actC v

theorem swap_actC : ∀ v : Raw, swap (actC v) = actC (swap v)
  | ((_, 0), []) | ((_, 0), _ :: _) | ((_, _ + 1), _) => rfl

theorem act_V {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) : ∀ (i : Fin 3) {v : Raw}, V p q v →
    V p q (act p q i v)
  | 0, _, h => ⟨da_HV hp h.1, h.2⟩
  | 1, _, h => by have h1 := swap_V h; exact swap_V ⟨da_HV hq h1.1, h1.2⟩
  | 2, _, h => ⟨⟨by dsimp; omega, h.1.2⟩, h.2⟩

theorem act_act {p q : ℕ} (hq : 2 ≤ q) : ∀ (i : Fin 3) {v : Raw}, V p q v →
    act p q i (act p q i v) = v
  | 0, _, h => Prod.ext (da_da h.1) rfl
  | 1, v, h => by
    have h1 := swap_V h
    show swap (actH q (swap (swap (actH q (swap v))))) = v
    rw [swap_swap (actH q (swap v)) h1.2,
      show actH q (actH q (swap v)) = swap v from Prod.ext (da_da h1.1) rfl, swap_swap v h.2]
  | 2, _, h => Prod.ext (by have := h.1.1; ext; (dsimp; omega); rfl) rfl

theorem len_actH_le {m : ℕ} : ∀ {v : Raw}, v.1.2 < m → len (actH m v) ≤ len v + 1
  | ((0, 0), _), _ | ((0, 1), _), _ | ((0, _ + 2), _), _ => by dsimp; omega
  | ((_ + 1, _), _), h => by dsimp at *; split_ifs <;> dsimp <;> omega

theorem len_act_le {p q : ℕ} (hq : 2 ≤ q) : ∀ (i : Fin 3) {v : Raw}, V p q v →
    len (act p q i v) ≤ len v + 1
  | 0, _, h => len_actH_le h.1.2
  | 1, v, h => by
    show len (swap (actH q (swap v))) ≤ len v + 1
    rw [len_swap, ← len_swap v]
    exact len_actH_le (swap_V h).1.2
  | 2, _, h => by have := h.1.1; dsimp at *; omega

theorem descent {p q : ℕ} :
    ∀ {v : Raw}, V p q v → v = ((0, 0), []) ∨ ∃ i : Fin 3, len (act p q i v) + 1 = len v
  | ((0, 0), []), _ => .inl rfl
  | ((0, 0), 0 :: _), h => absurd h.2.1 (Nat.lt_irrefl 0)
  | ((0, 0), 1 :: _), _ | ((0, 0), (_ + 2) :: _), _ => .inr ⟨1, by
      show len (swap (actH q _)) + 1 = _
      rw [len_swap]; dsimp [swap]; omega⟩
  | ((0, 1), _), _ | ((0, _ + 2), _), _ => .inr ⟨0, by dsimp; omega⟩
  | ((_ + 1, _), _), h => .inr ⟨2, by have := h.1.1; dsimp at *; omega⟩

theorem iter_ac (m : ℕ) : ∀ (n : ℕ) (v : Raw),
    (fun u => actH m (actC u))^[n] v = ((fun y => da m (dc y))^[n] v.1, v.2)
  | 0, _ => rfl
  | n + 1, _ => iter_ac m n _

theorem iter_bc {p q : ℕ} : ∀ (n : ℕ) (u : Raw), VT p q u.2 →
    (fun v => act p q 1 (act p q 2 v))^[n] (swap u) =
      swap ((fun y => da q (dc y))^[n] u.1, u.2)
  | 0, _, _ => rfl
  | n + 1, u, hu => by
    change (fun v => act p q 1 (act p q 2 v))^[n] (swap (actH q (swap (actC (swap u))))) = _
    rw [← swap_actC, swap_swap (actC u) hu, iter_bc n (actH q (actC u)) hu]; rfl

@[simp] theorem mem_ite_empty {α : Type*} {x : α} {P : Prop} [Decidable P] {s : Finset α} :
    x ∈ (if P then s else ∅) ↔ P ∧ x ∈ s := by
  split_ifs with h <;> simp [h]

abbrev bimg {α β : Type*} [DecidableEq α] (l u : ℕ)
    (F : ℕ → Finset β) (f : ℕ → β → α) (n : ℕ) : Finset α :=
  (range (n + 1)).biUnion fun k => if l ≤ k ∧ k < u then (F (n - k)).image (f k) else ∅

abbrev ser (f : ℕ → ℕ) : ℤ⟦X⟧ := mk fun n => (f n : ℤ)

theorem ser_bimg {α β : Type*} [DecidableEq α] [DecidableEq β]
    {l u : ℕ} {F : ℕ → Finset β} {f : ℕ → β → α}
    (hf : ∀ k y k' y', f k y = f k' y' ↔ k = k' ∧ y = y' := by simp [Prod.ext_iff, and_assoc]) :
    ser (fun n => (bimg l u F f n).card) =
      (∑ i ∈ Ico l u, (X : ℤ⟦X⟧) ^ i) * ser fun m => (F m).card := by
  ext n
  rw [ser, coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun a b =>
    coeff a (∑ i ∈ Ico l u, (X : ℤ⟦X⟧) ^ i) * coeff b (ser fun m => (F m).card), bimg, card_biUnion]
  · push_cast
    refine sum_congr rfl fun k _ => ?_
    have hinj : Function.Injective (f k) := fun x y h => ((hf k x k y).1 h).2
    split_ifs with h <;> simp [h, ser, coeff_X_pow, card_image_of_injective _ hinj]
  · intro k _ k' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro _ hx hx'
    rw [mem_ite_empty, mem_image] at hx hx'
    obtain ⟨_, y, _, rfl⟩ := hx; obtain ⟨_, y', _, he⟩ := hx'
    exact hne ((hf k' y' k y).1 he).1.symm

def tails (m₁ m₂ n : ℕ) : Finset (List ℕ) :=
  if _ : n = 0 then {[]} else
    (range (n + 1)).biUnion fun k =>
      if _ : 1 ≤ k ∧ k < m₁ then (tails m₂ m₁ (n - k)).image (List.cons k) else ∅
termination_by n
decreasing_by omega

theorem mem_tails : ∀ (r : List ℕ) (m₁ m₂ n : ℕ),
    r ∈ tails m₁ m₂ n ↔ VT m₁ m₂ r ∧ r.sum = n
  | r, m₁, m₂, n => by
    rw [tails]
    rcases r with _ | ⟨k, r⟩ <;> rcases n with _ | n <;> (simp [dite_eq_ite]; try omega)
    rw [mem_tails r]
    by_cases h : VT m₂ m₁ r <;> (simp [h]; try omega)

abbrev NFs (p q : ℕ) :=
  bimg 0 2 (bimg 0 p (tails q p) Prod.mk) fun e x => ((e, x.1), x.2)

@[simp] theorem mem_NFs {p q n : ℕ} : ∀ {v : Raw}, v ∈ NFs p q n ↔ V p q v ∧ len v = n
  | ((_, _), r) => by
    by_cases h : VT q p r <;> (simp [NFs, bimg, Prod.exists, and_assoc, mem_tails, h]; try omega)

theorem tails_series (m₁ m₂ : ℕ) :
    ser (fun n => (tails m₁ m₂ n).card) = 1 + SI m₁ (X : ℤ⟦X⟧) * ser (fun n => (tails m₂ m₁ n).card) := by
  rw [← ser_bimg (f := List.cons)]
  ext (_ | n) <;> (simp only [ser, map_add, coeff_one, coeff_mk]; rw [tails]; simp [bimg, dite_eq_ite])

section Coxeter

open CoxeterSystem

structure IsTri (M : CoxeterMatrix (Fin 3)) (p q : ℕ) : Prop where
  hp : 2 ≤ p
  hq : 2 ≤ q
  h01 : M 0 1 = 0
  h02 : M 0 2 = p
  h12 : M 1 2 = q

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W) {p q : ℕ}
  (hT : IsTri M p q)

def alt (i i' : Fin 3) (k : ℕ) : W := (cs.wordProd (alternatingWord i' i k))⁻¹

@[simp] theorem alt_zero (i i' : Fin 3) : alt cs i i' 0 = 1 := by simp [alt, alternatingWord]

theorem alt_succ (i i' : Fin 3) (k : ℕ) : alt cs i i' (k + 1) = cs.simple i * alt cs i' i k := by
  simp [alt, alternatingWord_succ, wordProd_append]

@[simp] def headP (i : Fin 3) (x : ℕ × ℕ) : W := cs.simple 2 ^ x.1 * alt cs i 2 x.2

@[simp] def tailP : Fin 3 → Fin 3 → List ℕ → W
  | _, _, [] => 1
  | i, i', k :: r => alt cs i 2 k * tailP i' i r

@[simp] abbrev piH (i i' : Fin 3) (v : Raw) : W := headP cs i v.1 * tailP cs i' i v.2

theorem piH_swap (i i' : Fin 3) : ∀ v : Raw, piH cs i' i (swap v) = piH cs i i' v
  | ((_, 0), []) | ((_, 0), _ :: _) | ((_, _ + 1), _) => by simp [swap, mul_assoc]

theorem headP_da (i : Fin 3) {m : ℕ} (hm : 2 ≤ m) (hM : M i 2 = m) :
    ∀ {x : ℕ × ℕ}, HV m x → headP cs i (da m x) = cs.simple i * headP cs i x
  | (0, 0), _ | (0, 1), _ | (0, _ + 2), _ => by simp [alt_succ]
  | (e + 1, j), hx => by
    dsimp at hx
    obtain rfl : e = 0 := by omega
    by_cases h : j + 2 < m
    · simp [h, alt_succ]
    · simp only [da, h, ↓reduceIte, headP, zero_add, pow_one, ← alt_succ]
      rw [alt, alt, cs.prod_alternatingWord_eq_prod_alternatingWord_sub 2 i (j + 2)
        (by rw [M.symmetric, hM]; omega), M.symmetric, hM,
        show m * 2 - (j + 2) = 2 * m - j - 3 + 1 by omega]

@[simp] abbrev piA (v : Raw) : W := piH cs 0 1 v

include hT in
theorem piA_act (i : Fin 3) {v : Raw} (hv : V p q v) :
    piA cs (act p q i v) = cs.simple i * piA cs v := by
  have := hT.hq
  match i with
  | 0 =>
    unfold piA piH act actH
    rw [headP_da cs 0 hT.hp hT.h02 hv.1, mul_assoc]
  | 1 =>
    unfold piA act
    rw [piH_swap cs 1 0, ← piH_swap cs 0 1 v]
    unfold piH actH
    rw [headP_da cs 1 hT.hq hT.h12 (swap_V hv).1, mul_assoc]
  | 2 =>
    rcases v with ⟨⟨_ | _ | e, j⟩, r⟩
    · simp [mul_assoc]
    · simp [← mul_assoc]
    · have := hv.1.1; dsimp at this; omega

abbrev NF (p q : ℕ) := {v : Raw // V p q v}

def gen (i : Fin 3) : Function.End (NF p q) :=
  fun v => ⟨act p q i v.1, act_V hT.hp hT.hq i v.2⟩

theorem gen_pow (i : Fin 3) : ∀ (n : ℕ) (v : NF p q),
    (((gen hT i * gen hT 2) ^ n) v).1 = (fun u => act p q i (act p q 2 u))^[n] v.1
  | 0, _ => rfl
  | n + 1, v => by rw [pow_succ]; exact gen_pow i n _

theorem pow_swap_of_sq {N : Type*} [Monoid N] {x y : N} (hx : x * x = 1) (n : ℕ)
    (h : (x * y) ^ n = 1) : (y * x) ^ n = 1 := by
  rw [← one_mul ((y * x) ^ n), ← hx, mul_assoc, SemiconjBy.pow_right (mul_assoc x y x).symm n,
    h, one_mul, hx]

theorem gen_liftable : M.IsLiftable (gen hT) := by
  have := hT.hq
  have hsq (i : Fin 3) : gen hT i * gen hT i = 1 := funext fun v => Subtype.ext (act_act hT.hq i v.2)
  have h0 : (gen hT 0 * gen hT 2) ^ p = 1 :=
    funext fun v => Subtype.ext <| (gen_pow hT 0 p v).trans
      ((iter_ac p p v.1).trans (Prod.ext (T_pow hT.hp v.2.1) rfl))
  have h1 : (gen hT 1 * gen hT 2) ^ q = 1 :=
    funext fun v => Subtype.ext <| (gen_pow hT 1 q v).trans <| by
      have hu := swap_V v.2
      rw [← swap_swap v.1 v.2.2, iter_bc q _ hu.2, T_pow hT.hq hu.1, swap_swap v.1 v.2.2]; rfl
  intro i j
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 => rw [M.diagonal, pow_one]; exact hsq _
  | 0, 1 => rw [hT.h01, pow_zero]
  | 1, 0 => rw [M.symmetric, hT.h01, pow_zero]
  | 0, 2 => rw [hT.h02]; exact h0
  | 2, 0 => rw [M.symmetric, hT.h02]; exact pow_swap_of_sq (hsq 0) p h0
  | 1, 2 => rw [hT.h12]; exact h1
  | 2, 1 => rw [M.symmetric, hT.h12]; exact pow_swap_of_sq (hsq 1) q h1

noncomputable def ev (w : W) : NF p q :=
  cs.lift ⟨gen hT, gen_liftable hT⟩ w ⟨((0, 0), []), ⟨⟨by decide, Nat.zero_lt_of_lt hT.hp⟩, trivial⟩⟩

@[simp] theorem ev_one : (ev cs hT 1).1 = ((0, 0), []) := by
  unfold ev; rw [map_one]; rfl

@[simp] theorem ev_simple_mul (i : Fin 3) (w : W) :
    (ev cs hT (cs.simple i * w)).1 = act p q i (ev cs hT w).1 := by
  unfold ev; rw [map_mul, cs.lift_apply_simple]; rfl

theorem piA_props {v : Raw} (hv : V p q v) :
    cs.length (piA cs v) ≤ len v ∧ (ev cs hT (piA cs v)).1 = v := by
  rcases descent hv with rfl | ⟨i, hi⟩
  · simp
  · have hv' := act_V hT.hp hT.hq i hv
    have hvv := act_act hT.hq i hv
    obtain ⟨ih1, ih2⟩ := piA_props hv'
    have hpi : piA cs v = cs.simple i * piA cs (act p q i v) := by
      rw [← piA_act cs hT i hv', hvv]
    refine ⟨?_, by rw [hpi, ev_simple_mul, ih2, hvv]⟩
    have := cs.length_mul_le (cs.simple i) (piA cs (act p q i v))
    rw [← hpi, cs.length_simple] at this; omega
termination_by len v
decreasing_by omega

theorem wordProd_props : ∀ ω : List (Fin 3),
    piA cs (ev cs hT (cs.wordProd ω)).1 = cs.wordProd ω ∧ len (ev cs hT (cs.wordProd ω)).1 ≤ ω.length
  | [] => by simp
  | i :: ω => by
    obtain ⟨ih1, ih2⟩ := wordProd_props ω
    rw [wordProd_cons, ev_simple_mul, piA_act cs hT i (ev cs hT _).2, ih1]
    have := len_act_le hT.hq i (ev cs hT (cs.wordProd ω)).2
    exact ⟨rfl, by simp only [List.length_cons]; omega⟩

include hT in
theorem sphere_eq_card (n : ℕ) : S cs n = (NFs p q n).card := by
  have ev_props (w : W) : piA cs (ev cs hT w).1 = w ∧ cs.length w = len (ev cs hT w).1 := by
    have hle := (piA_props cs hT (ev cs hT w).2).1
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    obtain ⟨h1, h2⟩ := wordProd_props cs hT ω
    rw [h1] at hle
    exact ⟨h1, le_antisymm hle (hω.eq ▸ h2)⟩
  rw [← Nat.card_eq_finsetCard]
  simp only [(ev_props _).2]
  exact Nat.card_congr ⟨fun w => ⟨(ev cs hT w.1).1, mem_NFs.2 ⟨(ev cs hT w.1).2, w.2⟩⟩,
    fun v => ⟨piA cs v.1, by rw [(piA_props cs hT (mem_NFs.1 v.2).1).2, (mem_NFs.1 v.2).2]⟩,
    fun w => Subtype.ext (ev_props w.1).1,
    fun v => Subtype.ext ((piA_props cs hT (mem_NFs.1 v.2).1).2)⟩

end Coxeter

variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
  (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

theorem growth_series {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) :
    GS cs * (1 - RF p q (X : ℤ⟦X⟧)) = (1 + X) * SR p (X : ℤ⟦X⟧) * SR q (X : ℤ⟦X⟧) := by
  rw [show GS cs = ser fun n => (NFs p q n).card by ext n; simp [ser, sphere_eq_card cs ⟨hp, hq, h01, h02, h12⟩],
    NFs, ser_bimg, ser_bimg, ← range_eq_Ico, ← range_eq_Ico,
    show SR 2 (X : ℤ⟦X⟧) = 1 + X by simp [sum_range_succ],
    show SR q (X : ℤ⟦X⟧) = 1 + SI q X by rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), pow_zero]]
  linear_combination (1 + X) * SR p (X : ℤ⟦X⟧) * tails_series q p +
    (1 + X) * SR p (X : ℤ⟦X⟧) * SI q (X : ℤ⟦X⟧) * tails_series p q

def triM (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : CoxeterMatrix (Fin 3) where
  M := !![1, 0, p; 0, 1, q; p, q, 1]
  isSymm := Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
  diagonal i := by fin_cases i <;> rfl
  off_diagonal i i' h := by fin_cases i <;> fin_cases i' <;> simp_all <;> omega

theorem triangle_matrix_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q :=
  ⟨triM p q hp hq, rfl, rfl, rfl⟩

theorem growth_series_23 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    GS cs * (1 - X ^ 2 - X ^ 3) = (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  have h := growth_series cs (by decide) (by decide) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h; linear_combination h

theorem growth_series_24 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    GS cs * (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  have h := growth_series cs (by decide) (by decide) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h; linear_combination h

theorem growth_series_33 (h01 : M 0 1 = 0) (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    GS cs * (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  have h := growth_series cs (by decide) (by decide) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h; linear_combination h

theorem sphere23_values (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    S cs 0 = 1 ∧ S cs 1 = 3 ∧ S cs 2 = 5 ∧ S cs 3 = 7 ∧ S cs 4 = 9 ∧
      ∀ n : ℕ, S cs (n + 5) = S cs (n + 3) + S cs (n + 2) := by
  have c (n : ℕ) := congrArg (coeff n) (by linear_combination growth_series_23 cs h01 h02 h12 :
    GS cs - GS cs * X ^ 2 - GS cs * X ^ 3 = 1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4)
  simp [coeff_mul_X_pow', coeff_X_pow, coeff_X] at c
  have c0 := c 0; have c1 := c 1; have c2 := c 2; have c3 := c 3; have c4 := c 4
  dsimp at c0 c1 c2 c3 c4
  refine ⟨?_, ?_, ?_, ?_, ?_, fun n => by have := c (n + 5); simp at this; omega⟩ <;> omega

theorem sphere23_rec_fails_at_4 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    S cs 4 ≠ S cs 2 + S cs 1 := by
  obtain ⟨-, h1, h2, -, h4, -⟩ := sphere23_values cs h01 h02 h12; omega

theorem sphere23_padovan (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    S cs n = pad (n + 5) := by
  obtain ⟨-, -, h2, h3, h4, hrec⟩ := sphere23_values cs h01 h02 h12
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | _ | _ | m <;> intro hn <;>
      first | omega | (simp [h2, h3, h4, hpr, hp0, hp1, hp2]; done) |
        rw [hrec m, ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega), ← hpr (m + 7)]

theorem sphere23_growth_bounds (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (S cs (n + 2) : ℝ) ∧ (S cs (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  obtain ⟨-, -, h2, h3', h4, hrec⟩ := sphere23_values cs h01 h02 h12
  have : 1.25 < ρ ∧ ρ < 1.5 ∧ ρ ^ 4 = ρ ^ 2 + ρ :=
    ⟨by nlinarith [sq_nonneg ρ, sq_nonneg (ρ + 1)], by nlinarith [sq_nonneg ρ, sq_nonneg (ρ + 1)],
      by linear_combination ρ * hρ3⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m <;>
      first | (simp [h2, h3', h4]; constructor <;> nlinarith) | skip
    obtain ⟨_, _⟩ := ih (m + 1) (by omega)
    obtain ⟨_, _⟩ := ih m (by omega)
    change 2 * ρ ^ (m + 5) ≤ (S cs (m + 5) : ℝ) ∧ (S cs (m + 5) : ℝ) ≤ 4 * ρ ^ (m + 5)
    rw [hrec m, show ρ ^ (m + 5) = ρ ^ (m + 3) + ρ ^ (m + 2) by linear_combination ρ ^ (m + 2) * hρ3]
    push_cast; constructor <;> linarith

theorem VT_mono : ∀ {r : List ℕ} {m₁ m₂ m₁' m₂' : ℕ},
    m₁ ≤ m₁' → m₂ ≤ m₂' → VT m₁ m₂ r → VT m₁' m₂' r
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: _, _, _, _, _, h1, h2, h => ⟨h.1, h.2.1.trans_le h1, VT_mono h2 h1 h.2.2⟩

theorem sphere_mono {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (h01' : M' 0 1 = 0) (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n : ℕ) :
    S cs n ≤ S cs' n := by
  rw [sphere_eq_card cs ⟨hp, hq, h01, h02, h12⟩,
    sphere_eq_card cs' ⟨hp.trans hpp, hq.trans hqq, h01', h02', h12'⟩]
  exact card_le_card fun v hv => by
    rw [mem_NFs] at hv ⊢
    exact ⟨⟨⟨hv.1.1.1, hv.1.1.2.trans_le hpp⟩, VT_mono hqq hpp hv.1.2⟩, hv.2⟩

theorem sphere_symm {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (h01' : M' 0 1 = 0) (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n : ℕ) :
    S cs n = S cs' n := by
  have hle {a b : ℕ} (hb : 1 ≤ b) : (NFs a b n).card ≤ (NFs b a n).card :=
    card_le_card_of_injOn swap
      (fun v hv => by
        obtain ⟨h1, h2⟩ := mem_NFs.1 hv
        exact mem_NFs.2 ⟨swap_V h1, (len_swap v).trans h2⟩)
      (fun v hv w hw h => by
        rw [← swap_swap v (mem_NFs.1 hv).1.2, h, swap_swap w (mem_NFs.1 hw).1.2])
  rw [sphere_eq_card cs ⟨hp, hq, h01, h02, h12⟩, sphere_eq_card cs' ⟨hq, hp, h01', h02', h12'⟩]
  exact le_antisymm (hle (by omega)) (hle (by omega))

theorem sphere_ge_plastic {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2))
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (S cs (n + 2) : ℝ) := by
  rw [ne_eq, Prod.mk.injEq] at hpq
  let cs23 := (triM 2 3 le_rfl (by decide)).toCoxeterSystem
  refine (sphere23_growth_bounds cs23 rfl rfl rfl ρ hρ hρ3 n).1.trans (Nat.cast_le.2 ?_)
  rcases Nat.lt_or_ge 2 p with hp3 | hp2
  · let cs32 := (triM 3 2 (by decide) le_rfl).toCoxeterSystem
    rw [sphere_symm cs23 cs32 le_rfl (by decide) rfl rfl rfl rfl rfl rfl]
    exact sphere_mono cs32 cs (by decide) le_rfl hp3 hq rfl rfl rfl h01 h02 h12 _
  · exact sphere_mono cs23 cs le_rfl (by decide) hp (by omega : 3 ≤ q) rfl rfl rfl h01 h02 h12 _

theorem sumIco_lt_of_lt {m m' : ℕ} (hm : 1 ≤ m) (h : m < m') {x : ℝ} (hx : 0 < x) :
    SI m x < SI m' x :=
  sum_lt_sum_of_subset (Ico_subset_Ico_right h.le) (mem_Ico.2 ⟨hm, h⟩)
    (by simp) (pow_pos hx m) fun j _ _ => pow_nonneg hx.le j

theorem rateFn_strictMono {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StrictMonoOn (fun x : ℝ => RF p q x) (Set.Ici 0) :=
  fun _ (hx : 0 ≤ _) _ _ hxy => mul_lt_mul''
    (sum_lt_sum (fun i _ => pow_le_pow_left₀ hx hxy.le i) ⟨1, mem_Ico.2 ⟨le_rfl, hp⟩, by simpa⟩)
    (sum_lt_sum (fun i _ => pow_le_pow_left₀ hx hxy.le i) ⟨1, mem_Ico.2 ⟨le_rfl, hq⟩, by simpa⟩)
    (by positivity) (by positivity)

theorem lt_of_RF_lt {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : RF p q a⁻¹ < RF p q b⁻¹) : b < a :=
  (inv_lt_inv₀ ha hb).1 (((rateFn_strictMono hp hq).lt_iff_lt (inv_nonneg.2 ha.le) (inv_nonneg.2 hb.le)).1 h)

theorem eq_of_RF_eq {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : RF p q a⁻¹ = RF p q b⁻¹) : a = b :=
  inv_inj.1 ((rateFn_strictMono hp hq).injOn (inv_nonneg.2 ha.le) (inv_nonneg.2 hb.le) h)

theorem rate_exists_unique {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ RE p q τ := by
  have : 1 ≤ p - 1 ∧ 1 ≤ q - 1 ∧ 3 ≤ (p - 1) + (q - 1) := by
    rw [ne_eq, Prod.mk.injEq] at hpq; omega
  have g0 : RF p q (0 : ℝ) = 0 := by
    rw [sum_eq_zero fun i hi => zero_pow (by rw [mem_Ico] at hi; omega), zero_mul]
  have g1 : (1 : ℝ) < RF p q (1 : ℝ) := by simp [← Nat.cast_mul]; nlinarith
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc zero_le_one (f := fun x => RF p q x) (by fun_prop)
    ⟨g0.le.trans zero_le_one, g1.le⟩
  simp only at hgx
  have hx0 : 0 < x := hx.1.lt_or_eq.resolve_right fun h => by rw [← h, g0] at hgx; linarith
  have hx1 : x < 1 := hx.2.lt_or_eq.resolve_right fun h => by rw [h] at hgx; linarith
  refine ⟨x⁻¹, ⟨(one_lt_inv₀ hx0).2 hx1, by rw [inv_inv]; exact hgx⟩, fun τ hτ =>
    eq_of_RF_eq hp hq (zero_lt_one.trans hτ.1) (inv_pos.2 hx0) (by rw [inv_inv, hτ.2, hgx])⟩

theorem rate23_iff {τ : ℝ} (hτ : 0 < τ) : RE 2 3 τ ↔ τ ^ 3 = τ + 1 := by
  have hid : τ ^ 3 * RF 2 3 τ⁻¹ = τ + 1 := by
    simp [sum_Ico_eq_sum_range, sum_range_succ]; field_simp
  rw [← mul_right_inj' (by positivity : τ ^ 3 ≠ 0), hid, mul_one, eq_comm]

theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  simpa only [and_congr_right fun h => rate23_iff (zero_lt_one.trans h)]
    using rate_exists_unique (p := 2) (q := 3) le_rfl (by decide) (by decide)

theorem VT_ones : ∀ (n : ℕ) {m₁ m₂ : ℕ}, 2 ≤ m₁ → 2 ≤ m₂ → VT m₁ m₂ (List.replicate n 1)
  | 0, _, _, _, _ => trivial
  | n + 1, _, _, h1, h2 => ⟨Nat.one_pos, h1, VT_ones n h2 h1⟩

theorem sphere_root_tendsto_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : RE p q τ) :
    Tendsto (fun n : ℕ => (S cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  have hT : IsTri M p q := ⟨hp, hq, h01, h02, h12⟩
  have hpos : ∀ n, 1 ≤ S cs n := fun n => by
    rw [sphere_eq_card cs hT]
    exact card_pos.2 ⟨((0, 0), List.replicate n 1),
      mem_NFs.2 ⟨⟨⟨Nat.zero_le 1, Nat.zero_lt_of_lt hp⟩, VT_ones n hq hp⟩, by simp⟩⟩
  have hrec : ∀ n, p + q ≤ n → S cs n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, S cs (n - (i + j)) := by
    intro n hn
    have h := congrArg (coeff n) (growth_series cs hp hq h01 h02 h12)
    rw [show (1 + X : ℤ⟦X⟧) = SR 2 X by simp [sum_range_succ], mul_sub, mul_one, map_sub,
      coeff_mk, sum_mul_sum] at h
    simp only [mul_sum, sum_mul, ← pow_add, map_sum, coeff_mul_X_pow', coeff_mk, coeff_X_pow] at h
    rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => ite_eq_left (by rw [mem_Ico] at hi hj; omega),
      sum_eq_zero fun a ha => sum_eq_zero fun b hb => sum_eq_zero fun c hc =>
        ite_eq_right (by rw [mem_range] at ha hb hc; omega), sub_eq_zero] at h
    exact_mod_cast h
  have hτ0 : 0 < τ := by linarith
  let c := (τ ^ (p + q))⁻¹
  let C := ∑ m ∈ range (p + q), (S cs m : ℝ)
  have hC : 0 < C := lt_of_lt_of_le (by exact_mod_cast hpos 0)
    (single_le_sum (f := fun m => (S cs m : ℝ)) (fun _ _ => by positivity) (mem_range.2 (by omega)))
  have hbds : ∀ n, c * τ ^ n ≤ S cs n ∧ (S cs n : ℝ) ≤ C * τ ^ n := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n (p + q) with hn | hn
      · exact ⟨(mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hτ.le hn.le) (by positivity)).trans
            (by rw [inv_mul_cancel₀ (by positivity)]; exact_mod_cast hpos n),
          (single_le_sum (f := fun m => (S cs m : ℝ)) (fun _ _ => by positivity) (mem_range.2 hn)).trans
            (le_mul_of_one_le_right hC.le (one_le_pow₀ hτ.le))⟩
      · have hsum : ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (n - (i + j)) = τ ^ n := by
          rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => by
            rw [pow_sub₀ _ hτ0.ne' (by rw [mem_Ico] at hi hj; omega), ← inv_pow, pow_add]]
          simp only [← mul_sum, ← sum_mul, hτeq, mul_one]
        rw [hrec n hn, ← hsum]; push_cast
        simp only [mul_sum]
        exact ⟨sum_le_sum fun i hi => sum_le_sum fun j hj => (ih _ (by rw [mem_Ico] at hi hj; omega)).1,
          sum_le_sum fun i hi => sum_le_sum fun j hj => (ih _ (by rw [mem_Ico] at hi hj; omega)).2⟩
  have ht (d : ℝ) (hd : 0 < d) : Tendsto (fun n : ℕ => d ^ ((n : ℝ)⁻¹) * τ) atTop (𝓝 τ) := by
    simpa [Function.comp_def, Real.rpow_zero] using
      ((Real.continuousAt_const_rpow (b := 0) hd.ne').tendsto.comp
        tendsto_inv_atTop_nhds_zero_nat).mul_const τ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (ht c (by positivity)) (ht C hC) ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop 1] with n hn <;>
    rw [← Real.pow_rpow_inv_natCast hτ0.le (by omega : n ≠ 0), ← Real.mul_rpow (by positivity) (by positivity)]
  · exact Real.rpow_le_rpow (by positivity) (hbds n).1 (by positivity)
  · exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hbds n).2 (by positivity)

theorem sphere23_root_tendsto (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (S cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 ρ) :=
  sphere_root_tendsto_rate cs (by decide) (by decide) h01 h02 h12 ρ hρ
    ((rate23_iff (zero_lt_one.trans hρ)).2 hρ3)

theorem rate_lt_rate {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) (τ τ' : ℝ) (hτ : 1 < τ) (hτ' : 1 < τ')
    (hτeq : RE p q τ) (hτeq' : RE p' q' τ') : τ < τ' := by
  rw [ne_eq, Prod.mk.injEq] at hne
  have hx : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have := sumIco_lt_of_lt le_rfl hp hx
  have := sumIco_lt_of_lt le_rfl hq hx
  have : SI q τ⁻¹ ≤ SI q' τ⁻¹ :=
    sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hqq) fun _ _ _ => by positivity
  refine lt_of_RF_lt (hp.trans hpp) (hq.trans hqq) (by linarith) (by linarith) ?_
  rcases Nat.lt_or_ge p p' with h | h
  · have := sumIco_lt_of_lt (by omega) h hx; simp at *; nlinarith
  · obtain rfl : p = p' := by omega
    have := sumIco_lt_of_lt (by omega) (by omega : q < q') hx
    simp at *; nlinarith

theorem plastic_le_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : RE p q τ) (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have hρ23 : RE 2 3 ρ := (rate23_iff (by linarith)).2 hρ3
  have hρ32 : RE 3 2 ρ := by rw [mul_comm]; exact hρ23
  by_cases h23 : (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)
  · rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [eq_of_RF_eq hp hq (by linarith) (by linarith) (hτeq.trans ‹RE _ _ ρ›.symm)]
  · have hlt : ρ < τ := by
      rcases Nat.lt_or_ge 2 p with hp3 | hp2
      · exact rate_lt_rate (by decide) le_rfl hp3 hq (by rintro ⟨rfl, rfl⟩; omega) ρ τ hρ hτ hρ32 hτeq
      · obtain rfl : p = 2 := by omega
        have hq3 : 3 ≤ q := not_lt.1 fun _ => by
          obtain rfl : q = 2 := by omega
          linarith [eq_of_RF_eq hp hq (by linarith : 0 < τ) zero_lt_one (by simpa using hτeq)]
        exact rate_lt_rate le_rfl (by decide) le_rfl hq3 (by rintro ⟨rfl, rfl⟩; omega) ρ τ hρ hτ hρ23 hτeq
    exact ⟨hlt.le, iff_of_false hlt.ne' h23⟩

theorem rate_lt_two {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : RE p q τ) : τ < 2 := by
  have hlt {m : ℕ} (hm : 2 ≤ m) : SI m (2⁻¹ : ℝ) < 1 := by
    have h := geom_sum_Ico_mul_neg (2⁻¹ : ℝ) (by omega : 1 ≤ m)
    have : 0 < (2⁻¹ : ℝ) ^ m := by positivity
    rw [pow_one] at h; linarith
  have := hlt hp; have := hlt hq; have : 0 ≤ SI p (2⁻¹ : ℝ) := by positivity
  exact lt_of_RF_lt hp hq (by norm_num) (by linarith) (by nlinarith)

theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) :
    ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q → ∀ τ : ℝ, 1 < τ → RE p q τ → σ < τ := by
  rcases le_or_gt σ 1 with h1 | h1
  · exact ⟨0, fun _ _ _ _ _ hτ _ => h1.trans_lt hτ⟩
  have hσ0 : 0 < σ := by linarith
  have hy0 : 0 < σ⁻¹ := inv_pos.2 hσ0
  have hy1 : σ⁻¹ < 1 := (inv_lt_one₀ hσ0).2 h1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < 2 * σ⁻¹ - 1 by nlinarith [mul_inv_cancel₀ hσ0.ne']) hy1
  refine ⟨N + 2, fun p q hp hq τ hτ heq => ?_⟩
  have hS {m : ℕ} (hm : N + 2 ≤ m) : 1 < SI m σ⁻¹ := by
    have h := geom_sum_Ico_mul_neg σ⁻¹ (by omega : 1 ≤ m)
    have : σ⁻¹ ^ m ≤ σ⁻¹ ^ N := pow_le_pow_of_le_one hy0.le hy1.le (by omega)
    rw [pow_one] at h; nlinarith
  have := hS hp; have := hS hq
  exact lt_of_RF_lt (by omega : 2 ≤ p) (by omega : 2 ≤ q) (by linarith) hσ0 (by nlinarith)

end TriangleGrowth
