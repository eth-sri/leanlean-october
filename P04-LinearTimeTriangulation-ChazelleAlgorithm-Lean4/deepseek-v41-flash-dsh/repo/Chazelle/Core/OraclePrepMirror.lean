module

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepLib

/-!
# Lemma 3.6 (WP-H), preprocessing part 4: walk keys in natural arithmetic

The zipper of the preprocessing works with walk positions `⟨w, hc⟩` of the chain model and needs
three tests on their keys, all decided here by natural arithmetic on `w`, `hc` and the chain
constants:

* `vaIdx C w`: the index in `C.P` of the walk vertex `w` (`6 ≤ w ≤ 2 m + 6`, `walk_vtx`);
* `nz C w hc`: the height code normalised to `0` when the parameter is `0` (`param_eq_zero_iff`);
  two keys are equal iff the walk edges and the normalised codes are (`key_eq_iff`);
* `inTest`: the key lies in the open halves `InI` of the tour range (`inI_iff`);
* `mirPos`: the mirrored walk position, whose key is `mk (key x)` (`mir_key`).
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (sideE)

namespace OracleQ

/-! ## Residues of small multiples -/

theorem mod_lt_two {x M : ℕ} (hx : x < 2 * M) :
    (x < M ∧ x % M = x) ∨ (M ≤ x ∧ x % M = x - M) := by
  rcases Nat.lt_or_ge x M with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨h, ?_⟩
    Ξ Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (⋄)

theorem mod_le_two {x M : ℕ} (_hM : 0 < M) (hx : x ≤ 2 * M) :
    (x < M ∧ x % M = x) ∨ (M ≤ x ∧ x < 2 * M ∧ x % M = x - M) ∨ (x = 2 * M ∧ x % M = 0) := by
  rcases Nat.lt_or_ge x (2 * M) with h | h
  · rcases mod_lt_two h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨h'.1, h, h'.2⟩)
  · have : x = 2 * M := ⋄
    subst this
    exact Or.inr (Or.inr ⟨rfl, Ρ Nat.mul_mod_left⟩)

variable (C : Chain)

/-! ## The walk vertices -/

/-- The index in `C.P` of the walk vertex `w`, for `6 ≤ w ≤ 2 m + 6`. -/
noncomputable def vaIdx (w : ℕ) : ℕ := (C.s + sideE C.m (tj C (w - 6))) % C.P.n

theorem vaIdx_lt (w : ℕ) : vaIdx C w < C.P.n := Nat.mod_lt _ C.n_pos

/-- **The walk vertex `w`** is the vertex `vaIdx w` of `C.P`. -/
theorem walk_vtx {w : ℕ} (h6 : 6 ≤ w) (h7 : w ≤ 2 * C.m + 6) :
    (chainModel C).W.vtx w = C.P.vtx (vaIdx C w) := by
  obtain ⟨i, rfl⟩ : ∃ i, w = i + 6 := ⟨w - 6, ⋄⟩
  show (C.sideWalk C.sideBeta).vtx (i + 6) = _
  Ξ C.sideWalk_vtx_tour _ (⋄)
  unfold Chain.sideTour Chain.vertex Chain.edgeIdx vaIdx
  Ξ Chain.sideIdx_eq, show i + 6 - 6 = i by omega
  rfl

theorem walk_next {w : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6) :
    (chainModel C).W.vtx ((w + 1) % (chainModel C).W.n) = C.P.vtx (vaIdx C (w + 1)) := by
  Ξ walk_n, Nat.mod_eq_of_lt (⋄)
  exact walk_vtx C (⋄) (⋄)

/-- Consecutive walk vertices of the tour are distinct vertices of `C.P`. -/
theorem vaIdx_succ_ne {w : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6) :
    vaIdx C w ≠ vaIdx C (w + 1) := by
  have hm := C.one_le
  have hmn := C.m_lt
  have hS := C.sideS_lt C.sideBeta
  unfold vaIdx tj
  Ξ show w + 1 - 6 = (w - 6) + 1 by omega
  set S := C.sideS C.sideBeta
  set i := w - 6
  have hi : i < 2 * C.m := ⋄
  -- the two chain indices differ by one
  obtain ⟨k, k', hk, hk', hkk⟩ : ∃ k k', sideE C.m ((S + i) % (2 * C.m)) = k ∧
      sideE C.m ((S + (i + 1)) % (2 * C.m)) = k' ∧ (k' = k + 1 ∨ k = k' + 1) := by
    refine ⟨_, _, rfl, rfl, ?_⟩
    have e1 : (S + (i + 1)) % (2 * C.m) = ((S + i) % (2 * C.m) + 1) % (2 * C.m) := by
      Ξ ← Nat.add_assoc, Nat.add_mod (S + i) 1, Nat.mod_eq_of_lt (show 1 < 2 * C.m by omega)
    Ξ e1
    have hX : (S + i) % (2 * C.m) < 2 * C.m := Nat.mod_lt _ (⋄)
    generalize (S + i) % (2 * C.m) = X at hX ⊢
    rcases Nat.lt_or_ge (X + 1) (2 * C.m) with h | h
    · rw [Nat.mod_eq_of_lt h]; unfold sideE; split_ifs <;> omega
    · rw [show X + 1 = 2 * C.m by omega, Nat.mod_self]; unfold sideE; split_ifs <;> omega
  Ξ hk, hk'
  have hkm : k ≤ C.m := by rw [← hk]; exact Chazelle.Chain.sideE_le (Nat.mod_lt _ (⋄)).le
  have hkm' : k' ≤ C.m := by rw [← hk']; exact Chazelle.Chain.sideE_le (Nat.mod_lt _ (⋄)).le
  intro h
  have hn2 : 2 ≤ C.P.n := ⋄
  rcases hkk with rfl | rfl
  · have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    Ξ' show C.s + (k + 1) - (C.s + k) = 1 by omega at this
    Ξ' Nat.one_mod_eq_zero_iff at this; omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq h
    Ξ' show C.s + (k' + 1) - (C.s + k') = 1 by omega at this
    Ξ' Nat.one_mod_eq_zero_iff at this; omega

/-- The walk edges `6 … 2 m + 6` are not horizontal. -/
theorem walk_nonhoriz (hD : DistinctHeights C.P) {w : ℕ} (h6 : 6 ≤ w) (h7 : w ≤ 2 * C.m + 6) :
    ((chainModel C).W.vtx w).2 ≠ ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)).2 := by
  rcases Nat.lt_or_ge w (2 * C.m + 6) with h | h
  · Ξ walk_vtx C h6 h7, walk_next C h6 h
    exact hD _ _ (vaIdx_lt C w) (vaIdx_lt C (w + 1)) (vaIdx_succ_ne C h6 h)
  · have hw : w = 2 * C.m + 6 := ⋄
    subst hw
    show ((C.sideWalk C.sideBeta).vtx (2 * C.m + 6)).2 ≠
      ((C.sideWalk C.sideBeta).vtx ((2 * C.m + 6 + 1) % (C.sideWalk C.sideBeta).n)).2
    Ξ C.sideWalk_vtx_wrap, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m
    unfold Chain.slitTop
    exact (C.top_snd_lt_radius).ne

/-! ## Parameters and keys -/

/-- The height code, normalised to `0` at the start vertex of the walk edge. -/
noncomputable def nz (w hc : ℕ) : ℕ := if hc = 0 ∨ hc = vaIdx C w + 1 then 0 else hc

theorem param_of_ne (hD : DistinctHeights C.P) {w : ℕ} (h6 : 6 ≤ w) (h7 : w ≤ 2 * C.m + 6)
    (h : ℕ) : (chainModel C).param C.P ⟨w, h + 1⟩ =
      ((C.P.vtx h).2 - ((chainModel C).W.vtx w).2) /
        (((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)).2 - ((chainModel C).W.vtx w).2) := by
  unfold Model.param Model.wa Model.wb
  simp only
  Ξ ite_eq_right (walk_nonhoriz C hD h6 h7)

/-- **The parameter is zero iff the normalised code is.** -/
theorem param_eq_zero_iff (hD : DistinctHeights C.P) {w hc : ℕ} (h6 : 6 ≤ w)
    (h7 : w ≤ 2 * C.m + 6) (hh : hc ≤ C.P.n) :
    (chainModel C).param C.P ⟨w, hc⟩ = 0 ↔ nz C w hc = 0 := by
  unfold nz
  rcases hc with _ | h
  · Θ Model.param
  · have hiff : ((if h + 1 = 0 ∨ h + 1 = vaIdx C w + 1 then 0 else h + 1) = 0) ↔
        h = vaIdx C w := by
      by_cases e : h = vaIdx C w
      · rw [ite_eq_left (Or.inr (Ρ e))]; Θ e
      · have : ¬(h + 1 = 0 ∨ h + 1 = vaIdx C w + 1) := ⋄
        rw [ite_eq_right this]; Θ e
    Ξ hiff, param_of_ne C hD h6 h7, walk_vtx C h6 h7
    have hne := walk_nonhoriz C hD h6 h7
    Ξ' walk_vtx C h6 h7 at hne
    have hd : ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)).2 -
        (C.P.vtx (vaIdx C w)).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    Ξ div_eq_zero_iff, sub_eq_zero, or_iff_left hd
    constructor
    · intro e
      by_contra hne'
      exact hD _ _ (⋄) (vaIdx_lt C w) hne' e
    · intro e; Ξ e

theorem key_eq_param (w hc : ℕ) :
    (chainModel C).key C.P ⟨w, hc⟩ = w + (chainModel C).param C.P ⟨w, hc⟩ := rfl

theorem floor_eq {w w2 : ℕ} {t t2 : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht2 : 0 ≤ t2) (ht21 : t2 < 1)
    (h : (w2 : ℝ) + t2 = w + t) : w2 = w ∧ t2 = t := by
  have a : (w2 : ℝ) < w + 1 := ⟡
  have b : (w : ℝ) < w2 + 1 := ⟡
  have a' : w2 < w + 1 := by exact_mod_cast a
  have b' : w < w2 + 1 := by exact_mod_cast b
  have e : w2 = w := ⋄
  subst e
  exact ⟨rfl, ⟡⟩

theorem nz_of_ne {w hc : ℕ} (h : nz C w hc ≠ 0) : nz C w hc = hc := by
  unfold nz at *; split_ifs at * with h' <;> first | exact absurd rfl h | rfl

/-- **Equal keys**: for `6 ≤ w ≤ 2 m + 6`, a proper position has the key of `⟨w, hc⟩` iff it lies
on the walk edge `w` with the same normalised height code. -/
theorem key_eq_iff (hD : DistinctHeights C.P) {w hc w2 hc2 : ℕ} (h6 : 6 ≤ w)
    (h7 : w ≤ 2 * C.m + 6) (hh : hc ≤ C.P.n) (hh2 : hc2 ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ⟨w, hc⟩ ∧ (chainModel C).param C.P ⟨w, hc⟩ < 1)
    (hp2 : 0 ≤ (chainModel C).param C.P ⟨w2, hc2⟩ ∧ (chainModel C).param C.P ⟨w2, hc2⟩ < 1) :
    (chainModel C).key C.P ⟨w2, hc2⟩ = (chainModel C).key C.P ⟨w, hc⟩ ↔
      w2 = w ∧ nz C w hc2 = nz C w hc := by
  Ξ key_eq_param, key_eq_param
  constructor
  · intro h
    obtain ⟨rfl, ht⟩ := floor_eq hp.1 hp.2 hp2.1 hp2.2 h
    refine ⟨rfl, ?_⟩
    by_cases h0 : (chainModel C).param C.P ⟨w2, hc⟩ = 0
    · rw [(param_eq_zero_iff C hD h6 h7 hh).1 h0,
        (param_eq_zero_iff C hD h6 h7 hh2).1 (ht.trans h0)]
    · have h0' : (chainModel C).param C.P ⟨w2, hc2⟩ ≠ 0 := fun e => h0 (ht ▸ e)
      have n1 : nz C w2 hc ≠ 0 := fun e => h0 ((param_eq_zero_iff C hD h6 h7 hh).2 e)
      have n2 : nz C w2 hc2 ≠ 0 := fun e => h0' ((param_eq_zero_iff C hD h6 h7 hh2).2 e)
      Ξ nz_of_ne C n1, nz_of_ne C n2
      have hc0 : hc ≠ 0 := fun e => by
        apply n1; unfold nz; Ξ ite_eq_left (Or.inl e)
      have hc20 : hc2 ≠ 0 := fun e => by
        apply n2; unfold nz; Ξ ite_eq_left (Or.inl e)
      obtain ⟨h1, rfl⟩ : ∃ h1, hc = h1 + 1 := ⟨hc - 1, ⋄⟩
      obtain ⟨h2, rfl⟩ : ∃ h2, hc2 = h2 + 1 := ⟨hc2 - 1, ⋄⟩
      Ξ' param_of_ne C hD h6 h7, param_of_ne C hD h6 h7 at ht
      have hne := walk_nonhoriz C hD h6 h7
      have hd : ((chainModel C).W.vtx ((w2 + 1) % (chainModel C).W.n)).2 -
          ((chainModel C).W.vtx w2).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      Ξ' div_left_inj' hd, sub_left_inj at ht
      by_contra hne'
      exact hD h2 h1 (⋄) (⋄) (fun e => hne' (Ρ e)) ht
  · rintro ⟨rfl, hz⟩
    by_cases h0 : nz C w2 hc = 0
    · rw [(param_eq_zero_iff C hD h6 h7 hh).2 h0,
        (param_eq_zero_iff C hD h6 h7 hh2).2 (hz.trans h0)]
    · have n2 : nz C w2 hc2 ≠ 0 := fun e => h0 (hz ▸ e)
      Ξ' nz_of_ne C h0, nz_of_ne C n2 at hz
      Ξ hz

/-- The key of a vertex position `⟨X, 0⟩`. -/
theorem key_zero (X : ℕ) : (chainModel C).key C.P ⟨X, 0⟩ = X := by
  Θ Model.key, Model.param

/-! ## The mirror -/

/-- The mirrored walk edge of a vertex position. -/
noncomputable def mirW0 (w : ℕ) : ℕ :=
  (if w ≤ 6 + rT C then 12 + rT C else 12 + rT C + 2 * C.m) - w

/-- The mirrored walk edge of an inner position. -/
noncomputable def mirW1 (w : ℕ) : ℕ :=
  (if w < 6 + rT C then 11 + rT C else 11 + rT C + 2 * C.m) - w

/-- **The mirrored walk position.** -/
noncomputable def mirPos (w hc : ℕ) : WPos :=
  if nz C w hc = 0 then ⟨mirW0 C w, 0⟩ else ⟨mirW1 C w, hc⟩

theorem rT_def : (rT C : ℝ) + 6 = κT C := by unfold κT; ring

/-- **The tour reversal**: the mirrored walk edge runs along the same chain edge backwards. -/
theorem rev_idx {w : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6) :
    vaIdx C (mirW1 C w) = vaIdx C (w + 1) ∧ vaIdx C (mirW1 C w + 1) = vaIdx C w := by
  have hm := C.one_le
  have hS := C.sideS_lt C.sideBeta
  have hR := rT_lt C
  unfold vaIdx tj
  set S := C.sideS C.sideBeta
  set R := rT C
  set M := 2 * C.m with hM
  have hRdef : R = (4 * C.m - 2 * S) % M := rfl
  set i := w - 6 with hi
  have hiM : i < M := ⋄
  -- the mirrored tour index
  obtain ⟨i', hi', hi'M⟩ : ∃ i', mirW1 C w - 6 = i' ∧ (i' = (if i < R then R - 1 - i else R + M - 1 - i)) := by
    refine ⟨_, rfl, ?_⟩
    unfold mirW1; split_ifs <;> omega
  have e1 : mirW1 C w + 1 - 6 = i' + 1 := by
    have : 6 ≤ mirW1 C w := by unfold mirW1; split_ifs <;> omega
    omega
  Ξ e1, hi', show w + 1 - 6 = i + 1 by omega
  -- the residues
  have hX := mod_lt_two (x := S + i) (M := M) (⋄)
  have hY := mod_lt_two (x := S + i') (M := M) (by split_ifs at hi'M <;> omega)
  have hR4 := mod_le_two (x := 4 * C.m - 2 * S) (M := M) (⋄) (⋄)
  Ξ' ← hRdef at hR4
  obtain ⟨X, hXd⟩ : ∃ X, (S + i) % M = X := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, (S + i') % M = Y := ⟨_, rfl⟩
  have hXY : Y = M - 1 - X := by
    Ξ' hXd at hX; Ξ' hYd at hY
    split_ifs at hi'M <;> rcases hX with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hY with ⟨c, d⟩ | ⟨c, d⟩ <;>
      rcases hR4 with ⟨e, f⟩ | ⟨e, f, g⟩ | ⟨e, f⟩ <;> omega
  have hXM : X < M := by rw [← hXd]; exact Nat.mod_lt _ (⋄)
  have e2 : (S + (i + 1)) % M = (X + 1) % M := by
    Ξ ← Nat.add_assoc, Nat.add_mod, hXd, Nat.mod_eq_of_lt (show 1 < M by omega)
  have e3 : (S + (i' + 1)) % M = (Y + 1) % M := by
    Ξ ← Nat.add_assoc, Nat.add_mod, hYd, Nat.mod_eq_of_lt (show 1 < M by omega)
  Ξ hYd, hXd, e2, e3, hXY
  have sym : ∀ j, j ≤ M → sideE C.m (M - j) = sideE C.m j := by
    intro j hj; unfold sideE; split_ifs <;> omega
  constructor
  · rcases Nat.lt_or_ge (X + 1) M with h | h
    · Ξ Nat.mod_eq_of_lt h, show M - 1 - X = M - (X + 1) by omega, sym _ h.le
    · Ξ show X + 1 = M by omega, Nat.mod_self, show M - 1 - X = 0 by omega
  · rcases Nat.eq_zero_or_pos X with h | h
    · Ξ h, show M - 1 - 0 + 1 = M by omega, Nat.mod_self
    · rw [show M - 1 - X + 1 = M - X by omega, Nat.mod_eq_of_lt (show M - X < M by omega),
        sym _ hXM.le]

/-- **The mirror of a walk position**: a proper position in the tour range whose key is the
mirror `mk` of the key. -/
theorem mir_key (hD : DistinctHeights C.P) {w hc : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6)
    (hh : hc ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ⟨w, hc⟩ ∧ (chainModel C).param C.P ⟨w, hc⟩ < 1) :
    (chainModel C).key C.P (mirPos C w hc) = mk C ((chainModel C).key C.P ⟨w, hc⟩) ∧
      0 ≤ (chainModel C).param C.P (mirPos C w hc) ∧
      (chainModel C).param C.P (mirPos C w hc) < 1 ∧ (mirPos C w hc).hgt ≤ C.P.n ∧
      6 ≤ (mirPos C w hc).edge ∧ (mirPos C w hc).edge ≤ 2 * C.m + 6 ∧
      (nz C w hc ≠ 0 → 0 < (chainModel C).param C.P (mirPos C w hc)) := by
  have hR := rT_lt C
  have hT := rT_def C
  unfold mirPos
  split_ifs with h0
  · -- a vertex position
    have hpar := (param_eq_zero_iff C hD h6 h7.le hh).2 h0
    rw [show (chainModel C).key C.P ⟨w, hc⟩ = w by rw [key_eq_param, hpar, add_zero], key_zero]
    have hm0 : 6 ≤ mirW0 C w ∧ mirW0 C w ≤ 2 * C.m + 6 := by unfold mirW0; split_ifs <;> omega
    refine ⟨?_, by simp [Model.param], by simp [Model.param], Nat.zero_le _, hm0.1, hm0.2,
      fun h => absurd h0 h⟩
    unfold mk mirW0
    by_cases hw : w ≤ 6 + rT C
    · have hw' : (w : ℝ) ≤ κT C := by rw [← hT]; exact_mod_cast (show w ≤ rT C + 6 by omega)
      rw [ite_eq_left hw, ite_eq_left hw', Nat.cast_sub (by omega)]; push_cast; rw [← hT]; ring
    · have hw' : ¬ (w : ℝ) ≤ κT C := by
        rw [← hT]; push Not; exact_mod_cast (show rT C + 6 < w by omega)
      rw [ite_eq_right hw, ite_eq_right hw', Nat.cast_sub (by omega)]; push_cast; rw [← hT]; ring
  · -- an inner position
    have hc0 : hc ≠ 0 := fun e => h0 (by unfold nz; rw [ite_eq_left (Or.inl e)])
    obtain ⟨h, rfl⟩ : ∃ h, hc = h + 1 := ⟨hc - 1, by omega⟩
    have hm1 : 6 ≤ mirW1 C w ∧ mirW1 C w < 2 * C.m + 6 := by unfold mirW1; split_ifs <;> omega
    obtain ⟨r1, r2⟩ := rev_idx C h6 h7
    have ht := param_of_ne C hD h6 h7.le h
    have ht' := param_of_ne C hD hm1.1 hm1.2.le h
    rw [walk_vtx C h6 h7.le, walk_next C h6 h7] at ht
    rw [walk_vtx C hm1.1 hm1.2.le, walk_next C hm1.1 hm1.2, r1, r2] at ht'
    set a := (C.P.vtx (vaIdx C w)).2
    set b := (C.P.vtx (vaIdx C (w + 1))).2
    have hab : b - a ≠ 0 := by
      have := walk_nonhoriz C hD h6 h7.le
      rw [walk_vtx C h6 h7.le, walk_next C h6 h7] at this
      exact sub_ne_zero.2 (Ne.symm this)
    have hba : a - b ≠ 0 := fun e => hab (by linarith)
    set t := (chainModel C).param C.P ⟨w, h + 1⟩ with htdef
    have hpt : (chainModel C).param C.P ⟨mirW1 C w, h + 1⟩ = 1 - t := by
      rw [ht', ht]; field_simp; ring
    have ht0 : t ≠ 0 := fun e => h0 ((param_eq_zero_iff C hD h6 h7.le hh).1 e)
    have htp : 0 < t := lt_of_le_of_ne hp.1 (Ne.symm ht0)
    refine ⟨?_, by rw [hpt]; linarith [hp.2], by rw [hpt]; linarith, hh, hm1.1, hm1.2.le,
      fun _ => by rw [hpt]; linarith [hp.2]⟩
    rw [key_eq_param, key_eq_param, hpt, ← htdef]
    unfold mk mirW1
    by_cases hw : w < 6 + rT C
    · have hw' : (w : ℝ) + t ≤ κT C := by
        rw [← hT]
        have : (w : ℝ) + 1 ≤ rT C + 6 := by exact_mod_cast (show w + 1 ≤ rT C + 6 by omega)
        linarith [hp.2]
      rw [ite_eq_left hw, ite_eq_left hw', Nat.cast_sub (by omega)]; push_cast; rw [← hT]; ring
    · have hw' : ¬ (w : ℝ) + t ≤ κT C := by
        rw [← hT]; push Not
        have : (rT C : ℝ) + 6 ≤ w := by exact_mod_cast (show rT C + 6 ≤ w by omega)
        linarith
      rw [ite_eq_right hw, ite_eq_right hw', Nat.cast_sub (by omega)]; push_cast; rw [← hT]; ring

/-- The normalised code of the mirror is its height code. -/
theorem nz_mir (hD : DistinctHeights C.P) {w hc : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6)
    (hh : hc ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ⟨w, hc⟩ ∧ (chainModel C).param C.P ⟨w, hc⟩ < 1) :
    nz C (mirPos C w hc).edge (mirPos C w hc).hgt = (mirPos C w hc).hgt := by
  obtain ⟨-, -, -, ph, e6, e7, hpos⟩ := mir_key C hD h6 h7 hh hp
  by_cases h0 : nz C w hc = 0
  · have : (mirPos C w hc).hgt = 0 := by unfold mirPos; Ξ ite_eq_left h0
    rw [this]; unfold nz; simp
  · have hp0 := hpos h0
    have hne : nz C (mirPos C w hc).edge (mirPos C w hc).hgt ≠ 0 := fun e =>
      hp0.ne' ((param_eq_zero_iff C hD e6 e7 ph).2 e)
    exact nz_of_ne C hne

/-- The natural test of `InI`. -/
def inTest (C : Chain) (z w : ℕ) : Prop :=
  if z = 0 then (6 < w ∧ w < 6 + rT C) ∨ (6 + rT C < w ∧ w < 2 * C.m + 6)
  else 6 ≤ w ∧ w < 2 * C.m + 6

/-- **The open halves of the tour range in natural arithmetic.** -/
theorem inI_iff (hD : DistinctHeights C.P) {w hc : ℕ} (hw : w < 2 * C.m + 7) (hh : hc ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ⟨w, hc⟩ ∧ (chainModel C).param C.P ⟨w, hc⟩ < 1) :
    InI C ((chainModel C).key C.P ⟨w, hc⟩) ↔ inTest C (nz C w hc) w := by
  have hR := rT_lt C
  have hT := rT_def C
  Ξ key_eq_param
  unfold InI inTest
  Ξ ← hT
  set t := (chainModel C).param C.P ⟨w, hc⟩
  by_cases hin : 6 ≤ w ∧ w < 2 * C.m + 6
  · by_cases h0 : nz C w hc = 0
    · have ht : t = 0 := (param_eq_zero_iff C hD hin.1 hin.2.le hh).2 h0
      Ξ ite_eq_left h0, ht, add_zero
      constructor
      · rintro (⟨a, b⟩ | ⟨a, b⟩)
        · left; constructor <;> [exact_mod_cast a; (have : (w : ℝ) < rT C + 6 := b; exact_mod_cast (show w < rT C + 6 by exact_mod_cast this) |>.trans_le (⋄))]
        · right; constructor
          · have : (rT C : ℝ) + 6 < w := a
            have : rT C + 6 < w := by exact_mod_cast this
            omega
          · exact_mod_cast b
      · rintro (⟨a, b⟩ | ⟨a, b⟩)
        · left; refine ⟨by exact_mod_cast a, ?_⟩
          exact_mod_cast (show w < rT C + 6 by omega)
        · right; refine ⟨?_, by exact_mod_cast b⟩
          exact_mod_cast (show rT C + 6 < w by omega)
    · have ht0 : t ≠ 0 := fun e => h0 ((param_eq_zero_iff C hD hin.1 hin.2.le hh).1 e)
      have htp : 0 < t := lt_of_le_of_ne hp.1 (Ne.symm ht0)
      Ξ ite_eq_right h0
      ϴ hin, and_self, iff_true
      have h6 : (6 : ℝ) ≤ w := by exact_mod_cast hin.1
      have h7 : (w : ℝ) + 1 ≤ 2 * C.m + 6 := by exact_mod_cast (show w + 1 ≤ 2 * C.m + 6 by omega)
      rcases Nat.lt_or_ge w (rT C + 6) with h | h
      · left; refine ⟨⟡, ?_⟩
        have : (w : ℝ) + 1 ≤ rT C + 6 := by exact_mod_cast (show w + 1 ≤ rT C + 6 by omega)
        linarith [hp.2]
      · right; refine ⟨?_, by linarith [hp.2]⟩
        have : (rT C : ℝ) + 6 ≤ w := by exact_mod_cast h
        linarith
  · have hfalse : ¬ ((if nz C w hc = 0 then (6 < w ∧ w < 6 + rT C) ∨
        (6 + rT C < w ∧ w < 2 * C.m + 6) else 6 ≤ w ∧ w < 2 * C.m + 6)) := by
      split_ifs <;> omega
    ϴ hfalse, iff_false
    rcases Nat.lt_or_ge w 6 with h | h
    · have : (w : ℝ) + 1 ≤ 6 := by exact_mod_cast (show w + 1 ≤ 6 by omega)
      rintro (⟨a, -⟩ | ⟨a, -⟩)
      · linarith [hp.2]
      · linarith [hp.2, (Nat.cast_nonneg (rT C) : (0 : ℝ) ≤ _)]
    · have hw' : w = 2 * C.m + 6 := ⋄
      have : (2 * C.m + 6 : ℝ) = w := by rw [hw']; push_cast; ring
      have hRl : (rT C : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hR
      rintro (⟨-, b⟩ | ⟨-, b⟩)
      · linarith [hp.1]
      · linarith [hp.1]

end OracleQ

end

end Chazelle.Core
