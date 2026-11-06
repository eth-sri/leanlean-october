module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseMirrorBase
public import Chazelle.Core.DownPhaseMirrorKey

/-!
# Mirror symmetry (F-D7), part 3: mirrored walks

`WalkMir W W' c`: the walk `W'` is the mirror image of `W` traversed backwards,
`W'.vtx j = mir (W.vtx ((c + n - j) mod n))`.  Position `(p', t')` of `W'` corresponds to the
position `posMir n c p' t'` of `W` (the same vertex for `t' = 0`, else walk edge
`(c - 1 - p') mod n` at parameter `1 - t'`), whose key is the reflected key `rk n c (p' + t')`;
the points are mirror images (`sidePt_mir`) and the left sectors correspond (`sideLeft_mir`, the
reflection reverses orientation and the traversal reverses it back), hence the side-aware
attachments (`sideAttach_mir`).
-/

namespace Chazelle.Core

namespace Mir

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset nrm)
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt sidePrev sideNext
  SideAttach)

/-! ## Local geometry -/

theorem sideCross_mir (u v : Point) : sideCross (mir u) (mir v) = sideCross v u := by
  core_grind

theorem sideDot_mir (u v : Point) : sideDot (mir u) (mir v) = sideDot u v := by
  unfold sideDot mir; simp

/-- **The mirror reverses the arc of directions.** -/
theorem sideCcw_mir (B X A : Point) : sideCcw (mir A) (mir X) (mir B) ↔ sideCcw B X A := by
  have e1 : sideCross X A * sideDot B B = -(sideCross B X * sideDot B A) +
      sideDot X B * sideCross B A := by unfold sideCross sideDot; ring
  have e2 : sideDot A X * sideDot B B = sideDot B A * sideDot B X +
      sideCross B A * sideCross B X := by unfold sideCross sideDot; ring
  have hBB : 0 ≤ sideDot B B := by unfold sideDot; nlinarith
  have hB0 : sideDot B B = 0 → sideDot B A = 0 := by
    intro h; unfold sideDot at h ⊢
    have h1 : B.1 = 0 := by nlinarith [sq_nonneg B.1, sq_nonneg B.2]
    simp_all
  have hdAB : sideDot A B = sideDot B A := by unfold sideDot; ring
  unfold sideCcw
  simp only [sideCross_mir, sideDot_mir, hdAB]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · simp_all
    · ram_grind
    · refine Or.inr (Or.inr (Or.inl ⟨h1, h2, ?_⟩))
      rw [h1, mul_zero, add_zero] at e1
      rcases hBB.lt_or_eq with hB | hB
      · nlinarith
      simp_all
    · refine Or.inr (Or.inr (Or.inr ⟨h1, h2, ?_⟩))
      rw [h1, mul_zero, add_zero] at e1
      rw [h1, zero_mul, add_zero] at e2
      rcases hBB.lt_or_eq with hB | hB
      · rcases h3 with h3 | h3
        · grind
        · right; nlinarith
      simp_all
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · simp_all
    · ram_grind
    · refine Or.inr (Or.inr (Or.inl ⟨h1, h2, ?_⟩))
      rw [h1, mul_zero, add_zero] at e1
      rcases hBB.lt_or_eq with hB | hB
      · nlinarith
      simp_all
    · refine Or.inr (Or.inr (Or.inr ⟨h1, h2, ?_⟩))
      rw [h1, mul_zero, add_zero] at e1
      rw [h1, zero_mul, add_zero] at e2
      rcases hBB.lt_or_eq with hB | hB
      · rcases h3 with h3 | h3
        · grind
        · right; nlinarith
      simp_all

theorem sideLeftOf_mir (a v b x : Point) :
    sideLeftOf (mir b) (mir v) (mir a) (mir x) ↔ sideLeftOf a v b x := by
  unfold sideLeftOf
  rw [mir_sub, mir_sub, mir_sub, sideCcw_mir]

/-- Reversing an edge flips the offset side. -/
theorem offset_rev (u v : Point) (t δ : ℝ) : offset v u t (-δ) = offset u v (1 - t) δ := by
  grind [Chazelle.Jordan.offset_fst, Chazelle.Jordan.offset_snd]

/-! ## Mirrored walks -/

/-- **`W'` is the mirror image of `W`, traversed backwards.** -/
structure WalkMir (W W' : Polygon) (c : ℕ) : Prop where
  n_eq : W'.n = W.n
  c_lt : c < W.n
  vtx : ∀ j, j < W.n → W'.vtx j = mir (W.vtx ((c + W.n - j) % W.n))

/-- The position of `W` corresponding to position `(p', t')` of `W'`. -/
noncomputable def posMir (n c p' : ℕ) (t' : ℝ) : ℕ × ℝ :=
  if t' = 0 then ((c + n - p') % n, 0) else ((c + 2 * n - 1 - p') % n, 1 - t')

variable {W W' : Polygon} {c : ℕ}

theorem idx_succ {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    ((c + 2 * n - 1 - p) % n + 1) % n = (c + n - p) % n := by
  rw [Nat.mod_add_mod, show c + 2 * n - 1 - p + 1 = (c + n - p) + n * 1 by omega,
    Nat.add_mul_mod_self_left]

theorem idx_next {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    (c + n - (p + 1) % n) % n = (c + 2 * n - 1 - p) % n := by
  by_cases h : p + 1 < n
  · rw [Nat.mod_eq_of_lt h, show c + 2 * n - 1 - p = (c + n - (p + 1)) + n * 1 by omega,
      Nat.add_mul_mod_self_left]
  · obtain rfl : p = n - 1 := by omega
    rw [show n - 1 + 1 = n by omega, Nat.mod_self, Nat.sub_zero,
      show c + 2 * n - 1 - (n - 1) = c + n by omega]

theorem idx_prev {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    (c + n - (p + n - 1) % n) % n = ((c + n - p) % n + 1) % n := by
  rw [Nat.mod_add_mod]
  by_cases h : 0 < p
  · rw [show p + n - 1 = (p - 1) + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show p - 1 < n by omega), show c + n - (p - 1) = c + n - p + 1 by omega]
  · obtain rfl : p = 0 := by omega
    rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (show n - 1 < n by omega),
      show c + n - (n - 1) = c + 1 by omega, show c + n - 0 + 1 = (c + 1) + n * 1 by omega,
      Nat.add_mul_mod_self_left]

theorem idx_prev2 {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    (c + n - (p + 1) % n) % n = ((c + n - p) % n + n - 1) % n := by
  rw [idx_next hn hp, show (c + n - p) % n + n - 1 = (c + n - p) % n + (n - 1) by omega,
    Nat.mod_add_mod, show c + n - p + (n - 1) = c + 2 * n - 1 - p by omega]

theorem idx_v {n c p : ℕ} (hc : c < n) (hp : p < n) :
    (c + n - p) % n = if p ≤ c then c - p else c + n - p := by
  split_ifs with h
  · rw [show c + n - p = (c - p) + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem idx_q {n c p : ℕ} (hc : c < n) (hp : p < n) :
    (c + 2 * n - 1 - p) % n = if p < c then c - 1 - p else c + n - 1 - p := by
  split_ifs with h
  · rw [show c + 2 * n - 1 - p = (c - 1 - p) + n * 2 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  · rw [show c + 2 * n - 1 - p = (c + n - 1 - p) + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

/-- The vertex index map is an involution. -/
theorem idx_invol {n c p : ℕ} (hc : c < n) (hp : p < n) : (c + n - (c + n - p) % n) % n = p := by
  rw [idx_v hc hp]
  split_ifs with h
  · rw [show c + n - (c - p) = p + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp]
  · rw [show c + n - (c + n - p) = p by omega, Nat.mod_eq_of_lt hp]

/-- The edge index map is an involution. -/
theorem idx_q_invol {n c p : ℕ} (hc : c < n) (hp : p < n) :
    (c + 2 * n - 1 - (c + 2 * n - 1 - p) % n) % n = p := by
  rw [idx_q hc hp]
  split_ifs with h
  · rw [show c + 2 * n - 1 - (c - 1 - p) = p + n * 2 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp]
  · rw [show c + 2 * n - 1 - (c + n - 1 - p) = p + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp]

theorem posMir_bounds {n c p' : ℕ} (hn : 0 < n) {t' : ℝ} (ht0 : 0 ≤ t') (ht1 : t' < 1) :
    (posMir n c p' t').1 < n ∧ 0 ≤ (posMir n c p' t').2 ∧ (posMir n c p' t').2 < 1 := by
  unfold posMir
  split_ifs with h
  · exact ⟨Nat.mod_lt _ hn, le_refl _, one_pos⟩
  · have : 0 < t' := lt_of_le_of_ne ht0 (Ne.symm h)
    exact ⟨Nat.mod_lt _ hn, by linarith, by simp_all⟩

/-- **`posMir` is an involution.** -/
theorem posMir_posMir {n c p' : ℕ} (hc : c < n) (hp : p' < n) {t' : ℝ} (ht1 : t' < 1) :
    posMir n c (posMir n c p' t').1 (posMir n c p' t').2 = (p', t') := by
  unfold posMir
  by_cases ht : t' = 0
  · simp only [ht, ↓reduceIte]
    rw [idx_invol hc hp]
  · have h1 : (1 : ℝ) - t' ≠ 0 := by linarith
    simp only [ht, ↓reduceIte, h1]
    rw [idx_q_invol hc hp, sub_sub_cancel]

/-- **The key of the corresponding position is the reflected key.** -/
theorem posMir_key {n c p' : ℕ} (hc : c < n) (hp : p' < n) {t' : ℝ} (ht0 : 0 ≤ t')
    (ht1 : t' < 1) :
    ((posMir n c p' t').1 : ℝ) + (posMir n c p' t').2 = rk n c (p' + t') := by
  unfold posMir
  by_cases ht : t' = 0
  · simp only [ht, ↓reduceIte, add_zero]
    exact (rk_nat hc hp).symm
  · simp only [ht, ↓reduceIte]
    exact (rk_edge hc hp (lt_of_le_of_ne ht0 (Ne.symm ht)) ht1).symm

namespace WalkMir

variable (h : WalkMir W W' c)
include h

theorem n_pos : 0 < W.n := lt_of_le_of_lt (Nat.zero_le _) h.c_lt

/-- **The mirror relation is symmetric.** -/
theorem symm : WalkMir W' W c := by
  refine ⟨h.n_eq.symm, by rw [h.n_eq]; exact h.c_lt, fun j hj => ?_⟩
  rw [h.n_eq] at hj ⊢
  rw [h.vtx _ (Nat.mod_lt _ h.n_pos), idx_invol h.c_lt hj, mir_mir]

section
variable {p' : ℕ} (hp : p' < W.n)
include hp
/-- **Points correspond.** -/
theorem sidePt_mir (t' : ℝ) :
    sidePt W' p' t' = mir (sidePt W (posMir W.n c p' t').1 (posMir W.n c p' t').2) := by
  unfold posMir
  by_cases ht : t' = 0
  · simp only [ht, ↓reduceIte]
    rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, h.vtx p' hp]
  · simp only [ht, ↓reduceIte]
    unfold sidePt
    rw [h.n_eq, h.vtx p' hp, h.vtx ((p' + 1) % W.n) (Nat.mod_lt _ h.n_pos),
      idx_next h.n_pos hp, idx_succ h.n_pos hp, ← Chazelle.Geometry.lerp_symm, mir_lerp]

/-- **Left sectors correspond.** -/
theorem sideLeft_mir {t' : ℝ} (ht1 : t' < 1) (x : Point) :
    sideLeft W' p' t' (mir x) ↔
      sideLeft W (posMir W.n c p' t').1 (posMir W.n c p' t').2 x := by
  unfold sideLeft
  rw [h.sidePt_mir hp]
  unfold posMir sidePrev sideNext
  by_cases ht : t' = 0
  · simp only [ht, ↓reduceIte]
    rw [h.n_eq, h.vtx _ (Nat.mod_lt _ h.n_pos), h.vtx _ (Nat.mod_lt _ h.n_pos),
      idx_prev h.n_pos hp, idx_prev2 h.n_pos hp]
    exact sideLeftOf_mir _ _ _ _
  · have h1 : (1 : ℝ) - t' ≠ 0 := by linarith
    simp only [ht, ↓reduceIte, h1]
    rw [h.n_eq, h.vtx p' hp, h.vtx _ (Nat.mod_lt _ h.n_pos), idx_next h.n_pos hp,
      idx_succ h.n_pos hp]
    exact sideLeftOf_mir _ _ _ _

/-- **Attachments correspond.** -/
theorem sideAttach_mir {t' : ℝ} (ht0 : 0 ≤ t') (ht1 : t' < 1)
    (d : Set Point) :
    SideAttach W' (mir '' d) p' t' ↔
      SideAttach W d (posMir W.n c p' t').1 (posMir W.n c p' t').2 := by
  obtain ⟨b1, b2, b3⟩ := posMir_bounds (c := c) (p' := p') h.n_pos ht0 ht1
  unfold SideAttach
  rw [h.sidePt_mir hp, mem_image_mir, mir_mir, h.n_eq]
  simp only [Set.forall_mem_image, mir_injective.ne_iff, dist_mir, h.sideLeft_mir hp ht1]
  simp_all +arith


end

end WalkMir

end

end Mir

end Chazelle.Core
