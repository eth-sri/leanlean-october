module

public import Chazelle.Core.DownPhaseHostData
public import Chazelle.Core.DownPhaseArcT
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics

/-!
# WP-M (X, part 6): the host keys of an arc

For an arc `(l, r)` of a region `U` (nonempty family), the host keys from `l` to `r` in cyclic
order are `hk (i_l + j)` (indices mod `N`) for `j = 0, …, d`.  Unwrapped (`ukey`), they are the
breakpoints of the arc: strictly increasing, the inner ones are walk vertex keys, and every walk
vertex key in the arc is one of them (`arc_keys`).  The gaps along the arc are arc gaps
(`arc_gap`).
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt)
open ArcT (wrapK)

variable {M : Model} {F : Set (Set Point)} {U : Set Point}

/-- **Unwrapping** relative to `l`: keys from `l` on stay, keys before `l` move up by `n`. -/
noncomputable def unwrapK (n l x : ℝ) : ℝ := if l ≤ x then x else x + n

/-- **Cyclic betweenness in unwrapped form.** -/
theorem cyc_unwrap {n l a b y : ℝ} (hl : 0 ≤ l ∧ l < n) (ha : 0 ≤ a ∧ a < n)
    (hb : 0 ≤ b ∧ b < n) (hy : 0 ≤ y ∧ y < n) (hab : unwrapK n l a < unwrapK n l b) :
    sideInArc a b y ↔ unwrapK n l a < unwrapK n l y ∧ unwrapK n l y < unwrapK n l b := by
  unfold unwrapK at *
  unfold sideInArc
  split_ifs at * <;> constructor <;> intro h <;> cyc_close2

theorem unwrapK_self {n l : ℝ} : unwrapK n l l = l := by unfold unwrapK; rw [ite_eq_left le_rfl]

theorem unwrapK_bounds {n l x : ℝ} (hl : 0 ≤ l ∧ l < n) (hx : 0 ≤ x ∧ x < n) :
    l ≤ unwrapK n l x ∧ unwrapK n l x < l + n := by
  unfold unwrapK; split_ifs with h <;> constructor <;> linarith

theorem wrapK_unwrapK {n l x : ℝ} (hx : 0 ≤ x ∧ x < n) : wrapK n (unwrapK n l x) = x := by
  unfold unwrapK wrapK
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; exact h2 hx.2
  · exfalso; linarith [hx.1]
  · ring

/-- The unwrapped key of the host key `j` steps after `i₀`. -/
noncomputable def ukey (M : Model) (F : Set (Set Point)) (U : Set Point) (i₀ j : ℕ) : ℝ :=
  if i₀ + j < nk M F U then hk M F U (i₀ + j) else hk M F U (i₀ + j - nk M F U) + M.W.n

section

variable (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
include hM hF hfin

theorem ukey_mono {i₀ j j' : ℕ} (hi₀ : i₀ < nk M F U) (hjj : j < j') (hj' : j' < nk M F U) :
    ukey M F U i₀ j < ukey M F U i₀ j' := by
  have hb : ∀ i, i < nk M F U → 0 ≤ hk M F U i ∧ hk M F U i < M.W.n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
  unfold ukey
  split_ifs with h1 h2 h2
  · exact hk_strictMono hM hF hfin (by omega) h2
  · have := hb _ h1; have := hb (i₀ + j' - nk M F U) (by omega); linarith
  · omega
  · have := hk_strictMono (U := U) hM hF hfin (i := i₀ + j - nk M F U)
      (j := i₀ + j' - nk M F U) (by omega) (by omega)
    linarith

theorem wrapK_ukey {i₀ j : ℕ} (hi₀ : i₀ < nk M F U) (hj : j < nk M F U) :
    wrapK M.W.n (ukey M F U i₀ j) = hk M F U ((i₀ + j) % nk M F U) := by
  have hb : ∀ i, i < nk M F U → 0 ≤ hk M F U i ∧ hk M F U i < M.W.n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
  unfold ukey wrapK
  split_ifs with h1 h2 h2
  · rw [Nat.mod_eq_of_lt h1]
  · exfalso; exact h2 (hb _ h1).2
  · exfalso; have := hb (i₀ + j - nk M F U) (by omega); linarith
  · rw [add_sub_cancel_right, show (i₀ + j) % nk M F U = i₀ + j - nk M F U by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]

/-- `ukey` is the unwrapped key relative to `hk i₀`. -/
theorem ukey_eq_unwrap {i₀ j : ℕ} (hi₀ : i₀ < nk M F U) (hj : j < nk M F U) :
    ukey M F U i₀ j = unwrapK M.W.n (hk M F U i₀) (hk M F U ((i₀ + j) % nk M F U)) := by
  unfold ukey unwrapK
  split_ifs with h1 h2 h2
  · rw [Nat.mod_eq_of_lt h1]
  · exfalso; rw [Nat.mod_eq_of_lt h1] at h2
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; exact h2 (by rw [add_zero])
    · exact h2 (hk_strictMono hM hF hfin (by omega) h1).le
  · exfalso
    rw [show (i₀ + j) % nk M F U = i₀ + j - nk M F U by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at h2
    exact not_le.2 (hk_strictMono hM hF hfin (i := i₀ + j - nk M F U) (j := i₀) (by omega)
      hi₀) h2
  · rw [show (i₀ + j) % nk M F U = i₀ + j - nk M F U by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]

omit hM hF hfin in
theorem ukey_zero {i₀ : ℕ} (hi₀ : i₀ < nk M F U) : ukey M F U i₀ 0 = hk M F U i₀ := by
  unfold ukey; rw [add_zero, ite_eq_left hi₀]

end

/-- Steps from `a` to `b` modulo `N`. -/
theorem add_steps_mod {N a b : ℕ} (ha : a < N) (hb : b < N) : (a + (b + N - a) % N) % N = b := by
  rcases Nat.lt_or_ge b a with h | h
  · have e1 : (b + N - a) % N = b + N - a := Nat.mod_eq_of_lt (by omega)
    rw [e1, show a + (b + N - a) = b + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · have e1 : (b + N - a) % N = b - a := by
      rw [show b + N - a = (b - a) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1, show a + (b - a) = b by omega, Nat.mod_eq_of_lt hb]

/-! ## The keys of an arc -/

/-- **The data of an arc**: its first host key index `i_l` and its number `d` of gaps. -/
structure ArcData (M : Model) (F : Set (Set Point)) (U : Set Point) (l r : ℝ) (i_l d : ℕ) :
    Prop where
  hil : i_l < nk M F U
  hd0 : 0 < d
  hdN : d < nk M F U
  hl : hk M F U i_l = l
  hr : hk M F U ((i_l + d) % nk M F U) = r
  hud : ukey M F U i_l d = unwrapK M.W.n l r
  inner : ∀ j, 0 < j → j < d → (∃ k : ℕ, hk M F U ((i_l + j) % nk M F U) = k) ∧
    sideInArc l r (hk M F U ((i_l + j) % nk M F U))
  vtx : ∀ x : ℝ, 0 ≤ x → x < M.W.n → sideInArc l r x → (∃ k : ℕ, x = k) →
    ∃ j, 0 < j ∧ j < d ∧ hk M F U ((i_l + j) % nk M F U) = x
  gaps : ∀ j, j < d → ∀ y : ℝ, 0 ≤ y → y < M.W.n →
    sideInArc (hk M F U ((i_l + j) % nk M F U)) (hk M F U ((i_l + (j + 1)) % nk M F U)) y →
    sideInArc l r y

/-- **The host keys of an arc.**  For an arc `(l, r)` of `U`, with `l = hk i_l` and `d` steps to
`r`: the unwrapped keys `ukey i_l j` (`j ≤ d`) run from `l` to the unwrapped `r`, the inner ones
are walk vertex keys inside the arc, every walk vertex key of the arc is one of them, and the
gaps between them are arc gaps. -/
theorem arc_keys (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (hne : F.Nonempty)
    (hU : U ∈ M.regions F) {l r : ℝ} (harc : M.IsArc F U l r) :
    ∃ i_l d, ArcData M F U l r i_l d := by
  set N := nk M F U with hN
  set n : ℝ := (M.W.n : ℝ)
  obtain ⟨hcl, hcr, hlr⟩ := WalkAx.arc_cuts hne harc
  have hlK : l ∈ hostKeys M F U := by
    obtain ⟨c, ⟨hc, ht⟩, p, t, hA, h⟩ := hM.exists_exit_at_start hF hfin hne hU harc
    exact Or.inl ⟨c, hc, ht, p, t, hA, h⟩
  have hrK : r ∈ hostKeys M F U := by
    obtain ⟨c, ⟨hc, ht⟩, p, t, hA, h⟩ := hM.exists_exit_at_end hF hfin hne hU harc
    exact Or.inl ⟨c, hc, ht, p, t, hA, h⟩
  obtain ⟨i_l, hil, hl⟩ := exists_hk hM hF hfin hlK
  obtain ⟨i_r, hir, hr⟩ := exists_hk hM hF hfin hrK
  have hne' : i_l ≠ i_r := fun h => hlr (by rw [← hl, ← hr, h])
  have hN2 : 2 ≤ N := by omega
  set d := (i_r + N - i_l) % N with hd
  have hdN : d < N := Nat.mod_lt _ (by omega)
  have hid : (i_l + d) % N = i_r := add_steps_mod hil hir
  have hd0 : 0 < d := by
    by_contra h0; push Not at h0
    have : d = 0 := by omega
    rw [this, add_zero, Nat.mod_eq_of_lt hil] at hid
    exact hne' hid
  have hb : ∀ i, i < N → 0 ≤ hk M F U i ∧ hk M F U i < n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
  have hlb : 0 ≤ l ∧ l < n := hl ▸ hb i_l hil
  have hrb : 0 ≤ r ∧ r < n := hr ▸ hb i_r hir
  -- the unwrapped keys
  have huk : ∀ j, j < N → ukey M F U i_l j = unwrapK n l (hk M F U ((i_l + j) % N)) := by
    intro j hj; rw [ukey_eq_unwrap hM hF hfin hil hj, hl]
  have hud : ukey M F U i_l d = unwrapK n l r := by rw [huk d hdN, hid, hr]
  have hu0 : ukey M F U i_l 0 = l := by rw [ukey_zero hil, hl]
  have hmem : ∀ j, j < N → 0 ≤ hk M F U ((i_l + j) % N) ∧ hk M F U ((i_l + j) % N) < n :=
    fun j _ => hb _ (Nat.mod_lt _ (by omega))
  have hlr' : unwrapK n l l < unwrapK n l r := by
    rw [unwrapK_self, ← hud, ← hu0]; exact ukey_mono hM hF hfin hil hd0 hdN
  -- inner keys are in the arc
  have hin : ∀ j, 0 < j → j < d → sideInArc l r (hk M F U ((i_l + j) % N)) := by
    intro j hj0 hjd
    rw [cyc_unwrap hlb hlb hrb (hmem j (by omega)) hlr', unwrapK_self, ← huk j (by omega)]
    refine ⟨?_, ?_⟩
    · rw [← hu0]; exact ukey_mono hM hF hfin hil hj0 (by omega)
    · rw [← hud]; exact ukey_mono hM hF hfin hil hjd hdN
  refine ⟨i_l, d, hil, hd0, hdN, hl, by rw [hid, hr], hud, fun j hj0 hjd => ⟨?_, hin j hj0 hjd⟩,
    ?_, ?_⟩
  · -- a host key inside an arc is a vertex key
    have hK := hk_mem (U := U) hM hF hfin (Nat.mod_lt (i_l + j) (show 0 < N by omega))
    rcases hK with hx | ⟨k, -, e, -⟩
    · exact absurd (exitKeys_subset_cuts hx) (harc.2.2.2.2.2.1 _ (hin j hj0 hjd))
    · exact ⟨k, e⟩
  · -- every vertex key inside is one of them
    rintro x hx0 hxn hxin ⟨k, rfl⟩
    have hkn : k < M.W.n := by
      have : (k : ℝ) < (M.W.n : ℝ) := hxn
      exact_mod_cast this
    have hxK : (k : ℝ) ∈ hostKeys M F U := Or.inr ⟨k, hkn, rfl, l, r, harc, hxin⟩
    obtain ⟨i, hi, hik⟩ := exists_hk hM hF hfin hxK
    set j := (i + N - i_l) % N with hj
    have hjN : j < N := Nat.mod_lt _ (by omega)
    have hij : (i_l + j) % N = i := add_steps_mod hil hi
    have hxb : 0 ≤ (k : ℝ) ∧ (k : ℝ) < n := ⟨hx0, hxn⟩
    have hxu := (cyc_unwrap hlb hlb hrb hxb hlr').1 hxin
    rw [unwrapK_self, ← hik, ← hij, ← huk j hjN] at hxu
    refine ⟨j, ?_, ?_, by rw [hij, hik]⟩
    · by_contra h0; push Not at h0
      have : j = 0 := by omega
      rw [this, hu0] at hxu; exact lt_irrefl _ hxu.1
    · by_contra hjd; push Not at hjd
      rcases hjd.lt_or_eq with h | h
      · have := ukey_mono hM hF hfin hil h hjN
        rw [unwrapK_self, hud] at *
        rw [← hud] at hxu
        linarith [hxu.2]
      · rw [← h, hud] at hxu; exact lt_irrefl _ hxu.2
  · -- the gaps along the arc
    intro j hjd y hy0 hyn hy
    have hyb : 0 ≤ y ∧ y < n := ⟨hy0, hyn⟩
    have hj0 := hmem j (by omega)
    have hj1 := hmem (j + 1) (by omega)
    have hu01 : unwrapK n l (hk M F U ((i_l + j) % N)) <
        unwrapK n l (hk M F U ((i_l + (j + 1)) % N)) := by
      rw [← huk j (by omega), ← huk (j + 1) (by omega)]
      exact ukey_mono hM hF hfin hil (by omega) (by omega)
    have hy' := (cyc_unwrap hlb hj0 hj1 hyb hu01).1 hy
    rw [cyc_unwrap hlb hlb hrb hyb hlr', unwrapK_self]
    rw [← huk j (by omega), ← huk (j + 1) (by omega)] at hy'
    constructor
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, hu0] at hy'; exact hy'.1
      · have := ukey_mono (U := U) hM hF hfin hil h0 (show j < N by omega)
        rw [hu0] at this; linarith [hy'.1]
    · rcases (show j + 1 ≤ d by omega).lt_or_eq with h1 | h1
      · have := ukey_mono (U := U) hM hF hfin hil h1 hdN
        rw [hud] at this; linarith [hy'.2]
      · rw [h1, hud] at hy'; exact hy'.2

/-! ## The pieces of an arc -/

theorem unwrapK_wrapK {n l y : ℝ} (_hl : 0 ≤ l) (_hn : 0 < n) (hy1 : l ≤ y) (hy2 : y < l + n) :
    unwrapK n l (wrapK n y) = y := by
  unfold wrapK
  by_cases h1 : y < n
  · rw [ite_eq_left h1]; unfold unwrapK; rw [ite_eq_left hy1]
  · rw [ite_eq_right h1]; unfold unwrapK
    have : ¬ l ≤ y - n := by push Not; linarith
    rwring [ite_eq_right this]

/-- **The walk point of an unwrapped key** in the closed key interval of walk edge `p` (taken
modulo `n`). -/
theorem hostPt_wrap_lerp (W : Polygon) (hn : 0 < W.n) {p : ℕ} (hp : p < 2 * W.n) {y : ℝ}
    (hy1 : (p : ℝ) ≤ y) (hy2 : y ≤ p + 1) (hy3 : y < 2 * W.n) :
    hostPt W (wrapK W.n y) =
      Chazelle.Geometry.lerp (W.vtx (p % W.n)) (W.vtx ((p % W.n + 1) % W.n)) (y - p) := by
  set n := W.n
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hy2.lt_or_eq with hy2 | hy2
  · -- inside the edge
    have ht0 : 0 ≤ y - p := by linarith
    have ht1 : y - p < 1 := by linarith
    unfold wrapK
    split_ifs with h
    · have hpn : p < n := by
        have : (p : ℝ) < n := lt_of_le_of_lt hy1 h
        exact_mod_cast this
      rw [show y = (p : ℝ) + (y - p) by ring, hostPt_eq W ht0 ht1, Nat.mod_eq_of_lt hpn]
      simp [add_sub_cancel_left]
      rfl
    · push Not at h
      have hpn : n ≤ p := by
        by_contra hpn; push Not at hpn
        have : (p : ℝ) + 1 ≤ n := by exact_mod_cast hpn
        linarith
      have hmod : p % n = p - n := by
        rw [Nat.mod_eq_sub_mod hpn, Nat.mod_eq_of_lt (by omega)]
      rw [show y - n = ((p - n : ℕ) : ℝ) + (y - p) by push_cast [hpn]; ring,
        hostPt_eq W ht0 ht1, hmod]
      rfl
  · -- the end of the edge
    subst hy2
    rw [show ((p : ℝ) + 1 - p) = 1 by ring, Chazelle.Geometry.lerp_one]
    unfold wrapK
    split_ifs with h
    · have hpn : p + 1 < n := by
        have : ((p + 1 : ℕ) : ℝ) < n := by push_cast; exact h
        exact_mod_cast this
      rw [show (p : ℝ) + 1 = ((p + 1 : ℕ) : ℝ) + 0 by pcr,
        hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero,
        Nat.mod_eq_of_lt (show p < n by omega), Nat.mod_eq_of_lt hpn]
    · push Not at h
      have hpn : n ≤ p + 1 := by
        have : (n : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by push_cast; exact h
        exact_mod_cast this
      have hlt : p + 1 - n < n := by
        have : ((p + 1 : ℕ) : ℝ) < ((2 * n : ℕ) : ℝ) := by push_cast; exact hy3
        have : p + 1 < 2 * n := by exact_mod_cast this
        omega
      rw [show (p : ℝ) + 1 - n = ((p + 1 - n : ℕ) : ℝ) + 0 by push_cast [hpn]; ring,
        hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero]
      congr 1
      rcases Nat.lt_or_ge p n with h' | h'
      · rwo [Nat.mod_eq_of_lt h', show p + 1 = n by omega, Nat.mod_self]
      · have e : p % n = p - n := by
          rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (show p - n < n by omega)]
        rw [e, Nat.mod_eq_of_lt (show p - n + 1 < n by omega)]
        omega

/-- **A piece of an arc** lies in one walk edge: between two consecutive host keys of an arc there
is no walk vertex key, so the walk points of the keys between them are those of one walk edge
`p` (modulo `n`), affinely in the key. -/
theorem arc_piece (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData M F U l r i_l d) {j : ℕ} (hj : j < d) :
    ∃ p : ℕ, (p : ℝ) ≤ ukey M F U i_l j ∧ ukey M F U i_l (j + 1) ≤ p + 1 ∧ p < 2 * M.W.n ∧
      ∀ y, ukey M F U i_l j ≤ y → y ≤ ukey M F U i_l (j + 1) →
        hostPt M.W (wrapK M.W.n y) = Chazelle.Geometry.lerp (M.W.vtx (p % M.W.n))
          (M.W.vtx ((p % M.W.n + 1) % M.W.n)) (y - p) := by
  set N := nk M F U
  set n : ℝ := (M.W.n : ℝ)
  have hil := hA.hil
  have hdN := hA.hdN
  have hb : ∀ i, i < N → 0 ≤ hk M F U i ∧ hk M F U i < n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
  have hlb  := hA.hl ▸ hb i_l hil
  have hn  := lt_of_le_of_lt hlb.1 hlb.2
  have hnN : 0 < M.W.n := by
    have : (0 : ℝ) < (M.W.n : ℝ) := hn
    exact_mod_cast this
  have hu0 : ukey M F U i_l 0 = l := by rw [ukey_zero hil, hA.hl]
  have hab : ukey M F U i_l j < ukey M F U i_l (j + 1) :=
    ukey_mono hM hF hfin hil (Nat.lt_succ_self j) (by omega)
  have hla : l ≤ ukey M F U i_l j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, hu0]
    · rw [← hu0]; exact (ukey_mono hM hF hfin hil h0 (by omega)).le
  have hbr : ukey M F U i_l (j + 1) ≤ unwrapK n l r := by
    rw [← hA.hud]
    rcases (show j + 1 ≤ d by omega).lt_or_eq with h | h
    · exact (ukey_mono hM hF hfin hil h hdN).le
    · rw [h]
  have hrb : 0 ≤ r ∧ r < n := hA.hr ▸ hb _ (Nat.mod_lt _ (by omega))
  have hur  := (unwrapK_bounds hlb hrb).2
  have ha0  := le_trans hlb.1 hla
  set p := ⌊ukey M F U i_l j⌋₊ with hp
  have hpa  := Nat.floor_le ha0
  have hap : ukey M F U i_l j < p + 1 := Nat.lt_floor_add_one _
  -- no vertex key inside the piece
  have hbp : ukey M F U i_l (j + 1) ≤ p + 1 := by
    by_contra hbp
    push Not at hbp
    set k : ℝ := (p : ℝ) + 1
    have hk1  := lt_of_le_of_lt hla hap
    have hk2  := lt_of_lt_of_le hbp hbr
    have hk3  := lt_trans hk2 hur
    have hwk := ArcT.wrapK_nonneg (n := n) (le_trans hlb.1 hk1.le) (by linarith [hlb.2])
    have hwl := ArcT.wrapK_lt hn (le_trans hlb.1 hk1.le) (by linarith [hlb.2])
    have huw  := unwrapK_wrapK hlb.1 hn hk1.le hk3
    have hlr' : unwrapK n l l < unwrapK n l r := by rw [unwrapK_self]; exact lt_trans hk1 hk2
    have hin : sideInArc l r (wrapK n k) := by
      rw [cyc_unwrap hlb hlb hrb ⟨hwk, hwl⟩ hlr', unwrapK_self, huw]
      exact ⟨hk1, hk2⟩
    have hint : ∃ k' : ℕ, wrapK n k = k' := by
      unfold wrapK
      split_ifs with h
      · exact ⟨p + 1, by pcr⟩
      · refine ⟨p + 1 - M.W.n, ?_⟩
        have : M.W.n ≤ p + 1 := by
          have : (M.W.n : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by push_cast; push Not at h; exact h
          exact_mod_cast this
        push_cast [this]; ring
    obtain ⟨j', hj'0, hj'd, hj'⟩ := hA.vtx _ hwk hwl hin hint
    have hu' : ukey M F U i_l j' = k := by
      rw [ukey_eq_unwrap hM hF hfin hil (by omega), hA.hl, hj', huw]
    have h1 : j < j' := by
      by_contra h; push Not at h
      rcases h.lt_or_eq with h | h
      · have := ukey_mono hM hF hfin hil h (by omega); linarith
      · rwli [h] at hu'
    have h2 : j' < j + 1 := by
      by_contra h; push Not at h
      rcases h.lt_or_eq with h | h
      · have := ukey_mono hM hF hfin hil h (by omega); linarith
      · rwli [← h] at hu'
    omega
  refine ⟨p, hpa, hbp, ?_, fun y hy1 hy2 => ?_⟩
  · have : ((p : ℕ) : ℝ) < ((2 * M.W.n : ℕ) : ℝ) := by pcl
    exact_mod_cast this
  · have hy3 : y < 2 * (M.W.n : ℝ) := by
      have := lt_of_le_of_lt (le_trans hy2 hbr) hur; linarith [hlb.2]
    have hp2 : p < 2 * M.W.n := by
      have : ((p : ℕ) : ℝ) < ((2 * M.W.n : ℕ) : ℝ) := by pcl
      exact_mod_cast this
    exact hostPt_wrap_lerp M.W hnN hp2 (le_trans hpa hy1) (le_trans hy2 hbp) hy3

end

end DownHost

end Chazelle.Core
