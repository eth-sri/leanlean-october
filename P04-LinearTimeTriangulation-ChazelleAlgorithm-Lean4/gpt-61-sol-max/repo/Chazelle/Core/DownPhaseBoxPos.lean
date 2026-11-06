module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseBoxChain
public import Chazelle.Core.NFBuildWt

/-!
# WP-M (B3′, part 3): walk positions of twin chains

For twin chains `C`, `C'` (`BoxT.Twin`) and a walk position `x` of the common index set whose
height code is `0` or the height of a vertex of `Q` inside the fixed band `|y| < B` of the box
stretch (`BandPos`), the positions in the two chain models correspond:

* the parameters are related monotonically (`param_mem_iff`, `param_eq_zero_iff`,
  `param_lt_iff` on one walk edge), so the keys are ordered alike (`key_lt_iff`, `key_eq_iff`)
  and the arc weights between such keys agree (`arcWt_eq`);
* the points correspond under the stretch (`pos_eq`), using the classification of the walk
  edges: horizontal (box top and bottom), vertical (box sides, slit), or between two chain
  vertices (`edge_kind`).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set Chazelle.Chain

/-! ## Monotone parameter algebra -/

/-- The parameter of the height `y` on an edge from height `a` to height `b`. -/
noncomputable def ratio (a b y : ℝ) : ℝ := (y - a) / (b - a)

section
variable {a b y : ℝ} (hab : a ≠ b)
include hab
theorem ratio_mem_iff :
    (0 ≤ ratio a b y ∧ ratio a b y < 1) ↔ (if a < b then a ≤ y ∧ y < b else b < y ∧ y ≤ a) := by
  unfold ratio
  rcases lt_or_gt_of_ne hab with h | h
  · rw [ite_eq_left h, le_div_iff₀ (by linarith), div_lt_one (by linarith)]
    simp_all
  · rw [ite_eq_right (not_lt.2 h.le), div_nonneg_iff, div_lt_one_of_neg (by linarith)]
    ram_grind

theorem ratio_eq_zero_iff : ratio a b y = 0 ↔ y = a := by
  core_grind


end

theorem ratio_lt_iff {a b y y' : ℝ} (hab : a ≠ b) :
    ratio a b y < ratio a b y' ↔ (if a < b then y < y' else y' < y) := by
  unfold ratio
  rcases lt_or_gt_of_ne hab with h | h
  · rw [ite_eq_left h, div_lt_div_iff_of_pos_right (by linarith)]
    simp_all
  · rw [ite_eq_right (not_lt.2 h.le), div_lt_div_right_of_neg (by linarith)]
    simp_all

variable {C C' : Chain}

theorem sig_strictMono : StrictMono (stretch (bnd C C') (kk C C')) := stretch_strictMono bnd_nonneg kk_pos

section
variable {x y : ℝ}
theorem sig_lt_iff : stretch (bnd C C') (kk C C') x < stretch (bnd C C') (kk C C') y ↔ x < y := sig_strictMono.lt_iff_lt

theorem sig_le_iff : stretch (bnd C C') (kk C C') x ≤ stretch (bnd C C') (kk C C') y ↔ x ≤ y := sig_strictMono.le_iff_le

theorem sig_inj : stretch (bnd C C') (kk C C') x = stretch (bnd C C') (kk C C') y ↔ x = y := sig_strictMono.injective.eq_iff


end

section
variable {a b y : ℝ} (hab : a ≠ b)
include hab
theorem ratio_mem_sig_iff :
    (0 ≤ ratio (stretch (bnd C C') (kk C C') a) (stretch (bnd C C') (kk C C') b) (stretch (bnd C C') (kk C C') y) ∧
      ratio (stretch (bnd C C') (kk C C') a) (stretch (bnd C C') (kk C C') b) (stretch (bnd C C') (kk C C') y) < 1) ↔ (0 ≤ ratio a b y ∧ ratio a b y < 1) := by
  rw [ratio_mem_iff (by rwa [Ne, sig_inj]), ratio_mem_iff hab]
  grind [sig_lt_iff, sig_le_iff]

theorem ratio_eq_zero_sig_iff :
    ratio (stretch (bnd C C') (kk C C') a) (stretch (bnd C C') (kk C C') b) (stretch (bnd C C') (kk C C') y) = 0 ↔ ratio a b y = 0 := by
  rw [ratio_eq_zero_iff (by rwa [Ne, sig_inj]), ratio_eq_zero_iff hab, sig_inj]


end

theorem ratio_lt_sig_iff {a b y y' : ℝ} (hab : a ≠ b) :
    ratio (stretch (bnd C C') (kk C C') a) (stretch (bnd C C') (kk C C') b) (stretch (bnd C C') (kk C C') y) < ratio (stretch (bnd C C') (kk C C') a) (stretch (bnd C C') (kk C C') b) (stretch (bnd C C') (kk C C') y') ↔
      ratio a b y < ratio a b y' := by
  rw [ratio_lt_iff (by rwa [Ne, sig_inj]), ratio_lt_iff hab]
  grind [sig_lt_iff]

/-! ## Positions -/

/-- A walk position whose height code is `0` or the height of a vertex of `Q` inside the fixed
band of the stretch. -/
def BandPos (C C' : Chain) (Q : Polygon) (x : WPos) : Prop :=
  x.hgt = 0 ∨ ∃ h, x.hgt = h + 1 ∧ |(Q.vtx h).2| < bnd C C'

section
variable (M : Model) (Q : Polygon)
/-- The parameter of a height code in the chain model, as a ratio. -/
theorem param_eq (x : WPos) (k : ℕ) (hk : x.hgt = k + 1) :
    M.param Q x = if (M.wa x.edge).2 = (M.wb x.edge).2 then 0
      else ratio (M.wa x.edge).2 (M.wb x.edge).2 (Q.vtx k).2 := by
  grind [Model.param, ratio]

/-- Keys of positions with parameters in `[0, 1)` compare lexicographically. -/
theorem key_lt_iff_lex {x x' : WPos}
    (hm : 0 ≤ M.param Q x ∧ M.param Q x < 1) (hm' : 0 ≤ M.param Q x' ∧ M.param Q x' < 1) :
    M.key Q x < M.key Q x' ↔ x.edge < x'.edge ∨ (x.edge = x'.edge ∧ M.param Q x < M.param Q x') := by
  unfold Model.key
  constructor
  · intro hlt
    rcases lt_trichotomy x.edge x'.edge with h1 | h1 | h1
    · omega
    · simp_all
    · exfalso
      have : (x'.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h1
      linarith
  · rintro (h1 | ⟨h1, h2⟩)
    · have : (x.edge : ℝ) + 1 ≤ x'.edge := by exact_mod_cast h1
      linarith
    simp_all


end

namespace Twin

variable (h : Twin C C')
include h

theorem wa_eq (p : ℕ) : (chainModel C').wa p = phi C C' ((chainModel C).wa p) :=
  h.phi_walk_vtx p

theorem wb_eq (p : ℕ) : (chainModel C').wb p = phi C C' ((chainModel C).wb p) := by
  show (C'.sideWalk C'.sideBeta).vtx ((p + 1) % (C'.sideWalk C'.sideBeta).n) = _
  rw [h.walk_n]; exact h.phi_walk_vtx _

omit h in
theorem sig_band {y : ℝ} (hy : |y| < bnd C C') : stretch (bnd C C') (kk C C') y = y :=
  stretch_of_abs_le bnd_nonneg hy.le

section
variable {Q : Polygon} {x : WPos}
/-- **The parameters in the two models.**  For a band position the parameter in `M'` is the
ratio of the stretched heights. -/
theorem param'_eq {k : ℕ} (hk : x.hgt = k + 1)
    (hy : |(Q.vtx k).2| < bnd C C') :
    (chainModel C').param Q x = if ((chainModel C).wa x.edge).2 = ((chainModel C).wb x.edge).2
      then 0 else ratio (stretch (bnd C C') (kk C C') ((chainModel C).wa x.edge).2)
        (stretch (bnd C C') (kk C C') ((chainModel C).wb x.edge).2) (stretch (bnd C C') (kk C C') (Q.vtx k).2) := by
  rw [param_eq _ Q x k hk, h.wa_eq, h.wb_eq, sig_band hy]
  simp only [phi, stretchPt]
  grind [Chazelle.Core.BoxT.sig_inj]

section
variable (hx : BandPos C C' Q x)
include hx
theorem param_mem_iff :
    (0 ≤ (chainModel C').param Q x ∧ (chainModel C').param Q x < 1) ↔
      (0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1) := by
  rcases hx with h0 | ⟨k, hk, hy⟩
  · grind [Model.param]
  · rw [h.param'_eq hk hy, param_eq _ Q x k hk]
    split_ifs with hh
    · simp_all
    · exact ratio_mem_sig_iff hh

theorem param_eq_zero_iff :
    (chainModel C').param Q x = 0 ↔ (chainModel C).param Q x = 0 := by
  rcases hx with h0 | ⟨k, hk, hy⟩
  · grind [Model.param]
  · rw [h.param'_eq hk hy, param_eq _ Q x k hk]
    split_ifs with hh
    · simp_all
    · exact ratio_eq_zero_sig_iff hh



end

end

/-- On one walk edge the parameters of band positions are ordered alike. -/
theorem param_lt_iff {Q : Polygon} {x x' : WPos} (hx : BandPos C C' Q x) (hx' : BandPos C C' Q x')
    (he : x.edge = x'.edge) (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1)
    (hm' : 0 ≤ (chainModel C).param Q x' ∧ (chainModel C).param Q x' < 1) :
    (chainModel C').param Q x < (chainModel C').param Q x' ↔
      (chainModel C).param Q x < (chainModel C).param Q x' := by
  have z1 := h.param_eq_zero_iff hx
  have z2 := h.param_eq_zero_iff hx'
  have r1 := (h.param_mem_iff hx).2 hm
  have r2 := (h.param_mem_iff hx').2 hm'
  -- when one parameter is zero the comparison is with zero
  have hzero : ∀ (u v u' v' : ℝ), 0 ≤ u → 0 ≤ v → 0 ≤ u' → 0 ≤ v' → (u' = 0 ↔ u = 0) →
      (v' = 0 ↔ v = 0) → (u = 0 ∨ v = 0) → (u' < v' ↔ u < v) := by
    ram_grind
  by_cases h0 : (chainModel C).param Q x = 0 ∨ (chainModel C).param Q x' = 0
  · exact hzero _ _ _ _ hm.1 hm'.1 r1.1 r2.1 z1 z2 h0
  push Not at h0
  rcases hx with hx0 | ⟨k, hk, hy⟩
  · exact absurd (by simp [Model.param, hx0]) h0.1
  rcases hx' with hx0 | ⟨k', hk', hy'⟩
  · exact absurd (by simp [Model.param, hx0]) h0.2
  have hne0 := h0.1
  rw [param_eq _ Q x k hk] at hne0
  rw [h.param'_eq hk hy, h.param'_eq hk' hy', param_eq _ Q x k hk, param_eq _ Q x' k' hk', ← he]
  by_cases hh : ((chainModel C).wa x.edge).2 = ((chainModel C).wb x.edge).2
  · ram_grind
  · simp only [hh, ↓reduceIte]; exact ratio_lt_sig_iff hh

section
variable {Q : Polygon} {x x' : WPos} (hx : BandPos C C' Q x) (hx' : BandPos C C' Q x') (hm : 0 ≤ (chainModel C).param Q x ∧ (chainModel C).param Q x < 1) (hm' : 0 ≤ (chainModel C).param Q x' ∧ (chainModel C).param Q x' < 1)
include hx hx' hm hm'
/-- **Keys are ordered alike in the two models.** -/
theorem key_lt_iff :
    (chainModel C').key Q x < (chainModel C').key Q x' ↔
      (chainModel C).key Q x < (chainModel C).key Q x' := by
  grind [Chazelle.Core.BoxT.Twin.param_mem_iff, Chazelle.Core.BoxT.key_lt_iff_lex, Chazelle.Core.BoxT.Twin.param_lt_iff]

/-- **Arc weights between band positions agree.** -/
theorem arcWt_eq :
    (chainModel C').arcWt ((chainModel C').key Q x) ((chainModel C').key Q x') =
      (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q x') := by
  have hn : (chainModel C).W.n = 2 * C.m + 6 + 1 := by rw [chainModel_n]
  have hn' : (chainModel C').W.n = 2 * C.m + 6 + 1 := by rw [chainModel_n, ← h.m_eq]
  have hc : ∀ p, p < (chainModel C).W.n →
      ((chainModel C).counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6) := fun p _ => Iff.rfl
  have hc' : ∀ p, p < (chainModel C').W.n →
      ((chainModel C').counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6) := by
    intro p _; show (6 ≤ p ∧ p < 2 * C'.m + 6) ↔ _; rw [h.m_eq]
  have r1 := (h.param_mem_iff hx).2 hm
  have r2 := (h.param_mem_iff hx').2 hm'
  rw [Model.arcWt_key _ hc (by omega) Q hm hm', Model.arcWt_key _ hc' (by omega) Q r1 r2]
  unfold arcWtNat keyCeil
  have hlt := h.key_lt_iff hx hx' hm hm'
  unfold Model.key at hlt
  simp only [hlt, h.param_eq_zero_iff hx']


end

end Twin

end

end BoxT

end Chazelle.Core
