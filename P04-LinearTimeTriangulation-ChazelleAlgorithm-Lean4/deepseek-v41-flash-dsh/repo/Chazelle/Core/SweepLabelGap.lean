module

public import Chazelle.Core.SweepLabel
public import Chazelle.Core.FactsTie

/-!
# The sweep (WP-D), part 4b: lemma (K) up to the gap (ties at the top, F2)

With a tie at the top of the chain of `M₂` (design doc §9.10) there may be no chord of `F`
separating the positions of the stretch before the gap from those after it, and lemma (K) fails
in general.  It survives up to the two regions of `S` at the sides of the gap: if two positions
of the stretch face the same region of `F` and their counterparts face different regions of `S`,
then the gap lies between them, the position before the gap has the region faced just after the
split vertex `(g' + L1)` of `M₂` (`AfterFaces`), and the position after the gap the region faced
just before `(g' + L1 + δ)` (`BeforeFaces`).

The gap facts needed (`CorrGap`, proved for a junction in `SweepLabelJ`):
* a chord of `S` attached strictly inside the gap meets the stretch in at most one point;
* at each copy of the split vertex of `M₂` at most one chord of `S` is attached;
* a chord of `F` through the split vertex of `M` is attached there.

* `sideInArc_rev_iff_off`, `no_cross_off`, `eventually_not_cut_after/before`: walk order and
  cuts in offsets (moved here from `SweepBracket`, `SweepQuery`).
* `label_gen3`: the generic lemma (K3).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft)
open WalkEmbed

namespace Sweep

/-! ## Walk order in offsets -/

/-- The complementary cyclic interval in offsets. -/
theorem sideInArc_rev_iff_off {n g u w x : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hu : 0 ≤ u)
    (hun : u < n) (hw : 0 ≤ w) (hwn : w < n) (hx : 0 ≤ x) (hxn : x < n)
    (huw : off n g u < off n g w) :
    sideInArc w u x ↔ off n g x < off n g u ∨ off n g w < off n g x := by
  unfold off at *
  unfold sideInArc
  split_ifs at * <;> constructor <;>
    first
    | (rintro ⟨h1, h2⟩; first | (left; linarith) | (right; linarith))
    | (rintro (h1 | h1) <;>
        first | (left; linarith) | (right; linarith) | (constructor <;> linarith))

/-- **Non-crossing in offsets.**  If one attachment of a chord `d` lies strictly between the two
attachments of a chord `c` (in offsets from `g`), so does (weakly) every other attachment of
`d`. -/
theorem no_cross_off {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c d : Set Point} (hc : c ∈ F) (hd : d ∈ F) (hcd : c ≠ d)
    {pa pb px py : ℕ} {ta tb tx ty : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (hX : SideAttach M.W d px tx) (hY : SideAttach M.W d py ty) {g : ℝ} (hg0 : 0 ≤ g)
    (hgn : g < M.W.n) (hab : off M.W.n g (pa + ta) < off M.W.n g (pb + tb))
    (hx1 : off M.W.n g (pa + ta) < off M.W.n g (px + tx))
    (hx2 : off M.W.n g (px + tx) < off M.W.n g (pb + tb)) :
    off M.W.n g (pa + ta) ≤ off M.W.n g (py + ty) ∧
      off M.W.n g (py + ty) ≤ off M.W.n g (pb + tb) := by
  obtain ⟨a0, a1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  obtain ⟨x0, x1⟩ := Corr.key_mem hX.1 hX.2.1 hX.2.2.1
  obtain ⟨y0, y1⟩ := Corr.key_mem hY.1 hY.2.1 hY.2.2.1
  by_contra hcon
  have hy : off M.W.n g (py + ty) < off M.W.n g (pa + ta) ∨
      off M.W.n g (pb + tb) < off M.W.n g (py + ty) := by
    by_contra h
    push Not at h
    exact hcon h
  apply hM.no_cross hF hfin hc hd hcd hA hB hAB hX hY
  exact ⟨(sideInArc_iff_off hg0 hgn a0 a1 b0 b1 x0 x1 hab).2 ⟨hx1, hx2⟩,
    (sideInArc_rev_iff_off hg0 hgn a0 a1 b0 b1 y0 y1 hab).2 hy⟩

section NonCut

variable {M : Model}

/-- The keys just after a key are not cuts. -/
theorem eventually_not_cut_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F (x + s) := by
  have hK := hM.finite_cuts hF hfin
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x + s ≠ y)).2 fun y _ => by
      rcases le_or_gt y x with hy | hy
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have : (0 : ℝ) < s := hs
        intro h; linarith
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y - x by linarith)] with s hs
        intro h; linarith [hs.2]
  filter_upwards [h] with s hs hcut
  exact hs _ hcut rfl

/-- The keys just before a key are not cuts. -/
theorem eventually_not_cut_before (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F (x - s) := by
  have hK := hM.finite_cuts hF hfin
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x - s ≠ y)).2 fun y _ => by
      rcases le_or_gt x y with hy | hy
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have : (0 : ℝ) < s := hs
        intro h; linarith
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - y by linarith)] with s hs
        intro h; linarith [hs.2]
  filter_upwards [h] with s hs hcut
  exact hs _ hcut rfl

end NonCut

/-! ## Faced regions just after and just before a position -/

/-- The positions just after `(p, t)` (on the same walk edge) face `U`. -/
def AfterFaces (M : Model) (p : ℕ) (t : ℝ) (U : Set Point) : Prop :=
  ∃ δ > (0 : ℝ), ∀ s, 0 < s → s < δ → t + s < 1 → M.Faces p (t + s) U

/-- The positions just before `(p, t)` (on the same walk edge if `0 < t`, on the previous one if
`t = 0`) face `U`. -/
def BeforeFaces (M : Model) (p : ℕ) (t : ℝ) (U : Set Point) : Prop :=
  ∃ δ > (0 : ℝ), (0 < t → ∀ s, 0 < s → s < δ → s < t → M.Faces p (t - s) U) ∧
    (t = 0 → ∀ s, 0 < s → s < δ → M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) U)

/-! ## Correspondences without a separating chord -/

/-- **A correspondence without a separating chord at the gap** (F2, `Corr` minus `box`) between the walk of a model `M` (read from the vertex `g`) and the walk
of a model `M₂` (read from `g'`): they agree along a first piece of length `L1` and, after a gap of
`δ` walk vertices of `M₂` (the box of `C₂`, when `δ > 0`), along a second piece of length `L2`.
Chords of `S` (in `M₂`) through walk points of `M₂` other than the base point contain chords of
`F` (in `M`) through the same point; distinct chords of `F` are not nested.  (The gap needs no
separating chord: with ties at the top of the chain of `M₂` there may be none, and lemma (K)
holds up to the two regions at the sides of the gap, `SweepLabelGap.label_gen3`.) -/
structure Corr0 (M M₂ : Model) (F S : Set (Set Point)) (g g' L1 L2 δ : ℕ) : Prop where
  hM : WalkAx M
  hM₂ : WalkAx M₂
  hF : F ⊆ M.Adm
  hfin : F.Finite
  hS : S ⊆ M₂.Adm
  hSfin : S.Finite
  hg : g < M.W.n
  hg' : g' < M₂.W.n
  hL : L1 + L2 ≤ M.W.n
  hL₂ : L1 + δ + L2 ≤ M₂.W.n
  hδ : δ = 0 → L2 = 0
  hfull : 0 < δ → L1 + δ + L2 = M₂.W.n
  A1 : Agree M.W M₂.W g g' L1
  A2 : Agree M.W M₂.W (g + L1) (g' + L1 + δ) L2
  noV : ∀ p < M₂.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < off M₂.W.n g' (p + t) →
    off M₂.W.n g' (p + t) < L1 + δ + L2 → sidePt M₂.W p t ≠ M₂.W.vtx g'
  trans : ∀ c ∈ S, ∀ q ∈ c, q ∉ M₂.D → q ≠ M₂.W.vtx g' → ∃ e ∈ F, q ∈ e ∧ e ⊆ c
  nest : ∀ e ∈ F, ∀ e' ∈ F, e ⊆ e' → e = e'

namespace Corr0

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

theorem n_pos (hC : Corr0 M M₂ F S g g' L1 L2 δ) : 0 < M.W.n := by have := hC.hg; omega

theorem n₂_pos (hC : Corr0 M M₂ F S g g' L1 L2 δ) : 0 < M₂.W.n := by have := hC.hg'; omega

theorem dq_lt (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) :
    dq L1 δ d < M₂.W.n := by
  have := hC.hL₂; unfold dq; split_ifs <;> omega

/-- Agreeing points. -/
theorem sidePt_eq (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) (t : ℝ) :
    sidePt M.W ((g + d) % M.W.n) t = sidePt M₂.W ((g' + dq L1 δ d) % M₂.W.n) t := by
  unfold dq
  split_ifs with h
  · exact hC.A1.sidePt_eq h t
  · have := hC.A2.sidePt_eq (d := d - L1) (⋄) t
    rwa [show g + L1 + (d - L1) = g + d by omega,
      show g' + L1 + δ + (d - L1) = g' + (d + δ) by omega] at this

/-- Agreeing attachments (away from the base and the split vertex). -/
theorem attach_iff (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) (c : Set Point) :
    SideAttach M.W c ((g + d) % M.W.n) t ↔ SideAttach M₂.W c ((g' + dq L1 δ d) % M₂.W.n) t := by
  unfold dq
  split_ifs with h
  · exact hC.A1.sideAttach_iff hC.n_pos hC.n₂_pos h (fun h0 => by
      have := (hsec h0).1; omega) c
  · have := hC.A2.sideAttach_iff hC.n_pos hC.n₂_pos (d := d - L1) (⋄) (t := t)
      (fun h0 => by have := (hsec h0).2; omega) c
    rwa [show g + L1 + (d - L1) = g + d by omega,
      show g' + L1 + δ + (d - L1) = g' + (d + δ) by omega] at this

/-- The offset of a position of the stretch of `M`. -/
theorem off_M (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    off M.W.n g (((g + d) % M.W.n : ℕ) + t) = d + t :=
  off_key hC.hg (by have := hC.hL; omega) ht ht1

/-- The offset of the corresponding position of `M₂`. -/
theorem off_M₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    off M₂.W.n g' (((g' + dq L1 δ d) % M₂.W.n : ℕ) + t) = dq L1 δ d + t :=
  off_key hC.hg' (hC.dq_lt hd) ht ht1

/-- **Transfer of an attachment** from `M₂` to `M` along the stretch. -/
theorem transfer (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) {c : Set Point} (hc : c ∈ S)
    (hA : SideAttach M₂.W c ((g' + dq L1 δ d) % M₂.W.n) t) :
    ∃ e ∈ F, e ⊆ c ∧ sidePt M.W ((g + d) % M.W.n) t ∈ e ∧
      SideAttach M.W e ((g + d) % M.W.n) t := by
  have hpos : 0 < (dq L1 δ d : ℝ) + t := by
    rcases ht.lt_or_eq with h | h
    · have : (0 : ℝ) ≤ dq L1 δ d := Nat.cast_nonneg _
      linarith
    · have hd0 := (hsec h.symm).1
      have : 1 ≤ dq L1 δ d := by unfold dq; split_ifs <;> omega
      have : (1 : ℝ) ≤ dq L1 δ d := by exact_mod_cast this
      linarith
  have hlt : (dq L1 δ d : ℝ) + t < L1 + δ + L2 := by
    have : dq L1 δ d + 1 ≤ L1 + δ + L2 := by unfold dq; split_ifs <;> omega
    have : (dq L1 δ d : ℝ) + 1 ≤ L1 + δ + L2 := by exact_mod_cast this
    linarith
  have hq : sidePt M₂.W ((g' + dq L1 δ d) % M₂.W.n) t ≠ M₂.W.vtx g' := by
    refine hC.noV _ (Nat.mod_lt _ hC.n₂_pos) t ht ht1 ?_ ?_ <;> Ξ hC.off_M₂ hd ht ht1
    · exact hpos
    · exact hlt
  have hqD : sidePt M₂.W ((g' + dq L1 δ d) % M₂.W.n) t ∉ M₂.D :=
    hC.hM₂.trace _ (Nat.mod_lt _ hC.n₂_pos) t ht ht1.le
  obtain ⟨e, he, hqe, hec⟩ := hC.trans c hc _ hA.2.2.2.1 hqD hq
  have hpt := hC.sidePt_eq hd t
  refine ⟨e, he, hec, by rw [hpt]; exact hqe, ?_⟩
  Ξ hC.attach_iff hd hsec
  obtain ⟨hp, ht0, ht1', -, r, hr, hl⟩ := hA
  exact ⟨hp, ht0, ht1', hqe, r, hr, fun x hx => hl x (hec hx)⟩

end Corr0

namespace Corr0

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- Decomposing a position of the walk of `M` by its offset from `g`. -/
theorem decomp (hC : Corr0 M M₂ F S g g' L1 L2 δ) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) :
    (g + dOf M.W.n g p) % M.W.n = p ∧ off M.W.n g (p + t) = dOf M.W.n g p + t :=
  ⟨add_dOf hC.hg hp, off_key' hC.hg hp ht ht1⟩

/-- Decomposing a position of the walk of `M₂` by its offset from `g'`. -/
theorem decomp₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {p : ℕ} (hp : p < M₂.W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) :
    (g' + dOf M₂.W.n g' p) % M₂.W.n = p ∧ off M₂.W.n g' (p + t) = dOf M₂.W.n g' p + t :=
  ⟨add_dOf hC.hg' hp, off_key' hC.hg' hp ht ht1⟩

/-- A second attachment of a transferred chord (through a point `q` of a chord `c` of `S`) never
lies between two positions of the stretch unless the corresponding attachment of `c` does. -/
theorem other_not_btw (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    {c : Set Point} (hc : c ∈ S) {pb : ℕ} {tb : ℝ} (hB : SideAttach M₂.W c pb tb)
    (hout : ¬ Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb)))
    {e : Set Point} (he : e ∈ F) (hec : e ⊆ c) {q : Point} (hqe : q ∈ e) (hqD : q ∉ M₂.D)
    (hqB : sidePt M₂.W pb tb ≠ q) {p₃ : ℕ} {t₃ : ℝ} (hA₃ : SideAttach M.W e p₃ t₃)
    (hne : sidePt M.W p₃ t₃ ≠ q) :
    ¬ Btw (d + t) (d' + t') (off M.W.n g (p₃ + t₃)) := by
  intro hb3
  have hn := hC.n_pos
  have hn₂ := hC.n₂_pos
  have hcS : c ∈ M₂.Adm := hC.hS hc
  have heF : e ∈ M.Adm := hC.hF he
  -- the offsets of the positions
  have hox0 : (0 : ℝ) < d + t := by have := ht.1; positivity
  have hox0' : (0 : ℝ) < d' + t' := by have := ht'.1; positivity
  have hoxL : (d : ℝ) + t < L1 + L2 := by
    have : (d : ℝ) + 1 ≤ L1 + L2 := by exact_mod_cast hd
    linarith [ht.2]
  have hoxL' : (d' : ℝ) + t' < L1 + L2 := by
    have : (d' : ℝ) + 1 ≤ L1 + L2 := by exact_mod_cast hd'
    linarith [ht'.2]
  obtain ⟨hp₃e, ho₃⟩ := hC.decomp hA₃.1 hA₃.2.1 hA₃.2.2.1
  set d₃ := dOf M.W.n g p₃ with hd₃def
  have ho₃b : 0 < (d₃ : ℝ) + t₃ ∧ (d₃ : ℝ) + t₃ < L1 + L2 := by
    Ξ ← ho₃
    rcases hb3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hd₃ : d₃ < L1 + L2 := by
    have : (d₃ : ℝ) < L1 + L2 := by linarith [hA₃.2.1, ho₃b.2]
    exact_mod_cast this
  -- the ends of `c`
  obtain ⟨a₀, b₀, hab₀, -, hend⟩ := end_of_not_mem hC.hM₂ hcS
  have hyb := hB.2.2.2.1
  have hybD : sidePt M₂.W pb tb ∉ M₂.D := hC.hM₂.trace _ hB.1 _ hB.2.1 hB.2.2.1.le
  -- the other end of `c` is the point of the attachment `(pb, tb)`
  have hother : ∀ y ∈ c, y ∉ M₂.D → y ≠ q → y = sidePt M₂.W pb tb := by
    intro y hy hyD hyq
    have h1 := hend q (hec hqe) hqD
    have h2 := hend y hy hyD
    have h3 := hend _ hyb hybD
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with h3 | h3 <;>
      first | exact absurd rfl hyq | exact h3.symm | exact absurd h3 hqB
  by_cases hsplit : t₃ = 0 ∧ d₃ = L1
  · -- the second attachment is at the split vertex
    obtain ⟨ht₃, hd₃L⟩ := hsplit
    have hL2 : 0 < L2 := by
      have : (d₃ : ℝ) + t₃ < L1 + L2 := ho₃b.2
      Ξ' ht₃, hd₃L at this
      have : (0 : ℝ) < L2 := ⟡
      exact_mod_cast this
    have hδ : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · exact absurd (hC.hδ h) (⋄)
      · exact h
    have hpt₃ : sidePt M.W p₃ t₃ = M₂.W.vtx ((g' + L1) % M₂.W.n) := by
      rw [ht₃, Chazelle.Chain.sidePt_zero, ← hp₃e, hd₃L]; exact hC.A1 L1 le_rfl
    have hy₃D : sidePt M.W p₃ t₃ ∉ M₂.D := by
      Ξ hpt₃, ← Chazelle.Chain.sidePt_zero
      exact hC.hM₂.trace _ (Nat.mod_lt _ hn₂) 0 le_rfl zero_le_one
    have hec' : e = c := eq_of_ends hC.hM hC.hM₂ heF hcS hec (Ne.symm hne) hqe hA₃.2.2.2.1 hqD hy₃D
    have hyb₃ : sidePt M₂.W pb tb = sidePt M.W p₃ t₃ :=
      (hother _ (hec hA₃.2.2.2.1) hy₃D hne).symm
    -- the positions lie on both sides of the gap
    have hL1pos : (0 : ℝ) < L1 := by rw [ht₃, hd₃L] at ho₃b; simpa using ho₃b.1
    have hx_side : ∀ {k : ℕ} {s : ℝ}, s ∈ Ioo (0 : ℝ) 1 → (k : ℝ) + s < L1 →
        ((dq L1 δ k : ℕ) : ℝ) + s < L1 := by
      intro k s hs h
      have hk : k < L1 := by
        have : (k : ℝ) < L1 := by linarith [hs.1]
        exact_mod_cast this
      unfold dq; rw [ite_eq_left hk]; exact h
    have hx_side' : ∀ {k : ℕ} {s : ℝ}, s ∈ Ioo (0 : ℝ) 1 → (L1 : ℝ) < k + s →
        (L1 : ℝ) + δ < ((dq L1 δ k : ℕ) : ℝ) + s := by
      intro k s hs h
      have hk : L1 ≤ k := by
        have : (L1 : ℝ) < k + 1 := by linarith [hs.2]
        have : L1 < k + 1 := by exact_mod_cast this
        omega
      unfold dq; rw [ite_eq_right (⋄)]; push_cast
      have : (L1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith [hs.1]
    obtain ⟨hpbe, hob⟩ := hC.decomp₂ hB.1 hB.2.1 hB.2.2.1
    set db := dOf M₂.W.n g' pb with hdbdef
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    -- the attachment `(pb, tb)` is outside the gap
    have hgap : off M₂.W.n g' (pb + tb) < L1 ∨ (L1 : ℝ) + δ < off M₂.W.n g' (pb + tb) := by
      Ξ' ho₃, ht₃, hd₃L, add_zero at hb3
      rcases hb3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a1 := hx_side ht h1
        have a2 := hx_side' ht' h2
        by_contra hc'; push Not at hc'
        exact hout (Or.inl ⟨by linarith [hc'.1], by linarith [hc'.2]⟩)
      · have a1 := hx_side ht' h1
        have a2 := hx_side' ht h2
        by_contra hc'; push Not at hc'
        exact hout (Or.inr ⟨by linarith [hc'.1], by linarith [hc'.2]⟩)
    -- transfer `(pb, tb)` to the walk of `M` and compare with the split vertex
    have key : ∀ d₀ : ℕ, d₀ < L1 + L2 → (tb = 0 → d₀ ≠ 0 ∧ d₀ ≠ L1) →
        (g' + dq L1 δ d₀) % M₂.W.n = pb → d₀ = L1 ∧ tb = 0 := by
      intro d₀ hd₀ hsec hpb
      have hB' : SideAttach M₂.W c ((g' + dq L1 δ d₀) % M₂.W.n) tb := by rw [hpb]; exact hB
      obtain ⟨e'', he'', he''c, hpt'', hA''⟩ := hC.transfer hd₀ hB.2.1 hB.2.2.1 hsec hc hB'
      have he''e : e'' = e := hC.nest e'' he'' e he (by rw [hec']; exact he''c)
      Ξ' he''e at hA''
      have hpteq : sidePt M.W ((g + d₀) % M.W.n) tb = sidePt M.W p₃ t₃ := by
        Ξ hC.sidePt_eq hd₀, hpb, hyb₃
      obtain ⟨h1, h2⟩ := WalkAx.attach_unique hC.hM heF hA'' hA₃ hpteq
      Ξ' ← hp₃e, hd₃L at h1
      exact ⟨add_mod_inj (by have := hC.hL; omega) (by have := hC.hL; omega) h1, Ρ h2, ht₃⟩
    have hobn : (db : ℝ) + tb < M₂.W.n := by
      have : db + 1 ≤ M₂.W.n := dOf_lt hn₂ g' pb
      have : (db : ℝ) + 1 ≤ M₂.W.n := by exact_mod_cast this
      linarith [hB.2.2.1]
    Ξ' hob at hgap
    rcases hgap with hlow | hhigh
    · have hdb : db < L1 := by
        have : (db : ℝ) < L1 := by linarith [hB.2.1]
        exact_mod_cast this
      by_cases h0 : db = 0 ∧ tb = 0
      · -- the base point is not the split vertex
        apply hC.noV ((g' + L1) % M₂.W.n) (Nat.mod_lt _ hn₂) 0 le_rfl zero_lt_one
        · rw [off_key hC.hg' (by have := hC.hL₂; omega) le_rfl zero_lt_one]; simpa using hL1pos
        · Ξ off_key hC.hg' (by have := hC.hL₂; omega) le_rfl zero_lt_one
          have : (0 : ℝ) < L2 := by exact_mod_cast hL2
          linarith
        · rw [Chazelle.Chain.sidePt_zero, ← hpt₃, ← hyb₃, ← hpbe, h0.1, h0.2, add_zero,
            Nat.mod_eq_of_lt hC.hg', Chazelle.Chain.sidePt_zero]
      · have hsec : tb = 0 → db ≠ 0 ∧ db ≠ L1 := fun htb =>
          ⟨fun hdb0 => h0 ⟨hdb0, htb⟩, ⋄⟩
        have hdq : dq L1 δ db = db := by unfold dq; Ξ ite_eq_left hdb
        obtain ⟨h1, -⟩ := key db (⋄) hsec (by rw [hdq]; exact hpbe)
        omega
    · have hdb : L1 + δ ≤ db := by
        by_contra hlt; push Not at hlt
        have : (db : ℝ) + 1 ≤ L1 + δ := by exact_mod_cast hlt
        linarith [hB.2.2.1]
      have hdbn : db < L1 + δ + L2 := by
        have : (db : ℝ) < L1 + δ + L2 := by
          have := hC.hfull hδ
          have : ((L1 + δ + L2 : ℕ) : ℝ) = M₂.W.n := by exact_mod_cast this
          push_cast at this; linarith [hB.2.1]
        exact_mod_cast this
      have hsec : tb = 0 → db - δ ≠ 0 ∧ db - δ ≠ L1 := by
        intro htb
        Ξ' htb, add_zero at hhigh
        have : L1 + δ < db := by exact_mod_cast hhigh
        constructor <;> omega
      have hdq : dq L1 δ (db - δ) = db := by unfold dq; rw [ite_eq_right (⋄)]; omega
      obtain ⟨h1, h2⟩ := key (db - δ) (⋄) hsec (by rw [hdq]; exact hpbe)
      Ξ' h2, add_zero at hhigh
      have : (db : ℝ) = L1 + δ := by
        have : db = L1 + δ := ⋄
        exact_mod_cast this
      linarith
  · -- the second attachment is at a regular position of the stretch
    have hsec₃ : t₃ = 0 → d₃ ≠ 0 ∧ d₃ ≠ L1 := by
      intro h0
      refine ⟨fun hz => ?_, fun hL => hsplit ⟨h0, hL⟩⟩
      have := ho₃b.1; Ξ' hz, h0 at this; simp at this
    have hA₃' : SideAttach M.W e ((g + d₃) % M.W.n) t₃ := by rw [hp₃e]; exact hA₃
    have hpt₃ : sidePt M.W p₃ t₃ = sidePt M₂.W ((g' + dq L1 δ d₃) % M₂.W.n) t₃ := by
      rw [← hp₃e]; exact hC.sidePt_eq hd₃ t₃
    have hy₃D : sidePt M.W p₃ t₃ ∉ M₂.D := by
      rw [hpt₃]; exact hC.hM₂.trace _ (Nat.mod_lt _ hn₂) _ hA₃.2.1 hA₃.2.2.1.le
    have hec' : e = c := eq_of_ends hC.hM hC.hM₂ heF hcS hec (Ne.symm hne) hqe hA₃.2.2.2.1 hqD hy₃D
    have hAc : SideAttach M₂.W c ((g' + dq L1 δ d₃) % M₂.W.n) t₃ := by
      rw [← hec']; exact (hC.attach_iff hd₃ hsec₃ e).1 hA₃'
    have hyb₃ : sidePt M₂.W pb tb = sidePt M₂.W ((g' + dq L1 δ d₃) % M₂.W.n) t₃ := by
      rw [← hpt₃]; exact (hother _ (hec hA₃.2.2.2.1) hy₃D hne).symm
    obtain ⟨h1, h2⟩ := WalkAx.attach_unique hC.hM₂ hcS hB hAc hyb₃
    apply hout
    have hob : off M₂.W.n g' (pb + tb) = ((dq L1 δ d₃ : ℕ) : ℝ) + t₃ := by
      rw [h1, h2]; exact hC.off_M₂ hd₃ hA₃.2.1 hA₃.2.2.1
    Ξ hob
    apply btw_of_psi (L1 := L1) (δ := δ)
    Ξ psi_dq ht.1.le ht.2, psi_dq ht'.1.le ht'.2, psi_dq hA₃.2.1 hA₃.2.2.1, ← ho₃
    exact hb3

end Corr0

namespace Corr0

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- **Mirroring a separation**: if a chord of `S` has one attachment between the positions of
`M₂` corresponding to two positions of the stretch and the other not, a chord of `F` has one
attachment between the two positions of `M` and the other not. -/
theorem mirror (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    {c : Set Point} (hc : c ∈ S) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta)
    (hB : SideAttach M₂.W c pb tb) (hAB : sidePt M₂.W pa ta ≠ sidePt M₂.W pb tb)
    (hin : Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pa + ta)))
    (hout : ¬ Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb))) :
    (∃ e ∈ F, ∃ (p₁ p₃ : ℕ) (t₁ t₃ : ℝ), SideAttach M.W e p₁ t₁ ∧ SideAttach M.W e p₃ t₃ ∧
      sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃ ∧ Btw (d + t) (d' + t') (off M.W.n g (p₁ + t₁)) ∧
      ¬ Btw (d + t) (d' + t') (off M.W.n g (p₃ + t₃))) ∨ InGap L1 δ (off M₂.W.n g' (pa + ta)) := by
  have hn := hC.n_pos
  have hn₂ := hC.n₂_pos
  obtain ⟨hpae, hoa⟩ := hC.decomp₂ hA.1 hA.2.1 hA.2.2.1
  set da := dOf M₂.W.n g' pa with hdadef
  have hbx : ∀ {k : ℕ} {s : ℝ}, k < L1 + L2 → s ∈ Ioo (0 : ℝ) 1 →
      0 < ((dq L1 δ k : ℕ) : ℝ) + s ∧ ((dq L1 δ k : ℕ) : ℝ) + s < L1 + δ + L2 := by
    intro k s hk hs
    refine ⟨by have := hs.1; positivity, ?_⟩
    have : dq L1 δ k + 1 ≤ L1 + δ + L2 := by unfold dq; split_ifs <;> omega
    have : ((dq L1 δ k : ℕ) : ℝ) + 1 ≤ L1 + δ + L2 := by exact_mod_cast this
    linarith [hs.2]
  obtain ⟨hx1, hx2⟩ := hbx hd ht
  obtain ⟨hx1', hx2'⟩ := hbx hd' ht'
  have hoab : 0 < off M₂.W.n g' (pa + ta) ∧ off M₂.W.n g' (pa + ta) < L1 + δ + L2 := by
    rcases hin with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  Ξ' hoa at hoab hin
  have hbtw := btw_psi (not_inGap_dq ht.1 ht.2) (not_inGap_dq ht'.1 ht'.2) hin
  Ξ' psi_dq ht.1.le ht.2, psi_dq ht'.1.le ht'.2 at hbtw
  set q := sidePt M₂.W pa ta with hq
  have hqD : q ∉ M₂.D := hC.hM₂.trace _ hA.1 _ hA.2.1 hA.2.2.1.le
  -- the transferred case
  have trans_case : ∀ d₀ : ℕ, d₀ < L1 + L2 → (ta = 0 → d₀ ≠ 0 ∧ d₀ ≠ L1) →
      (g' + dq L1 δ d₀) % M₂.W.n = pa → (d₀ : ℝ) + ta = psi L1 δ (da + ta) →
      ∃ e ∈ F, ∃ (p₁ p₃ : ℕ) (t₁ t₃ : ℝ), SideAttach M.W e p₁ t₁ ∧ SideAttach M.W e p₃ t₃ ∧
        sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃ ∧ Btw (d + t) (d' + t') (off M.W.n g (p₁ + t₁)) ∧
        ¬ Btw (d + t) (d' + t') (off M.W.n g (p₃ + t₃)) := by
    intro d₀ hd₀ hsec hpa hpsi
    have hA' : SideAttach M₂.W c ((g' + dq L1 δ d₀) % M₂.W.n) ta := by rw [hpa]; exact hA
    obtain ⟨e, he, hec, hpte, hAe⟩ := hC.transfer hd₀ hA.2.1 hA.2.2.1 hsec hc hA'
    have hptq : sidePt M.W ((g + d₀) % M.W.n) ta = q := Ρ hC.sidePt_eq hd₀, hpa
    obtain ⟨p₃, t₃, hA₃, hne₃⟩ := WalkAx.other_attach hC.hM (hC.hF he) hAe
    refine ⟨e, he, _, p₃, ta, t₃, hAe, hA₃, hne₃.symm, ?_, ?_⟩
    · rw [hC.off_M hd₀ hA.2.1 hA.2.2.1, hpsi]; exact hbtw
    · exact hC.other_not_btw hd hd' ht ht' hc hB hout he hec (by rw [← hptq]; exact hpte) hqD
        (Ne.symm hAB) hA₃ (by rw [← hptq]; exact hne₃)
  by_cases hA1 : da < L1
  · have hdq : dq L1 δ da = da := by unfold dq; Ξ ite_eq_left hA1
    refine Or.inl (trans_case da (⋄) (fun h0 => ⟨fun hz => ?_, ⋄⟩)
      (by rw [hdq]; exact hpae) ?_)
    · have := hoab.1; Ξ' h0, hz at this; simp at this
    · have := psi_dq (L1 := L1) (δ := δ) (d := da) hA.2.1 hA.2.2.1
      Ξ' hdq at this; exact this.symm
  by_cases hA3 : (L1 : ℝ) + δ < da + ta
  · have hda : L1 + δ ≤ da := by
      by_contra hlt; push Not at hlt
      have : (da : ℝ) + 1 ≤ L1 + δ := by exact_mod_cast hlt
      linarith [hA.2.2.1]
    have hdq : dq L1 δ (da - δ) = da := by unfold dq; rw [ite_eq_right (⋄)]; omega
    have hdan : da < L1 + δ + L2 := by
      have : (da : ℝ) < L1 + δ + L2 := by linarith [hA.2.1, hoab.2]
      exact_mod_cast this
    refine Or.inl (trans_case (da - δ) (⋄) (fun h0 => ?_) (by rw [hdq]; exact hpae) ?_)
    · Ξ' h0, add_zero at hA3
      have : L1 + δ < da := by exact_mod_cast hA3
      constructor <;> omega
    · have := psi_dq (L1 := L1) (δ := δ) (d := da - δ) hA.2.1 hA.2.2.1
      Ξ' hdq at this; exact this.symm
  -- the gap
  push Not at hA1 hA3
  right
  Ξ hoa
  refine ⟨?_, hA3⟩
  have : (L1 : ℝ) ≤ da := by exact_mod_cast hA1
  linarith [hA.2.1]

end Corr0

/-! ## The gap facts -/

/-- A point of the stretch of `M`: a position at offset in `(0, L)` from `g`. -/
def StrPt (M : Model) (g L : ℕ) (x : Point) : Prop :=
  ∃ d < L, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧ sidePt M.W ((g + d) % M.W.n) t = x

/-- **The gap facts** of a correspondence with a gap (`δ > 0`): a chord of `S` attached strictly
inside the gap meets the stretch of `M` in at most one point; at each copy of the split vertex
of `M₂` at most one chord of `S` is attached; a chord of `F` through the split vertex of `M`,
inside a chord of `S` attached at a copy of the split vertex in `M₂`, is attached at the split
vertex of `M`. -/
structure CorrGap (M M₂ : Model) (F S : Set (Set Point)) (g g' L1 L2 δ : ℕ) : Prop where
  gapOut : ∀ c ∈ S, ∀ (pa : ℕ) (ta : ℝ), SideAttach M₂.W c pa ta →
    (L1 : ℝ) < off M₂.W.n g' (pa + ta) → off M₂.W.n g' (pa + ta) < L1 + δ →
    ∀ x ∈ c, ∀ y ∈ c, StrPt M g (L1 + L2) x → StrPt M g (L1 + L2) y → x = y
  oneAt : ∀ k : ℕ, (k = L1 ∨ k = L1 + δ) → ∀ c ∈ S, ∀ c' ∈ S,
    SideAttach M₂.W c ((g' + k) % M₂.W.n) 0 → SideAttach M₂.W c' ((g' + k) % M₂.W.n) 0 →
      c = c'
  splitAttach : ∀ k : ℕ, (k = L1 ∨ k = L1 + δ) → ∀ c ∈ S,
    SideAttach M₂.W c ((g' + k) % M₂.W.n) 0 → ∀ e ∈ F, e ⊆ c →
      sidePt M.W ((g + L1) % M.W.n) 0 ∈ e → SideAttach M.W e ((g + L1) % M.W.n) 0

/-- **A third attachment** of an admissible chord is one of two attachments at distinct
points. -/
theorem attach_third {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {px py pz : ℕ} {tx ty tz : ℝ} (hX : SideAttach M.W c px tx) (hY : SideAttach M.W c py ty)
    (hXY : sidePt M.W px tx ≠ sidePt M.W py ty) (hZ : SideAttach M.W c pz tz) :
    (pz = px ∧ tz = tx) ∨ (pz = py ∧ tz = ty) := by
  obtain ⟨a, b, -, -, hend⟩ := end_of_not_mem hM hc
  have hx := hend _ hX.2.2.2.1 (hM.trace _ hX.1 _ hX.2.1 hX.2.2.1.le)
  have hy := hend _ hY.2.2.2.1 (hM.trace _ hY.1 _ hY.2.1 hY.2.2.1.le)
  have hz := hend _ hZ.2.2.2.1 (hM.trace _ hZ.1 _ hZ.2.1 hZ.2.2.1.le)
  have key : sidePt M.W pz tz = sidePt M.W px tx ∨ sidePt M.W pz tz = sidePt M.W py ty := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
      first
      | exact absurd (hx.trans hy.symm) hXY
      | exact Or.inl (hz.trans hx.symm)
      | exact Or.inr (hz.trans hy.symm)
  rcases key with h | h
  · exact Or.inl (WalkAx.attach_unique hM hc hZ hX h)
  · exact Or.inr (WalkAx.attach_unique hM hc hZ hY h)

namespace Corr0

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- A chord of `F` with exactly one attachment between two positions of the stretch separates
them. -/
theorem sepM (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    (hcut' : ¬ M.IsCut F (((g + d') % M.W.n : ℕ) + t')) (hne : (d : ℝ) + t ≠ d' + t')
    {e : Set Point} (he : e ∈ F) {p₁ p₃ : ℕ} {t₁ t₃ : ℝ} (hA₁ : SideAttach M.W e p₁ t₁)
    (hA₃ : SideAttach M.W e p₃ t₃) (hne₁₃ : sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃)
    (hb1 : Btw (d + t) (d' + t') (off M.W.n g (p₁ + t₁)))
    (hb3 : ¬ Btw (d + t) (d' + t') (off M.W.n g (p₃ + t₃))) :
    M.Separates e (((g + d) % M.W.n : ℕ) + t) (((g + d') % M.W.n : ℕ) + t') := by
  have hn := hC.n_pos
  refine ⟨p₁, p₃, t₁, t₃, hA₁, hA₃, hne₁₃, ?_⟩
  have hk13 := WalkAx.key_ne_of_pt_ne (M := M) hA₁ hA₃ hne₁₃
  obtain ⟨y0, y1⟩ := Corr.key_mem (Nat.mod_lt (g + d) hn) ht.1.le ht.2
  obtain ⟨y0', y1'⟩ := Corr.key_mem (Nat.mod_lt (g + d') hn) ht'.1.le ht'.2
  obtain ⟨a0, a1⟩ := Corr.key_mem hA₁.1 hA₁.2.1 hA₁.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hA₃.1 hA₃.2.1 hA₃.2.2.1
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hgn : (g : ℝ) < M.W.n := by exact_mod_cast hC.hg
  have hyy : (((g + d) % M.W.n : ℕ) : ℝ) + t ≠ (((g + d') % M.W.n : ℕ) : ℝ) + t' := by
    intro h
    have h2 := congrArg (off M.W.n g) h
    Ξ' hC.off_M hd ht.1.le ht.2, hC.off_M hd' ht'.1.le ht'.2 at h2
    exact hne h2
  have hya : ∀ {p : ℕ} {s : ℝ}, SideAttach M.W e p s →
      (((g + d) % M.W.n : ℕ) : ℝ) + t ≠ p + s ∧ (((g + d') % M.W.n : ℕ) : ℝ) + t' ≠ p + s :=
    fun hP => ⟨fun h => hcut ⟨e, he, _, _, hP, h⟩, fun h => hcut' ⟨e, he, _, _, hP, h⟩⟩
  refine (sep_iff_btw hg0 hgn a0 a1 b0 b1 y0 y1 y0' y1' hk13 hyy (hya hA₁).1 (hya hA₃).1
    (hya hA₁).2 (hya hA₃).2).2 ?_
  Ξ hC.off_M hd ht.1.le ht.2, hC.off_M hd' ht'.1.le ht'.2
  exact ⟨fun _ => hb3, fun _ => hb1⟩

/-- **Both attachments of a chord of `F` stay between two positions of one region**: if two
positions of the stretch face the same region of `F`, a chord of `F` attached between them has
every attachment at another point between them too. -/
theorem btw_other (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    (hcut' : ¬ M.IsCut F (((g + d') % M.W.n : ℕ) + t')) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ((g + d) % M.W.n) t U)
    (hf' : M.Faces ((g + d') % M.W.n) t' U) (hne : (d : ℝ) + t ≠ d' + t') {e : Set Point}
    (he : e ∈ F) {p₁ p₃ : ℕ} {t₁ t₃ : ℝ} (hA₁ : SideAttach M.W e p₁ t₁)
    (hA₃ : SideAttach M.W e p₃ t₃) (hne₁₃ : sidePt M.W p₁ t₁ ≠ sidePt M.W p₃ t₃)
    (hb1 : Btw (d + t) (d' + t') (off M.W.n g (p₁ + t₁))) :
    Btw (d + t) (d' + t') (off M.W.n g (p₃ + t₃)) := by
  by_contra hb3
  exact (hC.hM.eq_iff_not_separates hC.hF hC.hfin hU hU (Nat.mod_lt _ hC.n_pos)
    (Nat.mod_lt _ hC.n_pos) ht ht' hcut hcut' hf hf').1 rfl e he
    (hC.sepM hd hd' ht ht' hcut hcut' hne he hA₁ hA₃ hne₁₃ hb1 hb3)

/-- **The far attachment of a chord of `S` whose piece in `F` is attached between two positions
of one region** lies between their counterparts, and the piece has a second point in the
stretch. -/
theorem far_btw (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d d' : ℕ} (hd : d < L1 + L2)
    (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    (hcut' : ¬ M.IsCut F (((g + d') % M.W.n : ℕ) + t')) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ((g + d) % M.W.n) t U)
    (hf' : M.Faces ((g + d') % M.W.n) t' U) (hne : (d : ℝ) + t ≠ d' + t') {c : Set Point}
    (hc : c ∈ S) {pb : ℕ} {tb : ℝ} (hB : SideAttach M₂.W c pb tb) {e : Set Point} (he : e ∈ F)
    (hec : e ⊆ c) {q : Point} (hqe : q ∈ e) (hqD : q ∉ M₂.D) (hqB : sidePt M₂.W pb tb ≠ q)
    {pe : ℕ} {te : ℝ} (hAe : SideAttach M.W e pe te) (hpe : sidePt M.W pe te = q)
    (hbe : Btw (d + t) (d' + t') (off M.W.n g (pe + te))) :
    Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb)) ∧
      ∃ y ∈ c, StrPt M g (L1 + L2) y ∧ y ≠ q := by
  obtain ⟨p₃, t₃, hA₃, hne₃⟩ := WalkAx.other_attach hC.hM (hC.hF he) hAe
  have hb3 := hC.btw_other hd hd' ht ht' hcut hcut' hU hf hf' hne he hAe hA₃ (Ne.symm hne₃) hbe
  have hne₃' : sidePt M.W p₃ t₃ ≠ q := by rw [← hpe]; exact hne₃
  refine ⟨by_contra fun hout => hC.other_not_btw hd hd' ht ht' hc hB hout he hec hqe hqD hqB
    hA₃ hne₃' hb3, ?_⟩
  have hlo : (0 : ℝ) < d + t := by have := ht.1; positivity
  have hlo' : (0 : ℝ) < d' + t' := by have := ht'.1; positivity
  have hhi : (d : ℝ) + t < L1 + L2 := by
    have : (d : ℝ) + 1 ≤ L1 + L2 := by exact_mod_cast hd
    linarith [ht.2]
  have hhi' : (d' : ℝ) + t' < L1 + L2 := by
    have : (d' : ℝ) + 1 ≤ L1 + L2 := by exact_mod_cast hd'
    linarith [ht'.2]
  obtain ⟨hp₃e, ho₃⟩ := hC.decomp hA₃.1 hA₃.2.1 hA₃.2.2.1
  have hb : 0 < (dOf M.W.n g p₃ : ℝ) + t₃ ∧ (dOf M.W.n g p₃ : ℝ) + t₃ < L1 + L2 := by
    rw [← ho₃]; rcases hb3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hlt : dOf M.W.n g p₃ < L1 + L2 := by
    have : (dOf M.W.n g p₃ : ℝ) < L1 + L2 := by linarith [hA₃.2.1, hb.2]
    exact_mod_cast this
  exact ⟨sidePt M.W p₃ t₃, hec hA₃.2.2.2.1,
    ⟨dOf M.W.n g p₃, hlt, t₃, hA₃.2.1, hA₃.2.2.1, hb.1, Ρ hp₃e⟩, hne₃'⟩

/-- A key of `M₂` at the offset `L + u` (`0 ≤ u < 1`) is the key of `((g' + L) mod n₂, u)`. -/
theorem key_of_off₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {L : ℕ} (hL : L < M₂.W.n) {p : ℕ}
    {s u : ℝ} (hp : p < M₂.W.n) (hs0 : 0 ≤ s) (hs1 : s < 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (h : off M₂.W.n g' (p + s) = L + u) : p = (g' + L) % M₂.W.n ∧ s = u := by
  have hn₂ := hC.n₂_pos
  obtain ⟨k0, k1⟩ := Corr.key_mem hp hs0 hs1
  obtain ⟨m0, m1⟩ := Corr.key_mem (Nat.mod_lt (g' + L) hn₂) hu0 hu1
  have hg0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
  have hgn : (g' : ℝ) < M₂.W.n := by exact_mod_cast hC.hg'
  have e := off_inj hg0 hgn k0 k1 m0 m1 (h.trans (off_key hC.hg' hL hu0 hu1).symm)
  exact Chazelle.Chain.sideKey_inj hs0 hs1 hu0 hu1 e

/-- The counterpart of a non-cut position of the stretch is not a cut. -/
theorem not_cut₂ (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t)) :
    ¬ M₂.IsCut S (((g' + dq L1 δ d) % M₂.W.n : ℕ) + t) := by
  rintro ⟨c₀, hc₀, p, t₀, hA₀, hkey⟩
  obtain ⟨hp, ht0⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 hA₀.2.1 hA₀.2.2.1 hkey
  Ξ' ← hp, ← ht0 at hA₀
  obtain ⟨e, he, -, -, hAe⟩ := hC.transfer hd ht.1.le ht.2 (fun h => absurd h ht.1.ne') hc₀ hA₀
  exact hcut ⟨e, he, _, t, hAe, rfl⟩

/-- A separation in `M₂` as betweenness of offsets from `g'`. -/
theorem sep₂_btw (hC : Corr0 M M₂ F S g g' L1 L2 δ) {c : Set Point} (hc : c ∈ S) {p p' : ℕ}
    {s s' : ℝ} (hp : p < M₂.W.n) (hp' : p' < M₂.W.n) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hs' : s' ∈ Ioo (0 : ℝ) 1) (hnc : ¬ M₂.IsCut S (p + s)) (hnc' : ¬ M₂.IsCut S (p' + s'))
    {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta) (hB : SideAttach M₂.W c pb tb)
    (hAB : sidePt M₂.W pa ta ≠ sidePt M₂.W pb tb)
    (hiff : sideInArc (pa + ta) (pb + tb) (p + s) ↔ ¬ sideInArc (pa + ta) (pb + tb) (p' + s')) :
    (Btw (off M₂.W.n g' (p + s)) (off M₂.W.n g' (p' + s')) (off M₂.W.n g' (pa + ta)) ↔
      ¬ Btw (off M₂.W.n g' (p + s)) (off M₂.W.n g' (p' + s')) (off M₂.W.n g' (pb + tb))) := by
  have hxs : (p : ℝ) + s ≠ p' + s' := by intro h; Ξ' h at hiff; exact iff_not_self hiff
  have hxa : ∀ {q : ℕ} {u : ℝ}, SideAttach M₂.W c q u → (p : ℝ) + s ≠ q + u ∧
      (p' : ℝ) + s' ≠ q + u :=
    fun hP => ⟨fun h => hnc ⟨c, hc, _, _, hP, h⟩, fun h => hnc' ⟨c, hc, _, _, hP, h⟩⟩
  have hab := WalkAx.key_ne_of_pt_ne (M := M₂) hA hB hAB
  obtain ⟨k0, k1⟩ := Corr.key_mem hp hs.1.le hs.2
  obtain ⟨s0, s1⟩ := Corr.key_mem hp' hs'.1.le hs'.2
  obtain ⟨ka0, ka1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨kb0, kb1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hg'0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
  have hg'n : (g' : ℝ) < M₂.W.n := by exact_mod_cast hC.hg'
  exact (sep_iff_btw hg'0 hg'n ka0 ka1 kb0 kb1 k0 k1 s0 s1 hab hxs (hxa hA).1 (hxa hB).1
    (hxa hA).2 (hxa hB).2).1 hiff

/-! ## The two sides of the gap -/

/-- **The side before the gap.**  Two positions `d < L1 ≤ d'` of the stretch face the same region
of `F`, and a chord `c ∈ S` attached in the gap separates their counterparts.  Then the region of
`S` faced at the counterpart of `d` is the one faced just after the split vertex of `M₂`. -/
theorem gapS_of (hC : Corr0 M M₂ F S g g' L1 L2 δ) (hG : CorrGap M M₂ F S g g' L1 L2 δ)
    {d d' : ℕ} (hdL : d < L1) (hLd : L1 ≤ d') (hd' : d' < L1 + L2) {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    (hcut' : ¬ M.IsCut F (((g + d') % M.W.n : ℕ) + t')) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ((g + d) % M.W.n) t U)
    (hf' : M.Faces ((g + d') % M.W.n) t' U) {c : Set Point} (hc : c ∈ S) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta) (hB : SideAttach M₂.W c pb tb)
    (hAg : InGap L1 δ (off M₂.W.n g' (pa + ta)))
    (hout : ¬ Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb)))
    {V : Set Point} (hV : V ∈ M₂.regions S)
    (hfV : M₂.Faces ((g' + dq L1 δ d) % M₂.W.n) t V) :
    AfterFaces M₂ ((g' + L1) % M₂.W.n) 0 V := by
  have hn₂ := hC.n₂_pos
  have hd : d < L1 + L2 := ⋄
  have hL2 : 0 < L2 := ⋄
  have hδ : 0 < δ := by
    rcases Nat.eq_zero_or_pos δ with h | h
    · have := hC.hδ h; omega
    · exact h
  have hfull := hC.hfull hδ
  have hL1n : L1 < M₂.W.n := ⋄
  have hdq : dq L1 δ d = d := by unfold dq; Ξ ite_eq_left hdL
  have hdq' : dq L1 δ d' = d' + δ := by unfold dq; Ξ ite_eq_right (⋄)
  have hout' : ¬ Btw ((d : ℝ) + t) ((d' : ℝ) + δ + t') (off M₂.W.n g' (pb + tb)) := by
    have := hout; Ξ' hdq, hdq' at this; push_cast at this; exact this
  have hdLr : (d : ℝ) + t < L1 := by
    have : (d : ℝ) + 1 ≤ L1 := by exact_mod_cast hdL
    linarith [ht.2]
  have hLdr : (L1 : ℝ) ≤ d' := by exact_mod_cast hLd
  have hδr : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hL1pos : (0 : ℝ) < L1 := by linarith [ht.1, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hne : (d : ℝ) + t ≠ d' + t' := by intro h; linarith [ht'.1]
  have hg'0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
  have hg'n : (g' : ℝ) < M₂.W.n := by exact_mod_cast hC.hg'
  -- no cut just after the split vertex
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hC.hM₂ hC.hS hC.hSfin (((g' + L1) % M₂.W.n : ℕ) : ℝ))
  Ξ' mem_Ioi at hε₀
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun s hs0 hsε hs1 => ?_⟩
  Ξ' zero_add at hs1 ⊢
  have hsε₀ : s < ε₀ := lt_of_lt_of_le hsε (min_le_left _ _)
  have hnc : ¬ M₂.IsCut S (((g' + L1) % M₂.W.n : ℕ) + s) := hsub ⟨hs0, hsε₀⟩
  obtain ⟨V'', hV'', hfV''⟩ := hC.hM₂.exists_faces_of_not_cut hC.hS hC.hSfin
    (Nat.mod_lt _ hn₂) ⟨hs0, hs1⟩ hnc
  suffices hVV : V = V'' by rw [hVV]; exact hfV''
  have hc₂ := hC.not_cut₂ hd ht hcut
  refine (hC.hM₂.eq_iff_not_separates hC.hS hC.hSfin hV hV'' (Nat.mod_lt _ hn₂)
    (Nat.mod_lt _ hn₂) ht ⟨hs0, hs1⟩ hc₂ hnc hfV hfV'').2 ?_
  rintro c' hc' ⟨pa', pb', ta', tb', hA', hB', hAB', hiff'⟩
  have hsep := hC.sep₂_btw hc' (Nat.mod_lt _ hn₂) (Nat.mod_lt _ hn₂) ht ⟨hs0, hs1⟩ hc₂ hnc hA'
    hB' hAB' hiff'
  Ξ' hC.off_M₂ hd ht.1.le ht.2, hdq, off_key hC.hg' hL1n hs0.le hs1 at hsep
  -- the attachment of `c'` between the two positions
  have core : ∀ {pa₁ pb₁ : ℕ} {ta₁ tb₁ : ℝ}, SideAttach M₂.W c' pa₁ ta₁ →
      SideAttach M₂.W c' pb₁ tb₁ → sidePt M₂.W pa₁ ta₁ ≠ sidePt M₂.W pb₁ tb₁ →
      Btw (d + t) (L1 + s) (off M₂.W.n g' (pa₁ + ta₁)) →
      ¬ Btw (d + t) (L1 + s) (off M₂.W.n g' (pb₁ + tb₁)) → False := by
    intro pa₁ pb₁ ta₁ tb₁ hA₁ hB₁ hAB₁ hin₁ hout₁
    have hin₁' : (d : ℝ) + t < off M₂.W.n g' (pa₁ + ta₁) ∧
        off M₂.W.n g' (pa₁ + ta₁) < L1 + s := by
      rcases hin₁ with h | ⟨h1, h2⟩
      · exact h
      · exfalso; linarith
    -- no attachment strictly between the split vertex and `L1 + s`
    have hoaL : off M₂.W.n g' (pa₁ + ta₁) ≤ L1 := by
      by_contra hlt; push Not at hlt
      obtain ⟨hp, hu⟩ := hC.key_of_off₂ hL1n hA₁.1 hA₁.2.1 hA₁.2.2.1
        (u := off M₂.W.n g' (pa₁ + ta₁) - L1) (⟡) (by linarith [hin₁'.2]) (⋆)
      apply hsub ⟨show 0 < off M₂.W.n g' (pa₁ + ta₁) - L1 by linarith,
        show off M₂.W.n g' (pa₁ + ta₁) - L1 < ε₀ by linarith [hin₁'.2]⟩
      refine ⟨c', hc', pa₁, ta₁, hA₁, ?_⟩
      Ξ ← hu, hp
    have hqD₀ : sidePt M₂.W pa₁ ta₁ ∉ M₂.D := hC.hM₂.trace _ hA₁.1 _ hA₁.2.1 hA₁.2.2.1.le
    -- the piece of `c'` through the attachment, in `M`
    obtain ⟨e', he', hec', hqe', pe, te, hAe, hpe, hbe, hqS⟩ : ∃ e' ∈ F, e' ⊆ c' ∧
        sidePt M₂.W pa₁ ta₁ ∈ e' ∧ ∃ pe te, SideAttach M.W e' pe te ∧
          sidePt M.W pe te = sidePt M₂.W pa₁ ta₁ ∧ Btw (d + t) (d' + t') (off M.W.n g (pe + te)) ∧
          StrPt M g (L1 + L2) (sidePt M₂.W pa₁ ta₁) := by
      obtain ⟨hpae, hoae⟩ := hC.decomp₂ hA₁.1 hA₁.2.1 hA₁.2.2.1
      rcases hoaL.lt_or_eq with hlt | heq
      · -- a regular position before the split vertex
        have hdaL : dOf M₂.W.n g' pa₁ < L1 := by
          have : (dOf M₂.W.n g' pa₁ : ℝ) < L1 := by linarith [hA₁.2.1]
          exact_mod_cast this
        have hdqa : dq L1 δ (dOf M₂.W.n g' pa₁) = dOf M₂.W.n g' pa₁ := by
          unfold dq; Ξ ite_eq_left hdaL
        have hsec : ta₁ = 0 → dOf M₂.W.n g' pa₁ ≠ 0 ∧ dOf M₂.W.n g' pa₁ ≠ L1 := by
          intro h0
          refine ⟨fun hz => ?_, ⋄⟩
          have h1 := hin₁'.1
          Ξ' hoae, hz, h0 at h1
          push_cast at h1
          linarith [ht.1, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
        have hA₁' : SideAttach M₂.W c' ((g' + dq L1 δ (dOf M₂.W.n g' pa₁)) % M₂.W.n) ta₁ := by
          rw [hdqa, hpae]; exact hA₁
        obtain ⟨e', he', hec', hqe', hAe'⟩ :=
          hC.transfer (d := dOf M₂.W.n g' pa₁) (⋄) hA₁.2.1 hA₁.2.2.1 hsec hc' hA₁'
        have hpt : sidePt M.W ((g + dOf M₂.W.n g' pa₁) % M.W.n) ta₁ = sidePt M₂.W pa₁ ta₁ := by
          Ξ hC.sidePt_eq (by omega : dOf M₂.W.n g' pa₁ < L1 + L2) ta₁, hdqa, hpae
        refine ⟨e', he', hec', hpt ▸ hqe', _, _, hAe', hpt, ?_,
          ⟨dOf M₂.W.n g' pa₁, ⋄, ta₁, hA₁.2.1, hA₁.2.2.1, by linarith [hin₁'.1, ht.1,
            (Nat.cast_nonneg d : (0 : ℝ) ≤ d)], hpt⟩⟩
        Ξ hC.off_M (by omega : dOf M₂.W.n g' pa₁ < L1 + L2) hA₁.2.1 hA₁.2.2.1
        left; constructor <;> linarith [hin₁'.1, ht'.1]
      · -- at the split vertex
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ hL1n hA₁.1 hA₁.2.1 hA₁.2.2.1 (u := 0) le_rfl one_pos
          (by rw [heq]; ring)
        have hvtx : M.W.vtx ((g + L1) % M.W.n) = M₂.W.vtx ((g' + L1) % M₂.W.n) :=
          hC.A1 L1 le_rfl
        have hu : sidePt M.W ((g + L1) % M.W.n) 0 = sidePt M₂.W pa₁ ta₁ := by
          Ξ hp1, ht1, Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, hvtx
        have hnoV : sidePt M₂.W pa₁ ta₁ ≠ M₂.W.vtx g' := by
          Ξ hp1, ht1
          refine hC.noV _ (Nat.mod_lt _ hn₂) 0 le_rfl one_pos ?_ ?_ <;>
            Ξ off_key hC.hg' hL1n le_rfl one_pos
          · linarith
          · have : (0 : ℝ) < L2 := by exact_mod_cast hL2
            linarith
        obtain ⟨e', he', hqe', hec'⟩ := hC.trans c' hc' _ hA₁.2.2.2.1 hqD₀ hnoV
        have hA₁P : SideAttach M₂.W c' ((g' + L1) % M₂.W.n) 0 := by
          have := hA₁; Ξ' hp1, ht1 at this; exact this
        have hAe' := hG.splitAttach L1 (Or.inl rfl) c' hc' hA₁P e' he' hec'
          (by rw [hu]; exact hqe')
        refine ⟨e', he', hec', hqe', _, _, hAe', hu, ?_,
          ⟨L1, ⋄, 0, le_rfl, one_pos, ⟡, hu⟩⟩
        Ξ hC.off_M (by omega : L1 < L1 + L2) le_rfl one_pos
        left; constructor <;> linarith [ht'.1]
    obtain ⟨hbtw, y, hyc, hyS, hyq⟩ := hC.far_btw hd hd' ht ht' hcut hcut' hU hf hf' hne hc' hB₁
      he' hec' hqe' hqD₀ (fun h => hAB₁ h.symm) hAe hpe hbe
    Ξ' hdq, hdq' at hbtw
    push_cast at hbtw
    have hob : (L1 : ℝ) + s ≤ off M₂.W.n g' (pb₁ + tb₁) ∧
        off M₂.W.n g' (pb₁ + tb₁) < d' + δ + t' := by
      rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨?_, h2⟩
        by_contra hlt; push Not at hlt
        exact hout₁ (Or.inl ⟨h1, hlt⟩)
      · exfalso; linarith [ht'.1]
    -- `c'` is not `c`
    have hcc : c ≠ c' := by
      rintro rfl
      rcases attach_third hC.hM₂ (hC.hS hc) hA₁ hB₁ hAB₁ hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hout' (by rw [h1, h2]; left; exact ⟨hin₁'.1, by linarith [ht'.1]⟩)
      · exact hout' (by rw [h1, h2]; left; exact ⟨⟡, hob.2⟩)
    obtain ⟨hA1, hA2⟩ := hAg
    have hab₁ : off M₂.W.n g' (pa₁ + ta₁) < off M₂.W.n g' (pb₁ + tb₁) := by
      linarith [hob.1]
    by_cases hmid : off M₂.W.n g' (pa₁ + ta₁) < off M₂.W.n g' (pa + ta) ∧
        off M₂.W.n g' (pa + ta) < off M₂.W.n g' (pb₁ + tb₁)
    · obtain ⟨h1, h2⟩ := no_cross_off hC.hM₂ hC.hS hC.hSfin hc' hc (Ne.symm hcc) hA₁ hB₁ hAB₁ hA
        hB hg'0 hg'n hab₁ hmid.1 hmid.2
      exact hout' (Or.inl ⟨by linarith [hin₁'.1], by linarith [hob.2]⟩)
    have hge : off M₂.W.n g' (pb₁ + tb₁) ≤ off M₂.W.n g' (pa + ta) ∨
        off M₂.W.n g' (pa + ta) = off M₂.W.n g' (pa₁ + ta₁) := by
      by_contra hcon; push Not at hcon
      exact hmid ⟨lt_of_le_of_ne (le_trans hoaL hA1) (Ne.symm hcon.2), hcon.1⟩
    rcases hge with hge | heq
    · rcases lt_or_eq_of_le (le_trans hge hA2) with hlt | heq'
      · -- `c'` is attached strictly inside the gap
        exact hyq (hG.gapOut c' hc' pb₁ tb₁ hB₁ (by linarith [hob.1]) hlt y hyc _
          (hec' hqe') hyS hqS)
      · -- both at the copy of the split vertex after the gap
        have hA' : off M₂.W.n g' (pa + ta) = L1 + δ := le_antisymm hA2 (heq' ▸ hge)
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ (L := L1 + δ) (⋄) hB₁.1 hB₁.2.1 hB₁.2.2.1
          (u := 0) le_rfl one_pos (by rw [heq']; push_cast; ring)
        obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ (L := L1 + δ) (⋄) hA.1 hA.2.1 hA.2.2.1
          (u := 0) le_rfl one_pos (by rw [hA']; push_cast; ring)
        have hB₁' := hB₁
        have hA'' := hA
        Ξ' hp1, ht1 at hB₁'
        Ξ' hp2, ht2 at hA''
        exact hcc (hG.oneAt (L1 + δ) (Or.inr rfl) c hc c' hc' hA'' hB₁')
    · -- both at the copy of the split vertex before the gap
      have hoaL1 : off M₂.W.n g' (pa₁ + ta₁) = L1 := le_antisymm hoaL (heq ▸ hA1)
      obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ hL1n hA₁.1 hA₁.2.1 hA₁.2.2.1 (u := 0) le_rfl one_pos
        (by rw [hoaL1]; ring)
      obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ hL1n hA.1 hA.2.1 hA.2.2.1 (u := 0) le_rfl one_pos
        (by rw [heq, hoaL1]; ring)
      have hA₁' := hA₁
      have hA'' := hA
      Ξ' hp1, ht1 at hA₁'
      Ξ' hp2, ht2 at hA''
      exact hcc (hG.oneAt L1 (Or.inl rfl) c hc c' hc' hA'' hA₁')
  by_cases h : Btw (d + t) (L1 + s) (off M₂.W.n g' (pa' + ta'))
  · exact core hA' hB' hAB' h (hsep.1 h)
  · exact core hB' hA' (Ne.symm hAB') (by_contra fun hn' => h (hsep.2 hn')) h

/-- **The side after the gap.**  Two positions `d < L1 ≤ d'` of the stretch face the same region
of `F`, and a chord `c ∈ S` attached in the gap separates their counterparts.  Then the region of
`S` faced at the counterpart of `d'` is the one faced just before the second copy
`(g' + L1 + δ)` of the split vertex in `M₂`. -/
theorem gapE_of (hC : Corr0 M M₂ F S g g' L1 L2 δ) (hG : CorrGap M M₂ F S g g' L1 L2 δ)
    {d d' : ℕ} (hdL : d < L1) (hLd : L1 ≤ d') (hd' : d' < L1 + L2) {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    (hcut' : ¬ M.IsCut F (((g + d') % M.W.n : ℕ) + t')) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ((g + d) % M.W.n) t U)
    (hf' : M.Faces ((g + d') % M.W.n) t' U) {c : Set Point} (hc : c ∈ S) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M₂.W c pa ta) (hB : SideAttach M₂.W c pb tb)
    (hAg : InGap L1 δ (off M₂.W.n g' (pa + ta)))
    (hout : ¬ Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb)))
    {V : Set Point} (hV : V ∈ M₂.regions S)
    (hfV : M₂.Faces ((g' + dq L1 δ d') % M₂.W.n) t' V) :
    BeforeFaces M₂ ((g' + L1 + δ) % M₂.W.n) 0 V := by
  have hn₂ := hC.n₂_pos
  have hd : d < L1 + L2 := ⋄
  have hL2 : 0 < L2 := ⋄
  have hδ : 0 < δ := by
    rcases Nat.eq_zero_or_pos δ with h | h
    · have := hC.hδ h; omega
    · exact h
  have hfull := hC.hfull hδ
  have hL1n : L1 < M₂.W.n := ⋄
  have hdq : dq L1 δ d = d := by unfold dq; Ξ ite_eq_left hdL
  have hdq' : dq L1 δ d' = d' + δ := by unfold dq; Ξ ite_eq_right (⋄)
  have hout' : ¬ Btw ((d : ℝ) + t) ((d' : ℝ) + δ + t') (off M₂.W.n g' (pb + tb)) := by
    have := hout; Ξ' hdq, hdq' at this; push_cast at this; exact this
  have hdLr : (d : ℝ) + t < L1 := by
    have : (d : ℝ) + 1 ≤ L1 := by exact_mod_cast hdL
    linarith [ht.2]
  have hLdr : (L1 : ℝ) ≤ d' := by exact_mod_cast hLd
  have hδr : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hL2r : (0 : ℝ) < L2 := by exact_mod_cast hL2
  have hL1pos : (0 : ℝ) < L1 := by linarith [ht.1, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hne : (d : ℝ) + t ≠ d' + t' := by intro h; linarith [ht'.1]
  have hg'0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
  have hg'n : (g' : ℝ) < M₂.W.n := by exact_mod_cast hC.hg'
  have hnr : (M₂.W.n : ℝ) = L1 + δ + L2 := by exact_mod_cast hfull.symm
  -- the last edge of the gap
  set Q₀ := (g' + (L1 + δ - 1)) % M₂.W.n with hQ₀
  have hQ : ((g' + L1 + δ) % M₂.W.n + M₂.W.n - 1) % M₂.W.n = Q₀ := by
    Ξ hQ₀, show g' + L1 + δ = g' + (L1 + δ) by ring, mod_pred_mod hn₂ _ (⋄)
  have hLδn : L1 + δ - 1 < M₂.W.n := ⋄
  have hoffQ : ∀ u : ℝ, 0 ≤ u → u < 1 → off M₂.W.n g' ((Q₀ : ℝ) + u) = L1 + δ - 1 + u := by
    intro u hu0 hu1
    Ξ hQ₀, off_key hC.hg' hLδn hu0 hu1
    push_cast [show 1 ≤ L1 + δ by omega]
    ring
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_before hC.hM₂ hC.hS hC.hSfin ((Q₀ : ℝ) + 1))
  Ξ' mem_Ioi at hε₀
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun h => absurd h (lt_irrefl 0), fun _ s hs0 hsε => ?_⟩
  Ξ hQ
  have hs1 : s < 1 := lt_of_lt_of_le hsε (min_le_right _ _)
  have hsε₀ : s < ε₀ := lt_of_lt_of_le hsε (min_le_left _ _)
  have hnc : ¬ M₂.IsCut S ((Q₀ : ℝ) + (1 - s)) := by
    have := hsub ⟨hs0, hsε₀⟩
    ϴ' mem_ofPred_eq at this
    rwa [show (Q₀ : ℝ) + 1 - s = Q₀ + (1 - s) by ring] at this
  have hs' : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨⟡, ⟡⟩
  obtain ⟨V'', hV'', hfV''⟩ := hC.hM₂.exists_faces_of_not_cut hC.hS hC.hSfin
    (Nat.mod_lt _ hn₂) hs' hnc
  suffices hVV : V = V'' by rw [hVV]; exact hfV''
  have hc₂ := hC.not_cut₂ hd' ht' hcut'
  refine (hC.hM₂.eq_iff_not_separates hC.hS hC.hSfin hV hV'' (Nat.mod_lt _ hn₂)
    (Nat.mod_lt _ hn₂) ht' hs' hc₂ hnc hfV hfV'').2 ?_
  rintro c' hc' ⟨pa', pb', ta', tb', hA', hB', hAB', hiff'⟩
  have hsep := hC.sep₂_btw hc' (Nat.mod_lt _ hn₂) (Nat.mod_lt _ hn₂) ht' hs' hc₂ hnc hA'
    hB' hAB' hiff'
  Ξ' hC.off_M₂ hd' ht'.1.le ht'.2, hdq', hoffQ _ hs'.1.le hs'.2 at hsep
  push_cast at hsep
  have core : ∀ {pa₁ pb₁ : ℕ} {ta₁ tb₁ : ℝ}, SideAttach M₂.W c' pa₁ ta₁ →
      SideAttach M₂.W c' pb₁ tb₁ → sidePt M₂.W pa₁ ta₁ ≠ sidePt M₂.W pb₁ tb₁ →
      Btw (d' + δ + t') (L1 + δ - 1 + (1 - s)) (off M₂.W.n g' (pa₁ + ta₁)) →
      ¬ Btw (d' + δ + t') (L1 + δ - 1 + (1 - s)) (off M₂.W.n g' (pb₁ + tb₁)) → False := by
    intro pa₁ pb₁ ta₁ tb₁ hA₁ hB₁ hAB₁ hin₁ hout₁
    have hin₁' : (L1 : ℝ) + δ - s < off M₂.W.n g' (pa₁ + ta₁) ∧
        off M₂.W.n g' (pa₁ + ta₁) < d' + δ + t' := by
      rcases hin₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; linarith [ht'.1]
      · exact ⟨⟡, h2⟩
    -- no attachment strictly between `L1 + δ - s` and the second copy of the split vertex
    have hoaL : (L1 : ℝ) + δ ≤ off M₂.W.n g' (pa₁ + ta₁) := by
      by_contra hlt; push Not at hlt
      obtain ⟨hp, hu⟩ := hC.key_of_off₂ hLδn hA₁.1 hA₁.2.1 hA₁.2.2.1
        (u := off M₂.W.n g' (pa₁ + ta₁) - (L1 + δ - 1)) (by linarith [hin₁'.1])
        (⟡) (by push_cast [show 1 ≤ L1 + δ by omega]; ring)
      apply hsub ⟨show 0 < (L1 + δ : ℝ) - off M₂.W.n g' (pa₁ + ta₁) by linarith,
        show (L1 + δ : ℝ) - off M₂.W.n g' (pa₁ + ta₁) < ε₀ by linarith [hin₁'.1]⟩
      refine ⟨c', hc', pa₁, ta₁, hA₁, ?_⟩
      Ξ' ← hQ₀ at hp
      Ξ' hp at hu ⊢
      linarith [hu]
    have hqD₀ : sidePt M₂.W pa₁ ta₁ ∉ M₂.D := hC.hM₂.trace _ hA₁.1 _ hA₁.2.1 hA₁.2.2.1.le
    have hoan : off M₂.W.n g' (pa₁ + ta₁) < L1 + δ + L2 := by
      Ξ ← hnr
      exact off_lt (Corr.key_mem hA₁.1 hA₁.2.1 hA₁.2.2.1).2 hg'0
    obtain ⟨e', he', hec', hqe', pe, te, hAe, hpe, hbe, hqS⟩ : ∃ e' ∈ F, e' ⊆ c' ∧
        sidePt M₂.W pa₁ ta₁ ∈ e' ∧ ∃ pe te, SideAttach M.W e' pe te ∧
          sidePt M.W pe te = sidePt M₂.W pa₁ ta₁ ∧ Btw (d + t) (d' + t') (off M.W.n g (pe + te)) ∧
          StrPt M g (L1 + L2) (sidePt M₂.W pa₁ ta₁) := by
      obtain ⟨hpae, hoae⟩ := hC.decomp₂ hA₁.1 hA₁.2.1 hA₁.2.2.1
      rcases hoaL.lt_or_eq with hlt | heq
      · -- a regular position after the gap
        set db := dOf M₂.W.n g' pa₁ with hdb
        have hdbL : L1 + δ ≤ db := by
          by_contra hh; push Not at hh
          have : (db : ℝ) + 1 ≤ L1 + δ := by exact_mod_cast hh
          linarith [hA₁.2.2.1]
        have hdbn : db < L1 + δ + L2 := by
          have : (db : ℝ) < L1 + δ + L2 := by linarith [hA₁.2.1]
          exact_mod_cast this
        have hdqa : dq L1 δ (db - δ) = db := by unfold dq; rw [ite_eq_right (⋄)]; omega
        have hsec : ta₁ = 0 → db - δ ≠ 0 ∧ db - δ ≠ L1 := by
          intro h0
          refine ⟨⋄, fun hz => ?_⟩
          have : db = L1 + δ := ⋄
          have h1 := hlt
          Ξ' hoae, this, h0 at h1
          push_cast at h1
          linarith
        have hA₁' : SideAttach M₂.W c' ((g' + dq L1 δ (db - δ)) % M₂.W.n) ta₁ := by
          rw [hdqa, hpae]; exact hA₁
        obtain ⟨e', he', hec', hqe', hAe'⟩ :=
          hC.transfer (d := db - δ) (⋄) hA₁.2.1 hA₁.2.2.1 hsec hc' hA₁'
        have hpt : sidePt M.W ((g + (db - δ)) % M.W.n) ta₁ = sidePt M₂.W pa₁ ta₁ := by
          Ξ hC.sidePt_eq (by omega : db - δ < L1 + L2) ta₁, hdqa, hpae
        have hcast : ((db - δ : ℕ) : ℝ) = db - δ := by push_cast [show δ ≤ db by omega]; ring
        refine ⟨e', he', hec', hpt ▸ hqe', _, _, hAe', hpt, ?_,
          ⟨db - δ, ⋄, ta₁, hA₁.2.1, hA₁.2.2.1, by rw [hcast]; linarith, hpt⟩⟩
        Ξ hC.off_M (by omega : db - δ < L1 + L2) hA₁.2.1 hA₁.2.2.1, hcast
        left; constructor <;> linarith [hin₁'.2]
      · -- at the second copy of the split vertex
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ (L := L1 + δ) (⋄) hA₁.1 hA₁.2.1 hA₁.2.2.1
          (u := 0) le_rfl one_pos (by rw [← heq]; push_cast; ring)
        have hvtx : M.W.vtx ((g + L1) % M.W.n) = M₂.W.vtx ((g' + (L1 + δ)) % M₂.W.n) := by
          have := hC.A2 0 (Nat.zero_le _)
          rwa [add_zero, add_zero, show g' + L1 + δ = g' + (L1 + δ) by ring] at this
        have hu : sidePt M.W ((g + L1) % M.W.n) 0 = sidePt M₂.W pa₁ ta₁ := by
          Ξ hp1, ht1, Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, hvtx
        have hnoV : sidePt M₂.W pa₁ ta₁ ≠ M₂.W.vtx g' := by
          Ξ hp1, ht1
          refine hC.noV _ (Nat.mod_lt _ hn₂) 0 le_rfl one_pos ?_ ?_ <;>
            rw [off_key hC.hg' (by omega : L1 + δ < M₂.W.n) le_rfl one_pos] <;> push_cast <;>
            linarith
        obtain ⟨e', he', hqe', hec'⟩ := hC.trans c' hc' _ hA₁.2.2.2.1 hqD₀ hnoV
        have hA₁P : SideAttach M₂.W c' ((g' + (L1 + δ)) % M₂.W.n) 0 := by
          have := hA₁; Ξ' hp1, ht1 at this; exact this
        have hAe' := hG.splitAttach (L1 + δ) (Or.inr rfl) c' hc' hA₁P e' he' hec'
          (by rw [hu]; exact hqe')
        refine ⟨e', he', hec', hqe', _, _, hAe', hu, ?_,
          ⟨L1, ⋄, 0, le_rfl, one_pos, ⟡, hu⟩⟩
        Ξ hC.off_M (by omega : L1 < L1 + L2) le_rfl one_pos
        left; constructor <;> linarith [ht'.1]
    obtain ⟨hbtw, y, hyc, hyS, hyq⟩ := hC.far_btw hd hd' ht ht' hcut hcut' hU hf hf' hne hc' hB₁
      he' hec' hqe' hqD₀ (fun h => hAB₁ h.symm) hAe hpe hbe
    Ξ' hdq, hdq' at hbtw
    push_cast at hbtw
    have hob : (d : ℝ) + t < off M₂.W.n g' (pb₁ + tb₁) ∧
        off M₂.W.n g' (pb₁ + tb₁) ≤ L1 + δ - s := by
      rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨h1, ?_⟩
        by_contra hlt; push Not at hlt
        exact hout₁ (Or.inr ⟨⟡, h2⟩)
      · exfalso; linarith [ht'.1]
    have hcc : c ≠ c' := by
      rintro rfl
      rcases attach_third hC.hM₂ (hC.hS hc) hA₁ hB₁ hAB₁ hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hout' (by rw [h1, h2]; left; exact ⟨⟡, hin₁'.2⟩)
      · exact hout' (by rw [h1, h2]; left; exact ⟨hob.1, by linarith [ht'.1]⟩)
    obtain ⟨hA1, hA2⟩ := hAg
    have hab₁ : off M₂.W.n g' (pb₁ + tb₁) < off M₂.W.n g' (pa₁ + ta₁) := by
      linarith [hob.2]
    by_cases hmid : off M₂.W.n g' (pb₁ + tb₁) < off M₂.W.n g' (pa + ta) ∧
        off M₂.W.n g' (pa + ta) < off M₂.W.n g' (pa₁ + ta₁)
    · obtain ⟨h1, h2⟩ := no_cross_off hC.hM₂ hC.hS hC.hSfin hc' hc (Ne.symm hcc) hB₁ hA₁
        (Ne.symm hAB₁) hA hB hg'0 hg'n hab₁ hmid.1 hmid.2
      exact hout' (Or.inl ⟨by linarith [hob.1], by linarith [hin₁'.2]⟩)
    have hge : off M₂.W.n g' (pa + ta) ≤ off M₂.W.n g' (pb₁ + tb₁) ∨
        off M₂.W.n g' (pa + ta) = off M₂.W.n g' (pa₁ + ta₁) := by
      by_contra hcon; push Not at hcon
      exact hmid ⟨lt_of_le_of_ne' (⟡) hcon.1.ne', lt_of_le_of_ne (le_trans hA2 hoaL)
        hcon.2⟩
    rcases hge with hge | heq
    · rcases lt_or_eq_of_le (le_trans hA1 hge) with hlt | heq'
      · -- `c'` is attached strictly inside the gap
        exact hyq (hG.gapOut c' hc' pb₁ tb₁ hB₁ hlt (by linarith [hob.2]) y hyc _
          (hec' hqe') hyS hqS)
      · -- both at the split vertex before the gap
        have hA' : off M₂.W.n g' (pa + ta) = L1 := le_antisymm (heq' ▸ hge) hA1
        obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ hL1n hB₁.1 hB₁.2.1 hB₁.2.2.1
          (u := 0) le_rfl one_pos (by rw [← heq']; ring)
        obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ hL1n hA.1 hA.2.1 hA.2.2.1
          (u := 0) le_rfl one_pos (by rw [hA']; ring)
        have hB₁' := hB₁
        have hA'' := hA
        Ξ' hp1, ht1 at hB₁'
        Ξ' hp2, ht2 at hA''
        exact hcc (hG.oneAt L1 (Or.inl rfl) c hc c' hc' hA'' hB₁')
    · -- both at the second copy of the split vertex
      have hoaL1 : off M₂.W.n g' (pa₁ + ta₁) = L1 + δ := le_antisymm (heq ▸ hA2) hoaL
      obtain ⟨hp1, ht1⟩ := hC.key_of_off₂ (L := L1 + δ) (⋄) hA₁.1 hA₁.2.1 hA₁.2.2.1
        (u := 0) le_rfl one_pos (by rw [hoaL1]; push_cast; ring)
      obtain ⟨hp2, ht2⟩ := hC.key_of_off₂ (L := L1 + δ) (⋄) hA.1 hA.2.1 hA.2.2.1
        (u := 0) le_rfl one_pos (by rw [heq, hoaL1]; push_cast; ring)
      have hA₁' := hA₁
      have hA'' := hA
      Ξ' hp1, ht1 at hA₁'
      Ξ' hp2, ht2 at hA''
      exact hcc (hG.oneAt (L1 + δ) (Or.inr rfl) c hc c' hc' hA'' hA₁')
  by_cases h : Btw (d' + δ + t') (L1 + δ - 1 + (1 - s)) (off M₂.W.n g' (pa' + ta'))
  · exact core hA' hB' hAB' h (hsep.1 h)
  · exact core hB' hA' (Ne.symm hAB') (by_contra fun hn' => h (hsep.2 hn')) h

/-- **Lemma (K3), generic form.**  Two positions of the stretch of `M` (inside walk edges, not
cuts of `F`) facing the same region of `F` correspond to positions of `M₂` facing the same region
of `S`, or the gap lies between them and their regions of `S` are the ones faced just after the
split vertex of `M₂` (before the gap) and just before its second copy (after the gap). -/
theorem label_gen3 (hC : Corr0 M M₂ F S g g' L1 L2 δ) (hG : 0 < δ → CorrGap M M₂ F S g g' L1 L2 δ)
    {d d' : ℕ} (hd : d < L1 + L2) (hd' : d' < L1 + L2) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    (hcut' : ¬ M.IsCut F (((g + d') % M.W.n : ℕ) + t')) {U : Set Point}
    (hU : U ∈ M.regions F) (hf : M.Faces ((g + d) % M.W.n) t U)
    (hf' : M.Faces ((g + d') % M.W.n) t' U) {V V' : Set Point} (hV : V ∈ M₂.regions S)
    (hV' : V' ∈ M₂.regions S) (hfV : M₂.Faces ((g' + dq L1 δ d) % M₂.W.n) t V)
    (hfV' : M₂.Faces ((g' + dq L1 δ d') % M₂.W.n) t' V') :
    V = V' ∨ (0 < δ ∧ AfterFaces M₂ ((g' + L1) % M₂.W.n) 0 V ∧
        BeforeFaces M₂ ((g' + L1 + δ) % M₂.W.n) 0 V') ∨
      (0 < δ ∧ BeforeFaces M₂ ((g' + L1 + δ) % M₂.W.n) 0 V ∧
        AfterFaces M₂ ((g' + L1) % M₂.W.n) 0 V') := by
  by_cases hVV : V = V'
  · exact Or.inl hVV
  right
  have hn := hC.n_pos
  have hn₂ := hC.n₂_pos
  have hc₂ := hC.not_cut₂ hd ht hcut
  have hc₂' := hC.not_cut₂ hd' ht' hcut'
  obtain ⟨c, hc, hsepc⟩ : ∃ c ∈ S, M₂.Separates c (((g' + dq L1 δ d) % M₂.W.n : ℕ) + t)
      (((g' + dq L1 δ d') % M₂.W.n : ℕ) + t') := by
    by_contra hno
    push Not at hno
    exact hVV ((hC.hM₂.eq_iff_not_separates hC.hS hC.hSfin hV hV' (Nat.mod_lt _ hn₂)
      (Nat.mod_lt _ hn₂) ht ht' hc₂ hc₂' hfV hfV').2 hno)
  obtain ⟨pa, pb, ta, tb, hA, hB, hAB, hiff⟩ := hsepc
  have hsep := hC.sep₂_btw hc (Nat.mod_lt _ hn₂) (Nat.mod_lt _ hn₂) ht ht' hc₂ hc₂' hA hB hAB hiff
  Ξ' hC.off_M₂ hd ht.1.le ht.2, hC.off_M₂ hd' ht'.1.le ht'.2 at hsep
  -- the attachment between the counterparts is in the gap
  have hsame : ∀ {e : Set Point}, e ∈ F → ¬ M.Separates e (((g + d) % M.W.n : ℕ) + t)
      (((g + d') % M.W.n : ℕ) + t') := fun he hs =>
    (hC.hM.eq_iff_not_separates hC.hF hC.hfin hU hU (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ht ht'
      hcut hcut' hf hf').1 rfl _ he hs
  have hdd : (d : ℝ) + t ≠ d' + t' := by
    intro h
    obtain ⟨e1, e2⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 ht'.1.le ht'.2 h
    subst e1; subst e2
    exact hVV (WalkAx.faces_unique hV hV' hfV hfV')
  have gap_of : ∀ {pa pb : ℕ} {ta tb : ℝ}, SideAttach M₂.W c pa ta → SideAttach M₂.W c pb tb →
      sidePt M₂.W pa ta ≠ sidePt M₂.W pb tb →
      Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pa + ta)) →
      ¬ Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb)) →
      InGap L1 δ (off M₂.W.n g' (pa + ta)) := by
    intro pa pb ta tb hA hB hAB hin hout
    rcases hC.mirror hd hd' ht ht' hc hA hB hAB hin hout with
      ⟨e, he, p₁, p₃, t₁, t₃, hA₁, hA₃, hne, hb1, hb3⟩ | hg
    · exact absurd (hC.sepM hd hd' ht ht' hcut hcut' hdd he hA₁ hA₃ hne hb1 hb3) (hsame he)
    · exact hg
  -- orient the separating chord
  obtain ⟨pa, pb, ta, tb, hA, hB, hin, hout⟩ : ∃ pa pb ta tb, SideAttach M₂.W c pa ta ∧
      SideAttach M₂.W c pb tb ∧
      Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pa + ta)) ∧
      ¬ Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pb + tb)) ∧
      InGap L1 δ (off M₂.W.n g' (pa + ta)) := by
    by_cases h : Btw ((dq L1 δ d : ℕ) + t) ((dq L1 δ d' : ℕ) + t') (off M₂.W.n g' (pa + ta))
    · exact ⟨pa, pb, ta, tb, hA, hB, h, hsep.1 h, gap_of hA hB hAB h (hsep.1 h)⟩
    · have h' := by_contra fun hn' => h (hsep.2 hn')
      exact ⟨pb, pa, tb, ta, hB, hA, h', h, gap_of hB hA (Ne.symm hAB) h' h⟩
  obtain ⟨hgap, hin', hout'⟩ := And.intro hout.2 (And.intro hin hout.1)
  -- the two positions lie on both sides of the gap
  have hng := not_inGap_dq (L1 := L1) (δ := δ) (d := d) ht.1 ht.2
  have hng' := not_inGap_dq (L1 := L1) (δ := δ) (d := d') ht'.1 ht'.2
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have side : ∀ k : ℕ, ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → (k < L1 → ((dq L1 δ k : ℕ) : ℝ) + s < L1) ∧
      (L1 ≤ k → (L1 : ℝ) + δ < ((dq L1 δ k : ℕ) : ℝ) + s) := by
    intro k s hs
    constructor
    · intro hk
      have : (k : ℝ) + 1 ≤ L1 := by exact_mod_cast hk
      unfold dq; rw [ite_eq_left hk]; linarith [hs.2]
    · intro hk
      have : (L1 : ℝ) ≤ k := by exact_mod_cast hk
      unfold dq; rw [ite_eq_right (⋄)]; push_cast; linarith [hs.1]
  obtain ⟨hg1, hg2⟩ := hgap
  rcases lt_or_ge d L1 with hdL | hdL
  · have hLd : L1 ≤ d' := by
      by_contra hlt; push Not at hlt
      have a1 := (side d t ht).1 hdL
      have a2 := (side d' t' ht').1 hlt
      rcases hin' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hδp : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · have := hC.hδ h; omega
      · exact h
    have hG' : CorrGap M M₂ F S g g' L1 L2 δ := hG hδp
    exact Or.inl ⟨hδp, hC.gapS_of hG' hdL hLd hd' ht ht' hcut hcut' hU hf hf' hc hA hB ⟨hg1, hg2⟩
      hout' hV hfV,
      hC.gapE_of hG' hdL hLd hd' ht ht' hcut hcut' hU hf hf' hc hA hB ⟨hg1, hg2⟩ hout' hV' hfV'⟩
  · have hLd : d' < L1 := by
      by_contra hlt; push Not at hlt
      have a1 := (side d t ht).2 hdL
      have a2 := (side d' t' ht').2 hlt
      rcases hin' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hδp : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · have := hC.hδ h; omega
      · exact h
    have hG' : CorrGap M M₂ F S g g' L1 L2 δ := hG hδp
    exact Or.inr ⟨hδp, hC.gapE_of hG' hLd hdL hd ht' ht hcut' hcut hU hf' hf hc hA hB ⟨hg1, hg2⟩
      (fun h => hout' h.symm) hV hfV,
      hC.gapS_of hG' hLd hdL hd ht' ht hcut' hcut hU hf' hf hc hA hB ⟨hg1, hg2⟩
      (fun h => hout' h.symm) hV' hfV'⟩

end Corr0

end Sweep

end

end Chazelle.Core
