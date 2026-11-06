module

public import Chazelle.MacT
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.SpecNF
public import Chazelle.Core.Facts2Trap
public import Chazelle.Core.ClusterEulerRam
public import Chazelle.Existence.Diagonal
public import Chazelle.Core.TopIdx
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Chazelle.Core.Lemma41Cover

namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj)

/-- **Corrected `AttachFaceSpec`**: the conclusion of `AttachFaceSpec` for a chord that is the only
chord of `F` attached at the position. -/
def AttachFaceSpecNC : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set ztf), GoodModel M → M.ChordFamily Q F →
    ∀ c ∈ F, ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      ztdpx →
      ∃ U V, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
        Chazelle.Chain.TouchesIn M.D c U ∧ Chazelle.Chain.TouchesIn M.D c V ∧
        ∃ δ > (0 : ℝ), ∀ (p' : ℕ) (t' : ℝ), p' < M.W.n → 0 < t' → t' < 1 →
          (ztwze ∨
              ztwvw →
            M.Faces p' t' U) ∧
          (ztxuj ∨
              ztxjx →
            M.Faces p' t' V)

/-! ## Cyclic facts -/
theorem cyc_sub_start {a b y k : ℝ} (hy : sideInArc a b y) (hk : ¬ sideInArc a b k)
    (hka : k ≠ a) : sideInArc a k y := by
  have := lt_or_gt_of_ne hka
  unfold sideInArc at *
  grind
theorem cyc_ext2 {l a b x y m : ℝ} (hla : l ≠ a) (hab : a ≠ b) (hx : sideInArc l a x)
    (hy : sideInArc a b y) (hl : ¬ sideInArc a b l) (hm1 : ¬ sideInArc l a m) (hma : m ≠ a)
    (hm2 : ¬ sideInArc a b m) : sideInArc l y x ∧ ¬ sideInArc l y m ∧ y ≠ m := by
  have := lt_or_gt_of_ne hla
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne hma
  refine ⟨?_, ?_, by_grind⟩
  · unfold sideInArc at *
    grind
  · unfold sideInArc at *
    grind
theorem cyc_after_delta {k r x n δ : ℝ} (hkr : k ≠ r) (hx0 : 0 ≤ x) (_hxn : x < n) (_hr0 : 0 ≤ r)
    (hrn : r < n) (hδ : δ ≤ if k < r then r - k else r + n - k)
    (h : (0 < x - k ∧ x - k < δ) ∨ (0 < x + n - k ∧ x + n - k < δ)) : sideInArc k r x := by
  have := lt_or_gt_of_ne hkr
  zuiq
theorem cyc_before_delta {l k x n δ : ℝ} (hlk : l ≠ k) (_hx0 : 0 ≤ x) (hxn : x < n) (hl0 : 0 ≤ l)
    (_hln : l < n) (hδ : δ ≤ if l < k then k - l else k + n - l)
    (h : (0 < k - x ∧ k - x < δ) ∨ (0 < k + n - x ∧ k + n - x < δ)) : sideInArc l k x := by
  have := lt_or_gt_of_ne hlk
  zuiq
variable {K : Set ℝ}
/-- The successor of an element of a finite set of at least two reals. -/
theorem exists_succ_gap (hK : K.Finite) {k k' : ℝ} (hk : k ∈ K) (hk' : k' ∈ K)
    (hne : k ≠ k') : ∃ r ∈ K, r ≠ k ∧ ∀ m ∈ K, ¬ sideInArc k r m := by
  obtain ⟨m₀, hm₀, hmin⟩ := Set.exists_min_image K id hK ztuiy
  simp only [id] at hmin
  by_cases hA : ∃ m ∈ K, k < m
  · obtain ⟨r, ⟨hr, hkr⟩, hrm⟩ := Set.exists_min_image {m | m ∈ K ∧ k < m} id
      ztmks by_tauto
    refine ⟨r, hr, ne_of_gt hkr, fun m hm hin => ?_⟩
    zubix
    rw [ite_eq_left_of_eq_true _ _ (eq_true hkr)] at hin
    have := hrm m by_simp_all
    grind
  · zubhq
    have hm₀k : m₀ ≠ k := by
      grind
    refine ⟨m₀, hm₀, hm₀k, fun m hm hin => ?_⟩
    zubix
    grind

/-- The predecessor of an element of a finite set of at least two reals. -/
theorem exists_pred_gap (hK : K.Finite) {k k' : ℝ} (hk : k ∈ K) (hk' : k' ∈ K)
    (hne : k ≠ k') : ∃ l ∈ K, l ≠ k ∧ ∀ m ∈ K, ¬ sideInArc l k m := by
  obtain ⟨M₀, hM₀, hmax⟩ := Set.exists_max_image K id hK ztuiy
  simp only [id] at hmax
  by_cases hB : ∃ m ∈ K, m < k
  · obtain ⟨l, ⟨hl, hlk⟩, hlm⟩ := Set.exists_max_image {m | m ∈ K ∧ m < k} id
      ztmks by_tauto
    refine ⟨l, hl, ne_of_lt hlk, fun m hm hin => ?_⟩
    zubix
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlk)] at hin
    have := hlm m by_simp_all
    grind
  · zugrf
    have hM₀k : M₀ ≠ k := by
      grind
    refine ⟨M₀, hM₀, hM₀k, fun m hm hin => ?_⟩
    zubix
    grind
namespace WalkAx
variable {M : Model}

/-- **The start of an arc carries an exit chord**: some chord of `F` touching `U` is attached at
the start key of every arc of `U` (mirror of `exists_exit_at_end`). -/
theorem exists_exit_at_start (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hne : F.Nonempty) {U : Set Point} (hU : U ∈ M.regions F) {a b : ℝ}
    (harc : M.IsArc F U a b) :
    ∃ c ∈ {c | c ∈ F ∧ TouchesIn M.D c U}, ∃ p t, SideAttach M.W c p t ∧ a = p + t := by
  zupf
  zufuc
  zuljg
  zudr
  zubap
  zufjt
  zuixy
  zulwf
  -- a position `y` inside the arc
  obtain ⟨py, hpy, ty, hty, hyin, hycut, hyf⟩ := exists_pos_in_arc hne harc
  -- the gap before `a` and a position `x` in it
  obtain ⟨l, hl, hla, hlgap⟩ := exists_pred_gap hK hcuta hcutb hab
  obtain ⟨V, hV, harcV⟩ := hM.arc_of_gap hF hfin hl hcuta hla (fun k hk hc => hlgap k hc hk)
  obtain ⟨px, hpx, tx, htx, hxin, hxcut, hxV⟩ := exists_pos_in_arc hne harcV
  -- `V = U`
  zuov
  zuvh
  have hVfree :=
    (Chazelle.Chain.regionsIn_subset hV).trans zthag
  zuiob
  have hVVT :=
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVfree
  zuequ

  have hUTr : ztumm := by
    zummu
    exact ⟨u, ((Chazelle.Chain.regionsIn_subset hU).trans
      zthag) hu, rfl⟩
  have hxVT : M.Faces px tx VT := hxV.mono by_grind
  zudob
  have hlb : ztsob := by_grind
  have hsame : VT = U := by
    refine (hM.eq_iff_not_separates by_grind hTfin hVTr hUTr hpx hpy htx
      hty by_grind by_grind hxVT hyf).2 ?_
    zuctm
    have hkey : ∀ m, M.IsCut T m → ¬ sideInArc l a m ∧ m ≠ a ∧ ¬ sideInArc a b m := by
      zucng
      refine ztrak
      zunq
      tauto
    have kA := hkey _ ztkjj
    have kB := hkey _ ztkjm
    obtain ⟨hx', hA', hyA⟩ := cyc_ext2 hla hab hxin hyin hlb kA.1 kA.2.1 kA.2.2
    obtain ⟨-, hB', hyB⟩ := cyc_ext2 hla hab hxin hyin hlb kB.1 kB.2.1 kB.2.2
    have h := cyc_nosep hx' hA' hB' hyA hyB ztlqm
    grind
  zuhxr
  have hVeq : V = U := by
    zuidh
    · zubh
    grind
  zuktg
  -- the chord attached at `a` separates `x` from `y`
  obtain ⟨c₀, hc₀, pa, ta, hA₀, ha⟩ := hcuta
  obtain ⟨pb₀, tb₀, hB₀, hB₀ne⟩ := hM.other_attach ztmkp hA₀
  obtain ⟨K₁, K₂, hne', ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ :=
    hM.split ztmkp hA₀ hB₀ (Ne.symm hB₀ne)
  have hkB : ztidq := ⟨c₀, hc₀, pb₀, tb₀, hB₀, rfl⟩
  have hkne : (pb₀ : ℝ) + tb₀ ≠ a := by
    rw [ha]; exact key_ne_of_pt_ne hB₀ hA₀ hB₀ne
  have hyA : sideInArc ztbf zttvu ztdhy := by
    zuort; exact cyc_sub_start hyin by_grind hkne
  have hxA : sideInArc zttvu ztbf ztcat := by
    zuort; exact cyc_sub hxin by_grind hkne
  have hU1 := hM.region_subset_of_sector hc₀ hU hpy hty hyf ztoak
  have hU2 := hM.region_subset_of_sector hc₀ hU hpx htx hxV ztoal
  exact hne' ztdas

/-- **The walk next to an attachment.**  For a chord `c ∈ F` attached at `A = (p, t)` (key `k`),
the keys of the cut-free gap after `k` are an arc of a region `U`, those of the gap before `k` an
arc of a region `V`, `U ≠ V`, and `U` (resp. `V`) touches `c` when `c` is the only chord of `F`
attached at `A`. -/
theorem attach_face (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t) :
    ∃ U V l r, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
      M.IsArc F U ztk r ∧ M.IsArc F V l ztk ∧
      (ztdpx →
        TouchesIn M.D c U ∧ TouchesIn M.D c V) := by
  zubar
  zubap
  have hk : ztidq := ztcxr
  zuejc
  have hkB : ztidq := ztcxs
  have hkne := key_ne_of_pt_ne hA hB ztbsb
  obtain ⟨r, hr, hrk, hrgap⟩ := exists_succ_gap hK hk hkB hkne
  obtain ⟨l, hl, hlk, hlgap⟩ := exists_pred_gap hK hk hkB hkne
  obtain ⟨U, hU, harcU⟩ := hM.arc_of_gap hF hfin hk hr ztvbo
    (fun m hm hc => hrgap m hc hm)
  obtain ⟨V, hV, harcV⟩ := hM.arc_of_gap hF hfin hl hk hlk (fun m hm hc => hlgap m hc hm)
  refine ⟨U, V, l, r, hU, hV, ?_, harcU, harcV, fun hsole => ztcp⟩
  · -- the two sides of `c`
    intro hUV
    obtain ⟨K₁, K₂, hne', ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split ztlz hA hB ztbsb
    obtain ⟨py, hpy, ty, hty, hyin, -, hyf⟩ := exists_pos_in_arc hne harcU
    obtain ⟨px, hpx, tx, htx, hxin, -, hxf⟩ := exists_pos_in_arc hne harcV
    have hyA : ztuuw :=
      cyc_sub_start hyin by_simp_all ztqba
    have hxA : ztuuw :=
      cyc_sub hxin by_simp_all ztqba
    have hU1 := hM.region_subset_of_sector hc hU hpy hty hyf ztoak
    rw [hUV] at hU1
    have hU2 := hM.region_subset_of_sector hc hV hpx htx hxf ztoal
    zuov
    exact hne' ((connectedComponentIn_eq (hU1 hv)).trans (connectedComponentIn_eq (hU2 hv)).symm)
  · obtain ⟨c', hc', p', t', hA', hk'⟩ := hM.exists_exit_at_start hF hfin hne hU harcU
    zuejj

  · obtain ⟨c', hc', p', t', hA', hk'⟩ := hM.exists_exit_at_end hF hfin hne hV harcV
    zuejj
end WalkAx

/-- **WP-B: the walk next to an attachment** (`AttachFaceSpec` for a chord alone at its
position). -/
theorem attachFaceNC : AttachFaceSpecNC := by
  zudib

  obtain ⟨U, V, l, r, hU, hV, hUV, harcU, harcV, htouch⟩ :=
    hW.attach_face hF.2.1 hF.1 hc hA
  obtain ⟨hcU, hcV⟩ := htouch hsole
  have hk0 : ztmqv := by have := hA.2.1; positivity
  have hkn : (p : ℝ) + t < M.W.n := by
    have : ztbou := by exact_mod_cast hA.1
    zujcb
  obtain ⟨hr0, hrn⟩ := WalkAx.cut_bounds (harcU.2.2.2.2.1.resolve_right by_grind).2.1
  obtain ⟨hl0, hln⟩ := WalkAx.cut_bounds (harcV.2.2.2.2.1.resolve_right by_grind).1
  have hkr := (harcU.2.2.2.2.1.resolve_right by_grind).2.2
  have hlk := (harcV.2.2.2.2.1.resolve_right by_grind).2.2
  set δ₁ : ℝ := if (p : ℝ) + t < r then r - ztk else r + M.W.n - ztk with hδ₁
  set δ₂ : ℝ := if l < (p : ℝ) + t then ztk - l else ztk + M.W.n - l with hδ₂
  have hδ₁0 : 0 < δ₁ := by
    grind
  have hδ₂0 : 0 < δ₂ := by
    grind
  refine ⟨U, V, hU, hV, hUV, hcU, hcV, min δ₁ δ₂, by_grind,
    fun p' t' hp' ht0 ht1 => ztbwk⟩
  · zukgv
    have hxn : ztmru := by
      zuhvc

    have hin := cyc_after_delta hkr hx0 hxn hr0 hrn (min_le_left δ₁ δ₂) (by
      omega)
    exact harcU.2.2.2.2.2.2 p' t' hp' ht0 ht1 hin
  · zukgv
    have hxn : ztmru := by
      zuhvc

    have hin := cyc_before_delta hlk hx0 hxn hl0 hln (min_le_right δ₁ δ₂) (by
      omega)
    exact harcV.2.2.2.2.2.2 p' t' hp' ht0 ht1 hin
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section

/-- **WP-B: the cut structure** (`CutStructureSpec`, part 3 for non-cut positions). -/
theorem cutStructure : CutStructureSpec := cutStructureNC
open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn)
open Chazelle.Jordan (exists_openEdge_of_mem_boundary simple_three_le succIdx_ne)
open Chazelle.Visibility (hseg trapSet closedTrap IsTrap edgeX chords freeRegion chordUnion)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)
namespace FullDegInt
variable {Q : Polygon}

/-- A horizontal chord of the interior of `Q`. -/
def HC (Q : Polygon) (c : Set Point) : Prop :=
  ∃ y a b : ℝ, IsHChordIn ztrx y a b ∧ c = hseg y a b
theorem hc_full (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) : HC Q c := by
  obtain ⟨i, σ, -, -, -, rfl, h⟩ := Visibility.chords_spec hQ hc
  exact ⟨_, _, _, ⟨h.lt, fun hm => hm.2 h.left_mem, fun hm => hm.2 h.right_mem, h.open_int⟩,
    Visibility.chordSet_eq_hseg _ _ _⟩
variable {y a b : ℝ}
/-- A point of a chord in the domain is strictly inside it. -/
theorem open_of_mem (h : IsHChordIn ztrx y a b) {z : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ Q.filled \ Q.boundary) : a < z.1 ∧ z.1 < b := by
  zubpe
  refine zthnj
  · grind
  grind

/-- Two chords sharing a point of the domain are equal. -/
theorem eq_of_common {c c' : Set Point} (hc : HC Q c) (hc' : HC Q c') {z : Point} (hz : z ∈ c)
    (hz' : z ∈ c') (hzD : z ∈ Q.filled \ Q.boundary) : c = c' := by
  zuhs
  zubaz

  · rfl
  · zulxk
  · zulxl

/-- **A chord contains every point of its line joined to it inside the domain.** -/
theorem mem_of_joined (h : IsHChordIn ztrx y a b) {z : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ Q.filled \ Q.boundary) {w : Point} (hw : w.2 = y)
    (hj : ∀ s : ℝ, min z.1 w.1 ≤ s → s ≤ max z.1 w.1 → (ztkel : Point) ∈ Q.filled \ Q.boundary) :
    w ∈ hseg y a b := by
  zueuh

  · zuhby

  · zuhbz

/-- The points of a chord between two of its domain points are in the domain. -/
theorem between_mem (h : IsHChordIn ztrx y a b) {z z' : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ Q.filled \ Q.boundary) (hz' : z' ∈ hseg y a b)
    (hz'D : z' ∈ Q.filled \ Q.boundary) {s : ℝ} (h1 : z.1 ≤ s) (h2 : s ≤ z'.1) :
    (ztkel : Point) ∈ Q.filled \ Q.boundary :=
  h.open_mem s ztjpt ztjpu

/-- **A boundary point near which the points on one side (`τ = ±1`) are in the domain is a
vertex**, for a polygon with distinct heights. -/
theorem vertex_of_side (hQ : Q.Simple) (hDH : DistinctHeights Q) {w : Point}
    (hw : w ∈ Q.boundary) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hnear : ∀ᶠ p' in 𝓝 w, 0 < τ * (p'.2 - w.2) → p' ∈ Q.filled \ Q.boundary) :
    ∃ m < Q.n, w = Q.vtx m := by
  zubaj

  obtain ⟨e, he, t, ht, rfl⟩ := exists_openEdge_of_mem_boundary Q hw fun m hm h => hno m hm h
  set u := Q.vtx e
  set v := Q.vtx ztwki
  zuerp
  have huv := hDH e _ he ztcv (succIdx_ne Q hn he).symm
  have hd : ztsmu := by_grind
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hnear
  set L := dist u v + 1 with hL
  zujzk
  set δ := min ztzxc ztufe / 2 with hδ
  have hδ0 : ztcfy := by
    rw [hδ]; have := lt_min (lt_min ht.1 ztwgb) (div_pos hε hL0); linarith
  have hδm : δ < min ztzxc ztufe := by
    grind
  have hδt := hδm.trans_le ztwth
  have hδt' := hδm.trans_le ztwti
  have hδε : δ * L < ε := by
    have := hδm.trans_le ztgh; rwa [lt_div_iff₀ hL0] at this
  -- the direction along the edge that moves to the side `τ`
  set σ : ℝ := if 0 < τ * ztgv then 1 else -1 with hσ
  have hσ1 : ztim := by zungf; split_ifs <;> simp
  have hσpos : 0 < τ * ztbabi := by
    zungf
    have hτd : τ * ztgv ≠ 0 := mul_ne_zero (by rcases hτ with rfl | rfl <;> norm_num) hd
    zus
    · linarith
    grind
  set s := t + σ * δ with hs
  have hs0 : 0 ≤ s := by rcases hσ1 with h | h <;> zuokl <;> linarith
  have hs1 : s ≤ 1 := by rcases hσ1 with h | h <;> zuokl <;> linarith
  have hpt : lerp u v s ∈ Q.boundary := ⟨e, he, lerp_mem_segment _ _ hs0 hs1⟩
  apply (hball ?_ ?_).2 hpt
  · rw [dist_eq_norm]
    have : lerp u v s - lerp u v t = ztye • ztbnr := by
      apply point_ext <;> simp [lerp, hs] <;> ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hδ0, ← dist_eq_norm, dist_comm]
    have : ztguu := by rcases hσ1 with h | h <;> zvmwc <;> norm_num
    rw [this, one_mul]
    grind
  · simp only [lerp_snd, hs]
    have : u.2 + (t + σ * δ) * ztgv - (u.2 + t * ztgv) =
        δ * ztbabi := by_ring
    zubk
    nlinarith

/-- A vertex at a given height is unique. -/
theorem vtx_eq_of_height (hDH : DistinctHeights Q) {m k : ℕ} (hm : m < Q.n) (hk : k < Q.n)
    (h : (Q.vtx m).2 = (Q.vtx k).2) : m = k := by
  zuisa

/-- **Two chords touching a region from one horizontal side of a trapezoid, on the same side of
the vertex at that height, are equal.** -/
theorem side_chords_eq (hQ : Q.Simple) (hDH : DistinctHeights Q) {T : Set Point}
    (hT : T ⊆ Q.filled \ Q.boundary) {y₀ xl xr : ℝ} {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hcl : ∀ x, xl < x → x < xr → (ztcoo : Point) ∈ Q.filled)
    (hnear : ∀ x, xl < x → x < xr →
      ∀ᶠ p' in 𝓝 (ztcoo : Point), 0 < τ * ztkbz → p' ∈ T)
    {k₀ : ℕ} (hk₀ : k₀ < Q.n) (hk₀y : (Q.vtx k₀).2 = y₀)
    {c c' : Set Point} (hc : HC Q c) (hc' : HC Q c') {z z' : Point} (hz : z ∈ c) (hz' : z' ∈ c')
    (hzD : z ∈ Q.filled \ Q.boundary) (hz'D : z' ∈ Q.filled \ Q.boundary)
    (hzy : z.2 = y₀) (hz'y : z'.2 = y₀) (hzx : xl ≤ z.1 ∧ z.1 ≤ xr) (hz'x : xl ≤ z'.1 ∧ z'.1 ≤ xr)
    (hside : z.1 < (Q.vtx k₀).1 ↔ z'.1 < (Q.vtx k₀).1) : c = c' := by
  -- ordered version
  have key : ∀ {c c' : Set Point} {z z' : Point}, HC Q c → HC Q c' → z ∈ c → z' ∈ c' →
      z ∈ Q.filled \ Q.boundary → z' ∈ Q.filled \ Q.boundary → z.2 = y₀ → z'.2 = y₀ →
      xl ≤ z.1 → z'.1 ≤ xr → z.1 ≤ z'.1 →
      (z.1 < (Q.vtx k₀).1 ↔ z'.1 < (Q.vtx k₀).1) → c = c' := by
    intro c c' z z' hc hc' hz hz' hzD hz'D hzy hz'y hzl hz'r hle hside
    zuhs
    zubwr
    by_cases hall : ∀ s : ℝ, z.1 ≤ s → s ≤ z'.1 → (zttzn : Point) ∈ Q.filled \ Q.boundary
    · have hz'c : z' ∈ hseg y a b := mem_of_joined h hz hzD by_simp_all by_simp_all
      exact eq_of_common ztfxb hc' hz'c hz' hz'D
    · exfalso
      zugrg
      obtain ⟨s, hs1, hs2, hsD⟩ := hall
      have hs1' : z.1 < s := by_grind
      have hs2' : s < z'.1 := by_grind
      have hsl : xl < s := by_linarith
      have hsr : s < xr := by_linarith
      have hb : (zttzn : Point) ∈ Q.boundary := by
        simp_all
      obtain ⟨m, hm, hwm⟩ := vertex_of_side hQ hDH hb hτ
        ((hnear s hsl hsr).mono by_grind)
      have hmk := vtx_eq_of_height hDH hm hk₀ by_grind
      grind
  grind

/-- The side of a chord point relative to a vertex, read off from the chord. -/
theorem side_iff {c : Set Point} (hc : HC Q c) {y₀ : ℝ} {w₀ : Point}
    (hw₀ : w₀ ∉ Q.filled \ Q.boundary) (hw₀y : w₀.2 = y₀) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzy : z.2 = y₀) :
    (∃ z' ∈ c, z' ∈ Q.filled \ Q.boundary ∧ z'.2 = y₀ ∧ z'.1 < w₀.1) ↔ z.1 < w₀.1 := by
  zuhs
  zubwr
  constructor
  · zubur

    have := between_mem h hz' hz'D hz hzD hlt.le by_omega
    grind
  grind

/-- **Degree `≤ 4`** in the interior visibility map augmented by finitely many horizontal chords,
for a simple polygon with distinct vertex heights. -/
theorem deg_le_four (hQ : Q.Simple) (hDH : DistinctHeights Q) {G : Set ztf}
    (hG : ∀ c ∈ G, HC Q c) (hGfin : G.Finite) (hfull : chords Q ⊆ G) {U : Set Point}
    (hU : U ∈ regionsIn ztrx G) :
    {c | c ∈ G ∧ TouchesIn ztrx c U}.ncard ≤ 4 := by
  classical
  zuint
  obtain ⟨q, hqf, rfl⟩ := hU
  have hfreeR : freeIn D G ⊆ freeRegion Q := fun p hp =>
    ⟨hp.1, fun ⟨c, hc, hpc⟩ => hp.2 by_grind⟩
  have hqR := hfreeR hqf
  obtain ⟨i, j, y₁, y₂, h⟩ := Visibility.exists_isTrap hQ hqR
  set T := trapSet Q i j y₁ y₂ with hTdef
  zuioa
  have hUT : ztscv := by
    rw [hTdef, ← h.region_eq hQ hqR]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      ztmmk ((connectedComponentIn_subset _ _).trans hfreeR)
  have hTD : ztscq := h.trapSet_subset_interior hQ hqR
  zubko

  have hcl : closure U ⊆ closedTrap Q i j y₁ y₂ :=
    (closure_mono hUT).trans (Visibility.closure_trapSet_subset _ _ _ _ _)
  zucdd

  -- a domain point of the closed trapezoid at a middle height is inside
  have hmid : ∀ z ∈ D, z ∈ closedTrap Q i j y₁ y₂ → y₁ < z.2 → z.2 < y₂ → z ∈ T := by
    zubbr

    exact ⟨hz1, hz2, lt_of_le_of_ne h3 fun e => hzD.2 ⟨i, h.hi, h.mem_edgeL h1 h2 e.symm⟩,
      lt_of_le_of_ne h4 fun e => hzD.2 ztmqq⟩
  -- a chord meeting `T` contains its whole slice
  have hslice : ztbvg := by
    zuor

    zumfc
    zubyd
    have hseg :=
      Geometry.segment_subset_of_convex (Visibility.convex_trapSet _ _ _ _ _) hzT hwT
    zudwt

  -- `U` is on one side of a chord crossing `T`
  have hno : ztcgd := fun c hc z hz hzT p hp he =>
    (hfreeU hp).2 ztdbh
  zudhj
  have hbelow : ztbve := by
    zubgr
    have := hUc.subset_left_of_subset_union (u := {p : Point | p.2 < z.2}) ztdvc
      ztetr
      ztmcj
      ztwzy
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    tauto
  have habove : ztbvf := by
    zubgr
    have := hUc.subset_left_of_subset_union (u := {p : Point | z.2 < p.2}) ztetr
      ztdvc
      ztmcj
      ztwzz
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    tauto
  have hclle : ztbxe := fun y hy =>
    fun p hp => closure_minimal ztbrj
      ztjyx hp
  have hclge : ztbxf := fun y hy =>
    fun p hp => closure_minimal ztbrj
      ztobt hp
  -- the two classes of exit chords
  set E₁ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ ztdwo}
    with hE₁
  set E₂ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ ztdwn}
    with hE₂
  have hsub : ztdjx := by
    zulx

    zudt
    · zuff
      · zubgk

        · exact Or.inl ztcyb
        · exact Or.inr ztcyb
      · zuleo
    · zulek
  have hBool : ztmrb := by
    simp
  -- at most two chords above
  have hE₁ : E₁.ncard ≤ 2 := by
    zuke
    · zuex

      have hsub1 : ztmsz := by
        zugm
        zudzu
        have hmz : ztjac := by
          grind
        zumj

        zufo

      calc E₁.ncard ≤ ({c₀} : Set _).ncard := ncard_le_ncard hsub1 ztgir
        _ ≤ 2 := by_simp
    · zubhq
      obtain ⟨k₀, hk₀, hk₀y, -⟩ := h.top_vertex
      zudbr

      have htop : ztcgb := by
        zucd

        · zujvm
        · zudmm
      let f : Set Point → Bool := fun c => decide (∃ z ∈ c, z ∈ D ∧ z.2 = y₂ ∧ z.1 < w₀.1)
      have hinj : InjOn f E₁ := by
        zufxj
        zubho
        obtain ⟨z', hz', hz'D, hz'U, hz'y⟩ := htop c' hc'
        zucrq

        have hside : ztpqr := by
          grind
        zuwm

        exact side_chords_eq hQ hDH hTD ztbt
          (fun x hx1 hx2 => h.closure_subset_filled hQ hqR (h.top_mem_closure hx1 hx2))
          ztmkb hk₀ hk₀y ztjxi ztjxj hz hz' hzD
          hz'D hzy hz'y by_grind by_grind hside
      calc E₁.ncard ≤ (Set.univ : Set Bool).ncard :=
            ncard_le_ncard_of_injOn f ztpbc hinj
        _ = 2 := hBool
  -- at most two chords below
  have hE₂ : E₂.ncard ≤ 2 := by
    zukf
    · zuew

      have hsub1 : ztmta := by
        zugm
        zudzt
        have hmz : ztjav := by
          grind
        zumi

        zufo

      calc E₂.ncard ≤ ({c₀} : Set _).ncard := ncard_le_ncard hsub1 ztgir
        _ ≤ 2 := by_simp
    · zubhq
      obtain ⟨k₀, hk₀, hk₀y, -⟩ := h.bot_vertex
      zudbr

      have hbot : ztcgc := by
        zucd

        · zujvm
        · zudmm
      let f : Set Point → Bool := fun c => decide (∃ z ∈ c, z ∈ D ∧ z.2 = y₁ ∧ z.1 < w₀.1)
      have hinj : InjOn f E₂ := by
        zufxj
        zubhn
        obtain ⟨z', hz', hz'D, hz'U, hz'y⟩ := hbot c' hc'
        zucrq

        have hside : ztpqr := by
          grind
        zuwm

        exact side_chords_eq hQ hDH hTD ztp
          (fun x hx1 hx2 => h.closure_subset_filled hQ hqR (h.bot_mem_closure hx1 hx2))
          ztmka hk₀ hk₀y ztjxi ztjxj hz hz' hzD
          hz'D hzy hz'y by_grind by_grind hside
      calc E₂.ncard ≤ (Set.univ : Set Bool).ncard :=
            ncard_le_ncard_of_injOn f ztpbc hinj
        _ = 2 := hBool
  have hfin12 : ztkys :=
    (hGfin.subset fun c hc => hc.1).union ztikv
  calc {c | c ∈ G ∧ TouchesIn D c U}.ncard ≤ (E₁ ∪ E₂).ncard := ncard_le_ncard hsub hfin12
    _ ≤ E₁.ncard + E₂.ncard := ncard_union_le _ _
    _ ≤ 4 := by_omega
end FullDegInt

/-- **The interior half of `FullDegSpec`**: for a simple polygon with distinct vertex heights,
the full augmented map of the interior model has degree at most `4`. -/
theorem fullDegLe_interior {Q : Polygon} (hQ : Q.Simple) (hDH : DistinctHeights Q) :
    (interiorModel Q).FullDegLe Q 4 := by
  zuhgd
  refine FullDegInt.deg_le_four hQ hDH ?_
    ((Visibility.chords_finite Q).union hF.1) subset_union_left hU
  zubyh
  · exact FullDegInt.hc_full hQ hc
  · exact hF.2.1 hc
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section

/-- **WP-B: the interior conjunct of `FullDegSpec`**: for a simple input polygon with a good
shear, the full augmented map of the interior model of the geometry polygon `Qof P` has degree at
most `4`. -/
theorem fullDeg_interior (P : Polygon) (hP : P.Simple) (hε : ∃ ε, GoodShear P ε) :
    (interiorModel zta).FullDegLe zta 4 :=
  fullDegLe_interior ((shearInvariance ztbhs P).1 hP) (goodShear_epsOf hε).2.1
open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg rayPt)
open Chazelle.Geometry (point_ext)
namespace ChainObs
open SegObs

/-- A segment given by two points, ordered by height (lower end first). -/
noncomputable def ord (u w : Point) : Point × Point := if u.2 < w.2 then ztfuz else ztkgs
variable (u w : Point) {v : Point}
theorem seg_ord : seg (ord u w) = Chazelle.segment u w := by
  unfold ord seg
  split_ifs
  · rfl
  · zulxb
theorem ord_up {u w : Point} (h : u.2 ≠ w.2) : (ord u w).1.2 < (ord u w).2.2 := by
  zulus
theorem ord_ends :
    (u = (ord u w).1 ∨ u = (ord u w).2) ∧ (w = (ord u w).1 ∨ w = (ord u w).2) := by
  zulus
theorem ord_cases (h : v = (ord u w).1 ∨ v = (ord u w).2) :
    v = u ∨ v = w := by
  unfold ord at h
  grind
variable (C : Chain)

/-- The left side of the box. -/
noncomputable def sideL : Point × Point := (ztru, ztvx)

/-- The right side of the box. -/
noncomputable def sideR : Point × Point := (ztyn, ztbjg)

/-- The slit, as a segment. -/
noncomputable def slitSeg : Point × Point := (C.top, C.slitTop)

/-- **The obstacle segments of the chain model**: the chain edges, the slit, the vertical sides
of the box. -/
noncomputable def segs : Set ztdga :=
  {s | ∃ k < C.m, s = ord ztib ztwkj} ∪ {slitSeg C, sideL C, sideR C}
variable {C}

/-- The chain has pairwise distinct vertex indices up to `m`. -/
theorem edgeIdx_inj_le {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  unfold Chain.edgeIdx at h
  zumaz
  zuftc
  zucvh

/-- Distinct chain vertices have distinct heights. -/
theorem vertex_snd_ne (hDH : DistinctHeights C.P) {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m)
    (hjk : j ≠ k) : (C.vertex j).2 ≠ (C.vertex k).2 :=
  hDH _ _ ztdyj ztcsx fun h => hjk (edgeIdx_inj_le hj hk h)
theorem side_seg_fst {R : ℝ} (hR : 0 < R) {x : ℝ} {p : Point}
    (hp : p ∈ seg (ztiph : Point × Point)) : p.1 = x ∧ |p.2| ≤ R := by
  obtain ⟨h1, h2, h3⟩ := (mem_seg_iff (s := ztiph) by_simp_all).1 hp
  zufct
  refine ⟨by zvncq; zuoew, by_grind⟩

/-- Where a point of an obstacle segment lies. -/
theorem seg_cases {s : Point × Point} (hs : s ∈ segs C) {p : Point} (hp : p ∈ seg s) :
    (p ∈ C.set ∧ ∃ k < C.m, s = ord ztib ztwkj) ∨
      (s = slitSeg C ∧ p ∈ C.slit) ∨ (s = sideL C ∧ p.1 = -C.radius ∧ |p.2| ≤ C.radius) ∨
      (s = sideR C ∧ p.1 = C.radius ∧ |p.2| ≤ C.radius) := by
  zubcw
  · left
    refine ⟨ztcyc, k, hk, rfl⟩
    rw [seg_ord] at hp
    rw [C.chainEdge_eq]; exact hp
  · zubeu

    · tauto
    · exact Or.inr (Or.inr (Or.inl ztrej))
    · exact Or.inr (Or.inr (Or.inr ztrej))
theorem abs_fst_lt_of_set {p : Point} (hp : p ∈ C.set) : |p.1| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).1 C.coordBound_lt_radius
theorem abs_top_fst_lt : |C.top.1| < C.radius := C.top_mem_box.1

/-- **The domain of the segment obstacles is the chain domain.** -/
theorem dom_eq : dom C.radius ztfim = C.dom := by
  zufj
  simp only [dom, Chain.dom, Chain.obstacle, Set.mem_sdiff, Set.mem_union]
  refine and_congr_right fun hbox => not_congr ztlvy
  · zubhl
    rcases seg_cases hs hps with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp_all
    · simp_all
    · have := hbox.1; grind
    · have := hbox.1; grind
  · rcases hp with ⟨k, hk, hpk⟩ | hp
    · refine seg_subset_obs (Or.inl ztrds) ?_
      rw [seg_ord, ← C.chainEdge_eq]; omega
    · exact seg_subset_obs (s := slitSeg C) (Or.inr by_simp) hp

/-- The vertices within the height range of the box are chain vertices. -/
theorem vert_eq_vertex (hv : IsVert ztfim v) (hvR : |v.2| < C.radius) :
    ∃ j ≤ C.m, v = C.vertex j := by
  obtain ⟨s, hs, hvs⟩ := hv
  zubcw
  · rcases ord_cases _ _ hvs with rfl | rfl
    · grind
    grind
  · simp only [mem_insert_iff, mem_singleton_iff] at hs
    zubo
    rcases hs with rfl | rfl | rfl
    · rcases hvs with rfl | rfl
      · exact ⟨C.topIdx, C.topIdx_le, rfl⟩
      · simp [slitSeg, Chain.slitTop, abs_of_pos hR] at hvR
    · rcases hvs with rfl | rfl <;> simp [sideL, abs_of_pos hR] at hvR
    · rcases hvs with rfl | rfl <;> simp [sideR, abs_of_pos hR] at hvR

/-- **The segment obstacles of a chain model are good** (simple host, distinct heights). -/
theorem good (hP : C.P.Simple) (hDH : DistinctHeights C.P) : Good C.radius ztfim := by
  zubo
  zubnz
  zugnf

  · refine Set.Finite.union (((Set.finite_Iio C.m).image
      fun k => ord ztib ztwkj).subset ?_) (Set.toFinite _)
    zugth

  · zugg
    zubcw
    · exact ord_up (vertex_snd_ne hDH by_omega by_omega by_omega)
    · zubeu

      · tauto
      · zujox
      · zujoy
  · zuza

    · have := C.abs_le_coordBound_of_mem_set h
      exact ztres
    · zukoq
      refine ⟨by zuoum; exact abs_top_fst_lt.le, by_grind⟩
    · grind
    grind
  · zuhgv
    have hslit : ztxic := by
      zubok
      zugbo

      zuhdk
      exact ztmqt
    have hsetL : ztgvc := by
      zubok
      have := abs_fst_lt_of_set h1
      grind
    have hsetR : zthpw := by
      zubok
      have := abs_fst_lt_of_set h1
      grind
    have hslitL : ztgvd := by
      zubok
      zudtg
      have := abs_top_fst_lt (C := C)
      grind
    have hslitR : zthpx := by
      zubok
      zudtg
      have := abs_top_fst_lt (C := C)
      grind
    rcases seg_cases hs hp with ⟨h1, k, hk, rfl⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1, -⟩ | ⟨rfl, h1, -⟩ <;>
      zubbf
    · -- two chain edges
      zukcz
      have hidx := fun h => hkj ztrir
      have hmem : ztyyz := by
        zujx
        · have := hp; rw [seg_ord, ← C.chainEdge_eq] at this; tauto
        · have := hp'; rw [seg_ord, ← C.chainEdge_eq] at this; tauto
      zucpt

      · zujio
      · zuocz; exact ⟨_, by_omega, (ord_ends _ _).2⟩
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    grind
  · intro v w hv hw hvR hvw
    zufkd
    obtain ⟨k, hk, rfl⟩ := vert_eq_vertex hw by_simp_all
    zuct
    exact vertex_snd_ne hDH hj hk by_grind hvw

/-- **The vertex chords of a chain are full** for the segment obstacles: a domain point seen
horizontally from a chain vertex lies on the chord of that vertex in that direction. -/
theorem fullAt {G : Set ztf} (hG : C.chords ⊆ G) : FullAt C.radius ztfim G := by
  intro v hv hvR z hz hzv hbet
  zufkd
  rw [dom_eq] at hz hbet
  set v := C.vertex j with hvdef
  have hvbox := C.set_subset_box (C.vertex_mem_set hj)
  have hzv1 := fun e => C.not_mem_set_of_mem_dom hz (by
    rw [show z = v from point_ext e hzv]; exact C.vertex_mem_set hj)
  -- the direction and the distance
  obtain ⟨σ, hσ, d, hd, hzd, hint⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ d : ℝ, 0 < d ∧
      z = rayPt v σ d ∧ ∀ t, 0 < t → t < d → rayPt v σ t ∈ C.dom := by
    rcases lt_or_gt_of_ne hzv1 with h | h
    · refine ⟨-1, Or.inr rfl, v.1 - z.1, by_linarith, point_ext by_simp by_simp_all,
        fun t ht1 ht2 => ?_⟩
      have := hbet (v.1 - t) by_grind
        by_simp_all
      simpa [rayPt, sub_eq_add_neg] using this
    · refine ⟨1, Or.inl rfl, z.1 - v.1, by_linarith, point_ext by_simp by_simp_all,
        fun t ht1 ht2 => ?_⟩
      have := hbet (v.1 + t) by_simp_all
        by_grind
      zugid
  have hfree : C.DirFree j σ := by
    have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 d := Ioo_mem_nhdsGT hd
    exact e1.mono by_grind
  have hle : d ≤ C.chordParam j σ := (C.hit_of_initial hvbox hσ hd hint).1
  have hzc : z ∈ C.chordSet j σ := by
    rw [C.chordSet_eq_image hj hσ hfree]
    grind
  exact ⟨_, hG ⟨j, σ, hj, hσ, hfree, rfl⟩, hzc⟩
end ChainObs

/-- **The chain half of `FullDegSpec`**: for a chain of a simple polygon with pairwise distinct
vertex heights, the full augmented map of the chain model has degree at most `4`. -/
theorem fullDegLe_chain {C : Chain} (hP : C.P.Simple) (hDH : DistinctHeights C.P) (Q : Polygon) :
    (chainModel C).FullDegLe Q 4 := by
  zuhgd
  zudho
  show {c | c ∈ C.chords ∪ F ∧ TouchesIn C.dom c U}.ncard ≤ 4
  zulra
  refine SegObs.deg_le_four (ChainObs.good hP hDH) ?_
    ztuxa ztuxk ztmdp
  zubyh
  · zucnz

  · zucyd

/-- **WP-B: `FullDegSpec`** — the full augmented maps of every chain model of the geometry
polygon and of its interior model have degree at most `4`. -/
theorem fullDegSpec : FullDegSpec := by
  intro P hP hε
  have hQ : ztxw := (shearInvariance _ P).1 hP
  have hDH : ztxpn := (goodShear_epsOf hε).2.1
  refine ⟨fun C hC => ?_, fullDeg_interior P hP hε⟩
  exact fullDegLe_chain by_simp_all by_simp_all _
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp)
namespace Brute
open SegObs

/-! ## The generic wall lemma (segment obstacles) -/

/-- The abscissa of the line of a segment changes linearly with the height. -/
theorem xAt_sub (s : Point × Point) (y y' : ℝ) :
    xAt s y - xAt s y' = (y - y') * ztejg := by
  unfold xAt; ring

/-- Two points of an obstacle segment: the slope relation. -/
theorem slope_of_mem {s : Point × Point} (hs : s.1.2 < s.2.2) {u v : Point} (hu : u ∈ seg s)
    (hv : v ∈ seg s) : v.1 - u.1 = ztgv * ztejg := by
  rw [((mem_seg_iff hs).1 hu).2.2, ((mem_seg_iff hs).1 hv).2.2, xAt_sub]

/-- The offset curve tends to the base point. -/
theorem tendsto_offset (u v : Point) (t : ℝ) :
    Tendsto (fun δ => Jordan.offset u v t δ) (𝓝[>] (0 : ℝ)) (𝓝 (lerp u v t)) := by
  have hc : Continuous fun δ : ℝ => Jordan.offset u v t δ := by
    unfold Jordan.offset
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h0 : Jordan.offset u v t 0 = lerp u v t := by_simp
  have := hc.tendsto 0
  zubuv
  zuhv
variable {R : ℝ} {S : Set (Point × Point)} {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

/-- **The wall lemma.**  Let `U` be inside the trapezoid of `q`.  If the left side of the segment
`u → v` (an obstacle segment `s`) faces the trapezoid at parameter `t`, and the point of parameter
`t` is at no vertex height, then the segment is the left wall traversed downward, or the right wall
traversed upward. -/
theorem wall_of_faces (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {s : Point × Point}
    (hs : s ∈ S) {u v : Point} (hseg : seg s = Chazelle.segment u v) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hnv : ∀ w, IsVert S w → w.2 ≠ (lerp u v t).2)
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Jordan.offset u v t δ ∈ tr sL sR y₁ y₂) :
    (v.2 < u.2 ∧ s = sL) ∨ (u.2 < v.2 ∧ s = sR) := by
  set z := lerp u v t with hzdef
  have hz : z ∈ seg s := by rw [hseg]; exact Geometry.lerp_mem_segment u v ht0 ht1
  zufwj
  have huS : u ∈ seg s := by rw [hseg]; exact Geometry.left_mem_segment _ _
  have hvS : v ∈ seg s := by rw [hseg]; exact Geometry.right_mem_segment _ _
  have hzc :=
    closure_tr_subset _ _ _ _ (mem_closure_of_tendsto (tendsto_offset u v t) hev)
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hzc
  have hy1 : y₁ < z.2 := by
    refine lt_of_le_of_ne hp1 fun e => ?_
    obtain ⟨w, hw, hwy, -⟩ := h.bot_vertex
    grind
  have hy2 : z.2 < y₂ := by
    refine lt_of_le_of_ne hp2 fun e => ?_
    obtain ⟨w, hw, hwy, -⟩ := h.top_vertex
    grind
  -- a point of the offset curve in the trapezoid
  obtain ⟨δ, hδin, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0 := hδ
  obtain ⟨-, -, hoL, hoR⟩ := hδin
  rw [Jordan.offset_fst, Jordan.offset_snd] at hoL hoR
  have hz1 : z.1 = u.1 + t * ztmu := rfl
  have hz2 : ztyzg := rfl
  have huv : u.2 ≠ v.2 := by
    zuchf
    have h1 := hseg ▸ lo_mem_seg s
    have h2 := hseg ▸ hi_mem_seg s
    obtain ⟨a, -, -, ha⟩ := h1
    obtain ⟨b, -, -, hb⟩ := h2
    simp_all
  rcases lt_or_eq_of_le hp3 with hlt | heqL
  · rcases lt_or_eq_of_le hp4 with hlt' | heqR
    · exact absurd (h.no_obs hS (seg_subset_obs hs hz) hy1 hy2 hlt hlt') id
    · -- on the right wall
      have hzR := (mem_seg_iff ztjxn).2
        ⟨h.botR.trans hy1.le, hy2.le.trans h.topR, heqR⟩
      have hsR : s = sR := by
        zuct
        exact hnv z (hS.cross s hs sR h.hR hne z hz hzR) rfl
      subst hsR
      refine Or.inr ⟨lt_of_le_of_ne ?_ huv, rfl⟩
      zucrj

      rw [← heqR, hz2] at hx
      zukzp
      have hd : 0 < u.2 - v.2 := by_linarith
      have e : xAt s ztwvf - z.1 =
          δ * ztgv * k ^ 2 := by_grind
      have h1 : δ * ztgv * k ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg by_nlinarith ztwet
      have h2 : δ * ztgv < 0 := by_nlinarith
      grind
  · -- on the left wall
    have hzL := (mem_seg_iff ztjxm).2
      ⟨h.botL.trans hy1.le, hy2.le.trans h.topL, heqL.symm⟩
    have hsL : s = sL := by
      zuct
      exact hnv z (hS.cross s hs sL h.hL hne z hz hzL) rfl
    subst hsL
    refine Or.inl ⟨lt_of_le_of_ne ?_ (Ne.symm huv), rfl⟩
    zucrj

    rw [heqL, hz2] at hx
    zukzp
    have hd : ztrzp := by_linarith
    have e : xAt s ztwvf - z.1 =
        δ * ztgv * k ^ 2 := by_grind
    have h1 := mul_nonneg (mul_pos hδ0 hd).le ztwet
    have h2 := mul_pos hδ0 hd
    grind

/-! ## Small facts about the tour of the double boundary -/
variable {u w : Point}
/-- `ord` does not depend on the order of two points at different heights. -/
theorem ord_comm (h : u.2 ≠ w.2) : ChainObs.ord u w = ChainObs.ord w u := by
  rcases lt_or_gt_of_ne h with h' | h' <;> simp [ChainObs.ord, h', not_lt.2 h'.le]

/-- `ord` of a downward pair. -/
theorem ord_down (h : w.2 < u.2) : ChainObs.ord u w = ztkgs := by
  simp [ChainObs.ord, not_lt.2 h.le]

/-- `ord` of an upward pair. -/
theorem ord_upward (h : u.2 < w.2) : ChainObs.ord u w = ztfuz := by
  simp [ChainObs.ord, h]

/-- The positions of the Euler tour of the path are determined by the pair of consecutive
vertices they visit. -/
theorem sideE_pair_inj {m j j' : ℕ} (hj : j < 2 * m) (hj' : j' < 2 * m)
    (h1 : Chain.sideE m j = Chain.sideE m j') (h2 : Chain.sideE m ztl = Chain.sideE m ztdhr) :
    j = j' := by
  unfold Chain.sideE at h1 h2; grind
variable {C : Chain}

/-- **Each walk edge of the double boundary is determined by its two ends** (the tour traverses
each chain edge once in each direction). -/
theorem tour_inj (β : Bool) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m)
    (h1 : C.sideIdx β i = C.sideIdx β i') (h2 : C.sideIdx β ztg = C.sideIdx β ztduy) :
    i = i' := by
  zubco
  rw [Chain.sideIdx_eq, Chain.sideIdx_eq] at h1
  rw [Chain.sideIdx_succ, Chain.sideIdx_succ] at h2
  have hj := sideE_pair_inj ztnnj ztnnj h1 h2
  have h3 := hj
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' _ h3) hi hi'

/-- The walk edge `i + 6` of the chain model starts at the tour vertex `i`. -/
theorem wa_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) :
    (C.sideWalk β).vtx ztcy = C.vertex ztjhk :=
  C.sideWalk_vtx_tour β by_omega

/-- The walk edge `i + 6` of the chain model ends at the tour vertex `i + 1`. -/
theorem wb_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) :
    (C.sideWalk β).vtx ztyt = C.vertex ztwtn := by
  rw [C.sideWalk_n, Nat.mod_eq_of_lt by_omega, show i + 6 + 1 = ztg + 6 by ring]
  exact C.sideWalk_vtx_tour β by_omega

/-- The ends of a walk edge of the double boundary span a chain edge. -/
theorem tour_edge (hDH : DistinctHeights C.P) (β : Bool) (i : ℕ) :
    (C.vertex ztjhk).2 ≠ (C.vertex ztwtn).2 ∧
      ∃ k < C.m, ChainObs.ord (C.vertex ztjhk) ztbalx =
        ChainObs.ord ztib ztwkj := by
  have hl := C.sideIdx_le β i
  have hl' := C.sideIdx_le β ztg
  have hs := C.sideTour_step β i
  have hne : C.sideIdx β i ≠ C.sideIdx β ztg := by_omega
  have hv := ChainObs.vertex_snd_ne hDH hl hl' hne
  zumks
  rcases hs with h | h
  · grind
  · refine ⟨C.sideIdx β ztg, by_omega, ?_⟩
    rw [ord_comm hv, h]

/-! ## The classification of the counted walk edges facing a region of the full map -/

/-- The set of keys inside an arc is open. -/
theorem isOpen_sideInArc (a b : ℝ) : IsOpen {x : ℝ | sideInArc a b x} := by
  zuul
  · simp only [sideInArc, hab, ite_true]
    exact (isOpen_lt continuous_const continuous_id).inter zttpn
  · simp only [sideInArc, hab, ite_false]
    exact (isOpen_lt continuous_const continuous_id).union zttpn

/-- A point of an open set of reals can be moved off a finite set. -/
theorem exists_avoid {O : Set ℝ} (hO : IsOpen O) {t : ℝ} (ht : t ∈ O) {B : Set ℝ}
    (hB : B.Finite) : ∃ t' ∈ O, t' ∉ B := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t ht
  have hinf : (Metric.ball t ε).Infinite := by
    rw [Real.ball_eq_Ioo]; exact Set.Ioo_infinite by_linarith
  obtain ⟨t', ht'1, ht'2⟩ := (hinf.sdiff hB).nonempty
  grind

/-- **The classification.**  Let `U` be the region of `z` in the full map, with trapezoid data
`sL, sR`.  A counted walk edge `i + 6` whose open key interval part `(p + t)`, `0 < t < 1`, lies in
an arc of `U` is the left wall traversed downward or the right wall traversed upward. -/
theorem arc_edge_class (hP : C.P.Simple) (hDH : DistinctHeights C.P) {z : Point}
    {sL sR : Point × Point} {y₁ y₂ : ℝ} (hT : Trap C.radius ztjhr z sL sR y₁ y₂)
    (hU : connectedComponentIn zthgq z ⊆ tr sL sR y₁ y₂) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords ztzvk a b)
    {i : ℕ} (hi : i < 2 * C.m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hin : sideInArc a b ((i + 6 : ℕ) + t)) :
    ((C.vertex ztwlt).2 < (C.vertex ztlx).2 ∧
        ChainObs.ord ztxuy
          ztbalw = sL) ∨
      ((C.vertex ztlx).2 < (C.vertex ztwlt).2 ∧
        ChainObs.ord ztxuy
          ztbalw = sR) := by
  zukae
  set u := C.vertex ztlx with hu
  set v := C.vertex _ with hv
  obtain ⟨huv, k, hk, hord⟩ := tour_edge hDH C.sideBeta i
  have hs : ChainObs.ord u v ∈ ChainObs.segs C := Or.inl by_grind
  have hseg : seg _ = Chazelle.segment u v := ChainObs.seg_ord u v
  -- the parameters of the edge inside the arc
  set O : Set ℝ := {t' | 0 < t' ∧ t' < 1 ∧ sideInArc a b ((i + 6 : ℕ) + t')} with hO
  have hOopen : IsOpen O := by
    refine (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt continuous_id continuous_const).inter ?_)
    exact (isOpen_sideInArc a b).preimage (continuous_const.add continuous_id)
  set B : Set ℝ := (fun w : Point => ztpj / ztgv) '' {w | IsVert ztjhr w}
    with hB
  have hBfin : B.Finite := (finite_verts hS).image _
  obtain ⟨t', ⟨ht'0, ht'1, ht'in⟩, ht'B⟩ := exists_avoid hOopen ⟨ht0, ht1, hin⟩ hBfin
  have hnv : ∀ w, IsVert ztjhr w → w.2 ≠ (lerp u v t').2 := by
    intro w hw e
    apply ht'B
    refine ⟨w, hw, ?_⟩
    simp only [Geometry.lerp_snd] at e
    grind
  -- the edge faces the region
  have hF := hab.2.2.2.2.2.2 _ t' (by
    show i + 6 < (C.sideWalk C.sideBeta).n; rw [C.sideWalk_n]; omega) ht'0 ht'1 ht'in
  have hF' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Jordan.offset u v t' δ ∈ tr sL sR y₁ y₂ := by
    have e1 : (chainModel C).wa _ = u := wa_tour C.sideBeta hi
    have e2 : (chainModel C).wb _ = v := wb_tour C.sideBeta hi
    unfold Model.Faces at hF
    zvmws at hF
    exact hF.mono by_grind
  rcases wall_of_faces hS hT hs hseg ht'0.le ht'1.le hnv hF' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · grind
  grind

/-! ## The weight bounds -/

/-- The trapezoid data of a region of the full map. -/
theorem region_trap (hP : C.P.Simple) (hDH : DistinctHeights C.P) {z : Point}
    (hz : z ∈ freeIn C.dom C.chords) :
    ∃ sL sR y₁ y₂, Trap C.radius ztjhr z sL sR y₁ y₂ ∧
      connectedComponentIn zthgq z ⊆ tr sL sR y₁ y₂ := by
  zukae
  have hfull : FullAt C.radius _ C.chords := ChainObs.fullAt subset_rfl
  zudho
  rw [← hdom] at hz ⊢
  obtain ⟨sL, sR, y₁, y₂, hT⟩ := exists_trap hS hfull hz.1 hz.2
  exact ⟨sL, sR, y₁, y₂, hT, hT.region_subset hS hfull hz⟩

/-- The counted walk edges met by an arc (the set whose size is `arcWt`). -/
def arcEdgeSet (C : Chain) (a b : ℝ) : Set ℕ :=
  {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p ∧
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}
theorem arcWt_eq (a b : ℝ) : (chainModel C).arcWt a b = (arcEdgeSet C a b).ncard := rfl

/-- A member of the edge set of an arc of a region of the full map, with its class. -/
theorem arcEdge_class (hP : C.P.Simple) (hDH : DistinctHeights C.P) {z : Point}
    {sL sR : Point × Point} {y₁ y₂ : ℝ} (hT : Trap C.radius ztjhr z sL sR y₁ y₂)
    (hU : connectedComponentIn zthgq z ⊆ tr sL sR y₁ y₂) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords ztzvk a b)
    {p : ℕ} (hp : p ∈ arcEdgeSet C a b) :
    ∃ i, i < 2 * C.m ∧ p = i + 6 ∧
      (((C.vertex ztwlt).2 < (C.vertex ztlx).2 ∧
        ChainObs.ord ztxuy
          ztbalw = sL) ∨
      ((C.vertex ztlx).2 < (C.vertex ztwlt).2 ∧
        ChainObs.ord ztxuy
          ztbalw = sR)) := by
  obtain ⟨-, ⟨hc1, hc2⟩, t, ht0, ht1, hin⟩ := hp
  refine ⟨p - 6, by_omega, by_omega, ?_⟩
  have e : ((p - 6 + 6 : ℕ) : ℝ) = (p : ℝ) := by_simp_all
  exact arc_edge_class hP hDH hT hU hab by_omega ht0 ht1 by_simp_all

/-- Two walk edges of the same class are equal. -/
theorem class_inj (hP : C.P.Simple) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m)
    (hord : ChainObs.ord ztxuy
        ztbalw =
      ChainObs.ord (C.vertex zthab)
        (C.vertex ztxuu))
    (hdir : (C.vertex ztlx).2 < (C.vertex ztwlt).2 ↔
      (C.vertex zthab).2 < (C.vertex ztxuu).2)
    (hne : (C.vertex ztlx).2 ≠ (C.vertex ztwlt).2)
    (hne' : (C.vertex zthab).2 ≠
      (C.vertex ztxuu).2) : i = i' := by
  have hl := C.sideIdx_le C.sideBeta
  have key : C.vertex ztlx = C.vertex zthab ∧
      C.vertex ztwlt = C.vertex ztxuu := by
    zuto
    · rw [ord_upward h, ord_upward (hdir.1 h)] at hord
      simp_all
    · have h' : (C.vertex _).2 <
          (C.vertex _).2 :=
        lt_of_le_of_ne by_grind ztvbj
      rw [ord_down h, ord_down h'] at hord
      simp_all
  exact tour_inj C.sideBeta hi hi' (C.sideVertex_inj hP ztmlf ztmlf key.1)
    (C.sideVertex_inj hP ztmlf ztmlf key.2)

/-- **The arcs of the full map meet at most two counted walk edges.** -/
theorem fullMap_arcWt_le_two (hP : C.P.Simple) (hDH : DistinctHeights C.P) {U : Set Point}
    (hU : U ∈ (chainModel C).regions C.chords) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords U a b) : (chainModel C).arcWt a b ≤ 2 := by
  zubld

  zumlx
  set A := arcEdgeSet C a b
  set Dn := {p ∈ A | ∀ i, p = i + 6 →
    (C.vertex ztwlt).2 < (C.vertex ztlx).2}
  set Up := {p ∈ A | ∀ i, p = i + 6 →
    (C.vertex ztlx).2 < (C.vertex ztwlt).2}
  have hfinA : A.Finite := (Set.finite_lt_nat (chainModel C).W.n).subset fun p hp => hp.1
  have hcover : A ⊆ Dn ∪ Up := by
    zuda
    obtain ⟨i, -, rfl, hcl⟩ := arcEdge_class hP hDH hT hsub hab hp
    grind
  have hDn : Dn.ncard ≤ 1 := by
    zuev

    rcases hcl with ⟨-, h1⟩ | ⟨h1, -⟩
    · rcases hcl' with ⟨-, h1'⟩ | ⟨h1', -⟩
      · rw [class_inj hP hi hi' ztvsj
          by_grind hne hne']
      grind
    grind
  have hUp : Up.ncard ≤ 1 := by
    zuev

    rcases hcl with ⟨h1, -⟩ | ⟨-, h1⟩
    · grind
    · rcases hcl' with ⟨h1', -⟩ | ⟨-, h1'⟩
      · grind
      · rw [class_inj hP hi hi' ztvsj by_simp_all hne hne']
  calc A.ncard ≤ (Dn ∪ Up).ncard := Set.ncard_le_ncard hcover ((hfinA.subset by_grind).union
        ztqqd)
    _ ≤ Dn.ncard + Up.ncard := Set.ncard_union_le _ _
    _ ≤ 2 := by_omega

/-- **For a chain of one edge, the arcs of the full map meet at most one counted walk edge.** -/
theorem fullMap_arcWt_le_one (hP : C.P.Simple) (hDH : DistinctHeights C.P) (hm : C.m = 1)
    {U : Set Point} (hU : U ∈ (chainModel C).regions C.chords) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords U a b) : (chainModel C).arcWt a b ≤ 1 := by
  zubld

  have hLR : ztsmc := by
    intro e; zvmwe at hT; exact lt_irrefl _ (hT.lt_q.trans hT.q_lt)
  zumlx
  have hfinA : (arcEdgeSet C a b).Finite :=
    (Set.finite_lt_nat (chainModel C).W.n).subset fun p hp => hp.1
  rw [Set.ncard_le_one_iff hfinA]
  intro p p' hp hp'
  obtain ⟨i, hi, rfl, hcl⟩ := arcEdge_class hP hDH hT hsub hab hp
  obtain ⟨i', hi', rfl, hcl'⟩ := arcEdge_class hP hDH hT hsub hab hp'
  obtain ⟨hne, k, hk, hord⟩ := tour_edge hDH C.sideBeta i
  obtain ⟨hne', k', hk', hord'⟩ := tour_edge hDH C.sideBeta i'
  zufvc
  have hk0' : k' = 0 := by_omega
  subst hk0 hk0'
  have hsame := hord.trans hord'.symm
  rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hcl' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · rw [class_inj hP hi hi' hsame
      by_grind hne hne']
  · simp_all
  · simp_all
  · rw [class_inj hP hi hi' hsame by_simp_all hne hne']

/-- **The full map of a chain model is `2`-semigranular** (distinct heights). -/
theorem fullMap_semigranular_two (hP : C.P.Simple) (hDH : DistinctHeights C.P) :
    (chainModel C).Semigranular C.chords 2 := by
  zucne
  zufls

  exact fullMap_arcWt_le_two hP hDH hU hab

/-- **The full map of a one-edge chain model is `1`-semigranular** (distinct heights). -/
theorem fullMap_semigranular_one (hP : C.P.Simple) (hDH : DistinctHeights C.P) (hm : C.m = 1) :
    (chainModel C).Semigranular C.chords 1 := by
  zucne
  zufls

  exact fullMap_arcWt_le_one hP hDH hm hU hab

/-- **The full map is `γ`-semigranular** for every `γ ≥ 2`, and for `γ ≥ 1` when the chain has
one edge: exactly the granularities of the corrected `BruteSpec` precondition. -/
theorem fullMap_semigranular (hP : C.P.Simple) (hDH : DistinctHeights C.P) {γ : ℕ}
    (hγ : C.m = 1 ∧ 1 ≤ γ ∨ 2 ≤ γ) : (chainModel C).Semigranular C.chords γ := by
  zucne
  rcases hγ with ⟨hm, hγ⟩ | hγ
  · exact (fullMap_semigranular_one hP hDH hm U hU).trans hγ
  · exact (fullMap_semigranular_two hP hDH U hU).trans hγ
end Brute
end
namespace BoxT
@[expose] public section
open Set
open Chazelle.Chain (sideInArc)

/-- Closing tactic for cyclic case analyses with nested disjunctions. -/
macro "cyc_close2" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor! <;> linarith) | (right; constructor! <;> linarith)
  | (left; linarith) | (right; linarith)
  | (left; left; linarith) | (left; right; linarith)
  | (right; left; linarith) | (right; right; linarith)))

/-! ## Cyclic facts -/

/-- The successor `f` of `a` among keys containing `w ∈ (a, b)` lies in `(a, b)`. -/
theorem cyc_succ_in {a b w f : ℝ} (hw : sideInArc a b w) (hf : ¬ sideInArc a f w) (hfa : f ≠ a) :
    sideInArc a b f := by
  rcases lt_or_gt_of_ne hfa with h | h <;> unfold sideInArc at * <;> split_ifs at * <;> cyc_close2

/-- The predecessor `g` of `b` among keys containing `w ∈ (a, b)` lies in `(a, b)`. -/
theorem cyc_pred_in {a b w g : ℝ} (hw : sideInArc a b w) (hg : ¬ sideInArc g b w) (hgb : g ≠ b) :
    sideInArc a b g := by
  rcases lt_or_gt_of_ne hgb with h | h <;> unfold sideInArc at * <;> split_ifs at * <;> cyc_close2

/-- **The two end pieces.**  If `(a, b)` contains points `f, g` of an interval `I = [lo, hi]`
avoiding `a` and `b`, a key of `(a, b)` outside `I` lies in `(a, f)` or in `(g, b)`. -/
theorem cyc_pieces {lo hi a b f g x : ℝ} (hf : lo ≤ f ∧ f ≤ hi) (hg : lo ≤ g ∧ g ≤ hi)
    (ha : a < lo ∨ hi < a) (hb : b < lo ∨ hi < b) (hfin : sideInArc a b f)
    (hgin : sideInArc a b g) (hx : x < lo ∨ hi < x) (hin : sideInArc a b x) :
    sideInArc a f x ∨ sideInArc g b x := by
  unfold sideInArc at *
  grind

/-! ## Weights -/
variable {M : Model}

/-- The counted walk edges met by the open key interval `(a, b)`. -/
def edgesIn (M : Model) (a b : ℝ) : Set ℕ :=
  {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}
variable (a b : ℝ)
theorem arcWt_eq' : M.arcWt a b = (edgesIn M a b).ncard := rfl
theorem edgesIn_finite : (edgesIn M a b).Finite :=
  (Set.finite_lt_nat M.W.n).subset fun _ hp => hp.1
theorem arcWt_le_n : M.arcWt a b ≤ M.W.n := by
  zujho
  calc (edgesIn M a b).ncard ≤ ((Finset.range M.W.n : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard (fun p hp => by simpa using hp.1) ztgdv
    _ = M.W.n := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- The weight of an arc is at most the weight of its region. -/
theorem arcWt_le_weight {F : Set ztf} {X : Set Point} {a b : ℝ} (h : M.IsArc F X a b) :
    M.arcWt a b ≤ M.weight F X :=
  le_csSup ⟨M.W.n, by rintro _ ⟨ab, -, rfl⟩; exact arcWt_le_n _ _⟩ ⟨(a, b), h, rfl⟩
theorem arcWt_le_of_sub {a b a' b' : ℝ}
    (h : ∀ p : ℕ, M.counted p → ∀ t : ℝ, 0 < t → t < 1 → sideInArc a b ztk →
      sideInArc a' b' ztk) : M.arcWt a b ≤ M.arcWt a' b' := by
  rw [arcWt_eq', arcWt_eq']
  refine Set.ncard_le_ncard ?_ (edgesIn_finite a' b')
  zutp
  exact ⟨hp, hc, t, ht0, ht1, h p hc t ht0 ht1 hx⟩
theorem arcWt_le_add {a b a₁ b₁ a₂ b₂ : ℝ}
    (h : ∀ p : ℕ, M.counted p → ∀ t : ℝ, 0 < t → t < 1 → sideInArc a b ztk →
      sideInArc a₁ b₁ ztk ∨ sideInArc a₂ b₂ ztk) :
    M.arcWt a b ≤ M.arcWt a₁ b₁ + M.arcWt a₂ b₂ := by
  rw [arcWt_eq', arcWt_eq', arcWt_eq']
  calc (edgesIn M a b).ncard ≤ (edgesIn M a₁ b₁ ∪ edgesIn M a₂ b₂).ncard := by
        refine Set.ncard_le_ncard ?_ ((edgesIn_finite _ _).union (edgesIn_finite _ _))
        zutp
        rcases h p hc t ht0 ht1 hx with h' | h'
        · exact Or.inl ztklo
        · exact Or.inr ztklo
    _ ≤ _ := Set.ncard_union_le _ _
theorem isCut_mono {F F' : Set ztf} (hsub : F' ⊆ F) {k : ℝ} (h : M.IsCut F' k) :
    M.IsCut F k := by
  obtain ⟨c, hc, rest⟩ := h
  exact ⟨c, hsub hc, rest⟩

/-- **Dropping a block of chords at most doubles the weights.** -/
theorem semigranular_drop (hM : WalkAx M) {F F' : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hsub : F' ⊆ F) {lo hi : ℝ}
    (hcut : ∀ k, M.IsCut F k → M.IsCut F' k ∨ (lo ≤ k ∧ k ≤ hi))
    (hcut' : ∀ k, M.IsCut F' k → k < lo ∨ hi < k)
    (hcnt : ∀ p : ℕ, M.counted p → hi < p) {γ : ℕ} (hγ : M.Semigranular F γ) :
    M.Semigranular F' ztjfj := by
  have key : ∀ X ∈ M.regions F, ∀ a b, M.IsArc F X a b → M.arcWt a b ≤ γ :=
    fun X hX a b h => (arcWt_le_weight h).trans (hγ X hX)
  zubap
  have hkey : ∀ (p : ℕ) (t : ℝ), M.counted p → 0 < t → hi < p + t := fun p t hc ht => by
    grind
  zulml
  zudws

  show M.arcWt a b ≤ 2 * γ
  rcases harc.2.2.2.2.1 with ⟨hca, hcb, hab⟩ | ⟨hF'e, rfl, rfl⟩
  · have hcaF := isCut_mono hsub hca
    have hcbF := isCut_mono hsub hcb
    by_cases hw : ∃ w, sideInArc a b w ∧ M.IsCut F w
    · obtain ⟨w, hwin, hwc⟩ := hw
      obtain ⟨f, hfK, hfa, hfgap⟩ := exists_succ_gap hK hcaF hcbF hab
      obtain ⟨g, hgK, hgb, hggap⟩ := exists_pred_gap hK hcbF hcaF ztmbt
      have hfin' : sideInArc a b f := cyc_succ_in hwin (hfgap w hwc) hfa
      have hgin' : sideInArc a b g := cyc_pred_in hwin (hggap w hwc) hgb
      have hfI : lo ≤ f ∧ f ≤ hi :=
        (hcut f hfK).resolve_left (harc.2.2.2.2.2.1 f hfin')
      have hgI : lo ≤ g ∧ g ≤ hi :=
        (hcut g hgK).resolve_left (harc.2.2.2.2.2.1 g hgin')
      obtain ⟨X₁, hX₁, harc₁⟩ := hM.arc_of_gap hF hfin hcaF hfK ztvbe
        (fun k hk hc => hfgap k hc hk)
      obtain ⟨X₂, hX₂, harc₂⟩ := hM.arc_of_gap hF hfin hgK hcbF hgb
        (fun k hk hc => hggap k hc hk)
      have ha := hcut' a hca
      have hb := hcut' b hcb
      calc M.arcWt a b ≤ M.arcWt a f + M.arcWt g b := arcWt_le_add fun p hc t ht0 _ hx =>
            cyc_pieces hfI hgI ha hb hfin' hgin' (Or.inr (hkey p t hc ht0)) hx
        _ ≤ γ + γ := Nat.add_le_add (key X₁ hX₁ _ _ harc₁) (key X₂ hX₂ _ _ harc₂)
        _ = 2 * γ := by_ring
    · zumiw
      obtain ⟨X, hX, harcX⟩ := hM.arc_of_gap hF hfin hcaF hcbF hab (fun k hk hc => hw k hk hc)
      grind
  · by_cases hFe : F = ∅
    · grind
    · obtain ⟨k₁, k₂, h₁, h₂, hk⟩ := hM.two_cuts hF (Set.nonempty_iff_ne_empty.2 hFe)
      have hnoF' : ∀ k, ¬ M.IsCut F' k := by
        rintro k ⟨c, hc, -⟩; simp_all
      obtain ⟨f, hfK, hfmin⟩ := Set.exists_min_image {x | M.IsCut F x} id hK ⟨k₁, h₁⟩
      obtain ⟨g, hgK, hgmax⟩ := Set.exists_max_image {x | M.IsCut F x} id hK ⟨k₁, h₁⟩
      simp only [id] at hfmin hgmax
      have hfg : f < g := by
        rcases lt_or_ge f g with h | h
        · zubh
        · exfalso; apply hk
          have e1 := hfmin k₁ h₁; have e2 := hgmax k₁ h₁
          have e3 := hfmin k₂ h₂; grind
      have hgI := (hcut g hgK).resolve_left (hnoF' g)
      obtain ⟨X, hX, harcX⟩ := hM.arc_of_gap hF hfin hgK hfK (ne_of_gt hfg) (by
        intro k hk hc
        unfold sideInArc at hk
        rw [ite_eq_right (not_lt.2 hfg.le)] at hk
        zucot
        · linarith [hgmax k hc]
        · linarith [hfmin k hc])
      have := (arcWt_le_of_sub (M := M) (a := 0) (b := 0) (a' := g) (b' := f)
        fun p hc t ht0 _ _ => by
          zufdq
          grind).trans (key X hX _ _ harcX)
      omega
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)

/-- **Dropping a bottom block of chords keeps the degree bound.** -/
theorem degLe_drop {D : Set Point} {F F' : Set ztf} (hsys : ChordSystem D F)
    (hfin : F.Finite) (hsub : F' ⊆ F) {R ys yp : ℝ} (hR : 0 < R) (hys : -R ≤ ys) (hlt : ys < yp)
    (hDbox : ∀ z ∈ D, |z.1| < R ∧ |z.2| < R)
    (hUD : ∀ z : Point, -R < z.1 → z.1 < R → -R < z.2 → z.2 < yp → z ∈ D)
    (hF' : ∀ c ∈ F', ∀ z ∈ c, yp ≤ z.2)
    (hW : ∀ c ∈ F, c ∉ F' → ∀ z ∈ c, z.2 ≤ ys)
    {d : ℕ} (hd : ∀ U ∈ regionsIn D F, {c | c ∈ F ∧ TouchesIn D c U}.ncard ≤ d) :
    ∀ W ∈ regionsIn D F', {c | c ∈ F' ∧ TouchesIn D c W}.ncard ≤ d := by
  set U : Set Point := Ioo (-R) R ×ˢ Ioo (-R) yp with hUdef
  set Up : Set Point := Ioo (-R) R ×ˢ Ioo ys yp with hUpdef
  have hUo : ztule := isOpen_Ioo.prod isOpen_Ioo
  have hUpc : IsPreconnected Up := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hUD' : U ⊆ D := fun z hz => hUD z hz.1.1 hz.1.2 hz.2.1 hz.2.2
  have hUpF : Up ⊆ freeIn D F := by
    zugh
    refine ⟨hUD z hz.1.1 hz.1.2 by_grind hz.2.2, ?_⟩
    grind
  set p0 : Point := (0, (ys + yp) / 2)
  have hp0 : p0 ∈ Up := ⟨ztufy,
    ⟨by_grind, by_grind⟩⟩
  set X := connectedComponentIn ztfrg p0 with hXdef
  have hXr : X ∈ regionsIn D F := ⟨p0, hUpF hp0, rfl⟩
  have hXo : IsOpen X := hsys.regionsIn_open subset_rfl hXr
  have hUpX : Up ⊆ X := hUpc.subset_connectedComponentIn hp0 hUpF
  -- points of the closure of `U` above `ys` are in the closure of `X`
  have hclU : ∀ z, z ∈ closure U → ys < z.2 → z ∈ closure X := by
    zumhu
    have hO : IsOpen {w : Point | ys < w.2} := isOpen_lt continuous_const continuous_snd
    have := hO.inter_closure ⟨hzy, hz⟩
    refine closure_mono ?_ this
    rintro w ⟨hw1, hw2⟩
    grind
  have hclU' : closure U ⊆ {w : Point | w.2 ≤ yp} :=
    closure_minimal (fun w hw => hw.2.2.le) ztjyx
  -- a free point in the closure of `X` is in `X`
  have hfreeX : ∀ w, w ∈ freeIn D F → w ∈ closure X → w ∈ X := by
    intro w hw hwc
    set Y := connectedComponentIn ztfrg w
    have hYr : Y ∈ regionsIn D F := ztgps
    have hYo : IsOpen Y := hsys.regionsIn_open subset_rfl hYr
    have hwY : w ∈ Y := mem_connectedComponentIn hw
    obtain ⟨v, hvY, hvX⟩ := mem_closure_iff.1 hwc Y hYo hwY
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hYr hXr with h | h
    · grind
    · exact absurd (h.le_bot ⟨hvY, hvX⟩) zthxd
  intro W hWr
  have hWF' : W ⊆ freeIn D F' := Chazelle.Chain.regionsIn_subset hWr
  have hfin' : {c | c ∈ F ∧ TouchesIn D c X}.Finite := hfin.subset fun c hc => hc.1
  by_cases hWU : (W ∩ U).Nonempty
  · -- `W ⊆ U ∪ X`
    have hsubW : W ⊆ U ∪ X := by
      refine (Chazelle.Chain.regionsIn_isPreconnected hWr).subset_of_closure_inter_subset
        (hUo.union hXo) (by obtain ⟨w, h1, h2⟩ := hWU; exact ⟨w, h1, Or.inl h2⟩) ?_
      rintro w ⟨hwc, hwW⟩
      have hwD : w ∈ D := (hWF' hwW).1
      obtain ⟨hb1, hb2⟩ := hDbox w hwD
      zujhk
      by_cases hwF : w ∈ ⋃₀ F
      · obtain ⟨c, hc, hwc'⟩ := hwF
        have hc' : c ∉ F' := fun h => (hWF' hwW).2 ⟨c, h, hwc'⟩
        have := hW c hc hc' w hwc'
        exact Or.inl ⟨ztooa, ztuhe⟩
      · have hwfree : w ∈ freeIn D F := ⟨hwD, hwF⟩
        rw [closure_union] at hwc
        rcases hwc with hwc | hwc
        · by_cases hwy : w.2 < yp
          · exact Or.inl ⟨ztooa, ⟨hb2.1, hwy⟩⟩
          grind
        grind
    refine le_trans (Set.ncard_le_ncard ?_ hfin') (hd X hXr)
    rintro c ⟨hc, z, ⟨hzc, hzD⟩, hzW⟩
    refine ⟨hsub hc, z, ztklu, ?_⟩
    have hzy := hF' c hc z hzc
    have hz := closure_mono hsubW hzW
    rw [closure_union] at hz
    grind
  · -- `W` misses the dropped chords: it is a region of `F`
    have hWF : W ⊆ freeIn D F := by
      zucdk
      refine ⟨(hWF' hw).1, ?_⟩
      zuifk
      have hc' : c ∉ F' := fun h => (hWF' hw).2 ⟨c, h, hwc⟩
      have hwy := hW c hc hc' w hwc
      obtain ⟨hb1, hb2⟩ := hDbox w (hWF' hw).1
      zujhk
      exact hWU ⟨w, hw, ztooa, ztuhe⟩
    obtain ⟨w0, hw0⟩ := Chazelle.Chain.regionsIn_nonempty hWr
    have hWeq : W = connectedComponentIn ztfrg w0 := by
      zugjb
      · exact (Chazelle.Chain.regionsIn_isPreconnected hWr).subset_connectedComponentIn hw0 hWF
      · rw [Chazelle.Chain.regionsIn_eq_component hWr hw0]
        exact connectedComponentIn_mono w0 (Chazelle.Chain.freeIn_anti D hsub)
    have hWr' : W ∈ regionsIn D F := ⟨w0, hWF hw0, hWeq⟩
    refine le_trans (Set.ncard_le_ncard ?_ (hfin.subset fun c hc => hc.1)) (hd W hWr')
    rintro c ⟨hc, ht⟩
    grind
end
end BoxT
namespace ArcT
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sideInArc)
open BoxT (edgesIn arcWt_eq' edgesIn_finite arcWt_le_weight)

/-- Wrap an unwrapped key of `[0, 2n)` into `[0, n)`. -/
noncomputable def wrapK (n x : ℝ) : ℝ := if x < n then x else x - n

/-- The key is not a vertex key. -/
def NonVtx (x : ℝ) : Prop := ∀ k : ℕ, x ≠ k

/-- **A key correspondence** between the unwrapped key range `[lo, hi]` of `M₂` and a key range of
`M₁`. -/
structure ArcCorr (M₁ M₂ : Model) (F₁ F₂ : Set ztf) (U V : Set Point) (lo hi : ℝ)
    (κ : ℝ → ℝ) : Prop where
  lo_nonneg : 0 ≤ lo
  lo_lt : lo < M₂.W.n
  hi_le : hi ≤ lo + M₂.W.n
  mono : StrictMonoOn κ (Icc lo hi)
  range : ∀ x ∈ Icc lo hi, 0 ≤ κ x ∧ κ x < M₁.W.n
  onto : ∀ y, κ lo ≤ y → y ≤ κ hi → ∃ x ∈ Icc lo hi, κ x = y
  vtx : ∀ x ∈ Ioo lo hi, NonVtx x → NonVtx ztqzm
  vtx' : ∀ x ∈ Ioo lo hi, ¬ NonVtx x → ¬ NonVtx ztqzm
  cut : ∀ x ∈ Ioo lo hi, M₁.IsCut F₁ ztqzm → M₂.IsCut F₂ ztudj
  faces : ∀ x ∈ Ioo lo hi, NonVtx x →
    M₂.Faces ⌊wrapK M₂.W.n x⌋₊ (wrapK M₂.W.n x - ⌊wrapK M₂.W.n x⌋₊) V →
      M₁.Faces ⌊κ x⌋₊ (κ x - ⌊κ x⌋₊) U
  counted : ∀ x ∈ Ioo lo hi, NonVtx x → M₁.counted ⌊κ x⌋₊

/-! ## Floors -/
theorem floor_lt_of_nonVtx {x : ℝ} (h0 : 0 ≤ x) (hx : NonVtx x) :
    (⌊x⌋₊ : ℝ) < x ∧ x < ⌊x⌋₊ + 1 := by
  refine ⟨lt_of_le_of_ne (Nat.floor_le h0) (fun e => hx _ e.symm), Nat.lt_floor_add_one x⟩
variable {n x : ℝ}
theorem wrapK_nonneg (hx : 0 ≤ x) (_hx' : x < 2 * n) : 0 ≤ wrapK n x := by
  zujrg
theorem wrapK_lt (_hn : 0 < n) (_hx : 0 ≤ x) (hx' : x < 2 * n) : wrapK n x < n := by
  zujrg
theorem nonVtx_wrapK {n : ℕ} {x : ℝ} (hx : NonVtx x) : NonVtx ztojx := by
  intro k e
  unfold wrapK at e
  split_ifs at e
  · tauto
  · exact hx (k + n) by_grind
theorem nonVtx_of_wrapK {n : ℕ} {x : ℝ} (hx : NonVtx ztojx) : NonVtx x := by
  intro k e
  unfold wrapK at hx
  split_ifs at hx with h
  · tauto
  · have hk : n ≤ k := by
      simp_all
    exact hx (k - n) by_simp_all
namespace ArcCorr
variable {M₁ M₂ : Model} {F₁ F₂ : Set (Set Point)} {U V : Set Point} {lo hi : ℝ} {κ : ℝ → ℝ}
variable (h : ArcCorr M₁ M₂ F₁ F₂ U V lo hi κ)
include h

/-- Keys in one walk edge of `M₁` come from keys in one walk edge of `M₂`. -/
theorem floor_eq {x x' : ℝ} (hx : x ∈ Ioo lo hi) (hx' : x' ∈ Ioo lo hi) (hv : NonVtx x)
    (hv' : NonVtx x') (he : ⌊κ x⌋₊ = ⌊κ x'⌋₊) : ⌊x⌋₊ = ⌊x'⌋₊ := by
  have h0 : ∀ z ∈ Ioo lo hi, 0 ≤ z := fun z hz => le_trans h.lo_nonneg hz.1.le
  -- the general statement for `x ≤ x'`
  have key : ∀ z z', z ∈ Ioo lo hi → z' ∈ Ioo lo hi → NonVtx z → NonVtx z' → z ≤ z' →
      ⌊κ z⌋₊ = ⌊κ z'⌋₊ → ⌊z⌋₊ = ⌊z'⌋₊ := by
    intro z z' hz hz' hvz hvz' hle hf
    zuct
    have hlt := lt_of_le_of_ne (Nat.floor_le_floor hle) hne
    set k : ℕ := ⌊z⌋₊ + 1
    have hz1 := floor_lt_of_nonVtx by_simp_all hvz
    have hz2 := floor_lt_of_nonVtx by_simp_all hvz'
    have hk1 : z < k := by_grind
    have hk2 : (k : ℝ) < z' := by
      have : (k : ℝ) ≤ ⌊z'⌋₊ := by exact_mod_cast hlt
      grind
    have hkI : (k : ℝ) ∈ Ioo lo hi := by_grind
    have hkv : ¬ NonVtx (k : ℝ) := fun hn => hn k rfl
    have hkk := h.vtx' _ hkI hkv
    simp only [NonVtx, not_forall, not_not] at hkk
    obtain ⟨K, hK⟩ := hkk
    have hIcc : ∀ w ∈ Ioo lo hi, w ∈ Icc lo hi := by_grind
    have m1 := h.mono by_simp_all by_simp_all hk1
    have m2 := h.mono by_simp_all by_simp_all hk2
    have hy0 := (h.range z by_simp_all).1
    have hy0' : 0 ≤ κ z' := by_grind
    have f1 : (⌊κ z⌋₊ : ℝ) + 1 ≤ K := by
      have : ⌊κ z⌋₊ < K := by
        rw [Nat.floor_lt hy0]; simp_all
      zufc
    have f2 : (K : ℝ) ≤ ⌊κ z'⌋₊ := by
      have : K ≤ ⌊κ z'⌋₊ := Nat.le_floor by_grind
      zufc
    grind
  grind

/-- A cut-free interval inside the range has a cut-free image. -/
theorem image_free {a b : ℝ} (hlo : lo ≤ a) (hab : a < b) (hhi : b ≤ hi)
    (hfree : ∀ x ∈ Ioo a b, ¬ M₂.IsCut F₂ ztudj) :
    ∀ y ∈ Ioo (κ a) (κ b), ¬ M₁.IsCut F₁ y := by
  intro y hy hc
  have hIa : a ∈ Icc lo hi := by_grind
  have hIb : b ∈ Icc lo hi := by_grind
  have hlo' := h.mono.monotoneOn by_grind hIa hlo
  have hhi' := h.mono.monotoneOn hIb by_grind hhi
  obtain ⟨x, hx, rfl⟩ := h.onto y by_grind by_grind
  have hxa : a < x := by
    zuisb
    have := h.mono.monotoneOn hx hIa hxa
    grind
  have hxb : x < b := by
    zuisc
    have := h.mono.monotoneOn hIb hx hxb
    grind
  exact hfree x by_simp_all (h.cut x by_grind hc)
end ArcCorr

/-! ## A linear cut-free interval lies in the arc around one of its points -/
theorem linear_sub_arc {l r y₀ c d : ℝ} (hy₀ : sideInArc l r y₀) (hc : c < y₀) (hd : y₀ < d)
    (hl : ¬ (c < l ∧ l < d)) (hr : ¬ (c < r ∧ r < d)) :
    ∀ y, c < y → y < d → sideInArc l r y := by
  intro y hcy hyd
  unfold sideInArc at *
  grind

/-! ## The arc transfer -/
variable {M₁ M₂ : Model} {F₁ F₂ : Set (Set Point)} {U V : Set Point} {lo hi : ℝ} {κ : ℝ → ℝ}

/-- **Arc transfer**: a cut-free interval `(a, b)` of `M₂` inside the range of a correspondence,
facing `V`, weighs at most the region `U` of `F₁`. -/
theorem arcWt_le (hM₁ : WalkAx M₁) (hF₁ : F₁ ⊆ M₁.Adm) (hfin₁ : F₁.Finite)
    (hU : U ∈ M₁.regions F₁) (h : ArcCorr M₁ M₂ F₁ F₂ U V lo hi κ)
    {a b aa bb : ℝ} (hlo : lo ≤ aa) (hab : aa < bb) (hhi : bb ≤ hi)
    (hin : ∀ x : ℝ, 0 ≤ x → x < M₂.W.n → sideInArc a b x →
      ∃ xx ∈ Ioo aa bb, wrapK M₂.W.n xx = x)
    (hout : ∀ xx ∈ Ioo aa bb, sideInArc a b (wrapK M₂.W.n xx))
    (hfree : ∀ x : ℝ, sideInArc a b x → ¬ M₂.IsCut F₂ x)
    (hfac : ∀ (p : ℕ) (t : ℝ), p < M₂.W.n → 0 < t → t < 1 → sideInArc a b ztk →
      M₂.Faces p t V) :
    M₂.arcWt a b ≤ M₁.weight F₁ U := by
  set n₂ := M₂.W.n
  have hn₂ := lt_of_le_of_lt h.lo_nonneg h.lo_lt
  have hIcc : ∀ w, w ∈ Ioo aa bb → w ∈ Icc lo hi := by_grind
  have hIoo : ∀ w, w ∈ Ioo aa bb → w ∈ Ioo lo hi := by_grind
  have hx0 : ∀ w, w ∈ Ioo aa bb → 0 ≤ w := fun w hw => le_trans h.lo_nonneg by_grind
  have hx2 : ∀ w, w ∈ Ioo aa bb → w < 2 * n₂ := fun w hw => by
    have := (hIcc w hw).2; have := h.hi_le; have := h.lo_lt; linarith
  -- the image interval is cut-free
  have hfreeI := h.image_free hlo hab hhi by_grind
  -- the witness function
  classical
  set g : ℕ → ℝ := fun p =>
    if hp : ∃ xx ∈ Ioo aa bb, NonVtx xx ∧ ⌊wrapK n₂ xx⌋₊ = p then hp.choose else 0 with hg
  have hgspec : ∀ p ∈ edgesIn M₂ a b,
      g p ∈ Ioo aa bb ∧ NonVtx ztjwv ∧ ⌊wrapK n₂ ztjwv⌋₊ = p := by
    zuecg
    have hxn : ztmqv := by_positivity
    have hxlt : (p : ℝ) + t < n₂ := by
      have : (p : ℝ) + 1 ≤ n₂ := by exact_mod_cast hp
      linarith
    obtain ⟨xx, hxx, hw⟩ := hin _ hxn hxlt hx
    have hvw : NonVtx (wrapK n₂ xx) := by
      zunft; intro k e
      have hk1 : ztixl := by_linarith
      have hk2 : (k : ℝ) < ((p + 1 : ℕ) : ℝ) := by_grind
      have := Nat.cast_lt.1 hk1; have := Nat.cast_lt.1 hk2; omega
    have hex : ∃ xx ∈ Ioo aa bb, NonVtx xx ∧ ⌊wrapK n₂ xx⌋₊ = p := by
      refine ⟨xx, hxx, nonVtx_of_wrapK hvw, ?_⟩
      rw [hw, Nat.floor_eq_iff hxn]
      grind
    grind
  by_cases hE : (edgesIn M₂ a b).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hE
    rw [arcWt_eq', hE, Set.ncard_empty]; omega
  obtain ⟨p₀, hp₀⟩ := hE
  obtain ⟨hx₀, hv₀, -⟩ := hgspec p₀ hp₀
  set y₀ := κ (g p₀)
  have hy₀r := h.range _ (hIcc _ hx₀)
  have hy₀v := h.vtx _ by_grind hv₀
  have hy₀c : ¬ M₁.IsCut F₁ y₀ := fun hc =>
    hfree _ by_grind (h.cut _ by_grind hc)
  have hIa : aa ∈ Icc lo hi := by_grind
  have hIb : bb ∈ Icc lo hi := by_grind
  have hya : κ aa < y₀ := h.mono hIa by_grind hx₀.1
  have hyb : y₀ < κ bb := h.mono by_grind hIb hx₀.2
  -- the arc of `U` around `y₀`
  obtain ⟨l, r, harc, hlr⟩ : ∃ l r, M₁.IsArc F₁ U l r ∧ ∀ y ∈ Ioo (κ aa) (κ bb), sideInArc l r y := by
    have hfac₀ : ∀ y ∈ Ioo (κ aa) (κ bb), NonVtx y → M₁.Faces ⌊y⌋₊ (y - ⌊y⌋₊) U := by
      intro y hy hvy
      obtain ⟨x, hx, rfl⟩ := h.onto y
        (le_trans (h.mono.monotoneOn ⟨le_rfl, le_trans hlo hIa.2⟩ hIa hlo) hy.1.le)
        (le_trans hy.2.le (h.mono.monotoneOn hIb ⟨le_trans hIb.1 hIb.2, le_rfl⟩ hhi))
      have hxa : aa < x := by
        zuisb
        linarith [h.mono.monotoneOn hx hIa hxa, hy.1]
      have hxb : x < bb := by
        zuisc
        linarith [h.mono.monotoneOn hIb hx hxb, hy.2]
      have hvx : NonVtx x := by
        intro k e; apply h.vtx' x by_grind (fun hn => hn k e) hvy
      refine h.faces x by_grind hvx ?_
      have hw0 := wrapK_nonneg by_grind zttou
      have hwl := wrapK_lt hn₂ by_grind zttou
      have hwv := nonVtx_wrapK (n := n₂) hvx
      have hfl := floor_lt_of_nonVtx hw0 hwv
      apply hfac
      · have : (⌊wrapK n₂ x⌋₊ : ℝ) < n₂ := by_grind
        zufc
      · grind
      · grind
      · zuoui; tauto
    by_cases hF : F₁.Nonempty
    · have hp := (Nat.floor_le hy₀r.1)
      have hy₀p := floor_lt_of_nonVtx hy₀r.1 hy₀v
      obtain ⟨X, hX, l, r, harcX, hin₀⟩ := hM₁.arc_around hF₁ hfin₁ hF hy₀c
      -- `X = U`: both are faced just at `y₀`
      have hXU : ztsde := by
        have hpn : ⌊y₀⌋₊ < M₁.W.n := by
          have : (⌊y₀⌋₊ : ℝ) < M₁.W.n := by_grind
          zufc
        have ht0 : 0 < y₀ - ⌊y₀⌋₊ := by_grind
        have ht1 : y₀ - ⌊y₀⌋₊ < 1 := by_grind
        have hfX := harcX.2.2.2.2.2.2 _ _ hpn ht0 ht1 by_grind
        exact WalkAx.faces_unique hX hU hfX (hfac₀ y₀ by_grind hy₀v)
      zulsx
      refine ⟨l, r, harcX, ?_⟩
      have hl := fun hl =>
        hfreeI l hl (by
          rcases harcX.2.2.2.2.1 with ⟨hl', -⟩ | ⟨hF', -⟩
          · omega
          · exact absurd hF' hF.ne_empty)
      have hr := fun hr =>
        hfreeI r hr (by
          rcases harcX.2.2.2.2.1 with ⟨-, hr', -⟩ | ⟨hF', -⟩
          · omega
          · exact absurd hF' hF.ne_empty)
      zusy
      exact linear_sub_arc hin₀ hya hyb hl hr y hy.1 hy.2
    · -- the empty family: the pinned arc
      zukpw
      have hn1 : (0 : ℝ) < M₁.W.n := by_grind
      refine ⟨0, 0, ⟨le_rfl, hn1, le_rfl, hn1, by_grind,
        fun x _ hc => by obtain ⟨c, hc, -⟩ := hc; grind, ?_⟩, ?_⟩
      · zujbi
        obtain ⟨X, hX, hfX⟩ := hM₁.exists_faces_of_not_cut hF₁ hfin₁ hp ztcoy
          (fun hc => by obtain ⟨c, hc, -⟩ := hc; grind)
        -- a single region
        have hXU : ztsde := by
          zugqw
          zubpm
          have hfr : Chazelle.Chain.freeIn M₁.D F₁ = M₁.D := by
            zvoij; unfold Chazelle.Chain.freeIn; simp
          have hpre := hM₁.preconn
          rw [hfr] at hx hu ⊢
          rw [connectedComponentIn_eq (hpre.subset_connectedComponentIn hx subset_rfl
            by_omega |> fun h' => by exact h')]
        grind
      · zusy
        zufdq
        zuoqz
        left
        linarith [hy.1, (h.range aa hIa).1]
  -- the injection of edges
  zujho
  refine le_trans ?_ (arcWt_le_weight harc)
  zujho
  refine Set.ncard_le_ncard_of_injOn (fun p => ⌊κ ztjwv⌋₊) ?_ ?_ (edgesIn_finite l r)
  · zuda
    obtain ⟨hx, hv, -⟩ := hgspec p hp
    have hr := h.range _ (hIcc _ hx)
    have hyv := h.vtx _ by_grind hv
    have hfl := floor_lt_of_nonVtx hr.1 hyv
    refine ⟨?_, h.counted _ by_grind hv, κ ztjwv - ⌊κ ztjwv⌋₊, by_grind,
      by grind, ?_⟩
    · have : (⌊κ _⌋₊ : ℝ) < M₁.W.n := lt_of_le_of_lt (Nat.floor_le hr.1) hr.2
      zufc
    · zuoui
      exact hlr _ ⟨h.mono hIa by_grind hx.1, h.mono by_grind hIb hx.2⟩
  · intro p hp q hq e
    obtain ⟨hx, hv, hpe⟩ := hgspec p hp
    obtain ⟨hy, hw, hqe⟩ := hgspec q hq
    have hfl := h.floor_eq by_grind by_grind hv hw e
    rw [← hpe, ← hqe]
    -- equal floors give equal wrapped floors
    have hx0' := hx0 _ hx; have hy0' := hx0 _ hy
    zuiqh
    by_cases h1 : g p < n₂ <;> by_cases h2 : g q < n₂
    · grind
    · exfalso
      have a1 : ⌊g p⌋₊ < n₂ := by
        have := Nat.floor_lt hx0' |>.2 h1; omega
      have a2 : n₂ ≤ ⌊g q⌋₊ := Nat.le_floor by_grind
      omega
    · exfalso
      have a1 : ⌊g q⌋₊ < n₂ := by
        have := Nat.floor_lt hy0' |>.2 h2; omega
      have a2 : n₂ ≤ ⌊g p⌋₊ := Nat.le_floor by_grind
      omega
    · simp only [h1, h2, ↓reduceIte]
      push Not at h1 h2
      have e1 : ⌊g p - n₂⌋₊ = ⌊g p⌋₊ - n₂ := by
        simp
      have e2 : ⌊g q - n₂⌋₊ = ⌊g q⌋₊ - n₂ := by
        simp
      omega
variable (β : ℕ → ℝ) (N : ℕ)

/-- The index of the piece containing `x`: the number of inner breakpoints `≤ x`. -/
noncomputable def seg (x : ℝ) : ℕ := ((Finset.Ico 1 N).filter fun j => β j ≤ x).card

/-- **The piecewise linear key map.** -/
noncomputable def brk (c : ℝ) (x : ℝ) : ℝ :=
  c + seg β N x + ztyfw / ztxza
variable {β N}

/-- Increasing breakpoints. -/
def BrkInc (β : ℕ → ℝ) (N : ℕ) : Prop := ∀ j, j < N → β j < β ztl
theorem BrkInc.lt (h : BrkInc β N) {i j : ℕ} (hij : i < j) (hj : j ≤ N) : β i < β j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' by_omega) (h j by_omega)
    · zvmxl; tauto
theorem BrkInc.le (h : BrkInc β N) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : β i ≤ β j := by
  rcases hij.lt_or_eq with h' | h'
  · exact (h.lt h' hj).le
  simp_all

/-- **The piece of a key.** -/
theorem seg_spec (h : BrkInc β N) (hN : 1 ≤ N) {x : ℝ} (hx0 : β 0 ≤ x) (hxN : x < β N) :
    seg β N x < N ∧ β ztcdv ≤ x ∧ x < β ztdwd := by
  set S := (Finset.Ico 1 N).filter fun j => β j ≤ x with hS
  -- `S` is an initial segment `[1, k]`
  have hdown : ∀ j ∈ S, ∀ i, 1 ≤ i → i ≤ j → i ∈ S := by
    intro j hj i hi hij
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at hj ⊢
    exact ⟨⟨hi, by_omega⟩, le_trans (h.le hij by_omega) hj.2⟩
  have hcard : ∀ k, k ≤ N - 1 → (∀ i, 1 ≤ i → i ≤ k → β i ≤ x) → k ≤ S.card := by
    intro k hk hall
    have : Finset.Icc 1 k ⊆ S := by
      grind
    have := Finset.card_le_card this
    zujpk
  have hsub : S ⊆ Finset.Icc 1 S.card := by
    zun
    rw [Finset.mem_Icc]
    refine ⟨(Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1, ?_⟩
    have : Finset.Icc 1 j ⊆ S := fun i hi => by
      grind
    have := Finset.card_le_card this
    zujpk
  set k := S.card with hk
  have hkN : k ≤ N - 1 := by
    have : S ⊆ Finset.Ico 1 N := Finset.filter_subset _ _
    have := Finset.card_le_card this
    zulrm
  have hmem : ∀ j, j ∈ S ↔ 1 ≤ j ∧ j ≤ k := by
    zujbf
    constructor
    · grind
    · zubf
      zuhbw
      -- then `S ⊆ [1, j - 1]`, too small
      have : S ⊆ Finset.Icc 1 zthv := by
        grind
      have := Finset.card_le_card this
      zulrm
  show k < N ∧ β k ≤ x ∧ x < β zts
  zujfy
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · grind
    grind
  · by_cases hk1 : k + 1 = N
    · grind
    · zube

      have : k + 1 ∈ S := by
        grind
      grind
theorem seg_top (h : BrkInc β N) (_hN : 1 ≤ N) : seg β N ztmpm = N - 1 := by
  zuhav
  have : (Finset.Ico 1 N).filter (fun j => β j ≤ β N) = Finset.Ico 1 N := by
    apply Finset.filter_true_of_mem
    zun
    exact h.le (Finset.mem_Ico.1 hj).2.le le_rfl
  zukyy
variable {c : ℝ}

/-- The map on a piece. -/
theorem brk_piece (h : BrkInc β N) (hN : 1 ≤ N) {x : ℝ} (hx0 : β 0 ≤ x) (hxN : x < β N) :
    c + seg β N x ≤ brk β N c x ∧ brk β N c x < c + seg β N x + 1 := by
  zubrp
  have hpos : 0 < β ztdwd - β ztcdv := by_linarith
  zumrx
  constructor
  · have : 0 ≤ ztyfw / ztxza :=
      div_nonneg by_linarith hpos.le
    linarith
  · have : ztyfw / ztxza < 1 := by
      rw [div_lt_one hpos]; linarith
    linarith
theorem brk_top (h : BrkInc β N) (hN : 1 ≤ N) : brk β N c ztmpm = c + N := by
  zumrx
  rw [seg_top h hN, Nat.sub_add_cancel hN]
  have hpos : 0 < β N - β ztbpm := by
    have := h ztbpm by_omega; simp_all
  rw [div_self hpos.ne']
  have : ((N - 1 : ℕ) : ℝ) = N - 1 := by_simp_all
  grind
theorem brk_bot (h : BrkInc β N) (_hN : 1 ≤ N) : brk β N c ztmpl = c := by
  have hs : seg β N ztmpl = 0 := by
    zuhav
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    zun
    exact not_le.2 (h.lt (Finset.mem_Ico.1 hj).1 (Finset.mem_Ico.1 hj).2.le)
  zumry

/-- **The key map is strictly increasing.** -/
theorem brk_strictMonoOn (h : BrkInc β N) (hN : 1 ≤ N) :
    StrictMonoOn (brk β N c) (Icc ztmpl ztmpm) := by
  zuvc
  have hxN : ztuva := lt_of_lt_of_le hxy hy.2
  have px := brk_piece (c := c) h hN hx.1 hxN
  rcases hy.2.lt_or_eq with hyN | hyN
  · have py := brk_piece (c := c) h hN hy.1 hyN
    obtain ⟨-, hx1, hx2⟩ := seg_spec h hN hx.1 hxN
    obtain ⟨-, hy1, hy2⟩ := seg_spec h hN hy.1 hyN
    rcases lt_trichotomy ztcdv ztega with hs | hs | hs
    · have : ((seg β N x : ℕ) : ℝ) + 1 ≤ seg β N y := by exact_mod_cast hs
      grind
    · zumrx
      zvmyz at hx1 hx2 ⊢
      have hpos : 0 < β ztimb - β ztega := by_linarith
      have : (x - β ztega) / ztzhw <
          (y - β ztega) / ztzhw :=
        div_lt_div_of_pos_right by_linarith hpos
      linarith
    · exfalso
      have : seg β N y + 1 ≤ seg β N x := hs
      have := h.le this (by have := (seg_spec h hN hx.1 hxN).1; omega)
      linarith
  · rw [hyN, brk_top h hN]
    have := (seg_spec h hN hx.1 hxN).1
    have : ((seg β N x : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
    grind

/-- **The key map is onto.** -/
theorem brk_onto (h : BrkInc β N) (hN : 1 ≤ N) {y : ℝ} (hy0 : c ≤ y) (hyN : y ≤ c + N) :
    ∃ x ∈ Icc ztmpl ztmpm, brk β N c x = y := by
  rcases hyN.lt_or_eq with hyN | hyN
  swap
  · exact ⟨β N, ⟨h.le ztbg le_rfl, le_rfl⟩, by rw [brk_top h hN, hyN]⟩
  set j := ⌊y - c⌋₊ with hj
  have hjN : ztgun := by
    rw [hj, Nat.floor_lt by_linarith]; linarith
  have hj1 : (j : ℝ) ≤ y - c := Nat.floor_le by_linarith
  have hj2 : y - c < j + 1 := Nat.lt_floor_add_one _
  have hpos : 0 < β ztl - β j := by linarith [h j hjN]
  set x := β j + ztqzf * ztxzb
  have hx1 : β j ≤ x := by have := mul_nonneg (show 0 ≤ y - c - j by linarith) hpos.le; linarith
  have hx2 : x < β ztl := by
    have : ztqzf * ztxzb < 1 * ztxzb :=
      mul_lt_mul_of_pos_right by_linarith hpos
    linarith
  have hx0 : β 0 ≤ x := le_trans (h.le ztbg hjN.le) hx1
  have hxN : ztuva := lt_of_lt_of_le hx2 (h.le by_omega le_rfl)
  -- the piece of `x` is `j`
  have hseg : seg β N x = j := by
    zubrp
    rcases lt_trichotomy ztcdv j with hs | hs | hs
    · have := h.le (show seg β N x + 1 ≤ j by omega) hjN.le; linarith
    · zujux
    · have := h.le (show j + 1 ≤ seg β N x by omega) hk.le; linarith
  refine ⟨x, ⟨hx0, hxN.le⟩, ?_⟩
  zumrx
  grind

/-- **Breakpoints go to integer keys, and only they.** -/
theorem brk_int_iff (h : BrkInc β N) (hN : 1 ≤ N) {c₀ : ℕ} {x : ℝ} (hx0 : β 0 ≤ x)
    (hxN : x < β N) : (∃ k : ℕ, brk β N c₀ x = k) ↔ ∃ j, j < N ∧ x = β j := by
  zubrp
  have p := brk_piece (c := (c₀ : ℝ)) h hN hx0 hxN
  constructor
  · rintro ⟨k, hk'⟩
    refine ⟨seg β N x, hk, ?_⟩
    rw [hk'] at p
    have e : (k : ℝ) = c₀ + seg β N x := by
      have a1 : c₀ + seg β N x ≤ k := by exact_mod_cast p.1
      have a2 : k < c₀ + seg β N x + 1 := by exact_mod_cast p.2
      have : k = c₀ + seg β N x := by_omega
      simp_all
    zvmwe at hk'
    unfold brk at hk'
    grind
  · zuecp
    have hseg : seg β N ztmpn = j := by
      rcases lt_trichotomy (seg β N ztmpn) j with hs | hs | hs
      · have := h.le (show seg β N ztmpn + 1 ≤ j by omega) hj.le; linarith
      · zujux
      · have := h.lt (show j < seg β N ztmpn by omega) hk.le; linarith
    refine ⟨c₀ + j, ?_⟩
    zumry
end
end ArcT
namespace DownDrv
@[expose] public section
open Set
open Chazelle.Chain (IsHChordIn freeIn regionsIn)
open Chazelle.Visibility (hseg chords)
variable {Q : Polygon} {S : Set (Set Point)}

/-- **B-M1: a vertex chord not in `S` lies in one region of `S`.** -/
theorem full_in_region (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    {c : Set Point} (hc : c ∈ chords Q) (hcS : c ∉ S) :
    ∃ R ∈ (interiorModel Q).regions S, c ∩ (interiorModel Q).D ⊆ R ∧
      (c ∩ (interiorModel Q).D).Nonempty := by
  set D := (interiorModel Q).D with hD
  zujzi
  obtain ⟨y, a, b, hch, rfl⟩ := hHC
  zumcw
  -- the domain part of the chord is its open part
  have hopen : hseg y a b ∩ D ⊆ (fun x : ℝ => (ztjw : Point)) '' Ioo a b := by
    rintro w ⟨hw, hwD⟩
    obtain ⟨h1, h2⟩ := FullDegInt.open_of_mem hch hw hwD
    exact ⟨w.1, ztwo, Prod.ext rfl hw.1.symm⟩
  have hsubD : (fun x : ℝ => (ztjw : Point)) '' Ioo a b ⊆ hseg y a b ∩ D := by
    rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨rfl, h1.le, h2.le⟩, hch.open_mem x h1 h2⟩
  -- it avoids the chords of `S`
  have hfree : (fun x : ℝ => (ztjw : Point)) '' Ioo a b ⊆ freeIn D S := by
    zucdk
    obtain ⟨hwc, hwD⟩ := hsubD hw
    refine ⟨hwD, ?_⟩
    rintro ⟨e, he, hwe⟩
    obtain ⟨y', a', b', hch', rfl⟩ := hFam.2.1 he
    have := FullDegInt.eq_of_common ztlws ⟨y', a', b', hch', rfl⟩ hwc hwe hwD
    simp_all
  have hpre : IsPreconnected ((fun x : ℝ => (ztjw : Point)) '' Ioo a b) :=
    isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => (ztjw : Point)).continuousOn
  set z₀ : Point := ztwsj
  have hz₀ : z₀ ∈ (fun x : ℝ => (ztjw : Point)) '' Ioo a b :=
    ⟨ztth / 2, ⟨by_linarith, by_linarith⟩, rfl⟩
  refine ⟨connectedComponentIn ztbzw z₀, ⟨z₀, hfree hz₀, rfl⟩, ?_, ⟨z₀, hsubD hz₀⟩⟩
  exact hopen.trans (hpre.subset_connectedComponentIn hz₀ hfree)
end
end DownDrv
end Chazelle.Core
namespace Chazelle.Final
@[expose] public section
open Set
open Chazelle.Jordan (simple_vtx_inj simple_edge_inter)
open Chazelle.Visibility
open Chazelle.Mountain

/-! ### The trapezoid table -/

/-- A record of the trapezoid table: the indices of the left and right side edges and of the top
and bottom vertices of a trapezoid. -/
structure TrapRec where
  /-- The left side edge. -/
  left : ℕ
  /-- The right side edge. -/
  right : ℕ
  /-- The top vertex (leftmost vertex of the closed top side). -/
  top : ℕ
  /-- The bottom vertex (rightmost vertex of the closed bottom side). -/
  bot : ℕ
  deriving DecidableEq

/-- The trapezoid table handed over by the visibility-map stage. -/
abbrev TrapTable : Type := List TrapRec

/-- The record of trapezoid data. -/
noncomputable def trapRecOf {P : Polygon} (D : TrapData P) : TrapRec := ztomb

/-- **Validity of a trapezoid table.**  `T` is the list of records of a list `L` of trapezoid
data whose regions are pairwise distinct and are exactly the regions of the visibility map; so
the records are in bijection with the regions, and the record of a region `R` is
`⟨D.i, D.j, D.top, D.bot⟩` for trapezoid data `D` with `D.region = R` (which data is used does
not matter: `trapRecOf_eq_of_region_eq`). -/
def IsTrapTable (P : Polygon) (T : TrapTable) : Prop :=
  ∃ L : List (TrapData P), L.map trapRecOf = T ∧ (L.map TrapData.region).Nodup ∧
    ∀ R, R ∈ regions P ↔ ∃ D ∈ L, D.region = R

/-! ### The record depends only on the region -/
variable {P : Polygon} {T : TrapTable}
/-- Two trapezoid data with the same region have the same heights. -/
theorem heights_eq_of_region_eq (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : D.y₁ = D'.y₁ ∧ D.y₂ = D'.y₂ := by
  zuhyj
  have htop : D.top = D'.top := congrArg Prod.fst hd
  have hbot : D.bot = D'.bot := congrArg Prod.snd hd
  exact ⟨by rw [← D.bot_snd hP, ← D'.bot_snd hP, hbot],
    by rw [← D.top_snd hP, ← D'.top_snd hP, htop]⟩

/-- A point on the line of a side edge, strictly inside the height range, is not a vertex
unless it is off the closed corridor; used to separate two side edges. -/
theorem not_vtx_on_side (D : TrapData P) {y : ℝ}
    (h1 : D.y₁ < y) (h2 : y < D.y₂) {x : ℝ} (hx1 : edgeX P D.i y ≤ x) (hx2 : x ≤ edgeX P D.j y)
    {m : ℕ} (hm : m < P.n) (hmp : P.vtx m = ztjw) : False := by
  have e1 : (P.vtx m).1 = x := by zupdt
  have e2 : (P.vtx m).2 = y := by zupdt
  exact D.isTrap.no_vertex m hm by_simp_all by_simp_all
    by_simp_all by_simp_all

/-- A point of two distinct edges of a simple polygon is a vertex. -/
theorem exists_vtx_of_mem_two_edges {P : Polygon} (hP : P.Simple) {a b : ℕ} (ha : a < P.n)
    (hb : b < P.n) (hab : a ≠ b) {p : Point} (hpa : p ∈ P.edge a) (hpb : p ∈ P.edge b) :
    ∃ m < P.n, P.vtx m = p := by
  have hc : p ∈ P.commonEndpoints a b := by
    rw [← simple_edge_inter hP ha hb hab]; simp_all
  rcases hc.1 with e | e
  · grind
  · exact ⟨ztdf % P.n, Nat.mod_lt _ by_omega, e.symm⟩

/-- **The left side edge depends only on the region.** -/
theorem left_eq_of_region_eq (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : D.i = D'.i := by
  zufkb
  zuhw
  zubbk

  have e1 := D.isTrap.left_le_of_subset hP D.free D'.isTrap h.subset y hy
  have e2 := D'.isTrap.left_le_of_subset hP D'.free D.isTrap h.symm.subset y hy'
  have heq : edgeX P D.i y = edgeX P D'.i y := by_grind
  zuct
  have hp1 : (ztpat : Point) ∈ P.edge D.i := D.isTrap.mem_edgeL hy.1 hy.2 rfl
  have hp2 : (ztpat : Point) ∈ P.edge D'.i :=
    D'.isTrap.mem_edgeL hy'.1 hy'.2 heq
  obtain ⟨m, hm, hmp⟩ := exists_vtx_of_mem_two_edges hP D.isTrap.hi D'.isTrap.hi hne hp1 hp2
  zuhzg
  exact not_vtx_on_side D hyl hyr le_rfl hlt.le hm hmp

/-- **The right side edge depends only on the region.** -/
theorem right_eq_of_region_eq (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : D.j = D'.j := by
  zufkb
  zuhw
  zubbk

  have e1 := D.isTrap.right_le_of_subset hP D.free D'.isTrap h.subset y hy
  have e2 := D'.isTrap.right_le_of_subset hP D'.free D.isTrap h.symm.subset y hy'
  have heq : edgeX P D.j y = edgeX P D'.j y := by_grind
  zuct
  have hp1 : (ztpav : Point) ∈ P.edge D.j := D.isTrap.mem_edgeR hy.1 hy.2 rfl
  have hp2 : (ztpav : Point) ∈ P.edge D'.j :=
    D'.isTrap.mem_edgeR hy'.1 hy'.2 heq
  obtain ⟨m, hm, hmp⟩ := exists_vtx_of_mem_two_edges hP D.isTrap.hj D'.isTrap.hj hne hp1 hp2
  zuhzg
  exact not_vtx_on_side D hyl hyr hlt.le le_rfl hm hmp

/-- **The record depends only on the region.** -/
theorem trapRecOf_eq_of_region_eq (hP : P.Simple) (D D' : TrapData P)
    (h : D.region = D'.region) : trapRecOf D = trapRecOf D' := by
  zuhyj
  show (ztomb : TrapRec) = ⟨D'.i, D'.j, D'.top, D'.bot⟩
  rw [left_eq_of_region_eq hP D D' h, right_eq_of_region_eq hP D D' h,
    show D.top = D'.top from congrArg Prod.fst hd, show D.bot = D'.bot from congrArg Prod.snd hd]

/-! ### Properties of a trapezoid table -/

/-- The records of a trapezoid table are the records of trapezoid data. -/
theorem IsTrapTable.exists_of_mem (hT : IsTrapTable P T)
    {r : TrapRec} (hr : r ∈ T) : ∃ D : TrapData P, trapRecOf D = r := by
  obtain ⟨L, rfl, -, -⟩ := hT
  grind

/-- The record of any trapezoid data is in a trapezoid table. -/
theorem IsTrapTable.mem_of_trapData (hP : P.Simple) {T : TrapTable}
    (hT : IsTrapTable P T) (D : TrapData P) : trapRecOf D ∈ T := by
  obtain ⟨L, rfl, -, hreg⟩ := hT
  obtain ⟨D', hD', hreg'⟩ := (hreg D.region).1 ztpxd
  rw [← trapRecOf_eq_of_region_eq hP D' D hreg']
  grind

/-- **A trapezoid table has one record per region.** -/
theorem IsTrapTable.length_eq
    (hT : IsTrapTable P T) : T.length = (regions P).ncard := by
  classical
  obtain ⟨L, rfl, hnd, hreg⟩ := hT
  have hset : ((L.map TrapData.region).toFinset : Set _) = regions P := by
    ext R
    simp_all
  rw [List.length_map, ← hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    List.length_map]

/-- A trapezoid table has at most `2 n + 1` records. -/
theorem IsTrapTable.length_le (hP : P.Simple) {T : TrapTable}
    (hT : IsTrapTable P T) : T.length ≤ 2 * P.n + 1 := by
  rw [hT.length_eq]
  exact regions_ncard_le hP

/-! ### The vertex-chord table -/

/-- The horizontal direction coded by a boolean: `true` is right (`1`), `false` is left (`-1`). -/
noncomputable def dirSign (b : Bool) : ℝ := if b then 1 else -1

/-- A coded direction is `1` or `-1`. -/
theorem dirSign_cases (b : Bool) : dirSign b = 1 ∨ dirSign b = -1 := by
  cases b
  · tauto
  tauto

/-- A record of the vertex-chord table: the chord of vertex `src` in direction `dir` ends at
vertex `dst`. -/
structure ChordRec where
  /-- The vertex emitting the chord. -/
  src : ℕ
  /-- The direction (`true` = right). -/
  dir : Bool
  /-- The vertex where the chord ends. -/
  dst : ℕ
  deriving DecidableEq
variable {C : List ChordRec}

/-- The record describes a vertex-to-vertex chord: the direction is locally interior at `src`
and the chord ends at vertex `dst`. -/
def ChordRec.Valid (P : Polygon) (c : ChordRec) : Prop :=
  c.src < P.n ∧ c.dst < P.n ∧ DirInterior P c.src ztvpb ∧
    chordEnd P c.src ztvpb = P.vtx c.dst

/-- **Validity of a vertex-chord table**: its members are exactly the valid records, and each
pair (source, direction) occurs once. -/
def IsVtxChordTable (P : Polygon) (C : List ChordRec) : Prop :=
  (∀ c, c ∈ C ↔ c.Valid P) ∧ (C.map fun c => ztnwr).Nodup

/-- The index pairs of the valid records are exactly the vertex-to-vertex chords. -/
theorem mem_vtxChords_iff_chordRec {d : ℕ × ℕ} :
    d ∈ vtxChords P ↔ ∃ c : ChordRec, c.Valid P ∧ zttho = d := by
  constructor
  · rintro ⟨h1, h2, σ, hσ, hdir, hend⟩
    zur
    · exact ⟨⟨d.1, true, d.2⟩, ztonr, rfl⟩
    · exact ⟨⟨d.1, false, d.2⟩, ztonr, rfl⟩
  · rintro ⟨c, ⟨h1, h2, hdir, hend⟩, rfl⟩
    exact ⟨h1, h2, dirSign c.dir, dirSign_cases c.dir, hdir, hend⟩

/-- A vertex-chord table has at most `2 n` records. -/
theorem IsVtxChordTable.length_le (hC : IsVtxChordTable P C) :
    C.length ≤ 2 * P.n := by
  obtain ⟨hmem, hnd⟩ := hC
  have h1 : (C.map fun c => ztnwr).toFinset.card = C.length := by
    zuewt
  have h2 : (C.map fun c => ztnwr).toFinset ⊆
      Finset.range P.n ×ˢ (Finset.univ : Finset Bool) := by
    zuh
    zuigm
    zugox
    rw [Finset.mem_product, Finset.mem_range]
    exact ⟨((hmem c).1 hc).1, Finset.mem_univ _⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool, h1] at h3
  omega

/-! ### The final-stage input: the list of inserted diagonals -/

/-- Normalise an index pair as an unordered pair: smaller index first. -/
def sortPair (d : ℕ × ℕ) : ℕ × ℕ := (min d.1 d.2, max d.1 d.2)

/-- The normal form of a pair with distinct entries is the pair or its swap, ordered strictly. -/
theorem sortPair_eq_iff {e d : ℕ × ℕ} (he : e.1 ≠ e.2) :
    sortPair e = d ↔ d.1 < d.2 ∧ (e = d ∨ e = d.swap) := by
  obtain ⟨a, b⟩ := e
  obtain ⟨x, y⟩ := d
  simp only [sortPair, Prod.mk.injEq, Prod.swap_prod_mk] at he ⊢
  omega

/-- Whether the top and bottom vertices of a record are non-adjacent in a polygon with `n`
vertices. -/
def TrapRec.nonAdj (n : ℕ) (r : TrapRec) : Bool :=
  decide (r.bot ≠ ztogq % n ∧ r.top ≠ ztogp % n)

/-- The pairs `(top, bot)` of the records with non-adjacent top and bottom vertices. -/
def trapPairs (P : Polygon) (T : TrapTable) : List ztw :=
  (T.filter (TrapRec.nonAdj P.n)).map fun r => zttyb

/-- The pairs `(src, dst)` of the chord records. -/
def chordPairs (C : List ChordRec) : List ztw := C.map fun c => zttho

/-- **The list of inserted diagonals** computed by the final stage from the two tables: the
trapezoid pairs followed by the chord pairs, normalised as unordered pairs and deduplicated. -/
def diagList (P : Polygon) (T : TrapTable) (C : List ChordRec) : List ztw :=
  ((trapPairs P T ++ chordPairs C).map sortPair).dedup

/-- The trapezoid pairs of a valid table are exactly the trapezoid diagonals. -/
theorem mem_trapPairs_iff (hP : P.Simple) {T : TrapTable} (hT : IsTrapTable P T)
    {d : ℕ × ℕ} : d ∈ trapPairs P T ↔ d ∈ trapDiagonals P := by
  zumvg
  rw [List.mem_map]
  constructor
  · zuoc
    rw [List.mem_filter] at hr
    obtain ⟨D, rfl⟩ := hT.exists_of_mem hr.1
    refine ⟨D, ?_, rfl⟩
    have h := hr.2
    have h2 := of_decide_eq_true h
    zucvi
  · rintro ⟨D, hD, rfl⟩
    refine ⟨trapRecOf D, List.mem_filter.2 ⟨hT.mem_of_trapData hP D, ?_⟩, rfl⟩
    show decide _ = true
    exact decide_eq_true hD

/-- The chord pairs of a valid table are exactly the vertex-to-vertex chords. -/
theorem mem_chordPairs_iff (hC : IsVtxChordTable P C)
    {d : ℕ × ℕ} : d ∈ chordPairs C ↔ d ∈ vtxChords P := by
  unfold chordPairs
  rw [List.mem_map, mem_vtxChords_iff_chordRec]
  constructor
  · zuifm
    exact ⟨c, (hC.1 c).1 hc, rfl⟩
  · zuifm
    exact ⟨c, (hC.1 c).2 hc, rfl⟩

/-- The concatenated pairs are exactly the inserted diagonals. -/
theorem mem_pairs_iff (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) {d : ℕ × ℕ} :
    d ∈ trapPairs P T ++ chordPairs C ↔ d ∈ allDiagonals P := by
  rw [List.mem_append, mem_trapPairs_iff hP hT, mem_chordPairs_iff hC]
  rfl

/-- **Specification of the final-stage input**: the members of `diagList P T C` are exactly the
normal forms (as unordered pairs) of the inserted diagonals `allDiagonals P`. -/
theorem diagList_spec (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) (d : ℕ × ℕ) :
    d ∈ diagList P T C ↔ ∃ e ∈ allDiagonals P, sortPair e = d := by
  unfold diagList
  rw [List.mem_dedup, List.mem_map]
  constructor
  · zuecl
    exact ⟨e, (mem_pairs_iff hP hT hC).1 he, rfl⟩
  · zuecl
    exact ⟨e, (mem_pairs_iff hP hT hC).2 he, rfl⟩

/-- **Membership in the final-stage input**: `d ∈ diagList P T C` iff `d.1 < d.2` and `d` or
its swap is an inserted diagonal. -/
theorem diagList_mem_iff (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) (d : ℕ × ℕ) :
    d ∈ diagList P T C ↔ d.1 < d.2 ∧ (d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P) := by
  rw [diagList_spec hP hT hC]
  constructor
  · rintro ⟨e, he, hed⟩
    zuezl

  · rintro ⟨hlt, h | h⟩
    · exact ⟨d, h, (sortPair_eq_iff by_omega).2 by_simp_all⟩
    · exact ⟨d.swap, h, (sortPair_eq_iff by_grind).2 by_simp_all⟩

/-- The members of the final-stage input are pairs of distinct vertex indices, smaller first. -/
theorem diagList_lt (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) {d : ℕ × ℕ} (hd : d ∈ diagList P T C) :
    d.1 < d.2 ∧ d.2 < P.n := by
  obtain ⟨hlt, h | h⟩ := (diagList_mem_iff hP hT hC d).1 hd
  · exact ⟨hlt, (allDiagonals_lt hP h).2.1⟩
  · exact ⟨hlt, (allDiagonals_lt hP h).1⟩

/-- **No duplicates** (as unordered pairs: every member is in normal form). -/
theorem diagList_nodup (P : Polygon) (T : TrapTable) (C : List ChordRec) :
    (diagList P T C).Nodup :=
  List.nodup_dedup _

/-- **At most `4 n + 1` inserted diagonals are handed to the final stage.** -/
theorem diagList_length_le (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) :
    (diagList P T C).length ≤ 4 * P.n + 1 := by
  unfold diagList
  have h1 := (List.dedup_sublist ((trapPairs P T ++ chordPairs C).map sortPair)).length_le
  have h2 : (trapPairs P T).length ≤ T.length := by
    zumvg
    grind
  zuivk
  rw [List.length_map, List.length_append] at h1
  have h4 := hT.length_le hP
  have h5 := hC.length_le
  omega
open Filter Topology Metric
open Chazelle.Jordan (mem_ball_iff_abs prevIdx)
open Chazelle.Existence (vtx_mem_boundary boundary_near_vtx)
theorem height_of_mem_chordUnion {p : Point} (hp : p ∈ chordUnion P) :
    ∃ k < P.n, p.2 = (P.vtx k).2 := by
  zuvd

/-- The abscissa at height `h` of the line through `v` and `a` (meaningful when
`a.2 ≠ v.2`). -/
noncomputable def crossX (v a : Point) (h : ℝ) : ℝ := v.1 + (h - v.2) / ztclz * ztcts

/-- A point of the segment `[v, a]` at a height different from `v.2` has abscissa
`crossX v a h`. -/
theorem fst_eq_crossX {v a p : Point} (hp : p ∈ Chazelle.segment v a) (hh : p.2 ≠ v.2) :
    p.1 = crossX v a p.2 := by
  zuceb
  simp only at hh ⊢
  have hne : ztsdl := by
    simp_all
  unfold crossX
  simp_all

/-- An open interval contains a point different from two given reals. -/
theorem exists_Ioo_avoid {lo hi : ℝ} (h : lo < hi) (c₁ c₂ : ℝ) :
    ∃ x, lo < x ∧ x < hi ∧ x ≠ c₁ ∧ x ≠ c₂ := by
  have hd : 0 < hi - lo := by_linarith
  by_cases hA : lo + ztcw / 4 ≠ c₁ ∧ lo + ztcw / 4 ≠ c₂
  · exact ⟨_, by_linarith, by_linarith, hA.1, hA.2⟩
  by_cases hB : lo + ztcw / 2 ≠ c₁ ∧ lo + ztcw / 2 ≠ c₂
  · exact ⟨_, by_linarith, by_linarith, hB.1, hB.2⟩
  by_cases hC : lo + 3 * ztcw / 4 ≠ c₁ ∧ lo + 3 * ztcw / 4 ≠ c₂
  · exact ⟨_, by_linarith, by_linarith, hC.1, hC.2⟩
  grind

/-- The position of `x` relative to two cut points `m ≤ M`: `0` left of `m`, `1` between them,
`2` right of `M`. -/
noncomputable def piece3 (m M x : ℝ) : Fin 3 := if x < m then 0 else if x < M then 1 else 2

/-- Two points off the cut points, in the same piece: everything between them avoids the cut
points. -/
theorem piece3_between_aux {m M x x' z : ℝ} (hmM : m ≤ M) (hxm : x ≠ m) (hxM : x ≠ M)
    (hxm' : x' ≠ m) (hxM' : x' ≠ M) (h : piece3 m M x = piece3 m M x')
    (hz1 : min x x' ≤ z) (hz2 : z ≤ max x x') : z ≠ m ∧ z ≠ M := by
  unfold piece3 at h
  grind

/-- Two points off two cut points `c₁`, `c₂`, in the same piece: everything between them avoids
the cut points. -/
theorem piece3_between {c₁ c₂ x x' z : ℝ} (hx1 : x ≠ c₁) (hx2 : x ≠ c₂) (hx1' : x' ≠ c₁)
    (hx2' : x' ≠ c₂) (h : piece3 ztkav ztkar x = piece3 ztkav ztkar x')
    (hz1 : min x x' ≤ z) (hz2 : z ≤ max x x') : z ≠ c₁ ∧ z ≠ c₂ := by
  rcases le_total c₁ c₂ with hc | hc
  · rw [min_eq_left hc, max_eq_right hc] at h
    exact piece3_between_aux hc hx1 hx2 hx1' hx2' h hz1 hz2
  · rw [min_eq_right hc, max_eq_left hc] at h
    obtain ⟨h1, h2⟩ := piece3_between_aux hc hx2 hx1 hx2' hx1' h hz1 hz2
    simp_all

/-! ### At most three regions near a vertex on one side -/

/-- **At most three regions touch a vertex from one side.**  Let `F` be a filter of heights
converging to `v.2` from one side (or both), `v = P.vtx k`.  If each region of a family meets,
for all heights `h` eventually along `F`, the horizontal line at height `h` arbitrarily close to
`v` and away from any two prescribed abscissae, then the family has at most three members. -/
theorem ncard_le_three_of_near (hP : P.Simple) {k : ℕ} (hk : k < P.n)
    (F : Filter ℝ) [F.NeBot] (hF : F ≤ 𝓝[≠] (P.vtx k).2) {S : Set ztf}
    (hS : S ⊆ regions P)
    (hnear : ∀ R ∈ S, ∀ r > 0, ∀ c₁ c₂ : ℝ → ℝ, ∀ᶠ h in F,
      ∃ x, |x - (P.vtx k).1| < r ∧ (ztcon : Point) ∈ R ∧ x ≠ c₁ h ∧ x ≠ c₂ h) :
    S.ncard ≤ 3 := by
  obtain ⟨r, hr, hball⟩ := boundary_near_vtx hP hk
  zucqp

  have hSfin := (regions_finite hP).subset hS
  have hF' := hF.trans nhdsWithin_le_nhds
  -- a common height `h`
  have hev1 : ∀ᶠ h in F, ∀ R ∈ S, ∃ x, |x - v.1| < r ∧ (ztcon : Point) ∈ R ∧
      x ≠ crossX v a h ∧ x ≠ crossX v b h :=
    hSfin.eventually_all.2 fun R hR => hnear R hR r hr _ _
  have hev2 : ∀ᶠ h in F, h ≠ v.2 := Filter.mem_of_superset (hF self_mem_nhdsWithin) by_grind
  have hev3 : ∀ᶠ h in F, |h - v.2| < r := by
    refine hF' (Filter.mem_of_superset (Metric.ball_mem_nhds v.2 hr) fun h hh => ?_)
    tauto
  have hev4 : ∀ᶠ h in F, ∀ j ∈ Iio P.n, (P.vtx j).2 ≠ h := by
    refine (Set.finite_Iio P.n).eventually_all.2 fun j _ => ?_
    by_cases hj : (P.vtx j).2 = v.2
    · filter_upwards [hev2] with h hh
      grind
    · filter_upwards [hF' (eventually_ne_nhds ztvbg)] with h hh
      grind
  obtain ⟨h, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  choose! x hx using h1
  set c₁ := crossX v a h with hc₁
  set c₂ := crossX v b h with hc₂
  -- two witnesses in the same piece lie in the same region
  have key : ∀ R ∈ S, ∀ R' ∈ S, piece3 ztkav ztkar ztqyw =
      piece3 ztkav ztkar ztqyv → R = R' := by
    intro R hR R' hR' hpiece
    obtain ⟨hxR1, hxR2, hxR3, hxR4⟩ := hx R hR
    obtain ⟨hxR1', hxR2', hxR3', hxR4'⟩ := hx R' hR'
    set T : Set Point := (fun z : ℝ => (ztuer : Point)) '' Icc (min ztqyw ztqyv)
      (max ztqyw ztqyv) with hT
    have hTc : IsPreconnected T :=
      isPreconnected_Icc.image _ (Continuous.continuousOn ztepq)
    have hpT : (ztrym : Point) ∈ T := ⟨x R, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩
    have hpT' : (ztryl : Point) ∈ T := ⟨x R', ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
    have hTb : ∀ q ∈ T, q ∉ P.boundary := by
      rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩ hqb
      have hzne := piece3_between hxR3 hxR4 hxR3' hxR4' hpiece hz1 hz2
      have hqball : (ztuer : Point) ∈ ball v r := by
        zucjy
        refine ⟨?_, h3⟩
        zvncj at hxR1 hxR1' ⊢
        have := lt_min (by linarith : v.1 - r < x R) (by linarith : v.1 - r < x R')
        have := max_lt (by linarith : x R < v.1 + r) (by linarith : x R' < v.1 + r)
        grind
      rcases hball _ hqball hqb with hq | hq
      · rw [Geometry.segment_comm] at hq
        exact hzne.1 zttkh
      · exact hzne.2 zttkh
    have hRfree := regions_subset ztvtt hxR2
    have hTi :=
      subset_interior_of_isPreconnected hP hTc hTb hpT hRfree.1
    have hTf : T ⊆ freeRegion P := by
      zuco
      refine ⟨hTi hq, fun hqc => ?_⟩
      obtain ⟨j, hj, hjy⟩ := height_of_mem_chordUnion hqc
      obtain ⟨z, -, rfl⟩ := hq
      tauto
    have hsub := hTc.subset_connectedComponentIn hpT hTf
    have hRcc : R = connectedComponentIn ztesb (ztrym : Point) := by
      obtain ⟨z₀, -, hz₀⟩ := hS hR
      rw [hz₀] at hxR2 ⊢
      exact connectedComponentIn_eq hxR2
    have hmem : (ztryl : Point) ∈ R := by
      rw [hRcc]
      tauto
    rcases regions_eq_or_disjoint ztvtt (hS hR') with e | e
    · zulez
    · exact absurd hxR2' (Set.disjoint_left.1 e hmem)
  have hinj : InjOn (fun R => piece3 _ _ _) S :=
    key
  calc S.ncard ≤ (univ : Set _).ncard :=
        ncard_le_ncard_of_injOn _ by_grind hinj ztcwq
    _ = 3 := by_simp

/-! ### The regions touching a vertex from below and from above -/

/-- **A trapezoid with `v` on its closed top side reaches `v` from below**: for all heights `h`
slightly below `v.2`, it contains a point `(x, h)` with `x` within `r` of `v.1` and different from
two prescribed abscissae. -/
theorem trapData_eventually_below (hP : P.Simple) (D : TrapData P) {k : ℕ}
    (hk : k ∈ sideVtxSet P D.i D.j D.y₂) {r : ℝ} (hr : 0 < r) (c₁ c₂ : ℝ → ℝ) :
    ∀ᶠ h in 𝓝[<] (P.vtx k).2, ∃ x, |x - (P.vtx k).1| < r ∧ (ztcon : Point) ∈ D.region ∧
      x ≠ c₁ h ∧ x ≠ c₂ h := by
  zudqp

  zuhw
  have e2 : ∀ᶠ h in 𝓝 D.y₂, edgeX P D.i h < (P.vtx k).1 + r :=
    (continuous_edgeX P D.i).continuousAt.eventually_lt continuousAt_const by_linarith
  have e3 : ∀ᶠ h in 𝓝 D.y₂, (P.vtx k).1 - r < edgeX P D.j h :=
    continuousAt_const.eventually_lt (continuous_edgeX P D.j).continuousAt by_linarith
  filter_upwards [Ioo_mem_nhdsLT h12, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3]
    with h hh hh3 hh4
  zuhys
  have hlohi : ztyyy :=
    max_lt zttsq zttsp
  zuvi

  refine ⟨x, ?_, ⟨hh.1, hh.2, by_simp_all,
    by simp_all⟩, hxc1, hxc2⟩
  grind

/-- **A trapezoid with `v` on its closed bottom side reaches `v` from above.** -/
theorem trapData_eventually_above (hP : P.Simple) (D : TrapData P) {k : ℕ}
    (hk : k ∈ sideVtxSet P D.i D.j D.y₁) {r : ℝ} (hr : 0 < r) (c₁ c₂ : ℝ → ℝ) :
    ∀ᶠ h in 𝓝[>] (P.vtx k).2, ∃ x, |x - (P.vtx k).1| < r ∧ (ztcon : Point) ∈ D.region ∧
      x ≠ c₁ h ∧ x ≠ c₂ h := by
  zudqp

  zuhw
  have e2 : ∀ᶠ h in 𝓝 D.y₁, edgeX P D.i h < (P.vtx k).1 + r :=
    (continuous_edgeX P D.i).continuousAt.eventually_lt continuousAt_const by_linarith
  have e3 : ∀ᶠ h in 𝓝 D.y₁, (P.vtx k).1 - r < edgeX P D.j h :=
    continuousAt_const.eventually_lt (continuous_edgeX P D.j).continuousAt by_linarith
  filter_upwards [Ioo_mem_nhdsGT h12, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3]
    with h hh hh3 hh4
  zuhys
  have hlohi : ztyyy :=
    max_lt zttsq zttsp
  zuvi

  refine ⟨x, ?_, ⟨hh.1, hh.2, by_simp_all,
    by simp_all⟩, hxc1, hxc2⟩
  grind

/-- The regions whose trapezoid has vertex `k` on its closed top side. -/
def topRegions (P : Polygon) (k : ℕ) : Set ztf :=
  {R | ∃ D : TrapData P, D.region = R ∧ k ∈ sideVtxSet P D.i D.j D.y₂}

/-- The regions whose trapezoid has vertex `k` on its closed bottom side. -/
def botRegions (P : Polygon) (k : ℕ) : Set ztf :=
  {R | ∃ D : TrapData P, D.region = R ∧ k ∈ sideVtxSet P D.i D.j D.y₁}

/-- The regions touching a vertex from below are regions. -/
theorem topRegions_subset (hP : P.Simple) (k : ℕ) : topRegions P k ⊆ regions P := by
  zufma

/-- The regions touching a vertex from above are regions. -/
theorem botRegions_subset (hP : P.Simple) (k : ℕ) : botRegions P k ⊆ regions P := by
  zufma

/-- **At most three regions have a given vertex on the closed top side of their trapezoid.** -/
theorem topRegions_ncard_le (hP : P.Simple) (k : ℕ) : (topRegions P k).ncard ≤ 3 := by
  zujtm
  · refine ncard_le_three_of_near hP hk (𝓝[<] (P.vtx k).2)
      zttuf (topRegions_subset hP k) ?_
    zuewd
    exact trapData_eventually_below hP D hD hr c₁ c₂
  · have : topRegions P k = ∅ := by
      zucrl

    simp_all

/-- **At most three regions have a given vertex on the closed bottom side of their trapezoid.** -/
theorem botRegions_ncard_le (hP : P.Simple) (k : ℕ) : (botRegions P k).ncard ≤ 3 := by
  zujtm
  · refine ncard_le_three_of_near hP hk (𝓝[>] (P.vtx k).2)
      zttuf (botRegions_subset hP k) ?_
    zuewd
    exact trapData_eventually_above hP D hD hr c₁ c₂
  · have : botRegions P k = ∅ := by
      zucrl

    simp_all

/-! ### Counting the incident diagonals -/

/-- The inserted diagonals incident to vertex `v` (as ordered pairs). -/
def incident (P : Polygon) (v : ℕ) : Set ztw :=
  {d | d ∈ allDiagonals P ∧ zthgj}

/-- The set of incident diagonals is finite. -/
theorem incident_finite (hP : P.Simple) (v : ℕ) : (incident P v).Finite :=
  (allDiagonals_finite hP).subset fun _ h => h.1

/-- The trapezoid-diagonal map `d ↦ regionOfDiag P d` is injective. -/
theorem regionOfDiag_injOn (hP : P.Simple) :
    InjOn (regionOfDiag P) (trapDiagonals P) := by
  intro d hd d' hd' heq
  zubxg
  obtain ⟨D', -, rfl, hD'⟩ := regionOfDiag_spec hd'
  rw [hD, hD'] at heq
  exact TrapData.diag_eq_of_region_eq hP D D' heq

/-- **At most three trapezoid diagonals have top vertex `v`.** -/
theorem ncard_trapDiagonals_fst_le (hP : P.Simple) (v : ℕ) :
    {d | d ∈ trapDiagonals P ∧ d.1 = v}.ncard ≤ 3 := by
  refine le_trans (ncard_le_ncard_of_injOn _ ?_
    ztosz
    ((regions_finite hP).subset (topRegions_subset hP v))) (topRegions_ncard_le hP v)
  zuewg
  zubxg
  exact ⟨D, hD.symm, D.isTrap.topVtx_mem hP D.free⟩

/-- **At most three trapezoid diagonals have bottom vertex `v`.** -/
theorem ncard_trapDiagonals_snd_le (hP : P.Simple) (v : ℕ) :
    {d | d ∈ trapDiagonals P ∧ d.2 = v}.ncard ≤ 3 := by
  refine le_trans (ncard_le_ncard_of_injOn _ ?_
    ztosz
    ((regions_finite hP).subset (botRegions_subset hP v))) (botRegions_ncard_le hP v)
  zuewg
  zubxg
  exact ⟨D, hD.symm, D.isTrap.botVtx_mem hP D.free⟩

/-- **At most two vertex-to-vertex chords start at `v`** (one per direction). -/
theorem ncard_vtxChords_fst_le (hP : P.Simple) (v : ℕ) :
    {d | d ∈ vtxChords P ∧ d.1 = v}.ncard ≤ 2 := by
  have hsub : {d | d ∈ vtxChords P ∧ d.1 = v} ⊆
      {(v, vtxIndex P (chordEnd P v 1)), (v, vtxIndex P (chordEnd P v (-1)))} := by
    zuewg
    obtain ⟨-, hd2, σ, hσ, -, hend⟩ := hd
    have e : d = (d.1, vtxIndex P (chordEnd P d.1 σ)) := by
      rw [hend, vtxIndex_vtx hP hd2]
    grind
  calc _ ≤ ({ztkgo, ztkgo} :
        Set _).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ ({ztkgo} : Set _).ncard + 1 := ncard_insert_le _ _
    _ = 2 := by_simp

/-- **Two chords in the same direction ending at the same point start at the same vertex**: a
second chord would pass through the first vertex, but open chords are interior. -/
theorem chord_src_unique (hP : P.Simple) {i i' : ℕ} (hi : i < P.n)
    (hi' : i' < P.n) {σ : ℝ} (hd : DirInterior P i σ) (hd' : DirInterior P i' σ)
    (h : chordEnd P i σ = chordEnd P i' σ) : i = i' := by
  have hx : (P.vtx i).1 + σ * chordParam P i σ = (P.vtx i').1 + σ * chordParam P i' σ :=
    congrArg Prod.fst h
  have hy : (P.vtx i).2 = (P.vtx i').2 := by simpa using congrArg Prod.snd h
  have hpos := chordParam_pos hP hi hd
  have hpos' := chordParam_pos hP hi' hd'
  rcases lt_trichotomy zthvq (chordParam P i' σ) with hlt | heq | hgt
  · exfalso
    have hmem := (chord_spec hP hi' hd').2.2 ztfqn
      by_linarith by_linarith
    have he : rayPt (P.vtx i') σ ztfqn = P.vtx i := by
      zujev
      · show (P.vtx i').1 + σ * ztfqn = (P.vtx i).1
        grind
      simp_all
    zukud
    exact hmem.2 ztudb
  · apply simple_vtx_inj hP hi hi'
    grind
  · exfalso
    have hmem := (chord_spec hP hi hd).2.2 ztfqm
      by_linarith by_linarith
    have he : rayPt ztdn σ ztfqm = P.vtx i' := by
      zujev
      · show (P.vtx i).1 + σ * ztfqm = (P.vtx i').1
        grind
      simp_all
    zukud
    exact hmem.2 (vtx_mem_boundary P hi')

/-- The vertex-to-vertex chords in direction `σ` ending at `v` form a subsingleton. -/
theorem ncard_vtxChords_snd_dir_le (hP : P.Simple) (v : ℕ) (σ : ℝ) :
    {d | d ∈ vtxChords P ∧ d.2 = v ∧ DirInterior P d.1 σ ∧
      chordEnd P d.1 σ = P.vtx d.2}.ncard ≤ 1 := by
  rw [ncard_le_one_iff ztota]
  rintro d d' ⟨hd, hdv, hdir, hend⟩ ⟨hd', hdv', hdir', hend'⟩
  have h1 := chord_src_unique hP hd.1 hd'.1 hdir hdir'
    by_simp_all
  grind

/-- **At most two vertex-to-vertex chords end at `v`** (one per direction). -/
theorem ncard_vtxChords_snd_le (hP : P.Simple) (v : ℕ) :
    {d | d ∈ vtxChords P ∧ d.2 = v}.ncard ≤ 2 := by
  have hsub : {d | d ∈ vtxChords P ∧ d.2 = v} ⊆
      {d | d ∈ vtxChords P ∧ d.2 = v ∧ DirInterior P d.1 1 ∧ chordEnd P d.1 1 = P.vtx d.2} ∪
      {d | d ∈ vtxChords P ∧ d.2 = v ∧ DirInterior P d.1 (-1) ∧
        chordEnd P d.1 (-1) = P.vtx d.2} := by
    rintro d ⟨hd, hdv⟩
    obtain ⟨-, -, σ, hσ, hdir, hend⟩ := id hd
    grind
  calc _ ≤ _ := ncard_le_ncard hsub
        ztota
    _ ≤ _ := ncard_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (ncard_vtxChords_snd_dir_le hP v 1)
        (ncard_vtxChords_snd_dir_le hP v _)

/-- **Bounded degree**: at most `10` inserted diagonals are incident to any vertex of a simple
polygon (at most `3 + 3` trapezoid diagonals, `2 + 2` vertex-to-vertex chords). -/
theorem card_incident_le (hP : P.Simple) (v : ℕ) : (incident P v).ncard ≤ 10 := by
  set A := {d | d ∈ trapDiagonals P ∧ d.1 = v}
  set B := {d | d ∈ trapDiagonals P ∧ d.2 = v}
  set C := {d | d ∈ vtxChords P ∧ d.1 = v}
  set E := {d | d ∈ vtxChords P ∧ d.2 = v}
  have hsub : incident P v ⊆ ztbgp ∪ ztnjs := by
    rintro d ⟨hd | hd, h | h⟩
    · grind
    · grind
    · grind
    grind
  have hfin : (ztbgp ∪ ztnjs).Finite := by
    refine (allDiagonals_finite hP).subset ?_
    rintro d ((h | h) | (h | h))
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inr h.1
  calc (incident P v).ncard ≤ (ztbgp ∪ ztnjs).ncard := ncard_le_ncard hsub hfin
    _ ≤ (A ∪ B).ncard + (C ∪ E).ncard := ncard_union_le _ _
    _ ≤ (A.ncard + B.ncard) + (C.ncard + E.ncard) :=
        Nat.add_le_add ztodr ztodr
    _ ≤ (3 + 3) + ztssq :=
        Nat.add_le_add (Nat.add_le_add (ncard_trapDiagonals_fst_le hP v)
          (ncard_trapDiagonals_snd_le hP v))
          (Nat.add_le_add (ncard_vtxChords_fst_le hP v) (ncard_vtxChords_snd_le hP v))
    _ = 10 := by_norm_num

/-! ### Degrees in the final-stage input -/

/-- **Bounded degree in the final-stage input**: at most `10` members of `diagList P T C` are
incident to any vertex `v`. -/
theorem countP_diagList_le (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) (v : ℕ) :
    (diagList P T C).countP ztzev ≤ 10 := by
  classical
  rw [List.countP_eq_length_filter]
  set l := (diagList P T C).filter ztzev with hl
  have hnd : l.Nodup := (diagList_nodup P T C).filter _
  have hsub : (l.toFinset : Set _) ⊆ sortPair '' incident P v := by
    zuip
    rw [Finset.mem_coe, List.mem_toFinset, hl, List.mem_filter, decide_eq_true_iff] at hd
    obtain ⟨hd, hv⟩ := hd
    obtain ⟨e, he, hed⟩ := (diagList_spec hP hT hC d).1 hd
    refine ⟨e, ztood, hed⟩
    zuezl

  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = (l.toFinset : Set _).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (sortPair '' incident P v).ncard :=
        ncard_le_ncard hsub ((incident_finite hP v).image _)
    _ ≤ (incident P v).ncard := ncard_image_le (incident_finite hP v)
    _ ≤ 10 := card_incident_le hP v
end
end Chazelle.Final
namespace Chazelle.Core
@[expose] public section
open Chazelle.Machine (Stmt Exec)

/-! ## Registers and bands -/

/-- The allocator register. -/
def ALLOC : ℕ := 9999

/-- Hand-off: base address of the trapezoid table. -/
def REG_TRAP : ℕ := 9990
/-- Hand-off: length of the trapezoid table. -/
def REG_TRAPLEN : ℕ := 9991
/-- Hand-off: base address of the vertex-chord table. -/
def REG_CHORD : ℕ := 9992
/-- Hand-off: length of the vertex-chord table. -/
def REG_CHORDLEN : ℕ := 9993

/-- The band of a register. -/
def bandOf (r : ℕ) : ℕ := r / 10000

/-- Register `i` of band `b`. -/
def bandReg (b i : ℕ) : ℕ := 10000 * b + i
theorem bandOf_bandReg (b i : ℕ) (hi : i < 10000) : bandOf zttgm = b := by
  unfold bandOf bandReg
  omega
theorem bandOf_alloc : bandOf ALLOC = 0 := by_decide

/-! ## Frames and the judgement -/

/-- **The frame of a procedure** writing the bands `bands`: other registers (except `ALLOC`)
are unchanged, memory below the entry value of `ALLOC` is unchanged, nothing is emitted, and
`ALLOC` grows by at most the step count `k`. -/
def Frame (bands : Finset ℕ) (c c' : Config) (k : ℕ) : Prop :=
  ztgni ∧
    ztimw ∧
    zth ∧
    ztgo ∧
    c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

/-- **The specification judgement** of a structured statement. -/
def Meets (s : Stmt) (bands : Finset ℕ) (Pre : Polygon → ℕ → Config → Prop)
    (Post : Polygon → Config → Config → Prop) (cost : Polygon → Config → ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c : Config), WordsBounded W c → Pre P W c →
    c.nreg ALLOC + cost P c ≤ W →
      ∃ c' k, Exec P W s c c' k ∧ k ≤ cost P c ∧ Post P c c' ∧ Frame bands c c' k

/-- Frames compose. -/
theorem Frame.trans {B₁ B₂ : Finset ℕ} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : Frame B₁ c c₁ k₁)
    (h₂ : Frame B₂ c₁ c₂ k₂) : Frame (B₁ ∪ B₂) c c₂ ztbct := by
  zugj

  refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, o₂.trans o₁,
    a₁.trans a₂, by_omega⟩
  · simp_all
  · simp_all
  · grind
  grind

/-- A frame for fewer bands is a frame for more. -/
theorem Frame.mono {B B' : Finset ℕ} {c c' : Config} {k k' : ℕ} (h : Frame B c c' k)
    (hB : B ⊆ B') (hk : k ≤ k') : Frame B' c c' k' := by
  zugw
  exact ⟨by_grind, by_grind,
    m₁, rm₁, o₁, a₁, by_omega⟩

/-! ## Normal forms in memory -/

/-- **The memory layout of a normal form** at the handle `B` (design doc §3.4).  Header
`B … B+11`: `B` number of chords, `B+1` arcs, `B+2` regions, `B+3 … B+8` the bases
`CB, AB, RB, SB, LB, DB` of the chord, arc, region, sequence, list and decomposition areas,
`B+9` the root code, `B+10` the base `PB` of the leaf-parent table, `B+11` the number of
decomposition nodes.  Chord `i` at
`CB + 5 i`: `h, lp, rp, up, dn`.  Arc `j` at `AB + 5 j`: `reg, s.edge, s.hgt, e.edge, e.hgt`.
Region `r` at `RB + 5 r`: number of arcs, start of its arc list in the list area `LB`, number of
chords, start of its chord list, weight.  Arc-sequence table at `SB`.  Decomposition node `k` at
`DB + 3 k`: `par, lo, hi`.  Leaf parents at `PB`. -/
def NFAt (m : ℕ → ℕ) (B : ℕ) (N : NF) : Prop :=
  m B = N.chords.length ∧ m ztvf = N.arcs.length ∧ m zthb = N.regions.length ∧
    m (B + 9) = N.root ∧ m ztsvb = N.dec.length ∧
    (∀ i, i < N.chords.length →
      m (m ztkh + 5 * i) = (N.chord i).h ∧ m (m ztkh + 5 * i + 1) = (N.chord i).lp ∧
      m (m ztkh + 5 * i + 2) = (N.chord i).rp ∧ m (m ztkh + 5 * i + 3) = (N.chord i).up ∧
      m (m ztkh + 5 * i + 4) = (N.chord i).dn) ∧
    (∀ j, j < N.arcs.length →
      m (m ztow + 5 * j) = (N.arc j).reg ∧ m ztyjo = (N.arc j).s.edge ∧
      m ztyjp = (N.arc j).s.hgt ∧ m (m ztow + 5 * j + 3) = (N.arc j).e.edge ∧
      m (m ztow + 5 * j + 4) = (N.arc j).e.hgt) ∧
    (∀ r, r < N.regions.length →
      m (m zter + 5 * r) = (N.region r).arcs.length ∧
      m ztyjm = (N.region r).chords.length ∧
      m (m zter + 5 * r + 4) = (N.region r).wt ∧
      (∀ t, t < (N.region r).arcs.length →
        m (m ztlw + m ztxhc + t) = (N.region r).arcs.getD t 0) ∧
      (∀ t, t < (N.region r).chords.length →
        m ztbanz = (N.region r).chords.getD t 0)) ∧
    (∀ j, j < N.seq.length → m (m ztcsw + j) = N.seq.getD j 0) ∧
    (∀ k, k < N.dec.length →
      m (m ztjgp + 3 * k) = (N.dnode k).par ∧ m (m ztjgp + 3 * k + 1) = (N.dnode k).lo ∧
      m (m ztjgp + 3 * k + 2) = (N.dnode k).hi) ∧
    (∀ r, r < N.lpar.length → m (m (B + 10) + r) = N.lpar.getD r 0)

/-- **Robust memory facts**: `Φ` holds of every memory that agrees with `m` below `A`. -/
def Robust (A : ℕ) (m : ℕ → ℕ) (Φ : ztjx → Prop) : Prop :=
  ∀ m' : ℕ → ℕ, ztwv → Φ m'

/-- **The normal form at `B` is protected below `E`**: it can be read at `B` from every memory
agreeing with `m` below `E`, so it survives every later frame once `E` is at most the allocator.
(Review finding F3/R3: the earlier definition bounded the areas but not the per-region list
offsets, so it did not imply this.) -/
def NFWithin (m : ℕ → ℕ) (B E : ℕ) (N : NF) : Prop := Robust E m fun m' => NFAt m' B N
variable {A : ℕ} {m : ℕ → ℕ} {P : Polygon} {E E' : ℕ}
/-- A robust fact holds. -/
theorem Robust.holds {Φ : ztjx → Prop} (h : Robust A m Φ) : Φ m :=
  h m by_omega

/-- A robust fact survives any change of the memory at or above its bound. -/
theorem Robust.transport {m m' : ℕ → ℕ} {Φ : ztjx → Prop} (h : Robust A m Φ)
    (hm : ∀ a, a < A → m' a = m a) : Robust A m' Φ :=
  fun m'' h'' => h m'' by_simp_all

/-- A robust fact is robust for any larger bound. -/
theorem Robust.mono {A A' : ℕ} {m : ℕ → ℕ} {Φ : ztjx → Prop} (h : Robust A m Φ)
    (hA : A ≤ A') : Robust A' m Φ :=
  fun m'' h'' => h m'' by_grind

/-- A robust fact at the allocator survives a frame. -/
theorem Robust.frame {B : Finset ℕ} {c c' : Config} {k : ℕ} {Φ : ztjx → Prop}
    (h : Robust ztm c.nmem Φ) (hf : Frame B c c' k) :
    Robust ztdo c'.nmem Φ :=
  (h.transport fun a ha => hf.2.2.1 a ha).mono hf.2.2.2.2.2.1

/-- A normal form protected below `E` can be read. -/
theorem NFWithin.nfAt {B E : ℕ} {N : NF} (h : NFWithin m B E N) : NFAt m B N :=
  Robust.holds h

/-! ## Hosts and chains in memory -/

/-- **Host layout** at `B`: the number of items, then three words per item: kind (`0` run, `1`
vertex, `2` edge point) and two arguments. -/
def HostAt (m : ℕ → ℕ) (B : ℕ) (H : Host) : Prop :=
  m B = H.length ∧ ∀ i, i < H.length →
    match H.getD i ztmn with
    | .run a ℓ => m ztban = 0 ∧ m ztelu = a ∧ m ztgzt = ℓ
    | .pt (.vtx j) => m ztban = 1 ∧ m ztelu = j
    | .pt (.onEdge e h) => m ztban = 2 ∧ m ztelu = e ∧ m ztgzt = h

/-- **Chain descriptor** at `B`: host handle, start `s`, number of edges `m`, top index (relative
to the chain) and the orientation bit `sideBeta` (`1` = true).  The descriptor describes the chain
`C` of the host `H` realised in `Q`. -/
def ChainDescAt (m : ℕ → ℕ) (B : ℕ) (Q : Polygon) (H : Host) (C : Chain) : Prop :=
  HostAt m ztqtg H ∧ C.P = H.poly Q ∧ m ztvf = C.s ∧ m zthb = C.m ∧
    m ztkh = C.topIdx ∧ (m ztow = 1 ↔ C.sideBeta = true)

/-- **Model descriptor** at `B`: `m B = 0` and a chain descriptor at `B + 1` (chain model), or
`m B = 1` (interior model of `Q`) with the orientation bit `m (B + 1) = 1 ↔ LeftInside Q`, which
fixes the direction of the interior walk (review finding C3: without it, comparing keys on one
walk edge would cost `O(n)`). -/
def ModelDescAt (m : ℕ → ℕ) (B : ℕ) (Q : Polygon) (M : Model) : Prop :=
  (m B = 0 ∧ ∃ H C, ChainDescAt m ztvf Q H C ∧ M = chainModel C) ∨
    (m B = 1 ∧ (m ztvf = 1 ↔ Mountain.LeftInside Q) ∧ M = interiorModel Q)

/-! ## Well-formed descriptors (review findings C7, C8) -/

/-- **The word bound of the procedures that handle host curves**: `256 n + 16`.  A well-formed
host (`HostWF`, at most `64` items) has at most `64 n` points (`Host.pts_length_le`), so the index
arithmetic modulo the number `N` of host points (values `< 2 N`) stays within the word bound.
The phases get this bound from their budget `κ (n + 1)` (take `κ ≥ 272`).  (Finding S6: `+ 8`
rather than `+ 3`, since walk edges of a chain model of `≤ 64 n` host points reach `128 n + 4`.
Finding R-W1: the search of Lemma 3.2 adds two walk positions of a chain model, `< 2 (128 n + 7)`,
hence `256 n + 16`.) -/
def hostWords (n : ℕ) : ℕ := 256 * n + 16

/-- **A well-formed chain descriptor** at `B`, stored below `E` (findings C7, C8): the
descriptor words `B … B + 4` and the host layout lie below `E`; the host has at most `64` items
and is well formed (`HostWF`: runs and points in range); the start of the chain is below the
number of host points.  With `E` the allocator, the descriptor survives every later frame. -/
def ChainWF (P : Polygon) (E : ℕ) (m : ℕ → ℕ) (B : ℕ) : Prop :=
  B + 5 ≤ E ∧ ∀ H C, ChainDescAt m B zta H C →
    H.length ≤ 64 ∧ HostWF P.n H ∧ m B + 3 * H.length + 4 ≤ E ∧ C.s < C.P.n

/-- **A well-formed model descriptor** at `B`, stored below `E`: six words below `E`, and a
well-formed chain descriptor if it describes a chain model (finding C7: a handle near the word
bound could not be read; C8: host descriptors). -/
def ModelDescWF (P : Polygon) (E : ℕ) (m : ℕ → ℕ) (B : ℕ) : Prop :=
  B + 6 ≤ E ∧ (m B = 0 → ChainWF P E m ztvf)
theorem ChainWF.mono {m : ℕ → ℕ} {B : ℕ} (h : ChainWF P E m B)
    (hE : E ≤ E') : ChainWF P E' m B :=
  ⟨by have := h.1; omega, fun H C hC => by
    obtain ⟨h1, h2, h3, h4⟩ := h.2 H C hC
    grind⟩
theorem ModelDescWF.mono {m : ℕ → ℕ} {B : ℕ} (h : ModelDescWF P E m B)
    (hE : E ≤ E') : ModelDescWF P E' m B :=
  ⟨by have := h.1; omega, fun h0 => (h.2 h0).mono hE⟩

/-! ## The hand-off to the final stage -/

/-- The trapezoid table at `B`: four words per record (`left, right, top, bot`). -/
def TrapTableAt (m : ℕ → ℕ) (B : ℕ) (T : Final.TrapTable) : Prop :=
  ∀ i, i < T.length →
    m (B + 4 * i) = (T.getD i ztcor).left ∧ m (B + 4 * i + 1) = (T.getD i ztcor).right ∧
      m (B + 4 * i + 2) = (T.getD i ztcor).top ∧
      m (B + 4 * i + 3) = (T.getD i ztcor).bot

/-- The vertex-chord table at `B`: three words per record (`src`, direction bit (`1` = right),
`dst`). -/
def ChordTableAt (m : ℕ → ℕ) (B : ℕ) (Cs : List Final.ChordRec) : Prop :=
  ∀ i, i < Cs.length →
    m ztpvy = (Cs.getD i ztgnv).src ∧
      (m ztnje = 1 ↔ (Cs.getD i ztgnv).dir = true) ∧
      m ztnjf = (Cs.getD i ztgnv).dst

/-- **The precondition of the final stage**: valid tables for the geometry polygon `Q` in memory,
announced in the hand-off registers, below the allocator; nothing emitted yet. -/
def TablesReady (Q : Polygon) (c : Config) : Prop :=
  ∃ (T : Final.TrapTable) (Cs : List Final.ChordRec),
    Final.IsTrapTable Q T ∧ Final.IsVtxChordTable Q Cs ∧
    c.nreg REG_TRAPLEN = T.length ∧ TrapTableAt c.nmem (c.nreg REG_TRAP) T ∧
    c.nreg REG_CHORDLEN = Cs.length ∧ ChordTableAt c.nmem (c.nreg REG_CHORD) Cs ∧
    c.nreg REG_TRAP + 4 * T.length ≤ c.nreg ALLOC ∧
    c.nreg REG_CHORD + 3 * Cs.length ≤ c.nreg ALLOC ∧
    c.output = []
def CoreStageSpec : Prop :=
  ∃ (s : Stmt) (C K : ℕ), ∀ P : Polygon, P.Simple → ∀ W : ℕ, K * ztju ≤ W →
    ∃ c' k, Exec P W s initConfig c' k ∧ k ≤ C * ztju ∧ c'.nreg ALLOC ≤ C * ztju ∧
      ∃ Q : Polygon, ShearRel P Q ∧ Q.Simple ∧ TablesReady Q c'

/-- **The final stage** (visibility map to triangulation, [6], [11]; `Chazelle.Final`). -/
def FinalStageSpec : Prop :=
  ∃ (s : Stmt) (C K : ℕ), ∀ P Q : Polygon, P.Simple → Q.Simple → ShearRel P Q →
    ∀ (W : ℕ) (c : Config), WordsBounded W c → TablesReady Q c →
      c.nreg ALLOC + K * ztju ≤ W →
        ∃ c' k, Exec P W s c c' k ∧ k ≤ C * ztju ∧ Q.Triangulates c'.output

/-- `RunsWithin` is monotone in the step budget. -/
theorem runsWithin_mono {prog : Program} {P : Polygon} {W s s' : ℕ}
    {out : List Polygon.Triangle} (h : RunsWithin prog P W s out) (hs : s ≤ s') :
    RunsWithin prog P W s' out := by
  obtain ⟨k, hk, h1, h2⟩ := h
  exact ⟨k, hk.trans hs, h1, h2⟩

/-- **The final assembly.**  The two stage specifications and shear invariance give the target
theorem. -/
theorem linear_of_core (hcore : CoreStageSpec) (hfin : FinalStageSpec)
    (hsh : ShearInvarianceSpec) : LinearTimeTriangulation := by
  obtain ⟨s₁, C₁, K₁, h₁⟩ := hcore
  obtain ⟨s₂, C₂, K₂, h₂⟩ := hfin
  refine ⟨Machine.Stmt.compile (Stmt.seq s₁ s₂) 0 ++ [Instr.halt], C₁ + C₂ + 1, K₁ + C₁ + K₂ + 1,
    by omega, by_omega, ?_⟩
  intro P hP
  have hW : zthaz * ztju =
      K₁ * ztju + C₁ * ztju + K₂ * ztju + ztju := by_ring
  obtain ⟨c₁, k₁, e₁, hk₁, halloc, Q, hPQ, hQ, hready⟩ :=
    h₁ P hP ztbaae by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, htri⟩ := h₂ P Q hP hQ hPQ ztbaae c₁
    e₁.wb_right hready by_omega
  refine ⟨c₂.output, ?_, ?_⟩
  · have hr := Machine.runsWithin_of_exec ztsxa
    refine runsWithin_mono hr ?_
    grind
  · obtain ⟨ε, -, rfl, -⟩ := hPQ
    exact ((hsh ε P).2 _).1 htri
end
namespace Dec
@[expose] public section
open Relation Set Filter Topology
open Chazelle.Chain (TouchesIn regionsIn DualAdjIn)

/-- Two regions are joined by a chord record. -/
def RecAdj (N : NF) (a b : ℕ) : Prop :=
  ∃ i, i < N.nChords ∧ ((N.chord i).up = a ∧ (N.chord i).dn = b ∨ (N.chord i).up = b ∧ (N.chord i).dn = a)

/-- **The record tree** of a normal form, with degree cap `D`. -/
structure RecTree (N : NF) (D : ℕ) : Prop where
  ends_lt : ∀ i, i < N.nChords → (N.chord i).up < N.nRegions ∧ (N.chord i).dn < N.nRegions
  ends_ne : ∀ i, i < N.nChords → (N.chord i).up ≠ (N.chord i).dn
  lists : ∀ r, r < N.nRegions → ∀ i,
    i ∈ (N.region r).chords ↔ i < N.nChords ∧ ztgvh
  nodup : ∀ r, r < N.nRegions → (N.region r).chords.Nodup
  count : N.nRegions = N.nChords + 1
  conn : ∀ r s, r < N.nRegions → s < N.nRegions → ReflTransGen ztvda r s
  deg : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ D
theorem getD_of_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp_all
theorem chord_mem {N : NF} {i : ℕ} (hi : i < N.nChords) : N.chord i ∈ N.chords := by
  zudly
  rw [getD_of_lt hi]
  grind

/-- The region graph of a good model, with regions as intermediate nodes. -/
theorem regions_reach {M : Model} {Q : Polygon} {F : Set ztf} (hM : GoodModel M)
    (hF : M.ChordFamily Q F) {U V : Set Point} (hU : U ∈ M.regions F) (hV : V ∈ M.regions F) :
    ReflTransGen (DualAdjIn M.D F) U V := by
  zufgd

  zudhb

  zubh
section tree
variable {M : Model} {Q : Polygon} {N : NF} {D : ℕ}

/-- The regions of a chord record: the region above and the region below, distinct, and the only
regions the chord touches. -/
theorem chord_regions (hM : GoodModel M) (hN : IsNF M Q N) {reg : ℕ → Set Point}
    (hcorr : RegionCorr M Q N reg) (hsides : ChordSidesOK M Q N reg) {i : ℕ} (hi : i < N.nChords) :
    reg (N.chord i).up ≠ reg (N.chord i).dn ∧
      ∀ W ∈ M.regions ztdu, TouchesIn M.D ztdef W ↔
        W = reg (N.chord i).up ∨ W = reg (N.chord i).dn := by
  have hc : ztdjo := ztomd
  obtain ⟨U, V, hU, hV, hUV, hev, htouch⟩ := chordSides M Q ztdu hM hN.1 _ hc
  obtain ⟨z, ⟨hzc, hzD⟩, -⟩ := (htouch U hU).2 ztp
  obtain ⟨hup, hdn, hs⟩ := hsides i hi
  obtain ⟨ε₀, hε₀, hε⟩ := hs z hzc hzD
  have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ε₀ := by
    have : Set.Iio ε₀ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε₀)
    tauto
  have hev0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, ⟨hUV', hδε⟩, hδ0⟩ := ((hev z hzc hzD).and hev').and hev0 |>.exists
  obtain ⟨ha, hb⟩ := hε δ hδ0 hδε
  have hregU := hcorr.1 _ hup
  have hregV := hcorr.1 _ hdn
  have e1 : reg (N.chord i).up = U := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hregU hU with e | e
    · zulez
    grind
  have e2 : reg (N.chord i).dn = V := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hregV hV with e | e
    · zulez
    grind
  grind

/-- **The record tree of a valid normal form** of a good model with degree cap `D`. -/
theorem recTree_of (hM : GoodModel M) (hN : IsNF M Q N) (hD : M.DegLe ztdu D) :
    RecTree N D := by
  obtain ⟨hfam, hinj, -, reg, hcorr, hsides, -, hregs, -, -, -⟩ := id hN
  have hcr := fun i (hi : i < N.nChords) => chord_regions hM hN hcorr hsides hi
  have hregInj : ∀ a b, a < N.nRegions → b < N.nRegions → reg a = reg b → a = b := hcorr.2.1
  -- the touching regions of a chord, as indices
  have htouchIdx : ∀ i, i < N.nChords → ∀ r, r < N.nRegions →
      (TouchesIn M.D ztdef ztcz ↔ (N.chord i).up = r ∨ (N.chord i).dn = r) := by
    intro i hi r hr
    obtain ⟨hup, hdn, -⟩ := hsides i hi
    rw [(hcr i hi).2 _ ztjxq]
    grind
  have hlists : ∀ r, r < N.nRegions → ∀ i,
      i ∈ (N.region r).chords ↔ i < N.nChords ∧ ztgvh := by
    intro r hr i
    rw [((hregs r hr).1 i)]
    grind
  -- the chord map is injective and onto the family
  have hF : N.F M Q = ztdcz '' Set.Iio N.nChords := by
    zubcj
    constructor
    · zuod
      zubhg
      zuifc
      zunzn
    · zuin
      exact ztomd
  have hFcard : (N.F M Q).ncard = N.nChords := by
    have hio : Set.InjOn ztdcz (Set.Iio N.nChords) :=
      fun a ha b hb e => hinj a b ha hb e
    rw [hF, hio.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  have hRcard : ztyxv := by
    have : M.regions ztdu = reg '' Set.Iio N.nRegions := by
      zulge
      constructor
      · zulmt
        obtain ⟨r, hr, e⟩ := hcorr.2.2 U hU
        grind
      · zuoc
        exact hcorr.1 r hr
    have hio : Set.InjOn reg (Set.Iio N.nRegions) := fun a ha b hb e => hregInj a b ha hb e
    rw [this, hio.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  obtain ⟨-, hcount, -⟩ := regionTree M Q ztdu hM hfam
  refine ⟨fun i hi => ⟨(hsides i hi).1, (hsides i hi).2.1⟩,
    fun i hi e => (hcr i hi).1 ztdlt, hlists, fun r hr => (hregs r hr).2.1,
    by omega, ?_, ?_⟩
  · -- connectivity
    intro r s hr hs
    have hpath := regions_reach hM hfam ztjxq zttnh
    have key : ∀ W, ReflTransGen (DualAdjIn M.D ztdu) ztcz W → W ∈ M.regions ztdu →
        ∃ b, b < N.nRegions ∧ reg b = W ∧ ReflTransGen ztvda r b := by
      zulml
      induction hW with
      | refl => intro _; exact ⟨r, hr, rfl, ReflTransGen.refl⟩
      | tail hAB hBC ih =>
        rename_i B C
        zuhge
        obtain ⟨hB, hC, hne, c, hc, h1, h2⟩ := hBC
        obtain ⟨b, hb, rfl, hpb⟩ := ih hB
        obtain ⟨a, ha, rfl⟩ := hcorr.2.2 C hC
        zucyc
        zubhg
        have hci : ztiym := by zunzn
        rw [hci] at h1 h2
        have t1 := (htouchIdx i hi b hb).1 h1
        have t2 := (htouchIdx i hi a ha).1 h2
        have hab : b ≠ a := fun e => hne ztdlt
        refine ⟨a, ha, rfl, hpb.tail ztbfn⟩
        have hne' := (hcr i hi).1
        rcases t1 with e1 | e1 <;> rcases t2 with e2 | e2
        · omega
        · omega
        · omega
        · omega
    obtain ⟨b, hb, e, hp⟩ := key _ hpath zttnh
    grind
  · -- the degree
    zuz
    classical
    have hnd := (hregs r hr).2.1
    have hsub : ((N.region r).chords.toFinset.image fun i => (N.chord i).toSet M Q : Set ztf) ⊆
        {c | c ∈ N.F M Q ∧ TouchesIn M.D c ztcz} := by
      zung
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset] at hc
      grind
    have hfin : {c | c ∈ N.F M Q ∧ TouchesIn M.D c ztcz}.Finite :=
      hfam.1.subset fun c hc => hc.1
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd] at h1
    · exact h1.trans (hD _ ztjxq)
    · zukiz
      simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
      grind
