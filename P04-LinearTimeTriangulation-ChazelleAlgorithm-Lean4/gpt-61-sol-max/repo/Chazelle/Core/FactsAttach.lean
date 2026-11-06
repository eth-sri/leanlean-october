module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FactsTree

/-!
# WP-B: the walk next to an attachment (`AttachFaceSpec`, corrected)

The first version of `AttachFaceSpec` (without the hypothesis that `c` is the only chord of `F`
attached at the position) was false (review finding B2) when two chords of `F` are attached at the
same walk position (a walk vertex whose left sector contains both horizontal directions, e.g. the
outer side of a local minimum of a chain, with the two vertex chords going east and west): the
positions just before and just after that position face the regions *above* the two chords, and
the region on the far side of one chord does not touch the other.  `AttachFaceSpec` now has the
hypothesis; `AttachFaceSpecNC` is the same statement, `attachFaceNC`/`attachFace` prove it.
Without that hypothesis, `WalkAx.attach_face_regions` still gives two distinct regions faced just
after and just before the attachment, on the two sides of `c`.

Main ingredients: the gaps between consecutive cut keys (`exists_succ_gap`, `exists_pred_gap`),
the arcs of these gaps (`WalkAx.arc_of_gap`), the exit chord at the start of an arc
(`WalkAx.exists_exit_at_start`, mirror of `WalkAx.exists_exit_at_end`), and the split of the walk
by `c` (`WalkAx.split`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj)

/-- **Corrected `AttachFaceSpec`**: the conclusion of `AttachFaceSpec` for a chord that is the only
chord of `F` attached at the position. -/
def AttachFaceSpecNC : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    ∀ c ∈ F, ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      (∀ c' ∈ F, SideAttach M.W c' p t → c' = c) →
      ∃ U V, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
        Chazelle.Chain.TouchesIn M.D c U ∧ Chazelle.Chain.TouchesIn M.D c V ∧
        ∃ δ > (0 : ℝ), ∀ (p' : ℕ) (t' : ℝ), p' < M.W.n → 0 < t' → t' < 1 →
          ((0 < (p' : ℝ) + t' - (p + t) ∧ (p' : ℝ) + t' - (p + t) < δ) ∨
              (0 < (p' : ℝ) + t' + M.W.n - (p + t) ∧ (p' : ℝ) + t' + M.W.n - (p + t) < δ) →
            M.Faces p' t' U) ∧
          ((0 < (p + t) - ((p' : ℝ) + t') ∧ (p + t) - ((p' : ℝ) + t') < δ) ∨
              (0 < (p + t) + M.W.n - ((p' : ℝ) + t') ∧ (p + t) + M.W.n - ((p' : ℝ) + t') < δ) →
            M.Faces p' t' V)

/-! ## Cyclic facts -/

theorem cyc_sub_start {a b y k : ℝ} (hy : sideInArc a b y) (hk : ¬ sideInArc a b k)
    (hka : k ≠ a) : sideInArc a k y := by
  core_grind

theorem cyc_ext2 {l a b x y m : ℝ} (hla : l ≠ a) (hab : a ≠ b) (hx : sideInArc l a x)
    (hy : sideInArc a b y) (hl : ¬ sideInArc a b l) (hm1 : ¬ sideInArc l a m) (hma : m ≠ a)
    (hm2 : ¬ sideInArc a b m) : sideInArc l y x ∧ ¬ sideInArc l y m ∧ y ≠ m := by
  grind [sideInArc]

theorem cyc_after_delta {k r x n δ : ℝ} (hkr : k ≠ r) (hx0 : 0 ≤ x) (_hxn : x < n) (_hr0 : 0 ≤ r)
    (hrn : r < n) (hδ : δ ≤ if k < r then r - k else r + n - k)
    (h : (0 < x - k ∧ x - k < δ) ∨ (0 < x + n - k ∧ x + n - k < δ)) : sideInArc k r x := by
  core_grind

theorem cyc_before_delta {l k x n δ : ℝ} (hlk : l ≠ k) (_hx0 : 0 ≤ x) (hxn : x < n) (hl0 : 0 ≤ l)
    (_hln : l < n) (hδ : δ ≤ if l < k then k - l else k + n - l)
    (h : (0 < k - x ∧ k - x < δ) ∨ (0 < k + n - x ∧ k + n - x < δ)) : sideInArc l k x := by
  core_grind

section
variable {K : Set ℝ} (hK : K.Finite) {k k' : ℝ} (hk : k ∈ K) (hk' : k' ∈ K) (hne : k ≠ k')
include hK k' hk hk' hne
/-- The successor of an element of a finite set of at least two reals. -/
theorem exists_succ_gap : ∃ r ∈ K, r ≠ k ∧ ∀ m ∈ K, ¬ sideInArc k r m := by
  obtain ⟨m₀, hm₀, hmin⟩ := Set.exists_min_image K id hK ⟨k, hk⟩
  simp only [id] at hmin
  by_cases hA : ∃ m ∈ K, k < m
  · obtain ⟨r, ⟨hr, hkr⟩, hrm⟩ := Set.exists_min_image {m | m ∈ K ∧ k < m} id
      (hK.subset fun m hm => hm.1) (by obtain ⟨m, hm, hkm⟩ := hA; exact ⟨m, hm, hkm⟩)
    refine ⟨r, hr, ne_of_gt hkr, fun m hm hin => ?_⟩
    unfold sideInArc at hin
    rw [ite_eq_left_of_eq_true _ _ (eq_true hkr)] at hin
    have := hrm m ⟨hm, hin.1⟩
    grind
  · push Not at hA
    have hm₀k : m₀ ≠ k := by
      grind
    core_grind

/-- The predecessor of an element of a finite set of at least two reals. -/
theorem exists_pred_gap : ∃ l ∈ K, l ≠ k ∧ ∀ m ∈ K, ¬ sideInArc l k m := by
  obtain ⟨M₀, hM₀, hmax⟩ := Set.exists_max_image K id hK ⟨k, hk⟩
  simp only [id] at hmax
  by_cases hB : ∃ m ∈ K, m < k
  · obtain ⟨l, ⟨hl, hlk⟩, hlm⟩ := Set.exists_max_image {m | m ∈ K ∧ m < k} id
      (hK.subset fun m hm => hm.1) (by obtain ⟨m, hm, hmk⟩ := hB; exact ⟨m, hm, hmk⟩)
    refine ⟨l, hl, ne_of_lt hlk, fun m hm hin => ?_⟩
    unfold sideInArc at hin
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlk)] at hin
    have := hlm m ⟨hm, hin.2⟩
    grind
  · push Not at hB
    have hM₀k : M₀ ≠ k := by
      grind
    core_grind


end

namespace WalkAx

variable {M : Model}

section
variable (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
include hM hF hfin
/-- **The start of an arc carries an exit chord**: some chord of `F` touching `U` is attached at
the start key of every arc of `U` (mirror of `exists_exit_at_end`). -/
theorem exists_exit_at_start (hne : F.Nonempty) {U : Set Point} (hU : U ∈ M.regions F) {a b : ℝ}
    (harc : M.IsArc F U a b) :
    ∃ c ∈ {c | c ∈ F ∧ TouchesIn M.D c U}, ∃ p t, SideAttach M.W c p t ∧ a = p + t := by
  set T := {c | c ∈ F ∧ TouchesIn M.D c U} with hT
  have hTF : T ⊆ F := fun c hc => hc.1
  have hTfin : T.Finite := hfin.subset hTF
  have hsys := hM.sys F hF hfin
  have hK := hM.finite_cuts hF hfin
  obtain ⟨hcuta, hcutb, hab⟩ := arc_cuts hne harc
  have hfree := harc.2.2.2.2.2.1
  by_contra hno
  -- a position `y` inside the arc
  obtain ⟨py, hpy, ty, hty, hyin, hycut, hyf⟩ := exists_pos_in_arc hne harc
  -- the gap before `a` and a position `x` in it
  obtain ⟨l, hl, hla, hlgap⟩ := exists_pred_gap hK hcuta hcutb hab
  obtain ⟨V, hV, harcV⟩ := hM.arc_of_gap hF hfin hl hcuta hla (fun k hk hc => hlgap k hc hk)
  obtain ⟨px, hpx, tx, htx, hxin, hxcut, hxV⟩ := exists_pos_in_arc hne harcV
  -- `V = U`
  obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
  obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hU
  have hVfree : V ⊆ freeIn M.D T :=
    (Chazelle.Chain.regionsIn_subset hV).trans (Chazelle.Chain.freeIn_anti M.D hTF)
  set VT := connectedComponentIn (freeIn M.D T) v with hVT
  have hVVT : V ⊆ VT :=
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVfree
  have hVTr : VT ∈ M.regions T := ⟨v, hVfree hv, rfl⟩
  have hUT : U = connectedComponentIn (freeIn M.D T) u := region_of_exits hsys hU hu
  have hUTr : U ∈ M.regions T := by
    rw [hUT]
    exact ⟨u, ((Chazelle.Chain.regionsIn_subset hU).trans
      (Chazelle.Chain.freeIn_anti M.D hTF)) hu, rfl⟩
  have hxVT : M.Faces px tx VT := hxV.mono fun δ h => hVVT h
  have hTcut : ∀ k, M.IsCut T k → M.IsCut F k := fun k ⟨c, hc, h⟩ => ⟨c, hc.1, h⟩
  have hlb : ¬ sideInArc a b l := fun h => hfree l h hl
  have hsame : VT = U := by
    refine (hM.eq_iff_not_separates (fun c hc => hF hc.1) hTfin hVTr hUTr hpx hpy htx
      hty (fun h => hxcut (hTcut _ h)) (fun h => hycut (hTcut _ h)) hxVT hyf).2 ?_
    rintro c hc ⟨pa', pb', ta', tb', hA, hB, hAB, hiff⟩
    have hkey : ∀ m, M.IsCut T m → ¬ sideInArc l a m ∧ m ≠ a ∧ ¬ sideInArc a b m := by
      intro m hm
      refine ⟨fun h => hlgap m (hTcut m hm) h, ?_, fun h => hfree m h (hTcut m hm)⟩
      rintro rfl
      obtain ⟨c, hc, p, t, h1, h2⟩ := hm
      grind
    have kA := hkey _ ⟨c, hc, pa', ta', hA, rfl⟩
    have kB := hkey _ ⟨c, hc, pb', tb', hB, rfl⟩
    obtain ⟨hx', hA', hyA⟩ := cyc_ext2 hla hab hxin hyin hlb kA.1 kA.2.1 kA.2.2
    obtain ⟨-, hB', hyB⟩ := cyc_ext2 hla hab hxin hyin hlb kB.1 kB.2.1 kB.2.2
    have h := cyc_nosep hx' hA' hB' hyA hyB (key_ne_of_pt_ne hA hB hAB)
    grind
  
  have hVeq : V = U := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hV hU with h | h
    · exact h
    grind
  rw [hVeq] at hxV
  -- the chord attached at `a` separates `x` from `y`
  obtain ⟨c₀, hc₀, pa, ta, hA₀, ha⟩ := hcuta
  obtain ⟨pb₀, tb₀, hB₀, hB₀ne⟩ := hM.other_attach (hF hc₀) hA₀
  obtain ⟨K₁, K₂, hne', ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ :=
    hM.split (hF hc₀) hA₀ hB₀ (Ne.symm hB₀ne)
  have hkB : M.IsCut F (pb₀ + tb₀) := ⟨c₀, hc₀, pb₀, tb₀, hB₀, rfl⟩
  have hkne : (pb₀ : ℝ) + tb₀ ≠ a := by
    rw [ha]; exact key_ne_of_pt_ne hB₀ hA₀ hB₀ne
  have hyA : sideInArc (pa + ta) (pb₀ + tb₀) (py + ty) := by
    rw [← ha]; exact cyc_sub_start hyin (fun h => hfree _ h hkB) hkne
  have hxA : sideInArc (pb₀ + tb₀) (pa + ta) (px + tx) := by
    rw [← ha]; exact cyc_sub hxin (fun h => hlgap _ hkB h) hkne
  have hU1 := hM.region_subset_of_sector hc₀ hU hpy hty hyf (hK₁ py hpy ty hty.1.le hty.2 hyA)
  have hU2 := hM.region_subset_of_sector hc₀ hU hpx htx hxV (hK₂ px hpx tx htx.1.le htx.2 hxA)
  exact hne' ((connectedComponentIn_eq (hU1 hu)).trans (connectedComponentIn_eq (hU2 hu)).symm)

/-- **The walk next to an attachment.**  For a chord `c ∈ F` attached at `A = (p, t)` (key `k`),
the keys of the cut-free gap after `k` are an arc of a region `U`, those of the gap before `k` an
arc of a region `V`, `U ≠ V`, and `U` (resp. `V`) touches `c` when `c` is the only chord of `F`
attached at `A`. -/
theorem attach_face
    {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t) :
    ∃ U V l r, U ∈ M.regions F ∧ V ∈ M.regions F ∧ U ≠ V ∧
      M.IsArc F U (p + t) r ∧ M.IsArc F V l (p + t) ∧
      ((∀ c' ∈ F, SideAttach M.W c' p t → c' = c) →
        TouchesIn M.D c U ∧ TouchesIn M.D c V) := by
  have hne : F.Nonempty := ⟨c, hc⟩
  have hK := hM.finite_cuts hF hfin
  have hk : M.IsCut F (p + t) := ⟨c, hc, p, t, hA, rfl⟩
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hF hc) hA
  have hkB : M.IsCut F (pb + tb) := ⟨c, hc, pb, tb, hB, rfl⟩
  have hkne : (p : ℝ) + t ≠ pb + tb := key_ne_of_pt_ne hA hB (Ne.symm hBne)
  obtain ⟨r, hr, hrk, hrgap⟩ := exists_succ_gap hK hk hkB hkne
  obtain ⟨l, hl, hlk, hlgap⟩ := exists_pred_gap hK hk hkB hkne
  obtain ⟨U, hU, harcU⟩ := hM.arc_of_gap hF hfin hk hr (Ne.symm hrk)
    (fun m hm hc => hrgap m hc hm)
  obtain ⟨V, hV, harcV⟩ := hM.arc_of_gap hF hfin hl hk hlk (fun m hm hc => hlgap m hc hm)
  refine ⟨U, V, l, r, hU, hV, ?_, harcU, harcV, fun hsole => ⟨?_, ?_⟩⟩
  · -- the two sides of `c`
    intro hUV
    obtain ⟨K₁, K₂, hne', ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hc) hA hB (Ne.symm hBne)
    obtain ⟨py, hpy, ty, hty, hyin, -, hyf⟩ := exists_pos_in_arc hne harcU
    obtain ⟨px, hpx, tx, htx, hxin, -, hxf⟩ := exists_pos_in_arc hne harcV
    have hyA : sideInArc (p + t) (pb + tb) (py + ty) :=
      cyc_sub_start hyin (fun h => hrgap _ hkB h) (Ne.symm hkne)
    have hxA : sideInArc (pb + tb) (p + t) (px + tx) :=
      cyc_sub hxin (fun h => hlgap _ hkB h) (Ne.symm hkne)
    have hU1 := hM.region_subset_of_sector hc hU hpy hty hyf (hK₁ py hpy ty hty.1.le hty.2 hyA)
    rw [hUV] at hU1
    have hU2 := hM.region_subset_of_sector hc hV hpx htx hxf (hK₂ px hpx tx htx.1.le htx.2 hxA)
    obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
    exact hne' ((connectedComponentIn_eq (hU1 hv)).trans (connectedComponentIn_eq (hU2 hv)).symm)
  · obtain ⟨c', hc', p', t', hA', hk'⟩ := hM.exists_exit_at_start hF hfin hne hU harcU
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA'.2.1 hA'.2.2.1 hA.2.1 hA.2.2.1 hk'.symm
    grind
  · obtain ⟨c', hc', p', t', hA', hk'⟩ := hM.exists_exit_at_end hF hfin hne hV harcV
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA'.2.1 hA'.2.2.1 hA.2.1 hA.2.2.1 hk'.symm
    grind


end

end WalkAx

/-- **WP-B: the walk next to an attachment** (`AttachFaceSpec` for a chord alone at its
position). -/
theorem attachFaceNC : AttachFaceSpecNC := by
  intro M Q F hM hF c hc p t hA hsole
  have hW := walkAx_of_goodModel hM
  obtain ⟨U, V, l, r, hU, hV, hUV, harcU, harcV, htouch⟩ :=
    hW.attach_face hF.2.1 hF.1 hc hA
  obtain ⟨hcU, hcV⟩ := htouch hsole
  have hk0 : (0 : ℝ) ≤ p + t := by have := hA.2.1; positivity
  have hkn : (p : ℝ) + t < M.W.n := by
    have : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hA.1
    linarith [hA.2.2.1]
  obtain ⟨hr0, hrn⟩ := WalkAx.cut_bounds (harcU.2.2.2.2.1.resolve_right (fun h => by
    simp_all)).2.1
  obtain ⟨hl0, hln⟩ := WalkAx.cut_bounds (harcV.2.2.2.2.1.resolve_right (fun h => by
    simp_all)).1
  have hkr : (p : ℝ) + t ≠ r := (harcU.2.2.2.2.1.resolve_right (fun h => by
    simp_all)).2.2
  have hlk : l ≠ (p : ℝ) + t := (harcV.2.2.2.2.1.resolve_right (fun h => by
    simp_all)).2.2
  set δ₁ : ℝ := if (p : ℝ) + t < r then r - (p + t) else r + M.W.n - (p + t) with hδ₁
  set δ₂ : ℝ := if l < (p : ℝ) + t then (p + t) - l else (p + t) + M.W.n - l with hδ₂
  have hδ₁0 : 0 < δ₁ := by
    grind
  have hδ₂0 : 0 < δ₂ := by
    grind
  refine ⟨U, V, hU, hV, hUV, hcU, hcV, min δ₁ δ₂, lt_min hδ₁0 hδ₂0,
    fun p' t' hp' ht0 ht1 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hx0 : (0 : ℝ) ≤ p' + t' := by positivity
    have hxn : (p' : ℝ) + t' < M.W.n := by
      have : (p' : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp'
      linarith
    have hin := cyc_after_delta hkr hx0 hxn hr0 hrn (min_le_left δ₁ δ₂) (by
      omega)
    exact harcU.2.2.2.2.2.2 p' t' hp' ht0 ht1 hin
  · have hx0 : (0 : ℝ) ≤ p' + t' := by positivity
    have hxn : (p' : ℝ) + t' < M.W.n := by
      have : (p' : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp'
      linarith
    have hin := cyc_before_delta hlk hx0 hxn hl0 hln (min_le_right δ₁ δ₂) (by
      omega)
    exact harcV.2.2.2.2.2.2 p' t' hp' ht0 ht1 hin

end

end Chazelle.Core

namespace Chazelle.Core

@[expose] public section

/-- **WP-B: the cut structure** (`CutStructureSpec`, part 3 for non-cut positions). -/
theorem cutStructure : CutStructureSpec := cutStructureNC

end

end Chazelle.Core
