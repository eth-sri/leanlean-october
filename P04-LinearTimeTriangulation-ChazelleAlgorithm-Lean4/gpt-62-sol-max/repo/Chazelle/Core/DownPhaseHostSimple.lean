module

public import Chazelle.Core.DownPhaseHostGap
public import Chazelle.Core.WalkEmbed
public import Mathlib.Data.List.GetD

/-!
# WP-M (H1, part 4): the host polygon of a region of an interior submap is simple

For a simple polygon `Q`, a nonempty chord family `F` of the interior model `I = interiorModel Q`
and a region `U` of `F`, the **host polygon** `regionHost Q F U` lists the walk points of the
host keys of `U` (`DownHost.hostKeys`) in increasing key order.  It is the boundary `R*` of `U`
(arcs of `U` and its exit chords).  **`regionHost_simple`: it is a simple polygon** (obligation
H1 of `docs/design-downphase.md`).  No distinct-heights hypothesis is needed.

Proof: `DownHost.KeyHost.simple` (part 1) with the edges classified by `DownHost.gap` (part 3):
an edge whose key interval lies in an arc of `U` contains no walk vertex strictly inside, so it
is a piece of one walk edge (`arcEdge_of_noVertex`); otherwise it is a chord of `F`.  Two chord
edges are distinct chords (their key pairs differ, `N ≥ 3`), hence disjoint in the interior.  At
least three host keys exist (`three_le`): an arc of `U` has two, and the exit chord at its end
has a third end unless the arc lies in one walk edge, which the chord would then overlap.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideClean SideSectorIn ChordSystem
  freeIn regionsIn sideLeft_edge TouchesIn)
open Chazelle.Jordan (offset nrm sqLen sqLen_pos det_offset eventually_offset_mem convex_det_pos)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)

variable {M : Model}

/-! ## Walk points of keys -/

theorem lerp_lerp (u v : Point) (t t' s : ℝ) :
    lerp (lerp u v t) (lerp u v t') s = lerp u v (t + s * (t' - t)) := by
  apply point_ext <;> simp [lerp] <;> ring

/-- The walk point of a key `x ∈ [0, n)`: position `(⌊x⌋, x - ⌊x⌋)`. -/
noncomputable def hostPt (W : Polygon) (x : ℝ) : Point := sidePt W ⌊x⌋₊ (x - ⌊x⌋₊)

theorem floor_add {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : ⌊(p : ℝ) + t⌋₊ = p := by
  rw [Nat.floor_eq_iff (by positivity)]
  exact ⟨by linarith, by linarith⟩

theorem hostPt_eq (W : Polygon) {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    hostPt W (p + t) = sidePt W p t := by
  simp [hostPt, floor_add ht ht1]

theorem sidePt_one (W : Polygon) (p : ℕ) : sidePt W p 1 = W.vtx ((p + 1) % W.n) := by
  simp [sidePt]

/-- **An arc edge**: two keys `a ≠ b` with no walk vertex key strictly between them (cyclically)
span a piece of one walk edge, all of whose points are walk points with keys in the closed
interval from `a` to `b`. -/
theorem arcEdge_of_noVertex (W : Polygon) {a b : ℝ} (ha0 : 0 ≤ a) (han : a < W.n) (hb0 : 0 ≤ b)
    (hbn : b < W.n) (_hab : a ≠ b) (hnv : ∀ k : ℕ, k < W.n → ¬ sideInArc a b k) :
    ∀ z ∈ Chazelle.segment (hostPt W a) (hostPt W b), ∃ p, p < W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      z = sidePt W p t ∧ (if a < b then a ≤ p + t ∧ p + t ≤ b else a ≤ p + t ∨ p + t ≤ b) := by
  set p := ⌊a⌋₊ with hpdef
  have hp := Nat.floor_le ha0
  have hp1 := Nat.lt_floor_add_one a
  have hpn : p < W.n := by
    have := lt_of_le_of_lt hp han
    exact_mod_cast this
  have hA : hostPt W a = sidePt W p (a - p) := rfl
  -- the end `b` on the same walk edge `p`
  obtain ⟨t'', ht''a, ht''1, hB, hkey⟩ : ∃ t'' : ℝ, a - p < t'' ∧ t'' ≤ 1 ∧
      hostPt W b = sidePt W p t'' ∧
      (if a < b then b = p + t'' else b = 0 ∧ p + 1 = W.n ∧ t'' = 1) := by
    by_cases hlt : a < b
    · have hbp : b ≤ p + 1 := by
        by_contra h
        push Not at h
        have hk : p + 1 < W.n := by
          have : ((p + 1 : ℕ) : ℝ) < W.n := by push_cast; linarith
          exact_mod_cast this
        apply hnv (p + 1) hk
        unfold sideInArc; rw [ite_eq_left hlt]; push_cast; exact ⟨hp1, h⟩
      refine ⟨b - p, by linarith, by linarith, ?_, by rw [ite_eq_left hlt]; ring⟩
      rcases hbp.lt_or_eq with hbp | hbp
      · have := hostPt_eq W (p := p) (t := b - p) (by linarith) (by linarith)
        rwa [show (p : ℝ) + (b - p) = b by ring] at this
      · have hk : p + 1 < W.n := by
          have : ((p + 1 : ℕ) : ℝ) < W.n := by push_cast; linarith
          exact_mod_cast this
        have e : b = ((p + 1 : ℕ) : ℝ) + 0 := by push_cast; linarith
        rw [e, hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero,
          show ((p + 1 : ℕ) : ℝ) + 0 - p = 1 by push_cast; ring, sidePt_one,
          Nat.mod_eq_of_lt hk]
    · have hb0' : b = 0 := by
        by_contra h
        have hbpos := lt_of_le_of_ne hb0 (Ne.symm h)
        apply hnv 0 (by omega)
        unfold sideInArc; rw [ite_eq_right hlt]; right; simpa using hbpos
      have hpn1 : p + 1 = W.n := by
        by_contra h
        have hk : p + 1 < W.n := by omega
        apply hnv (p + 1) hk
        unfold sideInArc; rw [ite_eq_right hlt]; left; push_cast; exact hp1
      refine ⟨1, by linarith, le_rfl, ?_, by simp_all⟩
      rw [hb0', show (0 : ℝ) = ((0 : ℕ) : ℝ) + 0 by simp, hostPt_eq W le_rfl one_pos,
        Chazelle.Chain.sidePt_zero, sidePt_one, hpn1, Nat.mod_self]
  -- the points of the segment
  intro z hz
  rw [hA, hB] at hz
  obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hz
  have hlerp : lerp (sidePt W p (a - p)) (sidePt W p t'') s =
      sidePt W p (a - p + s * (t'' - (a - p))) := lerp_lerp _ _ _ _ _
  rw [hlerp]
  set u := a - p + s * (t'' - (a - p)) with hu
  have hu0 : a - p ≤ u := by nlinarith
  have hu1 : u ≤ t'' := by nlinarith
  rcases (hu1.trans ht''1).lt_or_eq with hlt1 | heq1
  · refine ⟨p, hpn, u, by linarith, hlt1, rfl, ?_⟩
    split_ifs at hkey ⊢ with hab'
    · rw [hkey]; constructor <;> linarith
    · left; linarith
  · have ht1 := le_antisymm ht''1 (heq1 ▸ hu1)
    refine ⟨(p + 1) % W.n, Nat.mod_lt _ (by omega), 0, le_rfl, one_pos, ?_, ?_⟩
    · rw [heq1, sidePt_one, Chazelle.Chain.sidePt_zero]
    · split_ifs at hkey ⊢ with hab'
      · have hk : p + 1 < W.n := by
          have : ((p + 1 : ℕ) : ℝ) < W.n := by push_cast; linarith
          exact_mod_cast this
        rw [Nat.mod_eq_of_lt hk, hkey, ht1]; push_cast; constructor <;> linarith
      simp [hkey.2.1, Nat.mod_self, hkey.1]

/-! ## Sorted keys -/

/-- The host keys of `U` in increasing order. -/
noncomputable def hostKeyList (M : Model) (F : Set (Set Point)) (U : Set Point) : List ℝ := by
  classical
  exact if h : (hostKeys M F U).Finite then h.toFinset.sort (· ≤ ·) else []

/-- **The host polygon of the region `U`**: the walk points of its host keys, in increasing
key order. -/
noncomputable def hostPts (M : Model) (F : Set (Set Point)) (U : Set Point) : List Point :=
  (hostKeyList M F U).map (hostPt M.W)

theorem hostKeyList_eq {F : Set (Set Point)} {U : Set Point} (h : (hostKeys M F U).Finite) :
    hostKeyList M F U = h.toFinset.sort (· ≤ ·) := by
  classical
  unfold hostKeyList; rw [dite_eq_left h]

/-- A strictly sorted list: no element lies strictly (cyclically) between two consecutive
entries. -/
theorem sorted_gap {L : List ℝ} (hmono : ∀ i j, i < j → j < L.length → L.getD i 0 < L.getD j 0)
    (h2 : 2 ≤ L.length) {i : ℕ} (hi : i < L.length) {x : ℝ} (hx : x ∈ L) :
    ¬ sideInArc (L.getD i 0) (L.getD ((i + 1) % L.length) 0) x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hxj : L[j] = L.getD j 0 := (List.getD_eq_getElem _ _ hj).symm
  rw [hxj]
  have hle : ∀ a b, a < L.length → b < L.length → L.getD a 0 < L.getD b 0 → a < b := by
    intro a b ha hb h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | rfl
    · exact lt_asymm h (hmono b a h'' ha)
    · exact lt_irrefl _ h
  unfold sideInArc
  by_cases hi1 : i + 1 < L.length
  · rw [Nat.mod_eq_of_lt hi1, ite_eq_left (hmono i (i + 1) (by omega) hi1)]
    rintro ⟨h1, h2'⟩
    have := hle i j hi hj h1
    have := hle j (i + 1) hj hi1 h2'
    omega
  · have e : (i + 1) % L.length = 0 := by rw [show i + 1 = L.length by omega, Nat.mod_self]
    rw [e, ite_eq_right (not_lt.2 (hmono 0 i (by omega) hi).le)]
    rintro (h1 | h1)
    · have := hle i j hi hj h1; omega
    · have := hle j 0 hj (by omega) h1; omega

/-- Index arithmetic: with at least three entries, two distinct consecutive pairs of a cyclic
list are distinct as sets. -/
theorem pair_ne {N i j : ℕ} (hN : 3 ≤ N) (hi : i < N) (hj : j < N) (hij : i ≠ j)
    (h1 : j = i ∨ j = (i + 1) % N) (h2 : (j + 1) % N = i ∨ (j + 1) % N = (i + 1) % N) : False := by
  have hs : ∀ k, k < N → (k + 1 < N ∧ (k + 1) % N = k + 1) ∨ (k + 1 = N ∧ (k + 1) % N = 0) := by
    intro k hk
    rcases Nat.lt_or_ge (k + 1) N with h | h
    · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
    simp [show k + 1 = N by omega, Nat.mod_self]
  rcases hs i hi with ⟨hi1, ei⟩ | ⟨hi1, ei⟩ <;> rcases hs j hj with ⟨hj1, ej⟩ | ⟨hj1, ej⟩ <;>
    rw [ei] at h1 h2 <;> rw [ej] at h2 <;> omega

/-! ## The host polygon of a region of the interior model -/

variable {Q : Polygon} {F : Set (Set Point)} {U : Set Point}

/-- Attachment keys of a chord are the keys of its two attachments. -/
theorem attach_key_cases (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb pc : ℕ}
    {ta tb tc : ℝ} (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (hC : SideAttach M.W c pc tc) :
    (pc : ℝ) + tc = pa + ta ∨ (pc : ℝ) + tc = pb + tb := by
  obtain ⟨e, -, -, -, -, -, hother⟩ := hM.attach_other_end hc hA
  by_cases h : sidePt M.W pc tc = sidePt M.W pa ta
  · obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hC hA h
    exact Or.inl rfl
  · have h1 := hother pc tc hC h
    have h2 := hother pb tb hB (fun h' => hAB h'.symm)
    obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hC hB (h1.trans h2.symm)
    exact Or.inr rfl

/-- **At least three host keys.** -/
theorem three_le (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q F) (hne : F.Nonempty)
    (hU : U ∈ (interiorModel Q).regions F) :
    ∃ x ∈ hostKeys (interiorModel Q) F U, ∃ y ∈ hostKeys (interiorModel Q) F U,
      ∃ z ∈ hostKeys (interiorModel Q) F U, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  set M := interiorModel Q with hMdef
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hGM : GoodModel M := Or.inr ⟨Q, hQ, rfl⟩
  obtain ⟨p, t, hp, ht0, ht1, hcut, hfac⟩ := hM.exists_faces_nc hF hfin hU
  obtain ⟨X, hX, l, r, harc, hin⟩ :=
    WalkEmbed.exists_arc_around hGM hFam (by positivity) hcut
  have hXU : X = U := WalkAx.faces_unique hX hU (harc.2.2.2.2.2.2 p t hp ht0 ht1 hin) hfac
  subst hXU
  have hl : l ∈ hostKeys M F X := by
    obtain ⟨c, ⟨hc, ht⟩, p', t', hA, h⟩ := hM.exists_exit_at_start hF hfin hne hU harc
    exact Or.inl ⟨c, hc, ht, p', t', hA, h⟩
  obtain ⟨c, ⟨hc, htc⟩, p₂, t₂, hA₂, hr⟩ := hM.exists_exit_at_end hF hfin hne hU harc
  have hrk : r ∈ hostKeys M F X := Or.inl ⟨c, hc, htc, p₂, t₂, hA₂, hr⟩
  have hlr : l ≠ r := (WalkAx.arc_cuts hne harc).2.2
  by_cases hmid : ∃ x ∈ hostKeys M F X, sideInArc l r x
  · obtain ⟨x, hx, hxin⟩ := hmid
    exact ⟨l, hl, r, hrk, x, hx, hlr, fun h => not_sideInArc_left l r (h ▸ hxin),
      fun h => not_sideInArc_right l r (h ▸ hxin)⟩
  push Not at hmid
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hF hc) hA₂
  have hf : (pb : ℝ) + tb ∈ hostKeys M F X := Or.inl ⟨c, hc, htc, pb, tb, hB, rfl⟩
  have hfr := WalkAx.key_ne_of_pt_ne hB hA₂ hBne
  rw [← hr] at hfr
  by_cases hfl : (pb : ℝ) + tb = l
  · exfalso
    -- the arc lies in one walk edge, and the chord `c` would overlap it
    have hb : 0 ≤ l ∧ l < M.W.n ∧ 0 ≤ r ∧ r < M.W.n :=
      ⟨harc.1, harc.2.1, harc.2.2.1, harc.2.2.2.1⟩
    have hnv : ∀ k : ℕ, k < M.W.n → ¬ sideInArc l r k := fun k hk hkin =>
      hmid k (Or.inr ⟨k, hk, rfl, l, r, harc, hkin⟩) hkin
    have hseg := arcEdge_of_noVertex M.W hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hlr hnv
    obtain ⟨-, -, hopen, -, -⟩ := hM.attach_seg (hF hc) hA₂ hB (fun h => hBne h.symm)
    have hmidD := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
    have hPr : sidePt M.W p₂ t₂ = hostPt M.W r := by rw [hr, hostPt_eq M.W hA₂.2.1 hA₂.2.2.1]
    have hPl : sidePt M.W pb tb = hostPt M.W l := by rw [← hfl, hostPt_eq M.W hB.2.1 hB.2.2.1]
    rw [hPr, hPl] at hmidD
    have hmem : lerp (hostPt M.W r) (hostPt M.W l) (1 / 2) ∈
        Chazelle.segment (hostPt M.W l) (hostPt M.W r) := by
      rw [Chazelle.Geometry.segment_comm]
      exact lerp_mem_segment _ _ (by norm_num) (by norm_num)
    obtain ⟨q, hq, τ, hτ0, hτ1, hzq, -⟩ := hseg _ hmem
    have hbd := sidePt_mem_boundary hq hτ0 hτ1.le
    rw [← hzq] at hbd
    have hWb : M.W.boundary = Q.boundary := (FactsInterior.interiorWalk_spec hQ).2.1
    rw [hWb] at hbd
    exact hmidD.2 hbd
  · exact ⟨l, hl, r, hrk, _, hf, hlr, Ne.symm hfl, Ne.symm hfr⟩

/-- **H1: the host polygon of a region of an interior submap is simple.**  For a simple polygon
`Q`, a nonempty chord family `F` of the interior model and a region `U` of `F`, the walk points
of the host keys of `U`, in increasing key order, form a simple polygon (the boundary `R*` of
`U`). -/
theorem hostPts_simple (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q F)
    (hne : F.Nonempty) (hU : U ∈ (interiorModel Q).regions F) :
    (⟨hostPts (interiorModel Q) F U⟩ : Polygon).Simple := by
  set M := interiorModel Q with hMdef
  have hM := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hWspec := FactsInterior.interiorWalk_spec hQ
  have hS := hostKeys_finite (U := U) hM hF hfin
  set L := hostKeyList M F U with hLdef
  have hL : L = hS.toFinset.sort (· ≤ ·) := hostKeyList_eq hS
  have hmemL : ∀ x, x ∈ L ↔ x ∈ hostKeys M F U := by
    intro x; rw [hL, Finset.mem_sort, Set.Finite.mem_toFinset]
  have hsorted : L.Pairwise (· ≤ ·) := by rw [hL]; exact Finset.pairwise_sort _ _
  have hnodup : L.Nodup := by rw [hL]; exact Finset.sort_nodup _ _
  set N := L.length with hN
  have hmono : ∀ i j, i < j → j < N → L.getD i 0 < L.getD j 0 := by
    intro i j hij hj
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
    refine lt_of_le_of_ne (List.pairwise_iff_getElem.1 hsorted i j (by omega) hj hij) ?_
    intro h
    have := (List.Nodup.getElem_inj_iff hnodup).1 h
    omega
  have hN3 : 3 ≤ N := by
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := three_le hQ hFam hne hU
    rw [hN, hL, Finset.length_sort]
    exact Finset.two_lt_card.2 ⟨x, by simpa using hx, y, by simpa using hy, z, by simpa using hz,
      hxy, hxz, hyz⟩
  set κ : ℕ → ℝ := fun i => L.getD i 0 with hκ
  have hinj : ∀ i j, i < N → j < N → κ i = κ j → i = j := by
    intro i j hi hj h
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h' | h'
    · exact absurd h (hmono i j h' hj).ne
    · exact absurd h.symm (hmono j i h' hi).ne
  have hκmem : ∀ i, i < N → κ i ∈ hostKeys M F U := by
    intro i hi
    rw [← hmemL]; simp only [hκ]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hsucc : ∀ i, i < N → (i + 1) % N < N := fun i _ => Nat.mod_lt _ (by omega)
  have hVlen : (hostPts M F U).length = N := by simp [hostPts, hLdef, hN]
  have hVget : ∀ i, i < N → (hostPts M F U).getD i (0, 0) = hostPt M.W (κ i) := by
    intro i hi
    have hi' : i < (hostPts M F U).length := by rwa [hVlen]
    rw [List.getD_eq_getElem _ _ hi']
    simp only [hostPts, List.getElem_map, hκ]
    rw [List.getD_eq_getElem _ _ hi]
  have hWb : M.W.boundary = Q.boundary := hWspec.2.1
  have hbd : ∀ z ∈ M.D, z ∉ M.W.boundary := by
    intro z hz hzb; rw [hWb] at hzb; exact hz.2 hzb
  -- the classification of the edges
  have hcases : ∀ i, i < N →
      (∀ z ∈ Chazelle.segment (hostPt M.W (κ i)) (hostPt M.W (κ ((i + 1) % N))),
        ∃ p, p < M.W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt M.W p t ∧
          InKeyIv κ N i ((p : ℝ) + t)) ∨
      (∃ c ∈ F, c = Chazelle.segment (hostPt M.W (κ i)) (hostPt M.W (κ ((i + 1) % N))) ∧
        (∀ s ∈ Ioo (0 : ℝ) 1,
          lerp (hostPt M.W (κ i)) (hostPt M.W (κ ((i + 1) % N))) s ∈ M.D) ∧
        (∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ (p : ℝ) + t = κ i) ∧
        (∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ (p : ℝ) + t = κ ((i + 1) % N)) ∧
        ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
          (p : ℝ) + t = κ i ∨ (p : ℝ) + t = κ ((i + 1) % N)) := by
    intro i hi
    have hsi := hsucc i hi
    have hab : κ i ≠ κ ((i + 1) % N) := fun h => by
      have := hinj _ _ hi hsi h
      by_cases h1 : i + 1 < N
      · rw [Nat.mod_eq_of_lt h1] at this; omega
      · rw [show i + 1 = N by omega, Nat.mod_self] at this; omega
    have hgapS := fun x hx => sorted_gap hmono (by omega) hi ((hmemL x).2 hx)
    rcases gap hM hF hfin hne hU (hκmem i hi) (hκmem _ hsi) hab hgapS with
      ⟨a', b', harc', hsub⟩ | ⟨c, hc, p, p', t, t', hA, hB, ha, hb, hAB⟩
    · left
      have hnv : ∀ k : ℕ, k < M.W.n → ¬ sideInArc (κ i) (κ ((i + 1) % N)) k :=
        fun k hk hkin => hgapS k (Or.inr ⟨k, hk, rfl, a', b', harc', hsub k hkin⟩) hkin
      have hb1 := hostKeys_bounds (hκmem i hi)
      have hb2 := hostKeys_bounds (hκmem _ hsi)
      intro z hz
      obtain ⟨p, hp, t, ht0, ht1, hzp, hkey⟩ :=
        arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2 hab hnv z hz
      refine ⟨p, hp, t, ht0, ht1, hzp, ?_⟩
      unfold InKeyIv
      by_cases h1 : i + 1 < N
      · rw [ite_eq_left h1]
        rw [Nat.mod_eq_of_lt h1] at hkey
        rwa [ite_eq_left (hmono i (i + 1) (by omega) h1)] at hkey
      · rw [ite_eq_right h1]
        rw [show i + 1 = N by omega, Nat.mod_self] at hkey
        rwa [ite_eq_right (not_lt.2 (hmono 0 i (by omega) hi).le)] at hkey
    · right
      have hPa : hostPt M.W (κ i) = sidePt M.W p t := by rw [ha, hostPt_eq M.W hA.2.1 hA.2.2.1]
      have hPb : hostPt M.W (κ ((i + 1) % N)) = sidePt M.W p' t' := by
        rw [hb, hostPt_eq M.W hB.2.1 hB.2.2.1]
      obtain ⟨hcab, -, hopen, -, -⟩ := hM.attach_seg (hF hc) hA hB hAB
      rw [hPa, hPb]
      refine ⟨c, hc, hcab, hopen, ⟨p, t, hA, ha.symm⟩, ⟨p', t', hB, hb.symm⟩, ?_⟩
      intro pc tc hC
      rw [ha, hb]
      exact attach_key_cases hM (hF hc) hA hB hAB hC
  -- an edge of the chord kind is not an arc edge
  have hnotarc : ∀ i, i < N →
      (∀ s : ℝ, 0 < s → s < 1 →
        lerp (hostPt M.W (κ i)) (hostPt M.W (κ ((i + 1) % N))) s ∈ M.D) →
      ¬ (∀ z ∈ Chazelle.segment (hostPt M.W (κ i)) (hostPt M.W (κ ((i + 1) % N))),
        ∃ p, p < M.W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt M.W p t ∧
          InKeyIv κ N i ((p : ℝ) + t)) := by
    intro i hi hD harc
    obtain ⟨p, hp, t, ht0, ht1, hzp, -⟩ := harc _ (lerp_mem_segment _ _ (show (0 : ℝ) ≤ 1 / 2 by
      norm_num) (by norm_num))
    exact hbd _ (hD (1 / 2) (by norm_num) (by norm_num))
      (hzp ▸ sidePt_mem_boundary hp ht0 ht1.le)
  refine KeyHost.simple (W := M.W) (D := M.D) (pp := fun i => ⌊κ i⌋₊)
    (tt := fun i => κ i - ⌊κ i⌋₊) ⟨?_, hWspec.1, ?_, ?_, ?_, ?_, ?_, hbd, ?_, ?_⟩
  · rwa [hVlen]
  · intro i hi
    rw [hVlen] at hi
    have hb := hostKeys_bounds (hκmem i hi)
    have := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
    exact_mod_cast this
  · intro i hi
    rw [hVlen] at hi
    have hb := hostKeys_bounds (hκmem i hi)
    show 0 ≤ κ i - ⌊κ i⌋₊
    linarith [Nat.floor_le hb.1]
  · intro i _
    show κ i - ⌊κ i⌋₊ < 1
    linarith [Nat.lt_floor_add_one (κ i)]
  · intro i hi
    rw [hVlen] at hi
    rw [hVget i hi]; rfl
  · simp only [hVlen, keyOf, add_sub_cancel] <;> omega
  · intro i hi
    rw [hVlen] at hi
    unfold ArcEdge ChordEdge keyOf
    simp only [add_sub_cancel]
    rw [hVlen, hVget i hi, hVget _ (hsucc i hi)]
    rcases hcases i hi with h | ⟨c, -, -, hopen, -⟩
    · exact Or.inl h
    · exact Or.inr fun s hs0 hs1 => hopen s ⟨hs0, hs1⟩
  · intro i j hi hj hij hci hcj s s' hs0 hs1 hs0' hs1'
    rw [hVlen] at hi hj
    unfold ChordEdge at hci hcj
    rw [hVlen] at hci hcj ⊢
    rw [hVget i hi, hVget _ (hsucc i hi)] at hci ⊢
    rw [hVget j hj, hVget _ (hsucc j hj)] at hcj ⊢
    rcases hcases i hi with h | ⟨ci, hci', hcieq, -, ⟨pi₁, ti₁, hAi₁, hki₁⟩, ⟨pi₂, ti₂, hAi₂, hki₂⟩,
      hallI⟩
    · exact absurd h (hnotarc i hi hci)
    rcases hcases j hj with h | ⟨cj, hcj', hcjeq, -, ⟨pj₁, tj₁, hAj₁, hkj₁⟩, ⟨pj₂, tj₂, hAj₂, hkj₂⟩,
      hallJ⟩
    · exact absurd h (hnotarc j hj hcj)
    intro heq
    by_cases hcc : ci = cj
    · subst hcc
      have e1 := hallI pj₁ tj₁ hAj₁
      have e2 := hallI pj₂ tj₂ hAj₂
      rw [hkj₁] at e1
      rw [hkj₂] at e2
      have hsj := hsucc j hj
      have hsi := hsucc i hi
      refine pair_ne hN3 hi hj hij ?_ ?_
      · rcases e1 with e | e
        · exact Or.inl (hinj _ _ hj hi e)
        · exact Or.inr (hinj _ _ hj hsi e)
      · rcases e2 with e | e
        · exact Or.inl (hinj _ _ hsj hi e)
        · exact Or.inr (hinj _ _ hsj hsi e)
    · have hz1 : lerp (hostPt M.W (κ i)) (hostPt M.W (κ ((i + 1) % N))) s ∈ ci := by
        rw [hcieq]; exact lerp_mem_segment _ _ hs0.le hs1.le
      have hz2 : lerp (hostPt M.W (κ j)) (hostPt M.W (κ ((j + 1) % N))) s' ∈ cj := by
        rw [hcjeq]; exact lerp_mem_segment _ _ hs0'.le hs1'.le
      rw [heq] at hz1
      exact chord_disj hM hF hfin hci' hcj' hcc hz1 hz2 (hcj s' hs0' hs1')

end

end DownHost

end Chazelle.Core
