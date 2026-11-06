module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.DownPhaseDrvTPiece
public import Chazelle.Core.OracleBook
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.OracleQuery

namespace Chazelle.Core
namespace DrvB
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt regionsIn freeIn)
open Chazelle.Visibility (DirInterior rayPt chordEnd chordSet chordParam chords hseg)
open DrvR (ivB qE walkItems regHost)
open BuildNF (buildNF)

/-! ## The shooting polygon of a region -/

/-- **The shooting polygon** `W₀` of the region `R` of `S`: simple, interior on its left, interior
`R`, boundary on `∂Q ∪ ⋃ S`, and complete for the missing vertex chords of `R`. -/
structure RegOK (Q : Polygon) (S : Set ztf) (R : Set Point) (W₀ : Polygon) : Prop where
  simple : W₀.Simple
  orient : Mountain.orient W₀ = 1
  int : W₀.filled \ W₀.boundary = R
  bd : W₀.boundary ⊆ Q.boundary ∪ ⋃₀ S
  reg : R ∈ (interiorModel Q).regions S
  complete : ∀ i σ, i < Q.n → ztdd → DirInterior Q i σ → chordSet Q i σ ∉ S →
    chordSet Q i σ ∩ (interiorModel Q).D ⊆ R →
      ∃ k, k < W₀.n ∧ W₀.vtx k = Q.vtx i ∧ DirInterior W₀ k σ
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {W₀ : Polygon}

/-- **Soundness of a shot in the shooting polygon.** -/
theorem RegOK.sound (h : RegOK Q S R W₀) (hQ : Q.Simple)
    (hFam : (interiorModel Q).ChordFamily Q S) {i k : ℕ} (hi : i < Q.n)
    (hv : W₀.vtx k = Q.vtx i) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hdir : DirInterior W₀ k σ) :
    DirInterior Q i σ ∧ chordSet Q i σ = chordSet W₀ k σ ∧ chordSet Q i σ ∈ chords Q ∧
      chordSet Q i σ ∉ S ∧ chordSet Q i σ ∩ (interiorModel Q).D ⊆ R :=
  DownDrv.chord_of_host hQ hFam h.reg h.simple h.int h.bd hi hv hσ hdir

/-! ## Rotations keep the orientation -/

/-- A rotation of a simple polygon has its orientation. -/
theorem orient_rotate {P : Polygon} (hP : P.Simple) (s : ℕ) :
    Mountain.orient ztqbh = Mountain.orient P := by
  zulkr
  have hs := Existence.simple_rotate P s hP
  have h0 : 0 < (P.rotate s).n := by zunrt; omega
  have h1 : ztbgo % (P.rotate s).n < P.n := by zunrt; exact Nat.mod_lt _ by_omega
  refine Mountain.orient_eq_of_filled_subset hP hs (i := s % P.n) (j := 0)
    ztcv h0 ?_ ?_ (by rw [Existence.filled_rotate])
  · rw [Existence.vtx_rotate _ _ by_omega, Nat.add_zero]
  · rw [Existence.vtx_rotate_succ _ _ by_omega]; simp

/-! ## The walk-order list of a host -/

/-- The walk-order list of host points stored in increasing index of `Q`. -/
def wlist (li : Bool) (pts : List SymPt) : List SymPt := if li then pts else pts.reverse
variable (li : Bool)
theorem wlist_length (pts : List SymPt) : (wlist li pts).length = pts.length := by
  unfold wlist; grind

/-- The point of walk-order index `k` is the stored point `k` (or `N - 1 - k` if reversed). -/
theorem wlist_getD {pts : List SymPt} {k : ℕ} (hk : k < pts.length) :
    (wlist li pts).getD k ztga = pts.getD (if li then k else pts.length - 1 - k) ztga := by
  unfold wlist
  grind

/-- The polygon of a list of symbolic points. -/
noncomputable def polyOf (Q : Polygon) (l : List SymPt) : Polygon := ⟨l.map ztbzb⟩
theorem polyOf_n (Q : Polygon) (l : List SymPt) : (polyOf Q l).n = l.length := by
  simp [polyOf, Polygon.n]
theorem polyOf_vtx (Q : Polygon) {l : List SymPt} {k : ℕ} (hk : k < l.length) :
    (polyOf Q l).vtx k = (l.getD k ztga).eval Q := by
  simp only [polyOf, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]

/-! ## The host of a region (`K > 0`) -/

/-- **The driver's host of a region gives a shooting polygon** (walk order). -/
theorem regOK_host {L : List zte} {E : List ℕ} {reg : ℕ → Set Point} {r : ℕ}
    (X : DownMath.RegCtx Q L E reg r) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ztwkr ztcz
      (polyOf Q (wlist li ((regHost li Q.n ztwkc r).pts Q.n))) := by
  zudbj
  set S := N.F ztd Q with hS
  obtain ⟨i0, g, hrep, hlen, hgK, hgc, hgi, hwf⟩ := DownMath.walk_rep X hli
  set WP := (walkItems li Q.n N r).flatMap (DownMath.wpts li Q.n) with hWP
  have hQ := X.hQ
  have hN : ztyyf := DownMath.isNF_build hQ X.hL X.hperm X.hsort
  zujzg
  have hnc : ztpku := DownMath.nChords_build hQ X.hL X.hperm X.hsort
  have hne : S.Nonempty :=
    ⟨_, (DownMath.chordPos_attach hN ztitl ztp).1⟩
  have hR : ztmwp := X.hregs.1.1 r X.hr
  set K := DownHost.nk ztd S ztcz with hKdef
  have hrep' : ∀ j, j < K → DownMath.RepPt li Q S ztcz (ztdhp % K) (WP.getD j ztga) :=
    fun j hj => hrep j by_omega
  have hrot : (⟨WP.map ztbzb⟩ : Polygon) = (DownHost.hostPoly Q S ztcz).rotate i0 :=
    DownMath.poly_of_rep hQ hFam hne hR hli X.hdh hlen hrep'
  have hwl : wlist li ztlcz = WP := by
    zumld
    unfold wlist
    grind
  have hP : polyOf Q (wlist li ztlcz) =
      (DownHost.hostPoly Q S ztcz).rotate i0 := by
    rw [hwl]; tauto
  zujig
  obtain ⟨hs, hint, hbd, -⟩ := DownMath.polyFacts_rotate hQ hFam hne hR i0
  have hHs : (DownHost.hostPoly Q S ztcz).Simple := DownHost.hostPts_simple hQ hFam hne hR
  refine ⟨hs, ?_, hint, hbd, hR, ?_⟩
  · rw [orient_rotate hHs]; exact DownDrv.hostPoly_orient hQ hFam hne hR
  · intro i σ hi hσ hdir hcS hcR
    zukbh
    obtain ⟨R', hR', i', σ', hi', hσ', hceq, hdir', hcR', j, hj, hjv, hdirj⟩ :=
      DownDrv.missing_found hQ hFam hne hc hcS
    obtain ⟨-, -, -, hnon⟩ := DownDrv.full_in_region hQ hFam hc hcS
    obtain ⟨rfl, rfl⟩ := DownDrv.chordSet_inj hQ X.hdh hi hi' hσ hσ' hdir hdir' hceq
    have hRR : reg r = R' := by
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint hR hR' with h | h
      · zubh
      · obtain ⟨z, hz⟩ := hnon
        exact absurd (h.le_bot ⟨hcR hz, hcR' hz⟩) by_simp
    subst hRR
    have hn0 : 0 < (DownHost.hostPoly Q S ztcz).n := by_omega
    obtain ⟨k, hk, hkj⟩ := Existence.exists_rot_index hn0 i0 j hj
    refine ⟨k, by_simp_all, ?_, ?_⟩
    · rw [Existence.vtx_rotate _ _ hk, hkj, hjv]
    · zultr
      rw [Existence.vtx_rotate _ _ hk, hkj, Existence.filled_rotate, Existence.boundary_rotate]
      exact hdirj

/-! ## The whole walk (`K = 0`) -/

/-- The interior of a simple polygon is the only region of the empty family. -/
theorem region_empty (hQ : Q.Simple) :
    (interiorModel Q).D ∈ (interiorModel Q).regions (∅ : Set ztf) := by
  zubdo
  zuidf
  have hfree : freeIn (interiorModel Q).D (∅ : Set ztf) = (interiorModel Q).D := by
    ext x; zunjh
  refine ztrfa
  rw [hfree]
  exact (hM.preconn.connectedComponentIn hz).symm

/-- **The interior walk is the shooting polygon of the empty family.** -/
theorem regOK_empty (hQ : Q.Simple) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ∅ (interiorModel Q).D ztkb := by
  zueuf
  refine ⟨hs, ho, by rw [hb, hf]; rfl, by_simp_all, region_empty hQ, ?_⟩
  intro i σ hi hσ hdir _ _
  have hk := DownMath.ivB_lt li hi
  refine ⟨ivB li Q.n i, by rw [DownMath.walk_n]; exact hk, ?_, ?_⟩
  · rw [DownMath.walk_vtx hli hk, ivB_ivB li hi]
  · zultr
    rw [DownMath.walk_vtx hli hk, ivB_ivB li hi, hf, hb]
    tauto

/-- The walk-order list of the host `[.run 0 (n - 1)]` is the interior walk. -/
theorem polyOf_wlist_run (hQ : Q.Simple) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    polyOf Q ztbaoc = interiorWalk Q := by
  zuhfh
  have hpts : Host.pts Q.n [HostItem.run 0 ztnv] =
      (List.range Q.n).map fun k => SymPt.vtx k := by
    simp only [Host.pts, List.flatMap_cons, List.flatMap_nil, List.append_nil, HostItem.pts]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ Q.n)]
    zucfh
    zugf
    rw [List.mem_range] at hk
    rw [Nat.zero_add, Nat.mod_eq_of_lt hk]
  have hlen : (wlist li ztwqf).length = Q.n := by
    rw [wlist_length, hpts, List.length_map, List.length_range]
  apply DownMath.poly_eq_of_vtx
  · rw [polyOf_n, hlen, DownMath.walk_n]
  · zugf
    rw [polyOf_n, hlen] at hk
    rw [polyOf_vtx Q by_omega, DownMath.walk_vtx hli hk,
      wlist_getD li by_simp_all, hpts]
    simp only [List.length_map, List.length_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range by_grind]
    rfl
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
@[expose] public section
open Set
open Chazelle.Visibility (DirInterior chordEnd chordSet chords OpenEdgePt)
open DrvR (ivB qE)
variable {Q : Polygon}

/-! ## Vertices among the symbolic points -/
open Classical in
/-- **The vertex of `Q` that a symbolic point is** (an edge point `.onEdge e h` is the vertex `h`
iff its abscissa is that of `v_h`). -/
noncomputable def qvx (Q : Polygon) : SymPt → Option ℕ
  | .vtx i => some i
  | .onEdge e h => if edgeXAt Q e h = (Q.vtx h).1 then some h else none
variable {s : SymPt} {i : ℕ}
theorem qvx_eval (h : qvx Q s = some i) : s.eval Q = Q.vtx i := by
  cases s with
  | vtx j => simp only [qvx, Option.some.injEq] at h; subst h; rfl
  | onEdge e h' =>
    zujot
    split_ifs at h with hx
    zufbb
    zubst
    exact Prod.ext hx rfl
theorem qvx_lt (hs : s.Lt Q.n) (h : qvx Q s = some i) : i < Q.n := by
  cases s with
  | vtx j => simp only [qvx, Option.some.injEq] at h; subst h; exact hs
  | onEdge e h' =>
    zujot
    zulsn
    zufbb
    zubst
    exact hs.2
theorem qvx_of_eval (hQ : Q.Simple) (hDH : DistinctHeights Q) {s : SymPt} (hs : s.Lt Q.n) {i : ℕ}
    (hi : i < Q.n) (h : s.eval Q = Q.vtx i) : qvx Q s = some i := by
  cases s with
  | vtx j =>
    zulsh
    exact congrArg some (hQ.2.1 _ _ hs hi h)
  | onEdge e h' =>
    have hy : (Q.vtx h').2 = (Q.vtx i).2 := by
      have := congrArg Prod.snd h; tauto
    have hh : h' = i := by
      by_contra hne; exact hDH _ _ hs.2 hi hne hy
    subst hh
    have hx : edgeXAt Q e h' = (Q.vtx h').1 := by
      have := congrArg Prod.fst h; tauto
    zulsh
    rw [ite_eq_left hx]

/-! ## The corner test on the walk-order list -/

/-- The corner test at point `k` of the walk-order list `l`, direction code `d`. -/
def emitAt (Q : Polygon) (l : List SymPt) (k d : ℕ) : Prop :=
  emitG ((l.getD ztbaaa ztga).eval Q)
    ((l.getD k ztga).eval Q) ((l.getD ztwnc ztga).eval Q) ztbgl

/-- **The corner test is the interior direction** in the shooting polygon. -/
theorem emitAt_iff {l : List SymPt} (hW : (polyOf Q l).Simple)
    (hL : Mountain.orient ztdvr = 1) {k : ℕ} (hk : k < l.length) (d : ℕ) :
    emitAt Q l k d ↔ DirInterior ztdvr k ztbgl := by
  have hn := Chazelle.Jordan.simple_three_le hW
  rw [polyOf_n] at hn
  rw [dirInterior_iff_emitG hW hL (by rw [polyOf_n]; exact hk) ztmnq]
  unfold emitAt
  have hp : Chazelle.Jordan.prevIdx ztdvr k = ztgkp % l.length := by
    unfold Chazelle.Jordan.prevIdx; rw [polyOf_n]
  rw [hp, polyOf_vtx Q ztcv, polyOf_vtx Q hk, polyOf_n,
    polyOf_vtx Q ztcv]

/-! ## The far walk edge -/
open Classical in
/-- **The walk edge carrying the far end** of the vertex chord of `i` in direction `sgnD d`. -/
noncomputable def farW (li : Bool) (Q : Polygon) (i d : ℕ) : ℕ :=
  if h : ∃ w, w < Q.n ∧ OpenEdgePt Q ztczw ztxdy then Classical.choose h
  else 0
theorem farW_spec (hQ : Q.Simple) (hDH : DistinctHeights Q) (li : Bool) {i d : ℕ} (hi : i < Q.n)
    (hdir : DirInterior Q i ztbgl) :
    farW li Q i d < Q.n ∧ OpenEdgePt Q (qE li Q.n ztjvc) ztxdy := by
  zuhfh
  have hex : ∃ w, w < Q.n ∧ OpenEdgePt Q ztczw ztxdy := by
    obtain ⟨q, hc, -, ho⟩ := far_cand hQ hDH hi ztmnq hdir
    exact ⟨qEi li Q.n q, qEi_lt li hc.1, by rw [qE_qEi li by_omega hc.1]; exact ho⟩
  unfold farW
  zulpq
  grind

/-- **Any walk edge whose edge of `Q` carries the far end is `farW`.** -/
theorem farW_eq (hQ : Q.Simple) (hDH : DistinctHeights Q) (li : Bool) {i d w : ℕ} (hi : i < Q.n)
    (hdir : DirInterior Q i ztbgl) (hw : w < Q.n)
    (h : OpenEdgePt Q ztczw ztxdy) : w = farW li Q i d := by
  zueuc
  exact qE_inj hw hf (openEdge_unique hQ (DownMath.qE_lt li hw) (DownMath.qE_lt li hf) h hfo)

/-! ## The emitted records -/
open Classical in
/-- The emitted indices `(k, d)`: point `k` is a vertex of `Q` and passes the corner test in
direction `d`. -/
noncomputable def emIdx (Q : Polygon) (l : List SymPt) : List ztw :=
  (List.range l.length).flatMap fun k => (List.range 2).filterMap fun d =>
    if (qvx Q ztxad).isSome ∧ emitAt Q l k d then some ztbub else none

/-- The record of an emitted index. -/
noncomputable def recAt (li : Bool) (Q : Polygon) (l : List SymPt) (kd : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  vtrip li Q.n ztxtw kd.2
    (farW li Q ztxtw kd.2)

/-- **The records emitted by a region.** -/
noncomputable def regList (li : Bool) (Q : Polygon) (l : List SymPt) : List zte :=
  (emIdx Q l).map ztrwn
theorem mem_emIdx {l : List SymPt} {kd : ℕ × ℕ} :
    kd ∈ emIdx Q l ↔ kd.1 < l.length ∧ kd.2 < 2 ∧ (qvx Q ztzwu).isSome ∧
      emitAt Q l kd.1 kd.2 := by
  zuldw

  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · grind
  · grind
theorem emIdx_nodup (l : List SymPt) : (emIdx Q l).Nodup := by
  zuldw

  zujgw
  refine ⟨fun k _ => ?_, ?_⟩
  · apply List.Nodup.filterMap _ List.nodup_range
    simp_all
  · refine List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_
    zugsl
theorem emIdx_length_le (l : List SymPt) : (emIdx Q l).length ≤ 2 * l.length := by
  classical
  unfold emIdx
  rw [List.length_flatMap]
  calc ((List.range l.length).map fun k => ((List.range 2).filterMap fun d =>
        if (qvx Q _).isSome ∧ emitAt Q l k d then some (k, d) else none).length).sum
      ≤ ((List.range l.length).map fun _ => 2).sum := by
        apply List.sum_le_sum
        grind
    _ = 2 * l.length := by simp [mul_comm]
theorem regList_length_le (li : Bool) (l : List SymPt) : (regList li Q l).length ≤ 2 * l.length := by
  unfold regList; rw [List.length_map]; exact emIdx_length_le l

/-! ## Soundness, completeness, distinctness -/
section
variable {S : Set (Set Point)} {R : Set Point} {l : List SymPt} {li : Bool}

/-- The facts of an emitted index. -/
theorem emIdx_facts (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : RegOK Q S R ztdvr) (hl : ∀ s ∈ l, s.Lt Q.n) {kd : ℕ × ℕ} (hkd : kd ∈ emIdx Q l) :
    ∃ i, qvx Q ztzwu = some i ∧ i < Q.n ∧ kd.1 < l.length ∧ kd.2 ≤ 1 ∧
      (polyOf Q l).vtx kd.1 = Q.vtx i ∧ DirInterior ztdvr kd.1 ztkex ∧
      DirInterior Q i ztkex ∧ chordSet Q i ztkex ∈ chords Q ∧
      chordSet Q i ztkex ∉ S ∧ chordSet Q i ztkex ∩ (interiorModel Q).D ⊆ R := by
  obtain ⟨hk, hd, hsome, hem⟩ := mem_emIdx.1 hkd
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hsome
  have hmem : l.getD kd.1 ztga ∈ l := by
    simp_all
  have hin := qvx_lt by_simp_all hi
  have hv : (polyOf Q l).vtx kd.1 = Q.vtx i := by rw [polyOf_vtx Q hk]; exact qvx_eval hi
  have hdirW := (emitAt_iff hR.simple hR.orient hk kd.2).1 hem
  obtain ⟨hdir, -, hc, hcS, hcR⟩ := hR.sound hQ hFam hin hv ztqwd hdirW
  simp_all

/-- **Soundness**: every emitted record is that of a vertex chord of `Q` missing from `S`, with its
domain part in the region, attached, with proper ends. -/
theorem regList_sound (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : RegOK Q S R ztdvr) (hl : ∀ s ∈ l, s.Lt Q.n) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ regList li Q l) :
    (recOf x).toSet ztd Q ∈ chords Q ∧
      (recOf x).toSet ztd Q ∉ S ∧
      (recOf x).toSet ztd Q ∩ (interiorModel Q).D ⊆ R ∧
      (recOf x).Attached ztd Q ∧
      ProperPos ztd Q Q.n (recOf x).lpos ∧
      ProperPos ztd Q Q.n (recOf x).rpos ∧ x.1 < Q.n := by
  unfold regList at hx
  obtain ⟨kd, hkd, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, hi, hin, -, hd, -, -, hdir, hc, hcS, hcR⟩ := emIdx_facts hQ hFam hR hl hkd
  zueud
  have hrec : recAt li Q l kd = vtrip li Q.n i kd.2 (farW li Q i kd.2) := by
    zufdm
  zumoc
  obtain ⟨hset, hatt, hpl, hpr, hlt⟩ := vtrip_ok hQ hDH hli hin hd hdir hf hfo
  simp_all

/-- **Completeness**: every vertex chord of `Q` missing from `S` with its domain part in the
region is emitted. -/
theorem regList_complete (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (hR : RegOK Q S R ztdvr)
    (hl : ∀ s ∈ l, s.Lt Q.n) {c : Set Point} (hc : c ∈ chords Q) (hcS : c ∉ S)
    (hcR : c ∩ (interiorModel Q).D ⊆ R) :
    ∃ x ∈ regList li Q l, (recOf x).toSet ztd Q = c := by
  zubhh
  obtain ⟨k, hk, hv, hdirW⟩ := hR.complete i σ hi hσ hdir hcS hcR
  rw [polyOf_n] at hk
  obtain ⟨d, hd, hσd⟩ : ∃ d, d ≤ 1 ∧ sgnD d = σ := by
    zur
    · exact ztqzu
    · exact ztqzx
  subst hσd
  have hmem : l.getD k ztga ∈ l := by
    simp_all
  have hq : qvx Q _ = some i :=
    qvx_of_eval hQ hDH (hl _ hmem) hi (by rw [← polyOf_vtx Q hk]; exact hv)
  have hkd : ztbub ∈ emIdx Q l :=
    mem_emIdx.2 ⟨hk, by_omega, by_simp_all, (emitAt_iff hR.simple hR.orient hk d).2 hdirW⟩
  refine ⟨recAt li Q l ztbub, List.mem_map.2 by_grind, ?_⟩
  have hrec : recAt li Q l ztbub = vtrip li Q.n i d ztjvc := by
    zufdm
  zueuc
  zumoc
  exact (vtrip_ok hQ hDH hli hi hd hdir hf hfo).1

/-- **Distinctness**: the emitted chords are pairwise distinct. -/
theorem regList_nodup (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) (hFam : (interiorModel Q).ChordFamily Q S)
    (hR : RegOK Q S R ztdvr) (hl : ∀ s ∈ l, s.Lt Q.n) :
    ((regList li Q l).map fun x => (recOf x).toSet ztd Q).Nodup := by
  unfold regList
  zuczm
  refine (emIdx_nodup l).map_on ?_
  zubtp
  obtain ⟨i, hi, hin, hak, had, hva, -, hdir, -⟩ := emIdx_facts hQ hFam hR hl ha
  obtain ⟨i', hi', hin', hbk, hbd, hvb, -, hdir', -⟩ := emIdx_facts hQ hFam hR hl hb
  zueud
  obtain ⟨hf', hfo'⟩ := farW_spec hQ hDH li hin' hdir'
  have ha' : recAt li Q l a = vtrip li Q.n i a.2 (farW li Q i a.2) := by
    zufdm
  have hb' : recAt li Q l b = vtrip li Q.n i' b.2 (farW li Q i' b.2) := by
    zufdm
  simp only [Function.comp] at hab
  rw [ha', hb', (vtrip_ok hQ hDH hli hin had hdir hf hfo).1,
    (vtrip_ok hQ hDH hli hin' hbd hdir' hf' hfo').1] at hab
  obtain ⟨rfl, hσ⟩ := DownDrv.chordSet_inj hQ hDH hin hin' ztqwd ztqwd hdir
    hdir' hab
  have hd : a.2 = b.2 := by
    unfold sgnD at hσ
    grind
  have hk : a.1 = b.1 := by
    have := hva.trans hvb.symm
    exact hR.simple.2.1 _ _ ztnuj ztnuj this
  grind
end
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
@[expose] public section
open Set
open Chazelle.Visibility (DirInterior chordEnd chordSet chords OpenEdgePt)
open DrvR (ivB qE walkItems regHost)
open BuildNF (buildNF codeLe)

/-! ## The family of a chord list -/

/-- The chords of a list of triples. -/
def famL (M : Model) (Q : Polygon) (L : List zte) : Set ztf :=
  {c | ∃ x ∈ L, c = (recOf x).toSet M Q}
variable (M : Model)
theorem famL_append (Q : Polygon) (L L₂ : List zte) :
    famL M Q ztfi = famL M Q L ∪ famL M Q L₂ := by
  ext c; simp [famL, or_and_right, exists_or]

/-- **The chords of `buildNF` are those of its list.** -/
theorem F_build (Q : Polygon) (L : List zte) (E : List ℕ) :
    (buildNF M Q L E).F M Q = famL M Q L := by
  zubcj
  simp only [NF.F, BuildNF.buildNF, List.mem_map, List.mem_range, famL]
  constructor
  · zubsg
    exact ztpey
  · zuod
    zuve
    refine ztexo
    have : ztxpo := by
      simp_all
    unfold BuildNF.chordRec
    zubk
    rfl

/-- A vertex chord meets the interior. -/
theorem chord_dom_nonempty {Q : Polygon} (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) :
    (c ∩ (interiorModel Q).D).Nonempty := by
  zubhh
  zuiyw
  refine ⟨Visibility.rayPt ztdli σ (Visibility.chordParam Q i σ / 2), ?_, ?_⟩
  · rw [Visibility.chordSet_eq_image hQ hi hdir]
    grind
  · exact (Visibility.chord_spec hQ hi hdir).2.2 _ by_linarith by_linarith

/-- The chords of `Q` are admissible chords of its interior model, at vertex heights. -/
theorem chords_family {Q : Polygon} (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) :
    c ∈ (interiorModel Q).Adm := FullDegInt.hc_full hQ hc

/-! ## Points of a well-formed host -/
theorem host_pts_lt {n : ℕ} (hn : 0 < n) {H : Host} (hH : HostWF n H) :
    ∀ s ∈ H.pts n, s.Lt n := by
  zugg
  simp only [Host.pts, List.mem_flatMap] at hs
  obtain ⟨it, hit, hs⟩ := hs
  have hwf := hH it hit
  cases it with
  | run a ℓ =>
    simp only [HostItem.pts, List.mem_map, List.mem_range] at hs
    obtain ⟨k, -, rfl⟩ := hs
    zuiss
  | pt x =>
    simp only [HostItem.pts, List.mem_singleton] at hs
    subst hs; exact hwf
theorem wlist_mem {li : Bool} {pts : List SymPt} {s : SymPt} (h : s ∈ wlist li pts) : s ∈ pts := by
  unfold wlist at h; grind

/-! ## The new chords (`K > 0`) -/

/-- The walk-order points of the host of region `r`. -/
noncomputable def regPts (li : Bool) (n : ℕ) (N : NF) (r : ℕ) : List SymPt :=
  wlist li ((regHost li n N r).pts n)

/-- **The new chords of the base case** (`K > 0`): the records emitted by the regions. -/
noncomputable def newL (li : Bool) (Q : Polygon) (N : NF) : List zte :=
  (List.range N.nRegions).flatMap fun r => regList li Q (regPts li Q.n N r)
section K
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

/-- The facts of one region. -/
theorem region_facts {r : ℕ} (X : DownMath.RegCtx Q L E reg r) (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ztwkr ztcz
      (polyOf Q ztbapo) ∧
      ∀ s ∈ regPts li Q.n ztwkc r, s.Lt Q.n := by
  refine ⟨regOK_host X hli, fun s hs => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hwf⟩ := DownMath.walk_rep X hli
  have hn : ztgtu := by have := X.hQ.1; omega
  have hwf' : HostWF Q.n (regHost li Q.n ztwkc r) := by
    unfold regHost; split_ifs
    · omega
    · zufxn
  exact host_pts_lt hn hwf' s ztwhv

/-- The context of the base case (`K > 0`). -/
structure BaseCtx (Q : Polygon) (L : List zte) (E : List ℕ) (reg : ℕ → Set Point)
    (li : Bool) : Prop where
  hQ : Q.Simple
  hdh : DistinctHeights Q
  hL : ChordTriplesOK ztd Q L
  hperm : E.Perm ztct
  hsort : E.Pairwise ztxnq
  hK : 0 < L.length
  hregs : Restore.NFRegs ztd Q ztwkc reg
  hli : li = true ↔ Mountain.LeftInside Q
theorem BaseCtx.rc (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (buildNF ztd Q L E).nRegions) : DownMath.RegCtx Q L E reg r :=
  ⟨B.hQ, B.hdh, B.hL, B.hperm, B.hsort, B.hK, B.hregs, hr⟩
theorem BaseCtx.fam (B : BaseCtx Q L E reg li) :
    (interiorModel Q).ChordFamily Q ztwkr :=
  (DownMath.isNF_build B.hQ B.hL B.hperm B.hsort).1
set_option maxHeartbeats 2000000 in
/-- The facts of a new chord. -/
theorem newL_mem (B : BaseCtx Q L E reg li) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ newL li Q ztwkc) :
    ∃ r, r < (buildNF ztd Q L E).nRegions ∧
      x ∈ regList li Q ztbapo ∧
      (recOf x).toSet ztd Q ∈ chords Q ∧
      (recOf x).toSet ztd Q ∉ famL ztd Q L ∧
      (recOf x).toSet ztd Q ∩ (interiorModel Q).D ⊆ reg r ∧
      (recOf x).Attached ztd Q ∧
      ProperPos ztd Q Q.n (recOf x).lpos ∧
      ProperPos ztd Q Q.n (recOf x).rpos ∧ x.1 < Q.n := by
  unfold newL at hx
  zucoe
  zukpr
  zubpb
  have := regList_sound B.hQ B.hdh B.hli B.fam hR hl hxr
  rw [F_build] at this
  grind

/-- **The new chord list is valid** with the old one. -/
theorem newL_ok (B : BaseCtx Q L E reg li) :
    ChordTriplesOK ztd Q ztbanr := by
  have hL := B.hL
  refine ztytk
  · -- finite
    have : {c | ∃ x ∈ L ++ newL li Q ztwkc, c = (recOf x).toSet ztd Q} =
        ztyay '' {x | x ∈ L ++ newL li Q ztwkc} := by
      grind
    zubk
    zuisj
  · zueq
    zuoy
    · exact hL.1.2.1 by_grind
    · obtain ⟨-, -, -, h, -⟩ := newL_mem B hx
      exact chords_family B.hQ h
  · zueq
    zuoy
    · exact hL.1.2.2 _ by_grind
    · zubtt
      tauto
  · -- distinct
    zukpp
    refine ⟨hL.2.1, ?_, ?_⟩
    · unfold newL
      rw [List.map_flatMap, List.nodup_flatMap]
      refine zthna
      · zukpr
        zubpb
        exact regList_nodup B.hQ B.hdh B.hli B.fam hR hl
      · refine List.nodup_range.pairwise_of_forall_ne fun r hr r' hr' hrr => ?_
        rw [List.mem_range] at hr hr'
        refine List.disjoint_left.2 fun c hc hc' => hrr ?_
        zucih

        zubpb
        obtain ⟨hR', hl'⟩ := region_facts ztpwf B.hli
        obtain ⟨hcQ, -, hcR, -⟩ := regList_sound B.hQ B.hdh B.hli B.fam hR hl hx
        obtain ⟨-, -, hcR', -⟩ := regList_sound B.hQ B.hdh B.hli B.fam hR' hl' hx'
        rw [hxx] at hcR'
        obtain ⟨z, hz⟩ := chord_dom_nonempty B.hQ hcQ
        have hreg := B.hregs.1
        rcases Chazelle.Chain.regionsIn_eq_or_disjoint (hreg.1 r hr) (hreg.1 r' hr') with h | h
        · exact hreg.2.1 r r' hr hr' h
        grind
    · zukja
      zulat
      zucih

      obtain ⟨-, -, -, -, h, -⟩ := newL_mem B hx'
      exact h ⟨x, hx, hxx⟩
  · zuh
    zuoy
    · exact hL.2.2.1 x hx
    · obtain ⟨-, -, -, -, -, -, h, -⟩ := newL_mem B hx
      zubh
  · zuh
    zuoy
    · exact hL.2.2.2 x hx
    · zubtt
      zubh

/-- **Every vertex chord of `Q` is a chord of the completed list.** -/
theorem newL_full (B : BaseCtx Q L E reg li) :
    chords Q ⊆ famL ztd Q ztbanr := by
  zung
  rw [famL_append]
  by_cases hcS : c ∈ famL ztd Q L
  · simp_all
  right
  zumbp
  rw [F_build] at hFam
  obtain ⟨R, hR, hcR, -⟩ := DownDrv.full_in_region B.hQ hFam hc hcS
  rw [← F_build (E := E)] at hR
  obtain ⟨r, hr, rfl⟩ := B.hregs.1.2.2 R hR
  obtain ⟨hRo, hl⟩ := region_facts ztgdd B.hli
  rw [F_build] at hRo
  obtain ⟨x, hx, hxc⟩ := regList_complete B.hQ B.hdh B.hli hRo hl hc hcS hcR
  exact ⟨x, List.mem_flatMap.2 by_grind, hxc.symm⟩
end K

/-! ## The new chords (`K = 0`) -/

/-- **The new chords of the base case** (`K = 0`): the records emitted by the whole walk. -/
noncomputable def newL0 (li : Bool) (Q : Polygon) : List zte :=
  regList li Q ztbaoc
section K0
variable {Q : Polygon} {li : Bool}
theorem run_pts_lt (hQ : Q.Simple) :
    ∀ s ∈ wlist li ztwqf, s.Lt Q.n := by
  zugg
  have hn : ztgtu := by have := hQ.1; omega
  refine host_pts_lt hn ?_ s ztwhv
  zujbe
  simp_all
theorem regOK0 (hQ : Q.Simple) (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ∅ (interiorModel Q).D (polyOf Q ztbaoc) := by
  rw [polyOf_wlist_run hQ hli]; exact regOK_empty hQ hli

/-- **The new chord list is valid** (`K = 0`). -/
theorem newL0_ok (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) :
    ChordTriplesOK ztd Q zttue := by
  have hFam : (interiorModel Q).ChordFamily Q (∅ : Set _) :=
    ⟨finite_empty, empty_subset _, by_simp_all⟩
  have hR := regOK0 hQ hli
  have hl := run_pts_lt (li := li) hQ
  refine ⟨ztcg, regList_nodup hQ hDH hli hFam hR hl, fun x hx => ?_, fun x hx => ?_⟩
  · have : {c | ∃ x ∈ newL0 li Q, c = (recOf x).toSet ztd Q} =
        ztyay '' {x | x ∈ newL0 li Q} := by
      grind
    zubk
    zuisj
  · zueq
    exact chords_family hQ (regList_sound hQ hDH hli hFam hR hl hx).1
  · zueq
    exact ⟨x.1, (regList_sound hQ hDH hli hFam hR hl hx).2.2.2.2.2.2, _, _, rfl⟩
  · exact (regList_sound hQ hDH hli hFam hR hl hx).2.2.2.1
  · exact (regList_sound hQ hDH hli hFam hR hl hx).2.2.2.2.2.2

/-- **Every vertex chord of `Q` is emitted** (`K = 0`). -/
theorem newL0_full (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) :
    chords Q ⊆ famL ztd Q zttue := by
  zung
  obtain ⟨x, hx, hxc⟩ := regList_complete hQ hDH hli (regOK0 hQ hli) (run_pts_lt hQ) hc
    ztwab (fun z hz => hz.2)
  tauto
end K0

/-! ## The number of new chords -/

/-- **A valid list of vertex chords has at most `2 n` chords.** -/
theorem length_le_of_chords {Q : Polygon} {L₂ : List zte}
    (hnd : (L₂.map fun x => (recOf x).toSet ztd Q).Nodup)
    (hc : ∀ x ∈ L₂, (recOf x).toSet ztd Q ∈ chords Q) : L₂.length ≤ 2 * Q.n := by
  have h1 : (L₂.map fun x => (recOf x).toSet ztd Q).toFinset.card = L₂.length := by
    zuewt
  have h2 : ((L₂.map fun x => (recOf x).toSet ztd Q).toFinset : Set _) ⊆
      chords Q := by
    intro c hc'
    simp only [List.coe_toFinset, mem_ofPred_eq, List.mem_map] at hc'
    grind
  have h3 := Set.ncard_le_ncard h2 (Visibility.chords_finite Q)
  zuigu
  exact h3.trans (Visibility.chords_ncard_le Q)
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace BuildNF
@[expose] public section
open List
open BuildRam (wtF)
variable {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The codes of a permutation of `range N` are below `N`. -/
theorem getD_lt_of_perm {N : ℕ} (hp : E.Perm (range N)) {m : ℕ} (hm : m < E.length) :
    E.getD m 0 < N := by
  rw [getD_eq_getElem?_getD, getElem?_eq_getElem hm, Option.getD_some]
  exact mem_range.1 (hp.mem_iff.1 ztvrk)

/-- The key of the first sorted code is at most the key of any later one. -/
theorem Input.key_first_le (h : Input M zta L E) {m : ℕ} (hm : m < E.length) :
    M.key zta ztojv ≤ M.key zta ztwwn := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  rw [h.key_s by_omega, h.key_s hm, BuildSort.kap_eq (by zuoyt; omega),
    BuildSort.kap_eq ztmdi]
  exact BuildSort.key_le_of_evLe (List.pairwise_iff_getElem.1 h.sorted 0 m (by
    grind) by_simp_all hpos)

/-- **The weight of an arc record** by the machine formula. -/
theorem Input.arcW_eq (h : Input M zta L E) {m : ℕ} (hm : m < E.length)
    (hgap : m ∈ gapStarts M zta L E) {lo hi : ℕ}
    (hc : ∀ p, p < M.W.n → ztceo) (hhi : hi ≤ M.W.n) {pz : ℕ}
    (hpz : pz = 1 ↔ M.counted (wposOf L ztwkh).edge ∧
      M.param zta ztbalg ≠ 0) (hpz1 : pz ≤ 1) :
    arcW M zta (arcRec M zta L E m) =
      wtF lo hi (wposOf L ztbgr).edge (wposOf L ztwkh).edge pz
        ztkwo := by
  have hlen := h.length_E
  have hm2 : ztbl % E.length < E.length := Nat.mod_lt _ by_omega
  have ps := BuildRam.properPos_ev h.valid (c := E.getD m 0) (by
    exact getD_lt_of_perm h.perm hm)
  have pe := BuildRam.properPos_ev h.valid (c := E.getD ztxei 0) (by
    exact getD_lt_of_perm h.perm hm2)
  have he := BuildRam.edge_lt h.valid (c := E.getD ztxei 0) (by
    exact getD_lt_of_perm h.perm hm2)
  unfold arcW arcRec
  zubi
  rw [M.arcWt_key hc hhi zta ⟨ps.1, ps.2.1⟩ ⟨pe.1, pe.2.1⟩]
  refine BuildRam.arcWtNat_eq_wtF (hc _ he) hpz hpz1 ?_
  change _ ↔ M.key zta _ < M.key zta _
  by_cases hw : m + 1 < E.length
  · rw [ite_eq_left hw, Nat.mod_eq_of_lt hw]
    have := (h.gap_iff hm).1 hgap
    grind
  · rw [ite_eq_right hw, show ztbl % E.length = 0 by
      rw [show m + 1 = E.length by omega, Nat.mod_self]]
    refine ⟨fun h' => absurd h' by_norm_num, fun h' => ?_⟩
    exact absurd (h.key_first_le hm) (not_le.2 h')
end
end BuildNF
end Chazelle.Core
namespace Chazelle.Core
namespace BuildNF
@[expose] public section
open List

/-- The chord word of the codes. -/
def cw (E : List ℕ) : List ℕ := E.map ztcfk

/-- The stack after `m` letters, bottom first. -/
def stk (E : List ℕ) (m : ℕ) : List ℕ := (BuildStack.run ztbwo).reverse

/-- The region index of the label after `m` letters. -/
def topR (E : List ℕ) (m : ℕ) : ℕ := ridx (BuildStack.label ztvmb m)
theorem topR_eq (E : List ℕ) (m : ℕ) :
    topR E m = if (stk E m).length = 0 then 0 else (stk E m).getD ztlzo 0 + 1 := by
  unfold topR stk BuildStack.label
  generalize BuildStack.run ztbwo = S
  zugrm
  · rfl
  · simp only [head?_cons, ridx, reverse_cons, length_append, length_reverse, length_cons,
      length_nil, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    simp
variable {E : List ℕ} {m : ℕ} {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}
theorem cw_getElem (hm : m < E.length) :
    ztvmb[m]' ztdgw = E.getD m 0 / 2 := by
  simp [cw, getD_eq_getElem?_getD, getElem?_eq_getElem hm]
theorem run_succ (hm : m < E.length) :
    BuildStack.run ((cw E).take ztbl) =
      BuildStack.step (BuildStack.run ztbwo) ztcgq := by
  rw [take_add_one, getElem?_eq_getElem ztdgw, Option.toList_some,
    BuildStack.run_snoc, cw_getElem hm]

/-- A pop. -/
theorem stk_pop (hm : m < E.length)
    (hh : (BuildStack.run ztbwo).head? = some ztcgq) :
    stk E ztbl = (stk E m).dropLast ∧ (stk E m).length = (stk E ztbl).length + 1 := by
  zuhre

  zulpx
  generalize BuildStack.run ztbwo = S at hh ⊢
  zugrm
  · simp_all
  simp

/-- A push. -/
theorem stk_push (hm : m < E.length)
    (hh : ¬ (BuildStack.run ztbwo).head? = some ztcgq) :
    stk E ztbl = stk E m ++ [E.getD m 0 / 2] := by
  zuhre

  simp_all

/-- The label is `x + 1` iff the stack top is `x`. -/
theorem topR_eq_succ_iff (E : List ℕ) (m x : ℕ) :
    topR E m = x + 1 ↔ (BuildStack.run ztbwo).head? = some x := by
  unfold topR BuildStack.label
  generalize (BuildStack.run ztbwo).head? = o
  cases o <;> zuoyx

/-- The gap predicate of `gapStarts`. -/
noncomputable def gapP (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (m : ℕ) : Bool :=
  decide ztwwi

/-- The gap starts below `m`. -/
noncomputable def gapsB (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (m : ℕ) :
    List ℕ := (range m).filter (gapP M Q L E)
theorem gapsB_full (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) :
    gapsB M Q L E E.length = gapStarts M Q L E := rfl
theorem gapsB_succ (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (m : ℕ) :
    gapsB M Q L E ztbl = gapsB M Q L E m ++ (if gapP M Q L E m then [m] else []) := by
  unfold gapsB
  rw [range_succ, filter_append]
  grind
theorem gapsB_length_le (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (m : ℕ) :
    (gapsB M Q L E m).length ≤ m := by
  unfold gapsB
  grind

/-- The gap predicate by keys. -/
theorem Input.gapP_iff {E : List ℕ}
    (h : Input M Q L E) {m : ℕ} (hm : m < E.length) :
    gapP M Q L E m = true ↔ (m + 1 = E.length ∨
      M.key Q ztwwn < M.key Q ztbalg) := by
  unfold gapP
  zummd
  by_cases h1 : m + 1 = E.length
  · omega
  · rw [Nat.mod_eq_of_lt by_omega, h.key_s hm, h.key_s by_omega]

/-- The word `f` of a chord record. -/
def cf (r : CRec) (f : ℕ) : ℕ :=
  if f = 0 then r.h else if f = 1 then r.lp else if f = 2 then r.rp else if f = 3 then r.up
  else r.dn

/-- The word `f` of an arc record. -/
def af (a : ARec) (f : ℕ) : ℕ :=
  if f = 0 then a.reg else if f = 1 then a.s.edge else if f = 2 then a.s.hgt
  else if f = 3 then a.e.edge else a.e.hgt
theorem take_succ_cw (hm : m < E.length) :
    (cw E).take ztbl = (cw E).take m ++ [E.getD m 0 / 2] := by
  rw [take_add_one, getElem?_eq_getElem ztdgw, Option.toList_some, cw_getElem hm]

/-- **The pass pops** at `m` iff the chord occurred before. -/
theorem Input.pop_iff {E : List ℕ}
    (h : Input M Q L E) {m : ℕ} (hm : m < E.length) :
    topR E m = E.getD m 0 / 2 + 1 ↔ E.getD m 0 / 2 ∈ (cw E).take m := by
  rw [topR_eq_succ_iff]
  obtain ⟨hnc, htw⟩ := h.word_ok
  have := push_iff (w := cw E) htw hnc (m := m) ztdgw
  zujhr
  omega

/-- **The chord record written at the first occurrence** `m` of a chord. -/
theorem Input.chordRec_new {E : List ℕ}
    (h : Input M Q L E) {m : ℕ} (hm : m < E.length) (hx : E.getD m 0 / 2 < L.length)
    (hn : E.getD m 0 / 2 ∉ (cw E).take m) :
    chordRec M Q L E ztcgq =
      { h := (L.getD ztcgq ztt).1, lp := (L.getD ztcgq ztt).2.1,
        rp := (L.getD ztcgq ztt).2.2,
        up := if E.getD m 0 % 2 < 1 then topR E m else E.getD m 0 / 2 + 1,
        dn := if E.getD m 0 % 2 < 1 then E.getD m 0 / 2 + 1 else topR E m } := by
  have hidx : (E.map ztcfk).idxOf ztcgq = m := by
    have := idxOf_new (w := cw E) (m := m) ztdgw (by rw [cw_getElem hm]; exact hn)
    zujhr
    tauto
  rw [h.chordRec_eq hx, hidx]
  unfold topR cw
  simp

/-- The arc record of a gap start. -/
theorem arcRec_eq (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (m : ℕ) :
    arcRec M Q L E m =
      { reg := topR E ztbl, s := wposOf L ztbgr,
        e := wposOf L ztwkh } := by
  unfold arcRec topR
  zumpf
  rfl
theorem cf_mk (h lp rp up dn f : ℕ) :
    cf ⟨h, lp, rp, up, dn⟩ f = if f = 0 then h else if f = 1 then lp else if f = 2 then rp
      else if f = 3 then up else dn := rfl
theorem af_mk (reg : ℕ) (s e : WPos) (f : ℕ) :
    af ⟨reg, s, e⟩ f = if f = 0 then reg else if f = 1 then s.edge else if f = 2 then s.hgt
      else if f = 3 then e.edge else e.hgt := rfl
end
end BuildNF
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
open BuildNF (wposOf)
@[expose] public section
def recWord (L : List zte) (q : ℕ) : ℕ :=
  if q % 4 = 0 then (wposOf L zttws).edge else if q % 4 = 1 then (wposOf L zttws).hgt
  else if q % 4 = 2 then q / 4 % 2 else q / 4 / 2

/-- One chord: its two records and its two codes. -/
def recBody : Stmt :=
  block [.loadN 43025 43021, .addN 43021 43021 43011, .loadN 43026 43021,
    .addN 43021 43021 43011, .loadN 43027 43021, .addN 43021 43021 43011,
    .addN 43028 43025 43011,
    .storeN 43022 43026, .addN 43022 43022 43011, .storeN 43022 43028, .addN 43022 43022 43011,
    .storeN 43022 43010, .addN 43022 43022 43011, .storeN 43022 43020, .addN 43022 43022 43011,
    .storeN 43022 43027, .addN 43022 43022 43011, .storeN 43022 43028, .addN 43022 43022 43011,
    .storeN 43022 43011, .addN 43022 43022 43011, .storeN 43022 43020, .addN 43022 43022 43011,
    .storeN 43023 43024, .addN 43023 43023 43011, .addN 43024 43024 43011,
    .storeN 43023 43024, .addN 43023 43023 43011, .addN 43024 43024 43011,
    .addN 43020 43020 43011]

/-- The record loop. -/
def recLoop : Stmt := .whileLtN 43020 43002 recBody

/-- The record words of chord `i`. -/
theorem recWord_eq (L : List zte) (i k : ℕ) (hk : k < 8) :
    recWord L (8 * i + k) =
      if k = 0 then (L.getD i ztt).2.1 else if k = 1 then (L.getD i ztt).1 + 1
      else if k = 2 then 0 else if k = 3 then i else if k = 4 then (L.getD i ztt).2.2
      else if k = 5 then (L.getD i ztt).1 + 1 else if k = 6 then 1 else i := by
  have e0 : ztvd % 2 = 0 := by_omega
  have e1 : ztzrg := by_omega
  have d0 : ztpid := by_omega
  have d1 : ztzrh := by_omega
  unfold recWord
  interval_cases k
  · rw [show ztpva % 4 = 0 by omega, show ztpva / 4 = 2 * i by omega]
    zuenj
  · rw [show ztpvb % 4 = 1 by omega, show ztpvb / 4 = 2 * i by omega]
    zuenj
  · rw [show ztpvc % 4 = 2 by omega, show ztpvc / 4 = 2 * i by omega]
    simp
  · rw [show ztpvd % 4 = 3 by omega, show ztpvd / 4 = 2 * i by omega]
    simp
  · rw [show ztpve % 4 = 0 by omega, show ztpve / 4 = 2 * i + 1 by omega]
    zuenk
  · rw [show ztpvf % 4 = 1 by omega, show ztpvf / 4 = 2 * i + 1 by omega]
    zuenk
  · rw [show ztpvg % 4 = 2 by omega, show ztpvg / 4 = 2 * i + 1 by omega]
    simp
  · rw [show ztpvh % 4 = 3 by omega, show ztpvh / 4 = 2 * i + 1 by omega]
    simp_all

/-- The record table gives `RecsAt`. -/
theorem recsAt_of {m : ℕ → ℕ} {T : ℕ} {L : List zte}
    (h : ∀ q, q < 8 * L.length → m (T + q) = recWord L q) : RecsAt m T L := by
  zung
  have w : ∀ k, k < 4 → m (T + 4 * c + k) = recWord L ztjfs := fun k hk => by
    grind
  have r : ∀ k, k < 4 → ztjfs % 4 = k ∧ ztjfs / 4 = c := fun k hk => ztgy
  zudfi
  · have := w 0 by_norm_num; rw [Nat.add_zero] at this
    rw [this, recWord, ite_eq_left by_omega, (r 0 by_norm_num).2]
  · rw [w 1 by_norm_num, recWord, (r 1 by_norm_num).1, (r 1 by_norm_num).2]; simp
  · rw [w 2 by_norm_num, recWord, (r 2 by_norm_num).1, (r 2 by_norm_num).2]; simp
  · rw [w 3 by_norm_num, recWord, (r 3 by_norm_num).1, (r 3 by_norm_num).2]; simp
section exec
variable {P : Polygon} {W : ℕ}

/-- The memory after `i` chords. -/
def recMem (m₀ : ℕ → ℕ) (L : List zte) (T S₀ i : ℕ) (a : ℕ) : ℕ :=
  if T ≤ a ∧ a < T + 8 * i then recWord L (a - T)
  else if S₀ ≤ a ∧ a < S₀ + 2 * i then a - S₀ else m₀ a

/-- The memory step of the record loop. -/
theorem recStep_mem {m₀ m : ℕ → ℕ} {L : List zte} {T S₀ i : ℕ}
    (hm : ∀ a, m a = recMem m₀ L T S₀ i a) (hi : i < L.length)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℕ}
    (e0 : a0 = T + 8 * i) (e1 : a1 = T + 8 * i + 1) (e2 : a2 = T + 8 * i + 2)
    (e3 : a3 = T + 8 * i + 3) (e4 : a4 = T + 8 * i + 4) (e5 : a5 = T + 8 * i + 5)
    (e6 : a6 = T + 8 * i + 6) (e7 : a7 = T + 8 * i + 7) (e8 : a8 = S₀ + 2 * i)
    (e9 : a9 = S₀ + 2 * i + 1)
    (w0 : v0 = (L.getD i ztt).2.1) (w1 : v1 = (L.getD i ztt).1 + 1) (w2 : v2 = 0)
    (w3 : v3 = i) (w4 : v4 = (L.getD i ztt).2.2) (w5 : v5 = (L.getD i ztt).1 + 1)
    (w6 : v6 = 1) (w7 : v7 = i) (w8 : v8 = 2 * i) (w9 : v9 = 2 * i + 1)
    (hS : S₀ = T + 8 * L.length) (a : ℕ) :
    upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m a0 v0) a1 v1) a2 v2) a3 v3) a4 v4) a5 v5)
      a6 v6) a7 v7) a8 v8) a9 v9 a = recMem m₀ L T S₀ (i + 1) a := by
  subst a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 S₀
  zudlr
  zubyr
  unfold recMem
  have hr : a < T ∨ (T ≤ a ∧ a < T + 8 * i) ∨ (∃ k, k < 8 ∧ a = T + 8 * i + k) ∨
      (T + 8 * i + 8 ≤ a ∧ a < T + 8 * L.length) ∨
      (T + 8 * L.length ≤ a ∧ a < T + 8 * L.length + 2 * i) ∨ a = T + 8 * L.length + 2 * i ∨
      a = T + 8 * L.length + 2 * i + 1 ∨ T + 8 * L.length + 2 * i + 2 ≤ a := by
    by_cases h : T + 8 * i ≤ a ∧ a < T + 8 * i + 8
    · exact Or.inr (Or.inr (Or.inl ⟨a - (T + 8 * i), by_omega, by_omega⟩))
    · omega
  rcases hr with h | h | ⟨k, hk, rfl⟩ | h | h | h | h | h
  · zubhy
  · zubhz
  · interval_cases k <;>
    · zubhz
      first
        | (rw [show T + 8 * i + 0 - T = 8 * i + 0 by omega, recWord_eq L i 0 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 1 - T = 8 * i + 1 by omega, recWord_eq L i 1 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 2 - T = 8 * i + 2 by omega, recWord_eq L i 2 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 3 - T = 8 * i + 3 by omega, recWord_eq L i 3 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 4 - T = 8 * i + 4 by omega, recWord_eq L i 4 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 5 - T = 8 * i + 5 by omega, recWord_eq L i 5 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 6 - T = 8 * i + 6 by omega, recWord_eq L i 6 by_norm_num]; rfl)
        | (rw [show T + 8 * i + 7 - T = 8 * i + 7 by omega, recWord_eq L i 7 by_norm_num]; rfl)
  · zubhy
  · zubhz
  · grind
  · grind
  · zubhy

/-- The invariant of the record loop. -/
structure RecInv (m₀ : ℕ → ℕ) (L : List zte) (B T S₀ : ℕ) (c₀ d : Config) : Prop where
  i_le : d.nreg 43020 ≤ L.length
  rK : d.nreg 43002 = L.length
  r0 : d.nreg 43010 = 0
  r1 : d.nreg 43011 = 1
  a21 : d.nreg 43021 = B + 3 * d.nreg 43020
  a22 : d.nreg 43022 = T + 8 * d.nreg 43020
  a23 : d.nreg 43023 = S₀ + 2 * d.nreg 43020
  a24 : d.nreg 43024 = 2 * d.nreg 43020
  fr : ∀ r, (r < 43020 ∨ 43028 < r) → d.nreg r = c₀.nreg r
  rr : d.rreg = c₀.rreg
  rm : d.rmem = c₀.rmem
  out : d.output = c₀.output
  mem : ∀ a, d.nmem a = recMem m₀ L T S₀ (d.nreg 43020) a

/-- **The record loop.** -/
theorem recLoop_exec {m₀ : ℕ → ℕ} {L : List zte} {B T S₀ : ℕ} (hL : ChordListAt m₀ B L)
    (hB : B + 3 * L.length ≤ T) (hS : S₀ = T + 8 * L.length) (hSW : S₀ + 2 * L.length ≤ W)
    (hhW : ∀ x ∈ L, x.1 + 1 ≤ W) {c₀ c : Config} (hw : WordsBounded W c)
    (hI : RecInv m₀ L B T S₀ c₀ c) (h0 : c.nreg 43020 = 0) :
    ∃ c' k, Exec P W recLoop c c' k ∧ k ≤ 32 * L.length + 2 ∧ 30 * L.length ≤ k ∧
      WordsBounded W c' ∧
      RecInv m₀ L B T S₀ c₀ c' ∧ c'.nreg 43020 = L.length := by
  obtain ⟨c', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 43020) (b := 43002) (body := recBody)
    (fun d => WordsBounded W d ∧ RecInv m₀ L B T S₀ c₀ d)
    (fun d => 32 * (L.length - d.nreg 43020)) (fun d => 30 * d.nreg 43020) ztoe
    (fun d ⟨hwd, hId⟩ htest => by
      rw [hId.rK] at htest
      obtain ⟨i, hi⟩ : ∃ i, d.nreg 43020 = i := zths
      rw [hi] at htest
      have ha21 := hId.a21; have ha22 := hId.a22; have ha23 := hId.a23; have ha24 := hId.a24
      rw [hi] at ha21 ha22 ha23 ha24
      have o := hId.r1; have z := hId.r0
      obtain ⟨l1, l2, l3⟩ := hL i htest
      have hx : L.getD i ztt ∈ L := BuildOrder.getD_mem htest
      have hh := hhW _ hx
      have m21 : d.nmem ztpvy = (L.getD i ztt).1 := by
        rw [hId.mem, recMem, ite_eq_right by_omega, ite_eq_right by_omega, l1]
      have m22 : d.nmem ztnje = (L.getD i ztt).2.1 := by
        rw [hId.mem, recMem, ite_eq_right by_omega, ite_eq_right by_omega, l2]
      have m23 : d.nmem ztnjf = (L.getD i ztt).2.2 := by
        rw [hId.mem, recMem, ite_eq_right by_omega, ite_eq_right by_omega, l3]
      unfold recBody
      exec_block
      all_goals first
        | (config_simp; simp (config := { failIfUnchanged := false }) only [hi, ha21, ha22, ha23,
            ha24, o, z, m21, m22, m23, hS]; omega)
        | skip
      have fr := hId.fr; have hm := hId.mem; simp only [hi] at hm
      refine ⟨⟨‹WordsBounded _ _›, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, hId.rr, hId.rm,
        hId.out, fun a => ?_⟩⟩, ?_, ?_⟩
      all_goals config_simp
      · omega
      · exact hId.rK
      · exact z
      · exact o
      · omega
      · omega
      · omega
      · omega
      · simp (disch := omega) only [upd_other]; grind
      · rw [hi, o]
        refine recStep_mem hm htest ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS a <;>
          simp only [ha21, ha22, ha23, ha24, z, m21, m22, m23, hS]
      · omega
      omega)
    ⟨hw, hI⟩
  refine ⟨c', k, e, ?_, ?_, hw', hI', ?_⟩
  · omega
  · have := hI'.i_le; rw [hI'.rK] at htest; omega
  · have := hI'.i_le; rw [hI'.rK] at htest; omega
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK SortL
open BuildNF (codeLe)
@[expose] public section
def setupA : Stmt :=
  block [.copyN 43001 40001, .copyN 43002 40002, .constN 43010 0, .constN 43011 1,
    .addN 42001 43002 43002, .copyN 42000 9999, .addN 43030 42001 42001,
    .addN 43030 43030 43030, .addN 43031 42000 43030, .addN 9999 43031 42001,
    .constN 43020 0, .copyN 43021 43001, .copyN 43022 42000, .copyN 43023 43031,
    .constN 43024 0]

/-- **Phase A**: records, code list, sort. -/
def phaseA : Stmt :=
  .seq setupA (.seq recLoop (.seq ztksc
    ztvdh))

/-- The cost bound of phase A. -/
def costA (K : ℕ) : ℕ := 32 * K + 22 + SortR.sortCost 11010 ztbds
theorem modelDescWF_mono {P : Polygon} {E E' : ℕ} {m : ℕ → ℕ} {D : ℕ}
    (h : ModelDescWF P E m D) (hE : E ≤ E') : ModelDescWF P E' m D :=
  ⟨by have := h.1; omega, fun h0 => (h.2 h0).mono hE⟩
theorem seg_range {m : ℕ → ℕ} {a n : ℕ} (h : ∀ i, i < n → m zteon = i) :
    seg m a n = List.range n := by
  zuhav
  conv_rhs => rw [← List.map_id ztpzu]
  exact List.map_congr_left fun i hi => h i ztuzp
section exec
variable {P : Polygon} {W : ℕ}

/-- A band outside `{bBuild, bSort, bSign}`. -/
theorem band_out {r : ℕ} (hr : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ)) :
    bandOf r ∉ insert bSort ({bSign, bBuild} : Finset ℕ) ∧
      (r < 10000 ∨ (20000 ≤ r ∧ r < 30000) ∨ 50000 ≤ r) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bBuild, bSort, bSign] at hr ⊢
  omega

/-- The setup of phase A. -/
theorem setupA_exec (c : Config) (hw : WordsBounded W c) {B K A₀ : ℕ} (hB' : c.nreg 40001 = B)
    (hK : c.nreg 40002 = K) (hA : c.nreg 9999 = A₀) (hroom : A₀ + 10 * K ≤ W) (hW1 : 1 ≤ W) :
    ∃ c₁ k₁, Exec P W setupA c c₁ k₁ ∧ k₁ = 15 ∧
    (c₁.nreg 43001 = B ∧ c₁.nreg 43002 = K ∧ c₁.nreg 43010 = 0 ∧ c₁.nreg 43011 = 1 ∧
      c₁.nreg 42001 = 2 * K ∧ c₁.nreg 42000 = A₀ ∧ c₁.nreg 43031 = A₀ + 8 * K ∧
      c₁.nreg 9999 = A₀ + 10 * K ∧ c₁.nreg 43020 = 0 ∧ c₁.nreg 43021 = B ∧
      c₁.nreg 43022 = A₀ ∧ c₁.nreg 43023 = A₀ + 8 * K ∧ c₁.nreg 43024 = 0 ∧
      (∀ r, r ≠ 43001 → r ≠ 43002 → r ≠ 43010 → r ≠ 43011 → r ≠ 42001 → r ≠ 42000 →
        r ≠ 43030 → r ≠ 43031 → r ≠ 9999 → r ≠ 43020 → r ≠ 43021 → r ≠ 43022 → r ≠ 43023 →
        r ≠ 43024 → c₁.nreg r = c.nreg r) ∧
      c₁.rreg = c.rreg ∧ c₁.nmem = c.nmem ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output)  := by
  unfold setupA
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hK, hA, hB']; omega)
    | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 h14 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals (config_simp <;> (try simp only [hK, hA, hB']) <;>
    (try simp (disch := omega) only [upd_other]) <;> omega)
set_option maxHeartbeats 1000000 in
/-- **Phase A.** -/
theorem phaseA_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List zte} {D B : ℕ}
    (hwf : ModelDescWF P ztm c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hL : ChordTriplesOK M zta L) (hCL : ChordListAt c.nmem B L)
    (hB : B + 3 * L.length ≤ c.nreg ALLOC) (hD : c.nreg 40000 = D) (hB' : c.nreg 40001 = B)
    (hK : c.nreg 40002 = L.length) (hroom : c.nreg ALLOC + costA L.length ≤ W) :
    ∃ c' k, Exec P W phaseA c c' k ∧ k ≤ costA L.length ∧ WordsBounded W c' ∧
      Frame {bBuild, bSort, bSign} c c' k ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = c.nreg ALLOC ∧ c'.nreg 42001 = 2 * L.length ∧
      c'.nreg 43001 = B ∧ c'.nreg 43002 = L.length ∧ c'.nreg 43010 = 0 ∧ c'.nreg 43011 = 1 ∧
      RecsAt c'.nmem ztm L ∧
      c.nreg ALLOC + 10 * L.length ≤ c'.nreg 30005 ∧
      c'.nreg 30005 + 2 * L.length ≤ c'.nreg ALLOC ∧
      ∃ E, seg c'.nmem ztvgl ztpu = E ∧
        E.Perm ztct ∧ E.Pairwise ztwqj := by
  zuce
  zuvu
  zubfv
  zufgi
  have hsc := SortR.sortCost_room 11010 ztbds
  have hroom' : A₀ + 32 * K + 22 + SortR.sortCost 11010 ztbds ≤ W := by
    unfold costA at hroom; omega
  -- setup
  zugs

  -- the record loop
  have hI₁ : ztyub :=
    { i_le := by_omega, rK := r2, r0 := r3, r1 := r4, a21 := by_omega,
      a22 := by_omega, a23 := by_omega, a24 := by_omega,
      fr := fun _ _ => rfl, rr := rfl, rm := rfl, out := rfl,
      mem := fun a => by zuojt; unfold recMem; grind }
  have hhW : ztlzc := fun x hx => by
    have := hL.2.2.2 x hx
    zubp
    omega
  obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, I₂, i₂⟩ := recLoop_exec (P := P) hCL hB rfl by_omega hhW w₁ hI₁ r9
  -- the sort's inputs
  have hA₂ : c₂.nreg 9999 = A₀ + 10 * K := by rw [I₂.fr _ ztjkq, r8]
  have hS₂ : c₂.nreg 43031 = A₀ + 8 * K := by rw [I₂.fr _ ztvcg, r7]
  have hN₂ : c₂.nreg 42001 = 2 * K := by rw [I₂.fr _ ztjkq, r5]
  obtain ⟨c₃, k₃, x₃, hk₃, v30003, v30004, g₃, mm₃, rr₃, rm₃, out₃⟩ : ∃ c₃ k₃,
      Exec P W ztksc c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 30003 = A₀ + 8 * K ∧ c₃.nreg 30004 = 2 * K ∧
      ztgsm ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have y1 := Exec.copyN (P := P) w₂ 30003 43031
    have y2 := Exec.copyN (P := P) y1.wb_right 30004 42001
    refine ⟨_, _, .seq y1 ztffc, rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl,
      rfl, rfl⟩
    · simp [hS₂]
    · simp [hN₂]
    · zuggd
  zuchd
  have hA₃ : ztora := by_grind
  -- memory at the sort
  have mem₃ : ∀ a, c₃.nmem a = recMem c.nmem L A₀ ztgcz K a := fun a => by
    rw [mm₃, I₂.mem, i₂]
  have hbelow : ztfal := fun a ha => by
    zuofm; unfold recMem; zvmyn
  have hrecs : RecsAt c₃.nmem A₀ L := recsAt_of fun q hq => by
    zuofm; unfold recMem; zungc
  have hlist : seg c₃.nmem ztgcz ztbds = List.range ztbds := seg_range fun i hi => by
    zuofm; unfold recMem; rw [ite_eq_right by_omega, ite_eq_left by_omega]; omega
  obtain ⟨hM₃, hwf₃⟩ := desc_agree hwf hM (m' := c₃.nmem) fun a ha => hbelow a ha
  have hwf₃' : ModelDescWF P ztjgn c₃.nmem D := modelDescWF_mono hwf₃ by_omega
  have hD₃ : c₃.nreg 40000 = D := by
    rw [g₃ _ by_norm_num by_norm_num, I₂.fr _ ztjkq,
      fr₁ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, hD]
  have hT₃ : c₃.nreg 42000 = A₀ := by
    rw [g₃ _ by_norm_num by_norm_num, I₂.fr _ ztjkq, r6]
  have hN₃ : c₃.nreg 42001 = 2 * K := by_grind
  -- the sort
  have hcmp := evCmp_ok (P := P) (W := W) hG hWn (A₀ := A₀ + 10 * K) by_omega hwf₃' hM₃ hL
    hrecs by_omega c₃.nreg
  have hJ₃ : EvJ c₃.nmem ztjgn D A₀ ztbds c₃.nreg c₃ :=
    ⟨hD₃, hT₃, hN₃, fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hJs : SortR.JStable (EvJ c₃.nmem ztjgn D A₀ ztbds c₃.nreg) zterl := by
    zvndv; exact evJ_stable _ _ _ _ _ _
  obtain ⟨c₄, k₄, x₄, hk₄, J₄, F₄, e₄, e₄', E, hE, hperm, hsort⟩ :=
    SortR.sortStmt_exec (P := P) (W := W) hcmp by_decide
      ztxgs
      ztxwp w₃ hJ₃ hJs (List.range ztbds)
      (by rw [List.length_range, v30003]; omega) (by rw [List.length_range, v30004])
      (by rw [List.length_range, show ALLOC = 9999 from rfl, hA₃, v30003]; omega)
      (by rw [List.length_range, show ALLOC = 9999 from rfl, hA₃]; omega)
  rw [List.length_range] at hk₄ e₄' hE
  obtain ⟨j1, j2, j3, j4, j5⟩ := J₄
  have X : Exec P W phaseA c c₄ ztwwh := .seq x₁ ztgxf
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := F₄
  have hA₄ : A₀ + 10 * K ≤ c₄.nreg 9999 := by
    zvndv at F6; exact F6
  have hA₄' : c₄.nreg 9999 ≤ A₀ + 10 * K + k₄ := by
    zvndv at F7; exact F7
  zvndv at F3 F4
  refine ⟨c₄, _, X, by unfold costA; omega, x₄.wb_right, ⟨fun r hr hra => ?_, fun r hr => ?_,
    fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩, j1, j2, j3, ?_, ?_, ?_, ?_,
    fun c hc => ?_, ?_, e₄', E, hE, hperm, ?_⟩
  · -- registers outside the bands
    obtain ⟨hr3, hr'⟩ := band_out hr
    have hra' : zteif := hra
    rw [F1 r hr3 hra, g₃ _ by_omega by_omega, I₂.fr _ by_omega]
    exact fr₁ _ by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega hra' by_omega by_omega by_omega by_omega by_omega
  · rw [F2 r (band_out hr).1, rr₃, I₂.rr, rr₁]
  · zufuh
    rw [F3 a ztzwx]
    exact hbelow a ha'
  · zufuh
    rw [F4 a ztzwx, rm₃, I₂.rm, rm₁]
  · rw [F5, out₃, I₂.out, out₁]
  · show A₀ ≤ c₄.nreg 9999; omega
  · show c₄.nreg 9999 ≤ A₀ + _; omega
  · rw [j5 _ by_norm_num by_norm_num, g₃ _ by_norm_num by_norm_num,
      I₂.fr _ ztjkq, r1]
  · rw [j5 _ by_norm_num by_norm_num, g₃ _ by_norm_num by_norm_num, I₂.rK]
  · rw [j5 _ by_norm_num by_norm_num, g₃ _ by_norm_num by_norm_num, I₂.r0]
  · rw [j5 _ by_norm_num by_norm_num, g₃ _ by_norm_num by_norm_num, I₂.r1]
  · obtain ⟨a1, a2, a3, a4⟩ := hrecs c hc
    refine ztfh <;> rw [j4 _ by_omega] <;> assumption
  · zvndv at e₄; omega
  · zuiyq
    zudsq
    zuglw

    have := hab.1
    unfold evLeB at this
    grind
end exec
def curS : Stmt :=
  .seq (.instr (.loadN 43110 43103))
    (.seq (loadRec 43110 43111 42110)
      ztgqt)

/-- The region index of the label into `dst`. -/
def topS (dst : ℕ) : Stmt :=
  .ifLtN 43010 43101 (block [.addN 43116 44006 43101, .subN 43116 43116 43011, .loadN dst 43116])
    ztbfs

/-- The chord record of `x = r43113` at `CT + 5 x`. -/
def chordS : Stmt :=
  .seq (block [.addN 43130 43113 43113, .addN 43130 43130 43113, .addN 43130 43130 43001,
      .loadN 43131 43130, .addN 43130 43130 43011, .loadN 43132 43130, .addN 43130 43130 43011,
      .loadN 43133 43130,
      .addN 43134 43113 43113, .addN 43134 43134 43134, .addN 43134 43134 43113,
      .addN 43134 43134 44001,
      .storeN 43134 43131, .addN 43134 43134 43011, .storeN 43134 43132,
      .addN 43134 43134 43011, .storeN 43134 43133, .addN 43134 43134 43011])
    (.ifLtN 42112 43011
      (block [.storeN 43134 43115, .addN 43134 43134 43011, .storeN 43134 43114])
      (block [.storeN 43134 43114, .addN 43134 43134 43011, .storeN 43134 43115]))

/-- Push `x + 1` after writing the chord record. -/
def pushS : Stmt :=
  .seq chordS (block [.addN 43116 44006 43101, .storeN 43116 43114, .addN 43101 43101 43011])

/-- Pop. -/
def popS : Stmt := .instr (.subN 43101 43101 43011)

/-- One step of the stack pass. -/
def stepS : Stmt := .ifLtN 43115 43114 pushS (.ifLtN 43114 43115 pushS popS)

/-- The arc record at `AT + 5 A` and its weight at `WT + A`. -/
def arcS : Stmt :=
  .seq (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
      .addN 43150 43150 44002,
      .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
      .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
      .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
      .copyN 41110 42113, .copyN 41111 42114])
    (.seq pzR (.seq wtS
      ztgqu))

/-- The gap test and the arc. -/
def gapS : Stmt :=
  .seq (.instr (.addN 43106 43100 43011))
    (.ifLtN 43106 42001
      (.seq (block [.addN 43140 43103 43011, .loadN 43141 43140])
        (.seq ztrtp
          (.seq ztoan
            (.ifLtN 42117 43011 (.seq ztoua arcS) .skip))))
      (.seq (.instr (.loadN 43141 43104))
        (.seq ztrtp (.seq (.instr (.constN 43120 0)) arcS))))

/-- The body of the main pass. -/
def passBody : Stmt :=
  .seq curS (.seq (topS 43115) (.seq stepS (.seq (topS 43117) (.seq gapS
    ztiqq))))

/-- **The main pass.** -/
def passLoop : Stmt := .whileLtN 43100 42001 passBody
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
@[expose] public section
macro "ifs_omega" : tactic =>
  `(tactic| repeat' (first | rw [ite_eq_left by_omega] | rw [ite_eq_right by_omega]))

/-! ## Write sets allowing natural stores -/

/-- `wrOK` with natural stores allowed. -/
def wrOKM (B : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | i => wrOK B i

/-- Every instruction satisfies `wrOKM B`. -/
def wrM (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOKM B i
  | .seq s t => wrM B s && wrM B t
  | .ifLtN _ _ t e => wrM B t && wrM B e
  | .ifLtR _ _ t e => wrM B t && wrM B e
  | .whileLtN _ _ b => wrM B b
  | .whileLtR _ _ b => wrM B b

/-- Registers outside `B`, the real memory and the output agree (the natural memory may change). -/
def FrameM (B : ℕ → Bool) (c c' : Config) : Prop :=
  ztcjh ∧ ztbge ∧
    c'.rmem = c.rmem ∧ c'.output = c.output
theorem FrameM.refl (B : ℕ → Bool) (c : Config) : FrameM B c c :=
  ⟨by_omega, by_simp_all, rfl, rfl⟩
variable {B : ℕ → Bool}
theorem FrameM.trans {c₁ c₂ c₃ : Config} (h₁ : FrameM B c₁ c₂)
    (h₂ : FrameM B c₂ c₃) : FrameM B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans zthhr, fun r hr => (h₂.2.1 r hr).trans ztfsm,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩
theorem FrameM.mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameM B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameM B' c c' :=
  ⟨fun r hr => h.1 r by_grind,
    fun r hr => h.2.1 r by_grind,
    h.2.2.1, h.2.2.2⟩
theorem FrameB.toM {c c' : Config} (h : FrameB B c c') : FrameM B c c' :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **Frame of a statement with natural stores.** -/
theorem exec_frameM {P : Polygon} {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrM B s = true) : FrameM B c c' := by
  induction h with
  | skip _ => exact FrameM.refl B _
  | @instr ins c c' _ he _ _ =>
    zvofk at hs
    cases ins <;> simp only [wrOKM, wrOK, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      refine zthmz <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrM, Bool.and_eq_true] at hs
    zueot
  | ifLtN_true _ _ ih =>
    zufci
  | ifLtN_false _ _ ih =>
    zufcj
  | ifLtR_true _ _ ih =>
    zufci
  | ifLtR_false _ _ ih =>
    zufcj
  | whileLtN_false _ _ => exact FrameM.refl B _
  | whileLtN_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans zthyj
  | whileLtR_false _ _ => exact FrameM.refl B _
  | whileLtR_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans zthyj

/-- A write set without stores allows stores. -/
theorem wrM_of_wr {s : Stmt} (h : wr B s = true) : wrM B s = true := by
  induction s with
  | skip => rfl
  | instr i => zvnhu at h; zvofk; cases i <;> zuoln
  | seq s t ihs iht =>
    zusd
  | ifLtN a b s t ihs iht =>
    zusd
  | ifLtR a b s t ihs iht =>
    zusd
  | whileLtN a b s ih => zvnhu at h; zunbz
  | whileLtR a b s ih => zvnhu at h; zunbz
theorem wrM_mono {B B' : ℕ → Bool} (hB : ∀ r, B r = true → B' r = true) {s : Stmt}
    (h : wrM B s = true) : wrM B' s = true := by
  induction s with
  | skip => rfl
  | instr i => zvofk at h ⊢; cases i <;> zuoln
  | seq s t ihs iht =>
    zuse
  | ifLtN a b s t ihs iht =>
    zuse
  | ifLtR a b s t ihs iht =>
    zuse
  | whileLtN a b s ih => zvofk at h; zunbz
  | whileLtR a b s ih => zvofk at h; zunbz
section exec
variable {P : Polygon} {W : ℕ}
theorem wr_curS : wr (fun r => decide (r = 43110 ∨ r = 43111 ∨ r = 42110 ∨ r = 42111 ∨
    r = 42112 ∨ r = 43113 ∨ r = 43114)) curS = true := by_decide
variable (d : Config)
/-- **The current code.** -/
theorem curS_exec (hw : WordsBounded W d) {c T : ℕ} (hc : d.nmem (d.nreg 43103) = c)
    (hT : d.nreg 42000 = T) (h1 : d.nreg 42102 = 1) (h1' : d.nreg 43011 = 1)
    (hTW : T + 4 * c + 3 ≤ W) (hxW : d.nmem ztcly + 1 ≤ W) :
    ∃ d' k, Exec P W curS d d' k ∧ k = 12 ∧
      d'.nreg 42110 = d.nmem ztjne ∧ d'.nreg 42111 = d.nmem zthcu ∧
      d'.nreg 42112 = d.nmem zthcv ∧ d'.nreg 43113 = d.nmem ztcly ∧
      d'.nreg 43114 = d.nmem ztcly + 1 ∧
      FrameB (fun r => decide (r = 43110 ∨ r = 43111 ∨ r = 42110 ∨ r = 42111 ∨
        r = 42112 ∨ r = 43113 ∨ r = 43114)) d d' := by
  have x₀ := Exec.loadN (P := P) hw 43110 43103
  set d₀ : Config := { d with nreg := upd d.nreg 43110 _ } with hd₀
  zugnw
  obtain ⟨d₁, k₁, x₁, hk₁, e₁, g₁, p₁, fr₁, m₁, -, -, -, a₁⟩ := loadRec_exec (P := P) d₀ w₀
    (src := 43110) (ad := 43111) (o := 42110) (c := c) (T := T)
    by_simp_all by_simp_all by_simp_all
    by_norm_num by_norm_num by_norm_num by_omega by_norm_num by_norm_num
  zubcr
  have o₁ : d₁.nreg 42102 = 1 := by
    simp_all
  have o₁' : d₁.nreg 43011 = 1 := by
    simp_all
  have mm₁ : ztpod := by_omega
  suffices H : ∃ d' k, Exec P W curS d d' k ∧ k = 12 ∧
      d'.nreg 42110 = d.nmem _ ∧ d'.nreg 42111 = d.nmem _ ∧
      d'.nreg 42112 = d.nmem _ ∧ d'.nreg 43113 = d.nmem _ ∧
      d'.nreg 43114 = d.nmem _ + 1 by
    obtain ⟨d', k, x, hk, v1, v2, v3, v4, v5⟩ := H
    exact ⟨d', k, x, hk, v1, v2, v3, v4, v5, exec_frameB x wr_curS⟩
  obtain ⟨d₂, k₂, x₂, hk₂, v₂⟩ : ∃ d₂ k₂, Exec P W
      ztgqt d₁ d₂ k₂ ∧
      k₂ = 3 ∧ d₂.nreg 43113 = d.nmem ztcly ∧
      d₂.nreg 43114 = d.nmem ztcly + 1 ∧
      (∀ r, r ≠ 43111 → r ≠ 43113 → r ≠ 43114 → d₂.nreg r = d₁.nreg r) := by
    exec_block
    · omega
    · simp_all
    simp_all
  obtain ⟨b3, b4, g₂⟩ := v₂
  refine ⟨d₂, _, .seq x₀ (.seq x₁ x₂), by_omega, ?_, ?_, ?_, b3, b4⟩
  · simp_all
  · simp_all
  simp_all
theorem wr_topS (dst : ℕ) : wr ztikg ztwgt = true := by
  simp [topS, wr, block, wrOK]

/-- **The region index of the label.** -/
theorem topS_exec (hw : WordsBounded W d) {dst : ℕ} (h0 : d.nreg 43010 = 0)
    (h1 : d.nreg 43011 = 1) (hSW : d.nreg 44006 + d.nreg 43101 ≤ W) :
    ∃ d' k, Exec P W ztwgt d d' k ∧ k ≤ 5 ∧
      d'.nreg dst = ztfyk ∧
      FrameB ztikg d d' := by
  suffices H : ∃ d' k, Exec P W _ d d' k ∧ k ≤ 5 ∧
      d'.nreg dst = (if d.nreg 43101 = 0 then 0 else d.nmem _) by
    zuwp
    exact ⟨d', k, x, hk, hv, exec_frameB x (wr_topS dst)⟩
  unfold topS
  by_cases hs : d.nreg 43101 = 0
  · refine spec_ifLtN_false by_omega (spec_instr (Exec.constN hw _ _ (by
      omega)) fun _ => ⟨by_omega, ?_⟩)
    simp_all
  · zudd
    exec_block
    · omega
    simp_all

/-- Five consecutive words written at `b`. -/
def wr5 (m : ℕ → ℕ) (b v0 v1 v2 v3 v4 : ℕ) (a : ℕ) : ℕ :=
  if a = b then v0 else if a = b + 1 then v1 else if a = b + 2 then v2 else if a = b + 3 then v3
  else if a = b + 4 then v4 else m a
theorem wr_chordS : wrM ztzfs chordS = true := by_decide

/-- **The chord record** of `x = r43113` at `CT + 5 x`. -/
theorem chordS_exec (hw : WordsBounded W d) {x B CT : ℕ} (hx : d.nreg 43113 = x)
    (hB : d.nreg 43001 = B) (hCT : d.nreg 44001 = CT) (h1 : d.nreg 43011 = 1)
    (hBW : B + 3 * x + 2 ≤ W) (hCW : CT + 5 * x + 4 ≤ W) :
    ∃ d' k, Exec P W chordS d d' k ∧ k ≤ 25 ∧
      d'.nmem = wr5 d.nmem ztpwr ztmih ztkvq
        ztkvr
        ztjyt
        ztjys ∧
      FrameM ztzfs d d' := by
  suffices H : ∃ d' k, Exec P W chordS d d' k ∧ k ≤ 25 ∧
      d'.nmem = wr5 d.nmem _ _ _
        _
        _
        _ by
    zuwp
    exact ⟨d', k, x, hk, hv, exec_frameM x wr_chordS⟩
  unfold chordS
  refine spec_seq ?_
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hx, hB, hCT, h1]; omega)
    | skip
  by_cases hp : d.nreg 42112 < 1
  · refine spec_ifLtN_true (by config_simp; omega) ?_
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [hx, hB, hCT, h1]; omega)
      | skip
    zubsc
    config_simp
    funext a
    simp only [hx, hB, hCT, h1, ite_eq_left hp, upd_apply, wr5]
    grind
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [hx, hB, hCT, h1]; omega)
      | skip
    zubsc
    config_simp
    funext a
    simp only [hx, hB, hCT, h1, ite_eq_right hp, upd_apply, wr5]
    grind

/-- The registers of the stack step. -/
def Bstep (r : ℕ) : Bool := decide ztgzb || decide (r = 43116 ∨ r = 43101)
theorem wr_stepS : wrM Bstep stepS = true := by_decide

/-- The memory after a push. -/
def pushMem (d : Config) (x B CT ST : ℕ) : ℕ → ℕ :=
  upd (wr5 d.nmem ztpwr ztmih ztkvq
    ztkvr
    ztjyt
    ztjys) (ST + d.nreg 43101) (d.nreg 43114)

/-- **The stack step**: pop if the label is `x + 1`, else chord record and push. -/
theorem stepS_exec (hw : WordsBounded W d) {x B CT ST : ℕ} (hx : d.nreg 43113 = x)
    (hB : d.nreg 43001 = B) (hCT : d.nreg 44001 = CT) (hST : d.nreg 44006 = ST)
    (h1 : d.nreg 43011 = 1) (hBW : B + 3 * x + 2 ≤ W) (hCW : CT + 5 * x + 4 ≤ W)
    (hSW : ST + d.nreg 43101 ≤ W) (hsW : d.nreg 43101 + 1 ≤ W) :
    ∃ d' k, Exec P W stepS d d' k ∧ k ≤ 32 ∧ FrameM Bstep d d' ∧
      (d.nreg 43115 = d.nreg 43114 → d'.nreg 43101 = d.nreg 43101 - 1 ∧ d'.nmem = d.nmem) ∧
      (d.nreg 43115 ≠ d.nreg 43114 → d'.nreg 43101 = d.nreg 43101 + 1 ∧
        d'.nmem = pushMem d x B CT ST) := by
  have push : ∃ d' k, Exec P W pushS d d' k ∧ k ≤ 28 ∧ d'.nreg 43101 = d.nreg 43101 + 1 ∧
      d'.nmem = pushMem d x B CT ST := by
    obtain ⟨d₁, k₁, x₁, hk₁, m₁, f₁⟩ := chordS_exec (P := P) d hw hx hB hCT h1 hBW hCW
    zubcr
    have r₁ : ∀ r, (r < 43130 ∨ 43135 ≤ r) → d₁.nreg r = d.nreg r := fun r hr =>
      f₁.1 r by_grind
    unfold pushS
    refine spec_seq ⟨d₁, k₁, x₁, ?_⟩
    exec_block
    · simp_all
    · simp_all
    · refine ztss <;> config_simp
      · simp_all
      · rw [r₁ _ by_norm_num, r₁ _ by_norm_num, r₁ _ by_norm_num, hST, m₁]; rfl
  unfold stepS
  by_cases a1 : d.nreg 43115 < d.nreg 43114
  · zudra
    refine ⟨d', k + 1, .ifLtN_true a1 x', by_omega, exec_frameM (.ifLtN_true a1 x') wr_stepS,
      by grind, by_simp_all⟩
  by_cases a2 : d.nreg 43114 < d.nreg 43115
  · zudra
    have X := Exec.ifLtN_false (t := pushS) a1 (Exec.ifLtN_true (e := popS) a2 x')
    refine ⟨d', _, X, by_omega, exec_frameM X wr_stepS, by_grind,
      by simp_all⟩
  · have x' := Exec.subN (P := P) hw 43101 43101 43011
    have X := Exec.ifLtN_false (t := pushS) a1 (Exec.ifLtN_false (t := pushS) a2 x')
    refine ⟨_, _, X, by_omega, exec_frameM X wr_stepS, fun _ => ztolz,
      by omega⟩
    simp_all
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
@[expose] public section
def Barc (r : ℕ) : Bool :=
  BpzR r || decide ztgza || decide (r = 43150 ∨ r = 43151 ∨ r = 43102) ||
    decide (r = 41110 ∨ r = 41111)
theorem wr_arcS : wrM Barc arcS = true := by
  rfl
theorem Barc_false {r : ℕ} (h : r < 10000 ∨ ztckp ∨ ztgyx ∨
    (41120 ≤ r ∧ r < 43102) ∨ (43102 < r ∧ r < 43121) ∨ (43128 ≤ r ∧ r < 43150) ∨ 43151 < r) :
    Barc r = false := by
  have : BpzR r = false := by
    cases hb : BpzR r
    · rfl
    · have := BpzR_true hb; omega
  simp only [Barc, this, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega
section exec
variable {P : Polygon} {W : ℕ}

/-- **The arc record and its weight.** -/
theorem arcS_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (d : Config)
    (hw : WordsBounded W d) {M : Model} {D H A AT WT : ℕ}
    (hD : d.nreg 40000 = D) (hwf : ModelDescWF P H d.nmem D) (hM : ModelDescAt d.nmem D zta M)
    (hHW : H ≤ W) (h23 : d.nreg 41023 = d.nmem D) (h19 : d.nreg 41019 = 1)
    (hA : d.nreg 43102 = A) (hAT : d.nreg 44002 = AT) (hWT : d.nreg 44007 = WT)
    (h1 : d.nreg 43011 = 1) (hlt : d.nreg 43120 ≤ 1)
    (he : d.nreg 42113 < M.W.n) (hh : d.nreg 42114 ≤ P.n)
    (hATH : H ≤ AT) (_hWTH : H ≤ WT) (hATW : AT + 5 * A + 4 ≤ W) (hWTW : WT + A + 1 ≤ W)
    (hcI : ∀ p, p < M.W.n → zthbh) :
    ∃ d' k, Exec P W arcS d d' k ∧ k ≤ 6040 ∧ FrameM Barc d d' ∧ d'.nreg 43102 = A + 1 ∧
      ∃ pz, pz ≤ 1 ∧ (pz = 1 ↔ M.counted ztgig ∧
          M.param zta ⟨d.nreg 42113, d.nreg 42114⟩ ≠ 0) ∧
        d'.nmem = upd (wr5 d.nmem ztgcx ztmil zthwg ztqlo
          ztgig ztqlp) (WT + A)
          (wtG ztmim ztmin zthwg ztgig pz ztqlq) := by
  -- the record
  obtain ⟨d₁, k₁, x₁, hk₁, m₁, r₁, v110, v111⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
        .addN 43150 43150 44002,
        .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
        .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
        .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
        .copyN 41110 42113, .copyN 41111 42114]) d d₁ k₁ ∧ k₁ = 15 ∧
      d₁.nmem = wr5 d.nmem ztgcx ztmil zthwg ztqlo
          ztgig ztqlp ∧
      FrameM ztgjl d d₁ ∧
      d₁.nreg 41110 = d.nreg 42113 ∧ d₁.nreg 41111 = d.nreg 42114 := by
    have hfr : ∀ {d₁ k₁}, Exec P W
      (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
        .addN 43150 43150 44002,
        .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
        .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
        .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
        .copyN 41110 42113, .copyN 41111 42114]) d d₁ k₁ →
        FrameM ztgjl d d₁ :=
      fun x => exec_frameM x by_decide
    suffices H : ∃ d₁ k₁, Exec P W
      (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
        .addN 43150 43150 44002,
        .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
        .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
        .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
        .copyN 41110 42113, .copyN 41111 42114]) d d₁ k₁ ∧ k₁ = 15 ∧
      d₁.nmem = wr5 d.nmem ztgcx ztmil zthwg ztqlo
          ztgig ztqlp ∧
      d₁.nreg 41110 = d.nreg 42113 ∧ d₁.nreg 41111 = d.nreg 42114 by
      obtain ⟨d₁, k₁, x, hk, hm, h10, h11⟩ := H
      exact ⟨d₁, k₁, x, hk, hm, hfr x, h10, h11⟩
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [hA, hAT, h1]; omega)
      | skip
    refine ⟨rfl, ?_, by config_simp, by config_simp⟩
    config_simp
    funext a
    simp only [hA, hAT, h1, upd_apply, wr5]
    grind
  zubcr
  have g₁ : ∀ r, r ≠ 43150 → r ≠ 41110 → r ≠ 41111 → d₁.nreg r = d.nreg r := fun r a1 a2 a3 =>
    r₁.1 r by_simp_all
  have mH₁ : ∀ a, a < H → d₁.nmem a = d.nmem a := fun a ha => by
    zvmxn; unfold wr5; ifs_omega
  obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM mH₁
  obtain ⟨hDW, hCW⟩ := locChainWF_of hwf₁ hHW hWn
  have hD6 := hwf.1
  zufge
  -- the parameter test
  obtain ⟨d₂, k₂, x₂, hk₂, f₂, pz1, pziff⟩ := pzR_exec (P := P) (M := M) hG hW' d₁ w₁
    (D := D) (e := d.nreg 42113) (h := d.nreg 42114)
    by_simp_all hM₁
    by_grind
    by_simp_all v110 v111 he hh hDW hCW
  zuboj
  have g₂ : ∀ r, BpzR r = false → d₂.nreg r = d₁.nreg r := f₂.1
  have bz : ∀ r, (r < 10000 ∨ ztckp ∨ ztgyx ∨
      41120 ≤ r) → BpzR r = false := fun r hr => by
    cases hb : BpzR r
    · rfl
    · have := BpzR_true hb; omega
  -- the weight
  have e₁₁ : ztutz := by
    grind
  have e₁₂₀ : d₂.nreg 43120 = d.nreg 43120 := by
    grind
  have e₁₁₃ : d₂.nreg 42113 = d.nreg 42113 := by
    grind
  have e₁₁₀ : d₂.nreg 42110 = d.nreg 42110 := by
    grind
  have e₂₀ : d₂.nreg 44020 = d.nreg 44020 := by
    grind
  have e₂₁ : d₂.nreg 44021 = d.nreg 44021 := by
    grind
  have hbound : d.nreg 42113 - d.nreg 44020 + d₂.nreg 41112 ≤ W := by
    by_cases hp : d₂.nreg 41112 = 1
    · have := ((hcI _ he).1 (pziff.1 hp).1)
      have := hw.1 44021
      omega
    · have := hw.1 42113
      omega
  obtain ⟨d₃, k₃, x₃, hk₃, v₃, f₃⟩ := wtS_exec (P := P) d₂ w₂ e₁₁ by_omega
    by_omega
  zuchd
  have g₃ : ∀ r, (r < 43121 ∨ 43128 ≤ r) → d₃.nreg r = d₂.nreg r := fun r hr =>
    f₃.1 r by_grind
  have g₃₁ : ∀ r, (r < 10000 ∨ ztckp ∨ ztgyx ∨
      (41120 ≤ r ∧ r < 43121) ∨ 43128 ≤ r) → r ≠ 43150 → d₃.nreg r = d.nreg r := fun r hr hr' => by
    rw [g₃ r by_omega, g₂ _ (bz _ by_omega), g₁ _ hr' by_omega by_omega]
  -- the weight into its table
  obtain ⟨d₄, k₄, x₄, hk₄, v₄, m₄, a₄⟩ : ∃ d₄ k₄, Exec P W
      ztgqu d₃ d₄ k₄ ∧
      k₄ = 3 ∧ d₄.nreg 43102 = A + 1 ∧ d₄.nmem = upd d₃.nmem (WT + A) (d₃.nreg 43121) ∧
      (∀ r, r ≠ 43151 → r ≠ 43102 → d₄.nreg r = d₃.nreg r) := by
    have r1 := g₃₁ 44007 by_omega by_norm_num
    have r2 := g₃₁ 43102 by_omega by_norm_num
    have r3 := g₃₁ 43011 by_omega by_norm_num
    exec_block
    · omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_⟩ <;> config_simp
      · omega
      · grind
      · zuro
  have X : Exec P W arcS d d₄ ztwwh := .seq x₁ ztgxf
  refine ⟨d₄, _, X, by_omega, exec_frameM X wr_arcS, v₄, d₂.nreg 41112, pz1, pziff, ?_⟩
  rw [m₄, f₃.2.2.1, f₂.2.2.1, m₁, v₃, e₁₁₀, e₁₁₃, e₂₀, e₂₁, e₁₂₀]
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (wposOf)
@[expose] public section
def Bgap (r : ℕ) : Bool :=
  Barc r || BhalfS 42116 42117 r || decide (r = 43106 ∨ r = 43140 ∨ r = 43141 ∨ r = 43142) ||
    decide (42113 ≤ r ∧ r < 42116) || decide (r = 43120)
theorem wr_gapS : wrM Bgap gapS = true := by
  have h1 : wrM Bgap arcS = true := wrM_mono ztjwh wr_arcS
  have h2 : wrM Bgap ztoan = true :=
    wrM_of_wr (wr_mono ztjwh wr_halfS)
  simp only [gapS, wrM, block, loadRec, h1, h2, Bool.and_true, Bool.true_and]
  decide
variable {r : ℕ}
theorem Bgap_false (h : r < 10000 ∨ ztckp ∨ ztgyy ∨
    (41120 ≤ r ∧ r < 42113) ∨ (42117 < r ∧ r < 43102) ∨ (43102 < r ∧ r < 43106) ∨
    (43106 < r ∧ r < 43120) ∨ (43128 ≤ r ∧ r < 43140) ∨ ztgzc ∨ 43151 < r) :
    Bgap r = false := by
  have ha := Barc_false (r := r) by_omega
  simp only [Bgap, ha, BhalfS, Bhalf, Bool.false_or, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega
theorem bhalf_of_bgap (h : Bgap r = false) : BhalfS 42116 42117 r = false := by
  simp only [Bgap, Bool.or_eq_false_iff] at h; simp_all
theorem ne_of_bgap (h : Bgap r = false) : r ≠ 43106 ∧ r ≠ 43140 ∧ r ≠ 43141 ∧
    r ≠ 43142 ∧ r ≠ 42113 ∧ r ≠ 42114 ∧ r ≠ 42115 ∧ r ≠ 43120 := by
  simp only [Bgap, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  omega
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
/-- **The gap test and the arc.** -/
theorem gapS_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (d : Config)
    (hw : WordsBounded W d) {M : Model} {L : List zte} {E : List ℕ}
    {D H T SE m A AT WT : ℕ} (hL : ChordTriplesOK M zta L)
    (hElen : E.length = 2 * L.length) (hEc : ∀ j, j < E.length → E.getD j 0 < 2 * L.length)
    (hm : m < E.length) (h100 : d.nreg 43100 = m) (hN : d.nreg 42001 = E.length)
    (h103 : d.nreg 43103 = SE + m) (h104 : d.nreg 43104 = SE)
    (hSE : ∀ j, j < E.length → d.nmem ztjmr = E.getD j 0)
    (hT : d.nreg 42000 = T) (hR : RecsAt d.nmem T L) (h102 : d.nreg 42102 = 1)
    (h110 : d.nreg 42110 = (wposOf L ztbgr).edge)
    (h111 : d.nreg 42111 = (wposOf L ztbgr).hgt)
    (hD : d.nreg 40000 = D) (hwf : ModelDescWF P H d.nmem D) (hM : ModelDescAt d.nmem D zta M)
    (hHW : H ≤ W) (h23 : d.nreg 41023 = d.nmem D) (h19 : d.nreg 41019 = 1)
    (hA : d.nreg 43102 = A) (hAT : d.nreg 44002 = AT) (hWT : d.nreg 44007 = WT)
    (h1 : d.nreg 43011 = 1) (hATH : H ≤ AT) (hWTH : H ≤ WT)
    (hATW : AT + 5 * A + 4 ≤ W) (hWTW : WT + A + 1 ≤ W) (hTW : T + 8 * L.length ≤ H)
    (hSEW : SE + E.length ≤ W)
    (hcI : ∀ p, p < M.W.n → zthbh) :
    ∃ d' k, Exec P W gapS d d' k ∧ k ≤ 11600 ∧ FrameM Bgap d d' ∧
      ((m + 1 = E.length ∨ M.key zta ztwwn <
          M.key zta ztbalg) →
        d'.nreg 43102 = A + 1 ∧
        ∃ pz, pz ≤ 1 ∧ (pz = 1 ↔ M.counted (wposOf L ztwkh).edge ∧
            M.param zta ztbalg ≠ 0) ∧
          d'.nmem = upd (wr5 d.nmem ztgcx ztmil
              (wposOf L ztbgr).edge (wposOf L ztbgr).hgt
              (wposOf L ztwkh).edge
              (wposOf L ztwkh).hgt) (WT + A)
            (wtG ztmim ztmin (wposOf L ztbgr).edge
              (wposOf L ztwkh).edge pz
              ztkwo)) ∧
      (¬ (m + 1 = E.length ∨ M.key zta ztwwn <
          M.key zta ztbalg) →
        d'.nreg 43102 = A ∧ d'.nmem = d.nmem) := by
  zubp
  zufge
  have hHW' := hwf.1
  obtain ⟨hDW, hCW⟩ := locChainWF_of hwf hHW hWn
  zukzm
  set m' := ztbl % N with hm'
  have hm'N : m' < N := Nat.mod_lt _ by_omega
  zuiod
  set c' := E.getD m' 0 with hc'
  have hcK := hEc m hm
  have hc'K := hEc m' hm'N
  have pe := properPos_ev hL hc'K
  have ee := edge_lt hL hc'K
  obtain ⟨r0, r1, -, -⟩ := hR c' hc'K
  -- the step `m + 1`
  have x₀ := Exec.addN (P := P) hw 43106 43100 43011 by_omega
  set d₀ : Config := { d with nreg := upd d.nreg 43106 _ } with hd₀
  zugnw
  have g₀ : ∀ r, r ≠ 43106 → d₀.nreg r = d.nreg r := fun r hr => by rw [hd₀]; zumwy
  have v₀ : d₀.nreg 43106 = m + 1 := by rw [hd₀]; simp [h100, h1]
  -- loading the end code and its record, common to both branches
  have load : ∀ {e : Config}, WordsBounded W e → e.nmem = d.nmem → e.nreg 43141 = c' →
      e.nreg 42000 = T → e.nreg 42102 = 1 →
      ∃ e' k, Exec P W _ e e' k ∧ k = 8 ∧
        e'.nreg 42113 = (wposOf L c').edge ∧ e'.nreg 42114 = (wposOf L c').hgt ∧
        (∀ r, r ≠ 43142 → r ≠ 42113 → r ≠ 42114 → r ≠ 42115 → e'.nreg r = e.nreg r) ∧
        e'.nmem = e.nmem := fun {e} we me e141 e42 e102 => by
    obtain ⟨e', k, x, hk, v1, v2, -, fr, mm, -⟩ := loadRec_exec (P := P) e we
      (src := 43141) (ad := 43142) (o := 42113) (c := c') (T := T) e141 e42 e102
      by_norm_num by_norm_num by_norm_num by_omega by_norm_num by_norm_num
    exact ⟨e', k, x, hk, by_grind, by_grind, fr, mm⟩
  -- the arc, common to both branches
  have arc : ∀ {e : Config}, WordsBounded W e → e.nmem = d.nmem →
      (∀ r, Bgap r = false → e.nreg r = d.nreg r) → e.nreg 43102 = A →
      e.nreg 42110 = d.nreg 42110 →
      e.nreg 42113 = (wposOf L c').edge → e.nreg 42114 = (wposOf L c').hgt →
      e.nreg 43120 = (if m + 1 < N then 1 else 0) → e.nreg 43117 = d.nreg 43117 →
      e.nreg 44020 = d.nreg 44020 → e.nreg 44021 = d.nreg 44021 →
      ∃ e' k, Exec P W arcS e e' k ∧ k ≤ 6040 ∧ FrameM Barc e e' ∧ e'.nreg 43102 = A + 1 ∧
        ∃ pz, pz ≤ 1 ∧ (pz = 1 ↔ M.counted (wposOf L c').edge ∧
            M.param _ ztbuh ≠ 0) ∧
          e'.nmem = upd _ _
            _ :=
      fun {e} we me fe e102 e110 e113 e114 e120 e117 e20 e21 => by
    obtain ⟨e', k, x, hk, fr, v, pz, pz1, pziff, mm⟩ := arcS_exec (P := P) hG hWn e we (M := M)
      (D := D) (H := H) (A := A) (AT := AT) (WT := WT)
      (by rw [fe _ ztbls, hD]) by_grind by_grind hHW
      (by rw [fe _ ztbls, h23, me]) (by rw [fe _ ztbls, h19])
      e102 (by rw [fe _ ztbls, hAT])
      (by rw [fe _ ztbls, hWT]) (by rw [fe _ ztbls, h1])
      (by rw [e120]; split_ifs <;> omega) by_grind (by rw [e114]; exact pe.2.2)
      hATH hWTH hATW hWTW (by rw [e20, e21]; omega)
    refine ⟨e', k, x, hk, fr, v, pz, pz1, by rw [e113, e114] at pziff; omega, ?_⟩
    rw [mm, me, e117, e110, h110, fe 42111 ztbls, h111, e113, e114, e20, e21,
      e120]
  unfold gapS
  refine spec_seq ⟨d₀, 1, x₀, ?_⟩
  have hsame : d₀.nmem = d.nmem := rfl
  by_cases hlt : m + 1 < N
  · -- no wrap: compare with `E[m + 1]`
    have hm'e : m' = m + 1 := Nat.mod_eq_of_lt hlt
    refine spec_ifLtN_true ztbpw ?_
    obtain ⟨d₁, X1, g₁, v₁, mm₁⟩ : ∃ d₁, Exec P W _ d₀ d₁ 2 ∧ (∀ r, r ≠ 43140 → r ≠ 43141 → d₁.nreg r = d₀.nreg r) ∧
        d₁.nreg 43141 = c' ∧ d₁.nmem = d.nmem := by
      have y1 := Exec.addN (P := P) w₀ 43140 43103 43011 (by
        rw [g₀ _ by_norm_num, g₀ _ by_norm_num, h103, h1]; omega)
      have y2 := Exec.loadN (P := P) y1.wb_right 43141 43140
      refine ⟨_, .seq y1 ztffc, fun r a1 a2 => by zungb, ?_, rfl⟩
      zufb
      rw [g₀ _ by_norm_num, g₀ _ by_norm_num, h103, h1, hsame, show SE + m + 1 = SE + ztbl
        by omega, hSE _ hlt, hc', hm'e]
    zumfu
    obtain ⟨d₂, k₂, x₂, hk₂, e₂, h₂, g₂, mm₂⟩ := load w₁ mm₁ v₁
      (by rw [g₁ _ by_norm_num by_norm_num, g₀ _ by_norm_num, hT])
      (by rw [g₁ _ by_norm_num by_norm_num, g₀ _ by_norm_num, h102])
    zuboj
    have G₂ : ∀ r, r ≠ 43106 → r ≠ 43140 → r ≠ 43141 → r ≠ 43142 → r ≠ 42113 → r ≠ 42114 →
        r ≠ 42115 → d₂.nreg r = d.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
      rw [g₂ r a4 a5 a6 a7, g₁ r a2 a3, g₀ r a1]
    have hD₂ : ztuty := by
      rw [G₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num, hD]
    have mm₂' : ztmvn := by rw [mm₂, mm₁]
    have pc := properPos_ev hL hcK
    have ec := edge_lt hL hcK
    obtain ⟨d₃, k₃, x₃, hk₃, -, dst₃, f₃⟩ := halfS_exec hG hW' d₂ w₂
      (qe := 42110) (qh := 42111) (se := 42113) (sh := 42114) (dd := 42116) (dst := 42117)
      by_decide by_decide by_decide by_omega by_grind
      (M := M) by_grind
      (by rw [G₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, h110]; exact ec)
      (by rw [G₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, h111]; exact pc.2.2)
    zuchd
    have hbit : d₃.nreg 42117 = if M.key zta ztbuh ≤ M.key zta ztbbg
        then 1 else 0 := by
      rw [dst₃, G₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, G₂ 42111 by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num by_norm_num by_norm_num, h110, h111, e₂, h₂]
      have := keyDec_ev hL hc'K hcK
      by_cases hk : M.key zta ztbuh ≤ M.key zta ztbbg
      · zuedi
      · rw [ite_eq_right ztmjm, ite_eq_right hk]
    have G₃ : ∀ r, Bgap r = false → d₃.nreg r = d.nreg r := fun r hr => by
      zucob
      rw [f₃.1 r (bhalf_of_bgap hr), G₂ r n1 n2 n3 n4 n5 n6 n7]
    have o₃ : d₃.nreg 43011 = 1 := by rw [G₃ _ ztbls, h1]
    have mm₃ : ztpoi := by rw [f₃.2.2.1, mm₂']
    have e113₃ : d₃.nreg 42113 = (wposOf L c').edge := by rw [f₃.1 _ by_decide, e₂]
    have e114₃ : d₃.nreg 42114 = (wposOf L c').hgt := by rw [f₃.1 _ by_decide, h₂]
    have e102₃ : d₃.nreg 43102 = A := by
      rw [f₃.1 _ by_decide, G₂ _ by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num by_norm_num, hA]
    have X0 : ∀ {s : Stmt} {d' : Config} {k : ℕ}, Exec P W s d₃ d' k →
        Exec P W _
          d₀ d' _ := fun x => .seq X1 (.seq x₂ (.seq x₃ x))
    by_cases hg : M.key zta ztbbg < M.key zta ztbuh
    · -- a gap: the arc
      have b0 : d₃.nreg 42117 = 0 := by rw [hbit, ite_eq_right (not_le.2 hg)]
      have z1 := Exec.constN (P := P) w₃ 43120 1 by_omega
      set d₄ : Config := { d₃ with nreg := upd d₃.nreg 43120 1 } with hd₄
      have g₄ : ∀ r, r ≠ 43120 → d₄.nreg r = d₃.nreg r := fun r hr => by zungl; zumwy
      obtain ⟨d₅, k₅, x₅, hk₅, fr₅, v₅, pz, pz1, pziff, mm₅⟩ := arc z1.wb_right
        by_omega
        (fun r hr => by rw [g₄ r (ne_of_bgap hr).2.2.2.2.2.2.2, G₃ r hr])
        (by rw [g₄ _ by_norm_num, e102₃])
        ztwrq
        (by rw [g₄ _ by_norm_num, e113₃]) (by rw [g₄ _ by_norm_num, e114₃])
        ztktl
        ztwrq
        ztwrq
        ztwrq
      have X := X0 (.ifLtN_true (e := .skip)
        (show d₃.nreg 42117 < d₃.nreg 43011 by rw [b0, o₃]; omega) ztsqk)
      refine ⟨d₅, _, X, by_omega, exec_frameM ztyot wr_gapS,
        fun _ => ztlwq, (absurd (Or.inr hg))⟩
    · -- no gap
      have b1 : d₃.nreg 42117 = 1 := by rw [hbit, ite_eq_left (not_lt.1 hg)]
      have X := X0 (.ifLtN_false (t := .seq ztoua arcS)
        (show ¬ d₃.nreg 42117 < d₃.nreg 43011 by rw [b1, o₃]; omega) ztpsb)
      refine ⟨d₃, _, X, by_omega, exec_frameM ztyot wr_gapS,
        fun h => absurd h (by rintro (h | h); omega; exact hg h), fun _ => ⟨e102₃, mm₃⟩⟩
  · -- the wrap: the end is `E[0]`
    have hmN : m + 1 = N := by_omega
    have hm'e : m' = 0 := by rw [hm', hmN, Nat.mod_self]
    refine spec_ifLtN_false ztbpw ?_
    have y1 := Exec.loadN (P := P) w₀ 43141 43104
    obtain ⟨d₁, X1, g₁, v₁, mm₁⟩ : ∃ d₁, Exec P W _ d₀ d₁ 1 ∧
        (∀ r, r ≠ 43141 → d₁.nreg r = d₀.nreg r) ∧ d₁.nreg 43141 = c' ∧ d₁.nmem = d.nmem := by
      refine ⟨_, y1, fun r a1 => by simp [a1], ?_, rfl⟩
      zufb
      rw [g₀ _ by_norm_num, h104, hsame, ← Nat.add_zero SE, hSE 0 by_omega, hc', hm'e]
    zumfu
    obtain ⟨d₂, k₂, x₂, hk₂, e₂, h₂, g₂, mm₂⟩ := load w₁ mm₁ v₁
      (by rw [g₁ _ by_norm_num, g₀ _ by_norm_num, hT])
      (by rw [g₁ _ by_norm_num, g₀ _ by_norm_num, h102])
    zuboj
    have G₂ : ∀ r, Bgap r = false → d₂.nreg r = d.nreg r := fun r hr => by
      zucob
      rw [g₂ r n4 n5 n6 n7, g₁ r n3, g₀ r n1]
    have e102₂ : d₂.nreg 43102 = A := by
      rw [g₂ _ by_norm_num by_norm_num by_norm_num by_norm_num, g₁ _ by_norm_num,
        g₀ _ by_norm_num, hA]
    have z1 := Exec.constN (P := P) w₂ 43120 0 ztbg
    set d₄ : Config := { d₂ with nreg := upd d₂.nreg 43120 0 } with hd₄
    have g₄ : ∀ r, r ≠ 43120 → d₄.nreg r = d₂.nreg r := fun r hr => by zungl; zumwy
    obtain ⟨d₅, k₅, x₅, hk₅, fr₅, v₅, pz, pz1, pziff, mm₅⟩ := arc z1.wb_right
      by_grind
      (fun r hr => by rw [g₄ r (ne_of_bgap hr).2.2.2.2.2.2.2, G₂ r hr])
      (by rw [g₄ _ by_norm_num, e102₂])
      ztwrp
      (by rw [g₄ _ by_norm_num, e₂]) (by rw [g₄ _ by_norm_num, h₂])
      ztktl
      ztwrp
      ztwrp
      ztwrp
    have X : Exec P W _ d₀ d₅ _ :=
      .seq X1 (.seq x₂ ztsqk)
    refine ⟨d₅, _, X, by_omega, exec_frameM (Exec.seq x₀ (Exec.ifLtN_false ztbpw X)) wr_gapS,
      fun _ => ztlwq, by_omega⟩
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (wposOf chordRec arcRec arcW cw stk topR gapP gapsB cf af)
@[expose] public section
structure PassFix (P : Polygon) (W : ℕ) (M : Model) (L : List zte) (E : List ℕ)
    (D H T SE B CT AT ST WT lo hd : ℕ) (mB : ℕ → ℕ) : Prop where
  inp : BuildNF.Input M zta L E
  good : GoodEnv P
  hwords : hostWords P.n ≤ W
  len : E.length = 2 * L.length
  wf : ModelDescWF P H mB D
  desc : ModelDescAt mB D zta M
  HW : H ≤ W
  recs : RecsAt mB T L
  TH : T + 8 * L.length ≤ H
  chl : ChordListAt mB B L
  BH : B + 3 * L.length ≤ H
  codes : ∀ j, j < E.length → mB ztjmr = E.getD j 0
  SEH : SE + E.length ≤ H
  l1 : H ≤ CT
  l2 : CT + 5 * L.length ≤ AT
  l3 : AT + 5 * E.length ≤ ST
  l4 : ST + E.length ≤ WT
  l5 : WT + E.length ≤ W
  cnt : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < lo + hd)
  cntW : lo + hd ≤ M.W.n

/-- The registers the main pass writes. -/
def Bpass (r : ℕ) : Bool :=
  Bgap r || Bstep r || decide (r = 43110 ∨ r = 43111 ∨ r = 42110 ∨ r = 42111 ∨ r = 42112 ∨
    r = 43113 ∨ r = 43114 ∨ r = 43115 ∨ r = 43116 ∨ r = 43117 ∨ r = 43100 ∨ r = 43103)

/-- **The invariant of the main pass** after `m` codes. -/
structure PassInv {P : Polygon} {W : ℕ} {M : Model} {L : List zte} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) (c₀ d : Config) (m : ℕ) : Prop where
  m_le : m ≤ E.length
  r100 : d.nreg 43100 = m
  r103 : d.nreg 43103 = SE + m
  r104 : d.nreg 43104 = SE
  r101 : d.nreg 43101 = (stk E m).length
  sp_le : (stk E m).length ≤ m
  r102 : d.nreg 43102 = (gapsB M zta L E m).length
  rD : d.nreg 40000 = D
  rT : d.nreg 42000 = T
  rN : d.nreg 42001 = E.length
  r1a : d.nreg 42102 = 1
  rB : d.nreg 43001 = B
  r0 : d.nreg 43010 = 0
  r1 : d.nreg 43011 = 1
  rCT : d.nreg 44001 = CT
  rAT : d.nreg 44002 = AT
  rST : d.nreg 44006 = ST
  rWT : d.nreg 44007 = WT
  rlo : d.nreg 44020 = lo
  rhd : d.nreg 44021 = hd
  r19 : d.nreg 41019 = 1
  r23 : d.nreg 41023 = mB D
  low : ∀ a, a < H → d.nmem a = mB a
  stack : ∀ k, k < (stk E m).length → d.nmem zttcw = (stk E m).getD k 0 + 1
  chords : ∀ x, x < L.length → x ∈ (cw E).take m → ∀ f, f < 5 →
    d.nmem (CT + 5 * x + f) = cf (chordRec M zta L E x) f
  arcs : ∀ j, j < (gapsB M zta L E m).length →
    (∀ f, f < 5 → d.nmem ztgzs =
      af ztxeu f) ∧
    d.nmem ztjnq = arcW M zta ztxeu
  frame : FrameM Bpass c₀ d
theorem wr5_in (m : ℕ → ℕ) (b v0 v1 v2 v3 v4 f : ℕ) (hf : f < 5) :
    wr5 m b v0 v1 v2 v3 v4 (b + f) =
      if f = 0 then v0 else if f = 1 then v1 else if f = 2 then v2 else if f = 3 then v3 else v4 := by
  unfold wr5
  grind
theorem wr5_out (m : ℕ → ℕ) (b v0 v1 v2 v3 v4 a : ℕ) (ha : a < b ∨ b + 5 ≤ a) :
    wr5 m b v0 v1 v2 v3 v4 a = m a := by
  unfold wr5
  ifs_omega
section exec
variable {P : Polygon} {W : ℕ}

/-- The stack top from the invariant. -/
theorem PassInv.top {M : Model} {L : List zte} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    {F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB} {c₀ d : Config} {m : ℕ}
    (I : PassInv F c₀ d m) :
    ztfyk = topR E m := by
  rw [BuildNF.topR_eq, I.r101, I.rST]
  zus
  · rfl
  · rw [show ST + (stk E m).length - 1 = ST + ztlzo by omega]
    exact I.stack _ by_omega
end exec
theorem wr_passBody : wrM Bpass passBody = true := by
  have h1 : wrM Bpass curS = true := wrM_of_wr (wr_mono (fun r hr => by
    zucy
    zunvy; omega) wr_curS)
  have h2 : ∀ dst, (dst = 43115 ∨ dst = 43117) → wrM Bpass _ = true := fun dst hd =>
    wrM_of_wr (wr_mono (fun r hr => by
      zucy
      zunvy; omega) (wr_topS dst))
  have h3 : wrM Bpass stepS = true := wrM_mono ztjwi wr_stepS
  have h4 : wrM Bpass gapS = true := wrM_mono ztjwi wr_gapS
  simp only [passBody, wrM, block, h1, h2 43115 ztp, h2 43117 ztbt, h3, h4,
    Bool.and_true, Bool.true_and]
  decide
theorem Bpass_false {r : ℕ} (h : r < 10000 ∨ ztckp ∨ ztgyy ∨
    ztngl ∨ ztngm ∨ ztngn ∨
    ztngo ∨ ztgyz ∨ ztngp ∨
    ztngq ∨ ztngr ∨ ztgzc ∨ 43151 < r) :
    Bpass r = false := by
  have hg := Bgap_false (r := r) by_omega
  simp only [Bpass, hg, Bstep, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega
theorem getD_dropLast {l : List ℕ} {k : ℕ} (hk : k < l.dropLast.length) :
    l.dropLast.getD k 0 = l.getD k 0 := by
  grind
section step
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **One iteration of the main pass.** -/
theorem passBody_step {M : Model} {L : List zte} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) {c₀ d : Config} {m : ℕ}
    (I : PassInv F c₀ d m) (hm : m < E.length) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W passBody d d' k ∧ k ≤ 11700 ∧ 12 ≤ k ∧ WordsBounded W d' ∧
      PassInv F c₀ d' ztbl := by
  have hN := F.len
  zukzj
  zukzm
  have hl1 := F.l1; have hl2 := F.l2; have hl3 := F.l3; have hl4 := F.l4; have hl5 := F.l5
  have hTH := F.TH; have hBH := F.BH; have hSEH := F.SEH; have hHW := F.HW
  zuiod
  have hcN : c < N := by have := BuildNF.getD_lt_of_perm F.inp.perm hm; omega
  set x := c / 2 with hx
  zukgz
  obtain ⟨re, rh, rpar, rch⟩ := F.recs c by_omega
  have lowd := I.low
  -- 1. the current code
  obtain ⟨d₁, k₁, x₁, hk₁, v10, v11, v12, v13, v14, f₁⟩ := curS_exec (P := P) d hw (c := c)
    (T := T) (by rw [I.r103, lowd _ by_omega, F.codes m hm]) I.rT I.r1a I.r1 by_omega
    by_grind
  rw [lowd _ by_omega, re] at v10
  rw [lowd _ by_omega, rh] at v11
  rw [lowd _ by_omega, rpar] at v12
  rw [lowd _ by_omega, rch] at v13 v14
  zubcr
  have g₁ : ∀ r, Bpass r = false → d₁.nreg r = d.nreg r := fun r hr => f₁.1 r (by
    simp only [Bpass, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    simp_all)
  have mm₁ := f₁.2.2.1
  have s₁ : d₁.nreg 43101 = d.nreg 43101 := f₁.1 _ by_decide
  -- 2. the label before
  obtain ⟨d₂, k₂, x₂, hk₂, v15, f₂⟩ := topS_exec (P := P) d₁ w₁ (dst := 43115)
    (by rw [g₁ 43010 ztffg, I.r0])
    (by rw [g₁ 43011 ztffg, I.r1])
    (by rw [g₁ 44006 ztffg, s₁, I.rST, I.r101]; have := I.sp_le; omega)
  rw [g₁ 44006 ztffg, s₁, mm₁, I.top] at v15
  zuboj
  have g₂ : ∀ r, r ≠ 43115 → r ≠ 43116 → d₂.nreg r = d₁.nreg r := fun r a1 a2 => f₂.1 r (by
    simp_all)
  have mm₂ : ztmvn := by rw [f₂.2.2.1, mm₁]
  -- 3. the stack step
  have x13 : d₂.nreg 43113 = x := by_simp_all
  have x14 : d₂.nreg 43114 = x + 1 := by_simp_all
  have x12 : d₂.nreg 42112 = c % 2 := by_simp_all
  have b₂ : d₂.nreg 43001 = B := by
    rw [g₂ _ by_norm_num by_norm_num, g₁ 43001 ztffg, I.rB]
  have ct₂ : d₂.nreg 44001 = CT := by
    rw [g₂ _ by_norm_num by_norm_num, g₁ 44001 ztffg, I.rCT]
  have st₂ : d₂.nreg 44006 = ST := by
    rw [g₂ _ by_norm_num by_norm_num, g₁ 44006 ztffg, I.rST]
  have o₂ : ztutz := by
    rw [g₂ _ by_norm_num by_norm_num, g₁ 43011 ztffg, I.r1]
  have sp₂ : d₂.nreg 43101 = (stk E m).length := by
    rw [g₂ _ by_norm_num by_norm_num, s₁, I.r101]
  have hsp := I.sp_le
  obtain ⟨d₃, k₃, x₃, hk₃, f₃, hpop, hpush⟩ := stepS_exec (P := P) d₂ w₂ (x := x) (B := B)
    (CT := CT) (ST := ST) x13 b₂ ct₂ st₂ o₂ by_omega by_omega by_omega
    by_omega
  zuchd
  have hpopiff : d₂.nreg 43115 = d₂.nreg 43114 ↔ x ∈ (cw E).take m := by
    rw [v15, x14]; exact F.inp.pop_iff hm
  have htake := BuildNF.take_succ_cw hm
  have S₃ : d₃.nreg 43101 = (stk E ztbl).length ∧ (stk E ztbl).length ≤ m + 1 ∧
      (∀ k, k < (stk E ztbl).length → d₃.nmem zttcw = (stk E ztbl).getD k 0 + 1) ∧
      (∀ a, zteop → d₃.nmem a = d.nmem a) ∧
      (∀ x', x' < K → x' ∈ (cw E).take ztbl → ∀ f, f < 5 →
        d₃.nmem (CT + 5 * x' + f) = cf (chordRec M zta L E x') f) := by
    by_cases hin : x ∈ (cw E).take m
    · -- pop
      obtain ⟨p1, p2⟩ := hpop (hpopiff.2 hin)
      have hh := (BuildNF.topR_eq_succ_iff E m x).1 by_grind
      obtain ⟨e1, e2⟩ := BuildNF.stk_pop hm hh
      refine ⟨by_omega, by_omega, fun k hk => ?_, by_grind,
        fun x' hx' hin' f hf => ?_⟩
      · rw [p2, mm₂, I.stack k by_omega, e1, getD_dropLast by_grind]
      · rw [p2, mm₂]
        zuduq

        · zuisq
        · subst h'; exact I.chords _ hx' hin f hf
    · -- push
      obtain ⟨p1, p2⟩ := hpush by_grind
      have hh : ¬ (BuildStack.run _).head? = some _ := fun h' =>
        hin ((F.inp.pop_iff hm).1 ((BuildNF.topR_eq_succ_iff E m x).2 h'))
      have e1 := BuildNF.stk_push hm hh
      have hlen : (stk E ztbl).length = (stk E m).length + 1 := by zvmxy; simp
      unfold pushMem at p2
      rw [sp₂, x14, x12, v15] at p2
      refine ⟨by_omega, by_omega, fun k hk => ?_, fun a ha => ?_,
        fun x' hx' hin' f hf => ?_⟩
      · rw [p2]
        by_cases hk' : k = (stk E m).length
        · zujpq
          rw [upd_same, e1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
        · rw [upd_other _ _ _ by_omega, wr5_out _ _ _ _ _ _ _ _ by_omega, mm₂,
            I.stack k by_omega, e1, List.getD_append _ _ _ _ by_omega]
      · rw [p2, upd_other _ _ _ by_omega, wr5_out _ _ _ _ _ _ _ _ by_omega, mm₂]
      · rw [p2, upd_other _ _ _ by_omega]
        zuduq

        · have hne : x' ≠ x := by_grind
          rw [wr5_out _ _ _ _ _ _ _ _ by_omega, mm₂]
          zuisq
        · zumqa
          rw [wr5_in _ _ _ _ _ _ _ _ hf, F.inp.chordRec_new hm hxK hin, BuildNF.cf_mk, mm₂]
          obtain ⟨l1, l2, l3⟩ := F.chl x hxK
          rw [lowd _ by_omega, lowd _ by_omega, lowd _ by_omega, l1, l2, l3]
  obtain ⟨sp₃, spl₃, stk₃, oth₃, ch₃⟩ := S₃
  have g₃ := fun r hr => f₃.1 r (by
    simp only [Bstep, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 4. the label after
  have G₂ : ∀ r, (r < 42110 ∨ (42112 < r ∧ r < 43110) ∨ ztgyz ∨
      (43114 < r ∧ r < 43115) ∨ 43116 < r) → d₂.nreg r = d.nreg r := fun r hr => by
    rw [g₂ r by_omega by_omega]
    exact f₁.1 r ztmz
  obtain ⟨d₄, k₄, x₄, hk₄, v17, f₄⟩ := topS_exec (P := P) d₃ w₃ (dst := 43117)
    (by rw [g₃ 43010 by_omega, G₂ 43010 by_omega, I.r0])
    (by rw [g₃ 43011 by_omega, o₂])
    (by rw [g₃ 44006 by_omega, st₂, sp₃]; omega)
  have top₃ : (if d₃.nreg 43101 = 0 then 0 else d₃.nmem (d₃.nreg 44006 + d₃.nreg 43101 - 1)) =
      topR E ztbl := by
    rw [BuildNF.topR_eq, sp₃, g₃ 44006 by_omega, st₂]
    zus
    · rfl
    · rw [show ST + (stk E _).length - 1 = ST + ((stk E ztbl).length - 1) by omega]
      exact stk₃ _ by_omega
  rw [top₃] at v17
  zujah
  have g₄ : ∀ r, r ≠ 43117 → r ≠ 43116 → d₄.nreg r = d₃.nreg r := fun r a1 a2 => f₄.1 r (by
    grind)
  have mm₄ := f₄.2.2.1
  have G₄ : ∀ r, (r < 42110 ∨ (42112 < r ∧ r < 43101) ∨ (43101 < r ∧ r < 43110) ∨
      ztgyz ∨ (43117 < r ∧ r < 43130) ∨ 43134 < r) →
      d₄.nreg r = d.nreg r := fun r hr => by
    rw [g₄ r by_omega by_omega, g₃ r by_omega, G₂ r by_omega]
  -- 5. the gap
  have lowd₄ : ∀ a, a < H → d₄.nmem a = mB a := fun a ha => by
    rw [mm₄, oth₃ a by_omega, lowd a ha]
  obtain ⟨hM₄, hwf₄⟩ := desc_agree F.wf F.desc lowd₄
  have hA := I.r102
  have hAle := BuildNF.gapsB_length_le M zta L E m
  set A := (gapsB M zta L E m).length with hAdef
  have e110 : d₄.nreg 42110 = (wposOf L c).edge := by
    rw [g₄ _ by_norm_num by_norm_num, g₃ _ by_omega, g₂ _ by_norm_num by_norm_num, v10]
  have e111 : d₄.nreg 42111 = (wposOf L c).hgt := by
    rw [g₄ _ by_norm_num by_norm_num, g₃ _ by_omega, g₂ _ by_norm_num by_norm_num, v11]
  have e117 : d₄.nreg 43117 = topR E _ := v17
  have ec : ∀ {j}, j < E.length → E.getD j 0 < 2 * L.length := (BuildNF.getD_lt_of_perm F.inp.perm)
  obtain ⟨d₅, k₅, x₅, hk₅, f₅, hgap, hnogap⟩ := gapS_exec (P := P) F.good F.hwords d₄ w₄
    (M := M) (L := L) (E := E) (D := D) (H := H) (T := T) (SE := SE) (m := m) (A := A)
    (AT := AT) (WT := WT) F.inp.valid hN (fun j hj => ec hj) hm
    (by rw [G₄ 43100 by_omega, I.r100]) (by rw [G₄ 42001 by_omega, I.rN])
    (by rw [G₄ 43103 by_omega, I.r103]) (by rw [G₄ 43104 by_omega, I.r104])
    (fun j hj => by rw [lowd₄ _ by_omega, F.codes j hj])
    (by rw [G₄ 42000 by_omega, I.rT])
    (fun c' hc' => by
      obtain ⟨a1, a2, a3, a4⟩ := F.recs c' hc'
      exact ⟨by rw [lowd₄ _ by_omega, a1], by rw [lowd₄ _ by_omega, a2],
        by rw [lowd₄ _ by_omega, a3], by rw [lowd₄ _ by_omega, a4]⟩)
    (by rw [G₄ 42102 by_omega, I.r1a]) e110 e111
    (by rw [G₄ 40000 by_omega, I.rD]) hwf₄ hM₄ hHW
    (by rw [G₄ 41023 by_omega, I.r23, lowd₄ _ (by have := F.wf.1; omega)])
    (by rw [G₄ 41019 by_omega, I.r19]) (by rw [G₄ 43102 by_omega, hA])
    (by rw [G₄ 44002 by_omega, I.rAT]) (by rw [G₄ 44007 by_omega, I.rWT])
    (by rw [G₄ 43011 by_omega, I.r1]) by_omega by_omega by_omega by_omega hTH
    by_omega
    (by rw [G₄ 44020 by_omega, G₄ 44021 by_omega, I.rlo, I.rhd]; exact F.cnt)
  zumga
  zuiux
  -- 6. the next position
  have a100 : d₅.nreg 43100 = m := by
    rw [g₅ _ ztbls, G₄ 43100 by_omega, I.r100]
  have a103 : d₅.nreg 43103 = SE + m := by
    rw [g₅ _ ztbls, G₄ 43103 by_omega, I.r103]
  have a011 : d₅.nreg 43011 = 1 := by
    rw [g₅ _ ztbls, G₄ 43011 by_omega, I.r1]
  obtain ⟨d₆, k₆, x₆, hk₆, n100, n103, g₆, mm₆⟩ : ∃ d₆ k₆, Exec P W
      ztiqq d₅ d₆ k₆ ∧ k₆ = 2 ∧
      d₆.nreg 43100 = m + 1 ∧ d₆.nreg 43103 = SE + ztbl ∧
      (∀ r, r ≠ 43100 → r ≠ 43103 → d₆.nreg r = d₅.nreg r) ∧ d₆.nmem = d₅.nmem := by
    exec_block
    · omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, fun r r1 r2 => ?_, rfl⟩ <;> config_simp
      · omega
      · omega
      · zuro
  have X : Exec P W passBody d d₆ _ :=
    .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ x₆))))
  have G₆ : ∀ r, (r < 10000 ∨ ztckp ∨ ztgyy ∨
      ztngl ∨ ztngm ∨ ztngn ∨
      ztngo ∨ ztngp ∨ ztngq ∨
      ztngr ∨ ztgzc ∨ 43151 < r) →
      d₆.nreg r = d.nreg r := fun r hr => by
    rw [g₆ r by_omega by_omega, g₅ r ztbls, G₄ r by_omega]
  have hgP := F.inp.gapP_iff hm
  have hsucc := BuildNF.gapsB_succ M zta L E m
  have hlo : d₄.nreg 44020 = lo := by rw [G₄ 44020 by_omega, I.rlo]
  have hhd : d₄.nreg 44021 = hd := by rw [G₄ 44021 by_omega, I.rhd]
  have oth₄ : ∀ a, zteop → d₄.nmem a = d.nmem a :=
    fun a ha => by rw [mm₄, oth₃ a ha]
  have ch₄ : ∀ a, a < AT → d₄.nmem a = d₃.nmem a := fun a _ => by zuoyy
  -- the new memory and arc count
  have M₆ : d₆.nreg 43102 = (gapsB M zta L E ztbl).length ∧
      (∀ a, a < AT → d₆.nmem a = d₃.nmem a) ∧ (∀ a, ST ≤ a → a < WT → d₆.nmem a = d₃.nmem a) ∧
      (∀ j, j < (gapsB M zta L E ztbl).length →
        (∀ f, f < 5 → d₆.nmem ztgzs =
          af ztxev f) ∧
        d₆.nmem ztjnq =
          arcW M zta ztxev) := by
    by_cases hg : gapP M zta L E m = true
    · obtain ⟨p1, pz, pz1, pziff, p2⟩ := hgap (hgP.1 hg)
      rw [hsucc, ite_eq_left hg]
      have hlen : (gapsB M zta L E m ++ [m]).length = A + 1 := by simp [hAdef]
      rw [mm₆, p2, hlen]
      refine ⟨by zunvz, fun a ha => ?_, fun a h1 h2 => ?_,
        fun j hj => ?_⟩
      · zucqe
      · zucqe
      · by_cases hjA : j < A
        · rw [List.getD_append _ _ _ _ by_omega]
          obtain ⟨o1, o2⟩ := I.arcs j hjA
          refine ztonl
          · rw [upd_other _ _ _ by_omega, wr5_out _ _ _ _ _ _ _ _ by_omega,
              oth₄ _ by_omega, o1 f hf]
          · rw [upd_other _ _ _ by_omega, wr5_out _ _ _ _ _ _ _ _ by_omega,
              oth₄ _ by_omega, o2]
        · have hjA' : ztsjq := by_omega
          subst hjA'
          rw [List.getD_append_right _ _ _ _ by_omega, hAdef, Nat.sub_self]
          zulrq
          refine ztonl
          · rw [upd_other _ _ _ by_omega, wr5_in _ _ _ _ _ _ _ _ hf, BuildNF.arcRec_eq,
              BuildNF.af_mk, e117]
          · rw [upd_same, hlo, hhd]
            have hmem : m ∈ BuildNF.gapStarts M zta L E := by
              rw [← BuildNF.gapsB_full]
              exact List.mem_filter.2 ⟨List.mem_range.2 hm, hg⟩
            have he := edge_lt F.inp.valid (c := E.getD ztxei 0)
              (ec ztcv)
            rw [F.inp.arcW_eq hm hmem F.cnt F.cntW pziff pz1,
              wtF_eq_wtG by_omega (fun h => ((F.cnt _ he).1 (pziff.1 h).1).1) pz1,
              Nat.add_sub_cancel_left]
    · have hng : ¬ (m + 1 = E.length ∨ M.key _ _ <
          M.key _ _) := fun h => hg (hgP.2 h)
      obtain ⟨p1, p2⟩ := hnogap hng
      rw [hsucc, ite_eq_right hg, List.append_nil]
      rw [mm₆, p2]
      refine ⟨by zunvz, by_omega,
        fun a _ _ => by zuoyy, fun j hj => ?_⟩
      obtain ⟨o1, o2⟩ := I.arcs j hj
      exact ⟨fun f hf => by rw [oth₄ _ by_omega, o1 f hf], by rw [oth₄ _ by_omega, o2]⟩
  obtain ⟨q1, q2, q3, q4⟩ := M₆
  refine ⟨d₆, _, X, by_omega, by_omega, x₆.wb_right, ?_⟩
  exact
    { m_le := by_omega
      r100 := n100
      r103 := n103
      r104 := by rw [G₆ 43104 by_omega, I.r104]
      r101 := by
        rw [g₆ _ by_norm_num by_norm_num, g₅ _ ztbls,
          g₄ _ by_norm_num by_norm_num, sp₃]
      sp_le := spl₃
      r102 := q1
      rD := by rw [G₆ 40000 by_omega, I.rD]
      rT := by rw [G₆ 42000 by_omega, I.rT]
      rN := by rw [G₆ 42001 by_omega, I.rN]
      r1a := by rw [G₆ 42102 by_omega, I.r1a]
      rB := by rw [G₆ 43001 by_omega, I.rB]
      r0 := by rw [G₆ 43010 by_omega, I.r0]
      r1 := by rw [G₆ 43011 by_omega, I.r1]
      rCT := by rw [G₆ 44001 by_omega, I.rCT]
      rAT := by rw [G₆ 44002 by_omega, I.rAT]
      rST := by rw [G₆ 44006 by_omega, I.rST]
      rWT := by rw [G₆ 44007 by_omega, I.rWT]
      rlo := by rw [G₆ 44020 by_omega, I.rlo]
      rhd := by rw [G₆ 44021 by_omega, I.rhd]
      r19 := by rw [G₆ 41019 by_omega, I.r19]
      r23 := by rw [G₆ 41023 by_omega, I.r23]
      low := fun a ha => by rw [q2 a by_omega, oth₃ a by_omega, lowd a ha]
      stack := fun k hk => by rw [q3 _ by_omega by_omega, stk₃ k hk]
      chords := fun x' hx' hin f hf => by rw [q2 _ by_omega, ch₃ x' hx' hin f hf]
      arcs := q4
      frame := I.frame.trans (exec_frameM X wr_passBody) }

/-- **The main pass**: from `PassInv 0`, the loop reaches `PassInv (2K)`. -/
theorem passLoop_exec {M : Model} {L : List zte} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) {c₀ d : Config}
    (I : PassInv F c₀ d 0) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W passLoop d d' k ∧ k ≤ 11702 * E.length + 2 ∧ 12 * E.length ≤ k ∧
      WordsBounded W d' ∧ PassInv F c₀ d' E.length := by
  obtain ⟨d', k, e, ⟨hw', m', I', hm'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P)
    (W := W) (a := 43100) (b := 42001) (body := passBody)
    (fun d => WordsBounded W d ∧ ∃ m, PassInv F c₀ d m ∧ d.nreg 43100 = m)
    (fun d => 11702 * (E.length - d.nreg 43100)) (fun d => 12 * d.nreg 43100) ztoe
    (fun d ⟨hwd, m, Id, hmd⟩ htest => by
      rw [Id.rN, hmd] at htest
      obtain ⟨d', k, x, hk, hk', hw', I'⟩ := passBody_step F Id htest hwd
      refine ⟨d', k, x, ⟨hw', m + 1, I', I'.r100⟩, ?_, ?_⟩
      · zuolo; omega
      · zuolo; omega)
    ⟨hw, 0, I, I.r100⟩
  have hmN := I'.m_le
  rw [I'.rN, hm'] at htest
  have : m' = E.length := by_omega
  zumo
  refine ⟨d', k, e, ?_, ?_, hw', I'⟩
  · omega
  · rw [I.r100, hm'] at hψ
    omega
end step
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs
@[expose] public section
section loops
variable {P : Polygon} {W : ℕ}
variable {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop)
/-- **A counted loop with a fixed cost per iteration.** -/
theorem forLoop (Kb N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c → ∃ c' k, Exec P W body c c' k ∧ Inv ztl c' ∧ k ≤ Kb)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W ztfmn c c' k ∧ Inv N c' ∧ k ≤ ztkq * zthbl + 2 := by
  induction hn : N - j generalizing j c with
  | zero =>
    zubaq

    zucq
    exact ztkje
  | succ t ih =>
    zucq
    zuem

    refine ztgsy
    zuewu

/-- **A counted loop with a cost `f j` for the iteration at counter value `j`.** -/
theorem forLoopSum (f : ℕ → ℕ) (N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c →
      ∃ c' k, Exec P W body c c' k ∧ Inv ztl c' ∧ k ≤ f j)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W ztfmn c c' k ∧ Inv N c' ∧
      k ≤ (∑ i ∈ Finset.Ico j N, (f i + 2)) + 2 := by
  induction hn : N - j generalizing j c with
  | zero =>
    zubaq

    zucq
    exact ⟨c, 2, .whileLtN_false by_omega hw, hc, by_simp⟩
  | succ t ih =>
    zucq
    zuem

    refine ztgsy
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    omega
end loops
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam
@[expose] public section
def cpBody : Stmt :=
  block [.addN 210064 210062 210060, .loadN 210065 210064, .addN 210064 210063 210060,
    .storeN 210064 210065, .addN 210060 210060 210034]

/-- **Copy `len` words from `src` to `dst`.** -/
def cpS : Stmt := .seq (.instr (.constN 210060 0)) (.whileLtN 210060 210061 cpBody)

/-- The registers `cpS` writes. -/
def Bcp (r : ℕ) : Bool := decide (r = 210060) || decide (r = 210064) || decide (r = 210065)
theorem wrM_cpBody : wrM Bcp cpBody = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
theorem cpBody_exec (d : Config) (hw : WordsBounded W d) {i S D : ℕ}
    (h60 : d.nreg 210060 = i) (h62 : d.nreg 210062 = S) (h63 : d.nreg 210063 = D)
    (h34 : d.nreg 210034 = 1) (hW1 : S + i ≤ W) (hW2 : D + i ≤ W) (hW3 : i + 1 ≤ W) :
    ∃ d' k, Exec P W cpBody d d' k ∧ k = 5 ∧ d'.nreg 210060 = i + 1 ∧
      d'.nmem = upd d.nmem ztbyg ztbahg ∧ FrameM Bcp d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W cpBody d d' k ∧ k = 5 ∧
      d'.nreg 210060 = i + 1 ∧ d'.nmem = upd d.nmem ztbyg ztbahg := by
    unfold cpBody
    exec_block
    all_goals try (config_simp; (try simp only [h60, h62, h63, h34]); omega)
    simp_all
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_cpBody⟩

/-- **The copy.** -/
theorem cpS_exec {d : Config} (hw : WordsBounded W d) {S D len : ℕ}
    (h61 : d.nreg 210061 = len) (h62 : d.nreg 210062 = S) (h63 : d.nreg 210063 = D)
    (h34 : d.nreg 210034 = 1) (hsep : S + len ≤ D ∨ D + len ≤ S)
    (hW : S + len ≤ W) (hW' : D + len + 1 ≤ W) :
    ∃ d' k, Exec P W cpS d d' k ∧ k ≤ 7 * len + 3 ∧ WordsBounded W d' ∧
      seg d'.nmem D len = seg d.nmem S len ∧
      (∀ a, (a < D ∨ D + len ≤ a) → d'.nmem a = d.nmem a) ∧ FrameM Bcp d d' := by
  have e₀ := Exec.constN (P := P) hw 210060 0 ztbg
  set d₀ : Config := { d with nreg := upd d.nreg 210060 0 } with hd₀
  have g₀ : ∀ r, r ≠ 210060 → d₀.nreg r = d.nreg r := fun r hr => by_simp_all
  have f₀ : FrameM Bcp d d₀ := exec_frameM e₀ by_decide
  let Inv : ℕ → Config → Prop := fun i e => WordsBounded W e ∧ e.nreg 210060 = i ∧
    e.nreg 210061 = len ∧ e.nreg 210062 = S ∧ e.nreg 210063 = D ∧ e.nreg 210034 = 1 ∧
    FrameM Bcp d e ∧
    ∀ a, e.nmem a = if D ≤ a ∧ a < D + i then d.nmem (S + zttej) else d.nmem a
  obtain ⟨d', k, ex, ⟨w', _, _, _, _, _, hf', hm'⟩, hk⟩ := forLoop (P := P) (W := W)
    (ir := 210060) (nr := 210061) Inv 5 len
    ztchw
    (fun i e hi ⟨hw, h1, h2, h3, h4, h5, hf, hm⟩ => by
      obtain ⟨e', k, ex, hk, h1', hm', hf'⟩ := cpBody_exec (P := P) e hw h1 h3 h4 h5
        by_omega by_omega by_omega
      have g : ∀ r, Bcp r = false → e'.nreg r = e.nreg r := hf'.1
      refine ⟨e', k, ex, ⟨ex.wb_right, h1', (g _ by_decide).trans h2, (g _ by_decide).trans h3,
        (g _ by_decide).trans h4, (g _ by_decide).trans h5, hf.trans hf', fun a => ?_⟩,
        by omega⟩
      zugec
      grind)
    (j := 0) ⟨e₀.wb_right, by_rfl, by_simp_all,
      by simp_all, by_simp_all, by_simp_all,
      f₀, fun a => by_simp_all⟩ (Nat.zero_le _)
  refine ⟨d', 1 + k, .seq e₀ ex, by_omega, w', ?_, fun a ha => ?_, hf'⟩
  · zumum
  grind
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt
@[expose] public section
def padLoop : Stmt := .whileLtN 210068 9999 (.instr (.addN 210068 210068 210069))

/-- **Padding** from the allocation pointer saved in register `src`. -/
def padS (src : ℕ) : Stmt :=
  .seq (.instr (.copyN 210068 src)) (.seq (.instr (.constN 210069 1)) padLoop)
section exec
variable {P : Polygon} {W : ℕ}
theorem padLoop_exec : ∀ (d : ℕ) (c : Config), WordsBounded W c → c.nreg 210069 = 1 →
    c.nreg 210068 ≤ c.nreg 9999 → c.nreg 9999 - c.nreg 210068 = d →
    Exec P W padLoop c { c with nreg := upd c.nreg 210068 (c.nreg 9999) } (3 * d + 2)
  | 0, c, hw, _, hle, hd => by
    have h : c.nreg 210068 = c.nreg 9999 := by_omega
    refine Exec.cast (k := 2) ztgvg by_omega
    zuezs
  | d + 1, c, hw, h69, hle, hd => by
    have e := Exec.addN (P := P) hw 210068 210068 210069 (by rw [h69]; have := hw.1 9999; omega)
    have h1 : ztfco 210069 = 1 := by
      simp_all
    have h2 : ztfco 9999 = c.nreg 9999 :=
      upd_other _ _ _ by_decide
    have h3 : ztfco 210068 = c.nreg 210068 + 1 := by
      simp_all
    have e' := padLoop_exec d _ e.wb_right h1 by_grind
      by_grind
    refine ((Exec.whileLtN_true by_omega e e').cast by_ring).cast_end ?_
    simp

/-- **The padding**: exactly `3 (r9999 - r_src) + 4` steps, only `210068`, `210069` written. -/
theorem padS_exec {src : ℕ} {c : Config} (hw : WordsBounded W c) (hs : c.nreg src ≤ c.nreg 9999)
    (hW : 1 ≤ W) :
    ∃ c', Exec P W (padS src) c c' (3 * (c.nreg 9999 - c.nreg src) + 4) ∧
      (∀ r, r ≠ 210068 → r ≠ 210069 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧ WordsBounded W c' := by
  have e₁ := Exec.copyN (P := P) hw 210068 src
  have e₂ := Exec.constN (P := P) e₁.wb_right 210069 1 hW
  have a68 : ztecw 210068 = c.nreg src := by
    simp
  have a69 : ztecw 210069 = 1 := upd_same _ _ _
  have aA : ztecw 9999 = c.nreg 9999 := by
    simp
  have e₃ := padLoop_exec (P := P) _ _ e₂.wb_right a69 by_simp_all rfl
  refine ⟨_, (Exec.seq e₁ ztnkw).cast by_grind,
    fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, e₃.wb_right⟩
  simp_all
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
theorem symPtIn_copy {c c' : Config} {x s : ℕ} {p : SymPt} (h : SymPtIn c x p)
    (h0 : c'.nreg s = c.nreg x) (h1 : c'.nreg ztbk = c.nreg zthf)
    (h2 : c'.nreg ztfp = c.nreg ztewm) : SymPtIn c' s p := by
  cases p with
  | vtx i => exact ⟨h0.trans h.1, h1.trans h.2⟩
  | onEdge e hh => exact ⟨h0.trans h.1, h1.trans h.2.1, h2.trans h.2.2⟩

/-- Register frames compose. -/
theorem fbTrans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameB B c₁ c₂) (h₂ : FrameB B c₂ c₃) :
    FrameB B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans zthhr, fun r hr => (h₂.2.1 r hr).trans ztfsm,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

/-- A register frame for fewer registers is one for more. -/
theorem fbMono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_grind,
    fun r hr => h.2.1 r by_grind,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Copy a register triple into the kernel registers from `s`. -/
def ldP (s x : ℕ) : List Instr := [.copyN s x, .copyN ztbk zthf, .copyN ztfp ztewm]

/-- **A sign test on three points held in register triples**, answer bit into `d`. -/
def tstR (op x y z d : ℕ) : Stmt :=
  .seq (block (ldP 10000 x ++ ldP 10003 y ++ ldP 10006 z ++ [.constN 10009 op]))
    ztkps

/-- A register triple outside the kernel's registers. -/
def OutK (x : ℕ) : Prop := x + 3 ≤ 10000 ∨ 10500 ≤ x
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **A sign test on register triples** (at most `245` steps). -/
theorem tstR_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {op : ℕ} (hop : op ≤ 3) {x y z d : ℕ}
    (hx : OutK x) (hy : OutK y) (hz : OutK z) (c : Config) (hw : WordsBounded W c)
    {s₁ s₂ s₃ : SymPt} (i₁ : SymPtIn c x s₁) (i₂ : SymPtIn c y s₂) (i₃ : SymPtIn c z s₃)
    (l₁ : s₁.Lt P.n) (l₂ : s₂.Lt P.n) (l₃ : s₃.Lt P.n) :
    ∃ c' k, Exec P W (tstR op x y z d) c c' k ∧ k ≤ 245 ∧ FrameB (Brute.Bt d) c c' ∧
      c'.nreg d ≤ 1 ∧
      (c'.nreg d = 1 ↔ SignTest op (s₁.eval (Qof P)) (s₂.eval (Qof P)) (s₃.eval (Qof P))) := by
  unfold OutK at hx hy hz
  have hop' : op ≤ W := by omega
  -- the loads
  obtain ⟨c₁, k₁, e₁, hk₁, q₁, q₂, q₃, q₉, hf₁⟩ : ∃ c₁ k₁, Exec P W (block (ldP 10000 x ++
      ldP 10003 y ++ ldP 10006 z ++ [.constN 10009 op])) c c₁ k₁ ∧ k₁ = 10 ∧
      SymPtIn c₁ 10000 s₁ ∧ SymPtIn c₁ 10003 s₂ ∧ SymPtIn c₁ 10006 s₃ ∧ c₁.nreg 10009 = op ∧
      FrameB Bk c c₁ := by
    obtain ⟨c₁, k₁, e₁, hk₁, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, fr⟩ :
        ∃ c₁ k₁, Exec P W (block (ldP 10000 x ++ ldP 10003 y ++ ldP 10006 z ++
          [.constN 10009 op])) c c₁ k₁ ∧ k₁ = 10 ∧
        c₁.nreg 10000 = c.nreg x ∧ c₁.nreg 10001 = c.nreg (x + 1) ∧
        c₁.nreg 10002 = c.nreg (x + 2) ∧ c₁.nreg 10003 = c.nreg y ∧
        c₁.nreg 10004 = c.nreg (y + 1) ∧ c₁.nreg 10005 = c.nreg (y + 2) ∧
        c₁.nreg 10006 = c.nreg z ∧ c₁.nreg 10007 = c.nreg (z + 1) ∧
        c₁.nreg 10008 = c.nreg (z + 2) ∧ c₁.nreg 10009 = op ∧
        (∀ r, (r < 10000 ∨ 10010 ≤ r) → c₁.nreg r = c.nreg r) ∧
        c₁.rreg = c.rreg ∧ c₁.nmem = c.nmem ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
      simp only [ldP, List.cons_append, List.nil_append]
      exec_block
      · omega
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;>
          (try intro r hr) <;> config_simp <;>
          (try simp only [Machine.upd_apply]) <;> (try split_ifs) <;> (try omega) <;>
          (repeat rw [ite_eq_right (by omega)])
    refine ⟨c₁, k₁, e₁, hk₁, symPtIn_copy i₁ r0 r1 r2, symPtIn_copy i₂ r3 r4 r5,
      symPtIn_copy i₃ r6 r7 r8, r9, ⟨fun r hr => ?_, fun r _ => by simp_all, fr.2.2.1,
      fr.2.2.2.1, fr.2.2.2.2⟩⟩
    · have : r < 10000 ∨ 10500 ≤ r := by unfold Bk at hr; grind
      grind
  have i₁' := i₁
  -- the kernel
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, s₂'⟩ := sig_exec (P := P) c₁ e₁.wb_right hG hW
    (by omega) l₁ l₂ l₃ q₁ q₂ q₃
  rw [q₉] at s₂'
  -- the answer
  have e₃ := Exec.copyN (P := P) e₂.wb_right d 10010
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg d (c₂.nreg 10010) } with hc₃
  refine ⟨c₃, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by omega, ?_, by simp_all,
    by simp_all⟩
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : Bk r = false ∧ r ≠ d := by
      unfold Brute.Bt at hr; simp_all
    simp only [c₃]
    rw [Machine.upd_other _ _ _ hr'.2, f₂.1 r hr'.1, hf₁.1 r hr'.1]
  · have hr' : Bk r = false := by
      unfold Brute.Bt at hr; simp_all
    simp only [c₃]; rw [f₂.2.1 r hr', hf₁.2.1 r hr']
  · simp only [c₃]; rw [f₂.2.2.1, hf₁.2.2.1]
  · simp only [c₃]; rw [f₂.2.2.2.1, hf₁.2.2.2.1]
  · simp only [c₃]; rw [f₂.2.2.2.2, hf₁.2.2.2.2]
