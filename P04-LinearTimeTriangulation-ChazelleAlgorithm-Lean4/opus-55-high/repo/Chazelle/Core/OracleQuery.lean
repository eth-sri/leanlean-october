module

public import Chazelle.MacT
public import Chazelle.Core.BruteCorner
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.Facts2Trap
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.OracleBook
public import Chazelle.Core.SpecNF

namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sideInArc sidePt regionsIn freeIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open OracleBook
namespace OracleQ
variable {C : Chain} {Q : Polygon} {N : NF}

/-- **The scanned points of a node**: the scanned edges of all arcs of its region (nothing for
padding). -/
noncomputable def nodeScan (C : Chain) (Q : Polygon) (N : NF) (v : ℕ) : Set Point :=
  {x | v < N.arcs.length ∧ ∃ p, p < N.arcs.length ∧ rgi N p = rgi N v ∧ x ∈ scanSet C Q N p}
theorem nodeScan_subset (v : ℕ) : nodeScan C Q N v ⊆ C.set := by
  rintro x ⟨-, p, -, -, hx⟩
  exact scanSet_subset C Q N p hx

/-- A point of the chain on a closed arc of a region lies on the scanned points of every node of
that region. -/
theorem mem_nodeScan (hN : IsNF ztc Q N) {reg : ℕ → Set Point}
    (_hR : RegionCorr ztc Q N reg) (hA : ArcsOK ztc Q N reg)
    {v : ℕ} (hv : v < N.arcs.length) {x : Point} (hxC : x ∈ C.set)
    (hx : ArcHit C ztwjh (reg ztcax) x) : x ∈ nodeScan C Q N v := by
  obtain ⟨a, b, harc, hmem⟩ := hx
  have hrv := (hA.1 _ (NFLoc.seq_lt hN hv)).1
  obtain ⟨j, hj, hjr, hja, hjb⟩ := hA.2.2.1 _ hrv a b harc
  obtain ⟨p, hp, hpj⟩ := NFLoc.seq_surj hN hj
  have hsk : ztyzd := by
    show (chainModel C).key Q (N.arc ztbjk).s = a
    simp_all
  have hek : ztyys := by
    show (chainModel C).key Q (N.arc ztbjk).e = b
    simp_all
  refine ⟨hv, p, hp, ?_, ?_⟩
  · show (N.arc ztbjk).reg = rgi N v
    rw [hpj, hjr]; rfl
  · -- the ends of the arc record are proper positions on walk edges
    obtain ⟨-, -, -, reg', -, -, -, -, -, -, hprop⟩ := id hN
    obtain ⟨hs, he⟩ := hprop _ ztctk
    have hkey : ∀ (w : WPos), ProperPos ztc Q Q.n w →
        (chainModel C).key Q w < (chainModel C).W.n → w.edge < (chainModel C).W.n := by
      zujbr
      have : ztfkn := by
        have := hw.1
        zuckv
        linarith
      simp_all
    have hsk' : (chainModel C).key Q (N.arc ztmh).s < (chainModel C).W.n := by
      have e : (chainModel C).key Q (N.arc _).s = sk _ Q N p := rfl
      rw [e, hsk]; exact harc.2.1
    have hek' : (chainModel C).key Q (N.arc ztmh).e < (chainModel C).W.n := by
      have e : (chainModel C).key Q (N.arc _).e = ek _ Q N p := rfl
      rw [e, hek]; exact harc.2.2.2.1
    have hsn := hkey _ hs hsk'
    have hen := hkey _ he hek'
    exact mem_scan C Q N hs he hsn hen hxC by_simp_all

/-- A ray point in the open box at height at most the top that lies on an arc is on the chain. -/
theorem mem_set_of_arcSet {x : Point} (hbox : x ∈ Chain.box C.radius) (hy : x.2 ≤ C.top.2)
    {a b : ℝ} (hx : x ∈ (chainModel C).arcSet a b) (hP : C.P.Simple) : x ∈ C.set := by
  have hnd := Sweep.arcSet_subset_compl_dom C hP a b hx
  rcases (Merge.not_mem_dom_iff C hy).1 hnd with h | h
  · simp_all
  omega

/-- Near `0`, the points of a finite set are only `0`. -/
theorem eventually_not_mem_of_finite {X : Set ℝ} (hX : X.Finite) : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∉ X := by
  have hc : IsClosed (X \ {0}) := by_simp_all
  have ho : (X \ {0})ᶜ ∈ 𝓝 (0 : ℝ) := hc.isOpen_compl.mem_nhds by_simp
  filter_upwards [nhdsWithin_le_nhds ho, self_mem_nhdsWithin] with t h1 h2
  grind

/-- No point lies on an arc of the empty set (arcs face their region at their inner keys). -/
theorem not_arcHit_empty {F : Set ztf} {x : Point} : ¬ ArcHit C F ∅ x := by
  rintro ⟨a, b, harc, -⟩
  obtain ⟨ha0, han, -, -, hends, -, hfac⟩ := harc
  -- a non-vertex key inside the arc
  have hn : ztixp := by rw [walk_n]; omega
  obtain ⟨p, t, hp, ht0, ht1, hin⟩ : ∃ p : ℕ, ∃ t : ℝ, p < (chainModel C).W.n ∧ 0 < t ∧ t < 1 ∧
      sideInArc a b ztk := by
    rcases hends with ⟨-, -, hab⟩ | ⟨-, rfl, rfl⟩
    · -- just after `a`
      obtain ⟨q, hq, hqa⟩ : ∃ q : ℕ, q < (chainModel C).W.n ∧ (q : ℝ) ≤ a ∧ a < q + 1 := by
        refine ⟨⌊a⌋₊, ?_, Nat.floor_le ha0, Nat.lt_floor_add_one a⟩
        have  := lt_of_le_of_lt (Nat.floor_le ha0) han
        simp_all
      set ε := (if a < b then min (q + 1 - a) zthu else q + 1 - a) / 2 with hε
      have hε0 : ztbad := by
        grind
      have hεq : a + ε < q + 1 := by
        grind
      refine ⟨q, a + ε - q, hq, by_grind, by_linarith, ?_⟩
      rw [show (q : ℝ) + (a + ε - q) = a + ε by ring]
      zuiq

    · refine ⟨0, 1 / 2, hn, by_norm_num, by_norm_num, ?_⟩
      unfold sideInArc; norm_num
  have := hfac p t hp ht0 ht1 hin
  obtain ⟨δ, hδ, -⟩ := this.exists

/-- **Correctness of the query of Lemma 3.6** from the quantities it computes.

* `hlab`: the labels (from `ClusterSpec`) are constant along the walks of the book graph that
  avoid `D*`.
* The ray from `z` (height `≤` top, `z` in the closed box, not starting along a chord) is followed
  up to the stopping parameter `T`: inside the box, off the chords, and off the scanned points of
  the nodes of `D*` (the first scan found nothing before `T`); the stopping point is off the domain.
* `hcand`: every node whose arc contains the stopping point (closed arc) is a candidate.
* `hSN`: the scanned nodes contain `D*` and the clusters of the candidates.
* `hbest`: `best` answers the first hit on the scanned points.

Then `best` is the answer: a first hit of the chain, or no hit. -/
theorem query_main (hP : C.P.Simple) (hD : DistinctHeights C.P)
    (hN : IsNF ztc Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr ztc Q N reg) (hA : ArcsOK ztc Q N reg)
    {B : BookData} (hB : GraphOK C Q N B)
    (Dm : Fin B.N → Prop) (ℓ : Fin B.N → ℕ)
    (hlab : ∀ u v (w : (bookGraph B).Walk u v), ztgnr → ℓ u = ℓ v)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 0 < T)
    (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ ztwjh)
    (hnoD : ∀ i : Fin B.N, Dm i → ∀ s, 0 < s → s < T → rayPt z σ s ∉ nodeScan C Q N i)
    (hstop : rayPt z σ T ∉ C.dom)
    (Cand : Fin B.N → Prop)
    (hcand : ∀ v : Fin B.N, v.1 < N.arcs.length →
      rayPt z σ T ∈ (chainModel C).arcSet (sk ztc Q N v) (ek ztc Q N v) →
        Cand v)
    (SN : Fin B.N → Prop)
    (hSN : ∀ i, (Dm i ∨ ∃ c, Cand c ∧ ℓ i = ℓ c) → SN i)
    {S : Set Point} (hS1 : ∀ i, SN i → nodeScan C Q N i ⊆ S) (hSC : S ⊆ C.set)
    {best : Option ℝ} (hbest : Sweep.FirstHitOpt S z σ best) :
    (∀ t, best = some t → FirstHit C.set z σ t) ∧ (best = none → NoHit C.set z σ) := by
  set F := N.F _ Q with hFdef
  zumbq
  have hfin := finite_crossings C (fun k _ => vertex_snd_ne C hD) z hσ
  -- the initial part of the ray is free
  have hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ freeIn C.dom F := by
    filter_upwards [eventually_not_mem_of_finite hfin, Ioo_mem_nhdsGT hT] with t h1 h2
    exact mem_freeIn_of_ray C hz by_grind h1 by_grind
  have hfree := hini.mono fun t ht => ht.1
  obtain ⟨hT0, hnd, hdom⟩ := Merge.hit_of_freeAt C hz hσ hfree
  set t₀ := C.hitParam z σ
  by_cases hon : rayPt z σ t₀ ∈ C.set
  · -- the true hit is on the chain: it is scanned
    have hfirst := firstHit_chain_of_hit C hz hσ hfree hon
    obtain ⟨U, hU, hUi⟩ := exists_initial_region C hfree (hini.mono fun t ht => ht.2)
    obtain ⟨R, hRr, hRi⟩ := exists_final_region C hz hT hbox hfin hnoF
    -- the node of `R` at the stopping point
    obtain ⟨a₀, ha₀, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hRi
    have hRhit : ArcHit C F R _ :=
      arcHit_left C hP hFam hRr hz hσ ha₀ (fun t h1 h2 => hsub by_grind) hstop
    obtain ⟨a, b, harc, hmem⟩ := hRhit
    obtain ⟨r, hr, rfl⟩ := hR.2.2 R hRr
    zubhi

    have hpN := lt_of_lt_of_le hp hB.arcs_le
    have hrp : rgi N p = r := by
      show (N.arc ztbjk).reg = r
      grind
    let iR : Fin B.N := ztopb
    have hrgR : rgNode reg N B iR = reg r := by
      show (if p < N.arcs.length then reg ztdvx else ∅) = reg r
      grind
    have hcandR : Cand iR := by
      refine hcand iR hp ?_
      have hsk : ztyzd := by
        show (chainModel C).key Q (N.arc ztbjk).s = a
        grind
      have hek : ztyys := by
        show (chainModel C).key Q (N.arc ztbjk).e = b
        grind
      grind
    -- no node of `D*` is hit before `T`
    have hDh : ∀ i, Dm i → ∀ s, 0 < s → s < T →
        ¬ ArcHit C F (rgNode reg N B i) ztbwc := by
      intro i hi s hs0 hsT hh
      by_cases hiA : i.1 < N.arcs.length
      · have e : rgNode reg N B i = reg (rgi N i) := by
          show ztlqa = _
          grind
        zukrd
        obtain ⟨a', b', harc', hmem'⟩ := hh
        have hxC := mem_set_of_arcSet by_grind by_tauto hmem' hP
        exact hnoD i hi s hs0 hsT (mem_nodeScan hN hR hA hiA hxC ⟨a', b', harc', hmem'⟩)
      · have e : rgNode reg N B i = ∅ := by
          show ztlqa = _
          grind
        zukrd
        exact not_arcHit_empty hh
    obtain ⟨iU, hiU, hsel⟩ := cluster_query_nodes C hP hFam _ _
      (conn_of_graphOK hN hR hA hB) (cross_of_graphOK hP hN hR hA hB) Dm ℓ hlab hz hσ hT hbox
      hfin hnoF hDh hU hUi (iR := iR) by_grind by_grind
    have hSN : SN iU := by_grind
    -- the true hit is on an arc of `U`, hence scanned
    obtain ⟨a₁, b₁, harc₁, hmem₁⟩ := Sweep.local_shoot C hP hFam hU hz hσ hUi
    have hiUA : iU.1 < N.arcs.length := by
      zukr
      have e : rgNode reg N B iU = ∅ := by
        show ztlqb = _
        grind
      zvmwe at hiU
      rw [← hiU] at hU
      exact (Chazelle.Chain.regionsIn_nonempty hU).ne_empty rfl
    have hiU' : reg (rgi N iU) = U := by
      rw [← hiU]
      show reg _ = ztlqb
      grind
    have hinS :=
      hS1 iU hSN (mem_nodeScan hN hR hA hiUA hon (by rw [hiU']; exact ⟨a₁, b₁, harc₁, hmem₁⟩))
    have hSfirst := Sweep.firstHit_of_subset hSC hfirst hinS
    refine ⟨fun t ht => ?_, fun hn => ?_⟩
    · zucfb
      rw [Sweep.firstHit_unique hbest hSfirst]; omega
    · subst hn
      exact absurd hinS (hbest t₀ hT0)
  · -- the true hit is the side of the box: no hit at all
    have hno := noHit_chain_of_hit C hz hσ hfree hon
    refine ⟨fun t ht => ?_, by_grind⟩
    zucfb
    exact absurd (hSC hbest.2.1) (hno t hbest.1)
end OracleQ
open Chazelle.Chain (sideE)
open Chazelle.Visibility (xAt)
namespace OracleQ
section Edge
variable (Q : Polygon)

/-- The height of vertex `h` lies in the (closed) height range of edge `e`. -/
def Spans (e h : ℕ) : Prop :=
  min (Q.vtx e).2 (Q.vtx ztwki).2 ≤ (Q.vtx h).2 ∧
    (Q.vtx h).2 ≤ max (Q.vtx e).2 (Q.vtx ztwki).2

/-- The abscissa of the point of edge `e` at the height of vertex `h`. -/
noncomputable def xe (e h : ℕ) : ℝ := edgeXAt Q e h
open Classical in
/-- **The answer for one edge**: the ray from `z` in direction `σ` at the height of vertex `h`
meets edge `e` at parameter `σ (xe - z.1)` if the height is in range and the parameter is
positive. -/
noncomputable def edgeHit (z : Point) (σ : ℝ) (e h : ℕ) : Option ℝ :=
  if Spans Q e h ∧ 0 < σ * ztiml then some (σ * ztiml) else none
variable {σ : ℝ} {e h : ℕ}
theorem sigma_sq (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  grind

/-- A ray point at the height of the ray lies on a non-horizontal edge iff the height is in range
and the abscissa is the edge's. -/
theorem rayPt_mem_edge_iff (hne : (Q.vtx e).2 ≠ (Q.vtx ztwki).2)
    {z : Point} (hz : z.2 = (Q.vtx h).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) :
    rayPt z σ t ∈ Q.edge e ↔ Spans Q e h ∧ t = σ * ztiml := by
  zucrd
  rw [Chazelle.Visibility.mem_segment_iff_xAt hne]
  simp only [rayPt_fst, rayPt_snd, hz]
  have hx : xAt ztgep ztbakx (Q.vtx h).2 = xe Q e h := rfl
  zucjv
  have hs := sigma_sq hσ
  constructor
  · rintro ⟨hsp, hx'⟩
    refine ztooq
    grind
  · rintro ⟨hsp, rfl⟩
    refine ztooq
    grind

/-- **The answer for one edge.** -/
theorem edgeHit_spec (hne : (Q.vtx e).2 ≠ (Q.vtx ztwki).2)
    {z : Point} (hz : z.2 = (Q.vtx h).2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Sweep.FirstHitOpt (Q.edge e) z σ (edgeHit Q z σ e h) := by
  unfold edgeHit
  zugif
  · refine ⟨hc.2, (rayPt_mem_edge_iff Q hne hz hσ _).2 ⟨hc.1, rfl⟩, fun t' ht' hlt hm => ?_⟩
    have := ((rayPt_mem_edge_iff Q hne hz hσ _).1 hm).2
    linarith
  · zumhm
    obtain ⟨hsp, rfl⟩ := (rayPt_mem_edge_iff Q hne hz hσ _).1 hm
    simp_all

/-- **The height range by sign tests** (distinct heights, indices in range). -/
theorem spans_iff (hD : DistinctHeights Q) {e h : ℕ} (he : e < Q.n) (hh : h < Q.n) :
    Spans Q e h ↔ (h = e ∨ h = ztda % Q.n) ∨
      ztbaka ∨
      ztbakb := by
  zudot
  have he1 : ztda % Q.n < Q.n := Nat.mod_lt _ hn
  unfold Spans
  constructor
  · zubf
    by_cases hhe : h = e
    · omega
    by_cases hhe1 : h = ztda % Q.n
    · omega
    have n1 := hD h e hh he hhe
    have n2 := hD h _ hh he1 hhe1
    grind
  · rintro ((rfl | rfl) | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · simp
    · simp
    · grind
    grind

/-- **Ahead of the origin, by a sign test.** -/
theorem ahead_iff (hσ : σ = 1 ∨ σ = -1) (x z : ℝ) :
    0 < σ * ztudu ↔ (σ = 1 ∧ z < x) ∨ (σ = -1 ∧ x < z) := by
  zur
  · grind
  grind

/-- **Comparing two hits, by a sign test.** -/
theorem better_iff (hσ : σ = 1 ∨ σ = -1) (x x' z : ℝ) :
    σ * ztudu < σ * (x' - z) ↔ (σ = 1 ∧ x < x') ∨ (σ = -1 ∧ x' < x) := by
  zur
  · grind
  grind
end Edge

/-! ## The minimum of two answers -/

/-! ## Tour edges as chain edges -/
section Tour
variable (C : Chain)

/-- **The chain edge of tour position `i`.** -/
noncomputable def tci (i : ℕ) : ℕ := if tj C i < C.m then tj C i else 2 * C.m - 1 - tj C i
variable (i : ℕ)
theorem tci_lt : tci C i < C.m := by
  have := tj_lt C i
  have := C.one_le
  unfold tci; grind

/-- **The segment of tour position `i` is the chain edge `tci i`.** -/
theorem tour_seg :
    Chazelle.segment ztnjy ztyoq =
      C.chainEdge ztoiu := by
  zumlb
  zueev
  zuhds
  have e2 : C.sideIdx C.sideBeta ztg = sideE C.m ztkfu := C.sideIdx_succ C.sideBeta i
  zudoo
  zuea
  unfold tci
  zuccs

  have sE3 : zthpv := fun x hx => by
    zudma

  zudlu
  · grind
  · rw [sE3 j by_omega, sE3 ztl by_omega, Geometry.segment_comm,
      show 2 * C.m - ztl = 2 * C.m - 1 - j by omega,
      show 2 * C.m - j = 2 * C.m - 1 - j + 1 by omega]

/-- **The points of a walk edge that the scan looks at**: the chain edge of a tour edge, nothing
on the box and the slit. -/
noncomputable def wseg (w : ℕ) : Set Point :=
  if 6 ≤ w ∧ w < 2 * C.m + 6 then C.chainEdge ztyrz else ∅

/-- **The scanned points of an arc** are the union of the `wseg` of its scanned walk edges. -/
theorem mem_scanSet_iff (Q : Polygon) (N : NF) (p : ℕ) (x : Point) :
    x ∈ scanSet C Q N p ↔ ∃ k, k ≤ scanLen C Q N p ∧
      x ∈ wseg C (scanIdx (chainModel C).W.n N p k) := by
  constructor
  · rintro ⟨k, hk, i, hi, hidx, hx⟩
    zulow
    unfold wseg
    rw [hidx, ite_eq_left (show 6 ≤ i + 6 ∧ i + 6 < 2 * C.m + 6 by omega), show i + 6 - 6 = i by omega, ← tour_seg]
    zufsg
  · zuecq
    unfold wseg at hx
    split_ifs at hx with hw
    · refine ⟨k, hk, scanIdx (chainModel C).W.n N p k - 6, by_omega, by_omega, ?_⟩
      rw [tour_seg]; exact hx
    simp_all
end Tour
section Wrap
variable {M : Model} {Q : Polygon} {N : NF}

/-- **Only the last arc of the spine wraps.** -/
theorem wrap_iff (hN : IsNF M Q N) (hGM : GoodModel M) {p : ℕ} (hp : p < N.arcs.length) :
    sk M Q N p < ek M Q N p ↔ p + 1 < N.arcs.length := by
  zugyb
  by_cases hne : (N.F M Q).Nonempty
  · zueah
    constructor
    · zufia
      by_contra hr
      -- the end of the last arc is a cut, which starts an arc: its start is not after `sk p`
      zumq

      obtain ⟨r, hr', hrj⟩ := NFLoc.seq_surj hN hj
      have hsr : ztlbg := by
        show M.key Q (N.arc ztnne).s = _
        simp_all
      have := sk_mono hN (show r ≤ p by omega) hp
      linarith
    · zuibu
      zubzg

      zukr
      zueoy
  · zuewy

    zueji
    have heq : sk M Q N p = ek M Q N p := by
      rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1', h2'⟩
      · simp_all
      simp_all
    grind
end Wrap
section Len
variable (C : Chain) (Q : Polygon) (N : NF)

/-- **The number of scanned walk edges of an arc, minus one**, as the program computes it. -/
def scanLenR (n A p : ℕ) : ℕ :=
  (if p + 1 < A then (N.arc ztmh).e.edge - (N.arc ztmh).s.edge
    else (N.arc ztmh).e.edge + n - (N.arc ztmh).s.edge) + 2
theorem scanLen_eq (hN : IsNF ztc Q N) (hP : C.P.Simple) {p : ℕ}
    (hp : p < N.arcs.length) :
    scanLen C Q N p = scanLenR N (chainModel C).W.n N.arcs.length p := by
  unfold scanLen scanLenR
  have hw := wrap_iff hN ztxgi hp
  simp_all
end Len
end OracleQ
namespace ShootCut
section Run
variable (C : Chain) {Q : Polygon} {H : Host}

/-- The tour coordinate of tour position `i`. -/
noncomputable def tJ (i : ℕ) : ℕ := ztwz % ztbb
theorem tJ_lt (i : ℕ) : tJ C i < 2 * C.m := Nat.mod_lt _ C.two_m_pos
variable {i d : ℕ}
theorem tJ_add (h : tJ C i + d < 2 * C.m) : tJ C zteth = tJ C i + d := by
  unfold tJ at h ⊢
  rw [← Nat.add_assoc, ← Nat.mod_add_mod, Nat.mod_eq_of_lt h]

/-- The walk vertex of tour position `i` is the chain vertex `sideE m (tJ i)`. -/
theorem walk_vtx (i : ℕ) (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx ztcy = C.vertex (sideE C.m ztdwj) := by
  show (C.sideWalk C.sideBeta).vtx ztcy = _
  zukot
  rfl

/-- The chain index at tour position `i + d` when the tour climbs. -/
theorem sideE_up (hJ : tJ C i + d ≤ C.m) :
    sideE C.m ztzyh = sideE C.m ztdwj + d := by
  zueqa
  rw [tJ_add C by_omega]
  zudma

/-- The chain index at tour position `i + d` when the tour descends. -/
theorem sideE_down (hm : C.m ≤ tJ C i) (hJ : tJ C i + d ≤ 2 * C.m) :
    sideE C.m ztzyh = sideE C.m ztdwj - d := by
  zueqa
  zukdi
  rcases (show tJ C i + d < 2 * C.m ∨ tJ C i + d = 2 * C.m by omega) with h | h
  · rw [tJ_add C h]
    zudma

  · have e : tJ C zteth = 0 := by
      have e1 : tJ C zteth = (tJ C i + d) % ztbb := by
        zumve
      simp_all
    zui
    zudma

/-- **A run stretch, climbing.** -/
theorem run_up (hP : C.P = H.poly Q) {i d : ℕ} (hJ : tJ C i + d ≤ C.m) (hi : i + d ≤ 2 * C.m)
    {r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : zttx % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t + d ≤ ℓ)
    (hq : ztne % Q.n + d < Q.n) :
    (chainModel C).W.vtx ztqrb = Q.vtx (ztne % Q.n + d) := by
  zubn

  -- host index
  have hidx : ztbfu % C.P.n = NFLoc.preLen Q.n H r + zthkq := by
    zudvi
    zuey
    omega
  have hpt : ztpze[ztbfu % C.P.n]? =
      some (SymPt.vtx ((a + zthkq) % Q.n)) := by
    rw [hidx, NFLoc.pts_getElem? Q.n H hr by_omega (by rw [hrun]; simp [NFLoc.itemCnt]; omega),
      hrun, show NFLoc.preLen Q.n H r + zthkq - NFLoc.preLen Q.n H r = t + d by omega,
      NFLoc.run_pts_getElem? _ _ _ ht]
  rw [show i + d + 6 = zteth + 6 by ring, walk_vtx C _ hi,
    NFLoc.chain_vertex_host C hP _ hpt]
  show Q.vtx _ = _
  zucr
  zudot
  rw [← Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt (show d < Q.n by omega),
    Nat.mod_eq_of_lt hq]

/-- **A run stretch, descending.** -/
theorem run_down (hP : C.P = H.poly Q) {i d : ℕ} (hm : C.m ≤ tJ C i) (hJ : tJ C i + d ≤ 2 * C.m)
    (hi : i + d ≤ 2 * C.m)
    {r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : zttx % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t ≤ ℓ) (hdt : d ≤ t)
    (hq : d ≤ ztne % Q.n) (hn : 0 < Q.n) :
    (chainModel C).W.vtx ztqrb = Q.vtx ztzhu := by
  zubn

  have hkd : ztzqb := by
    have := sideE_down C (d := d) hm hJ
    zucgr
    unfold sideE at *
    split_ifs at * <;> omega
  have hidx : ztbfu % C.P.n = NFLoc.preLen Q.n H r + ztdwh := by
    zubsn

    have e2 : C.s + ztzha =
        C.P.n * ztbaaz + ztyvh := by
      omega
    zuhld
  have hpt : ztpze[ztbfu % C.P.n]? =
      some (SymPt.vtx ((a + ztdwh) % Q.n)) := by
    rw [hidx, NFLoc.pts_getElem? (p := NFLoc.preLen Q.n H r + ztdwh) Q.n H hr by_omega
        (by rw [hrun]; simp only [NFLoc.itemCnt]; omega),
      hrun, show NFLoc.preLen Q.n H r + ztdwh - NFLoc.preLen Q.n H r = t - d by omega,
      NFLoc.run_pts_getElem? _ _ _ by_omega]
  rw [show i + d + 6 = zteth + 6 by ring, walk_vtx C _ hi,
    NFLoc.chain_vertex_host C hP _ hpt]
  show Q.vtx _ = _
  zucr
  have e := Nat.div_add_mod ztne Q.n
  have e2 : a + ztdwh = Q.n * (ztne / Q.n) + ztzhu := by_omega
  zudfq
end Run

/-! ## Chains of `Q` -/

/-- **The vertices of a chain of `Q`** without wrap: `Q.vtx (x + d)`. -/
theorem grade_vertex {Q : Polygon} {Cα : Chain} (hP : Cα.P = Q) (hx : Cα.s + Cα.m < Q.n) {d : ℕ}
    (hd : d ≤ Cα.m) : Cα.vertex d = Q.vtx (Cα.s + d) := by
  zugil
  subst hP
  zuey
def HostBreak (n : ℕ) (H : Host) (u : ℕ) : Prop :=
  ∃ r, r < H.length ∧ NFLoc.preLen n H r ≤ u ∧ u < NFLoc.preLen n H ztgu ∧
    match H.getD r ztmn with
    | .pt _ => True
    | .run a ℓ => u - NFLoc.preLen n H r = 0 ∨ u - NFLoc.preLen n H r = ℓ ∨
        ztkqn % n = 0 ∨ ztkqn % n = n - 1
noncomputable instance (n : ℕ) (H : Host) : DecidablePred ztsxx :=
  Classical.decPred _

/-- The (at most four) break offsets of an item. -/
def brkOffs (n : ℕ) : HostItem → Finset ℕ
  | .pt _ => {0}
  | .run a ℓ => {0, ℓ, (n - a % n) % n, (2 * n - 1 - a % n) % n}
theorem card_brkOffs (n : ℕ) (it : HostItem) : (brkOffs n it).card ≤ 4 := by
  cases it with
  | pt x => simp [brkOffs]
  | run a ℓ =>
    unfold brkOffs
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ztmxz
    refine Nat.succ_le_succ ztmxz
    simp

/-- All break host points. -/
def brkSet (n : ℕ) (H : Host) : Finset ℕ :=
  (Finset.range H.length).biUnion fun r =>
    (brkOffs n ztztm).image fun t => NFLoc.preLen n H r + t
theorem card_brkSet (n : ℕ) (H : Host) : (brkSet n H).card ≤ 4 * H.length := by
  unfold brkSet
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ r ∈ Finset.range H.length,
        ((brkOffs n ztztm).image fun t => NFLoc.preLen n H r + t).card
      ≤ ∑ _r ∈ Finset.range H.length, 4 :=
        Finset.sum_le_sum fun r _ => Finset.card_image_le.trans (card_brkOffs n _)
    _ = 4 * H.length := by simp [mul_comm]

/-- The unique offset in `[0, n)` with a given residue. -/
theorem off_of_mod {n a t c : ℕ} (hn : 0 < n) (ht : t < n) (_hc : c < n) (h : ztne % n = c) :
    t = (n + c - a % n) % n := by
  have e := Nat.div_add_mod a n
  have e2 := Nat.div_add_mod ztne n
  have ha := Nat.mod_lt a hn
  zuktn
  -- `a % n + t ≡ c`
  have h2 : (a % n + t) % n = c := by_simp_all
  rcases (show a % n + t < n ∨ n ≤ a % n + t by omega) with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h2
    rw [show n + c - a % n = t + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt by_omega] at h2
    rw [show n + c - a % n = t by omega, Nat.mod_eq_of_lt ht]
variable {n : ℕ} {H : Host}
/-- **Break host points lie in `brkSet`** (for well-formed hosts: runs shorter than `n`). -/
theorem hostBreak_mem (hn : 0 < n) (hwf : HostWF n H) {u : ℕ}
    (h : HostBreak n H u) : u ∈ brkSet n H := by
  obtain ⟨r, hr, h1, h2, hc⟩ := h
  unfold brkSet
  refine Finset.mem_biUnion.2 ⟨r, Finset.mem_range.2 hr, Finset.mem_image.2 ?_⟩
  refine ⟨u - NFLoc.preLen n H r, ?_, by_omega⟩
  zuizj
  have hget : H.getD r ztmn = H[r] := by_simp_all
  rw [hget] at hc ⊢
  have hit := hwf H[r] ztpzp
  generalize H[r] = it at hc hsucc hit
  cases it with
  | pt x =>
    zubiq
    simp only [brkOffs, Finset.mem_singleton]
    omega
  | run a ℓ =>
    zubiq
    zujpe
    have ht : u - NFLoc.preLen n H r < n := by_omega
    simp only [brkOffs, Finset.mem_insert, Finset.mem_singleton]
    rcases hc with hc | hc | hc | hc
    · omega
    · omega
    · zurx
      rw [off_of_mod hn ht hn hc, Nat.add_zero]
    · zubef
      rw [off_of_mod hn ht by_omega hc]
      grind
theorem card_hostBreak_le (hn : 0 < n) (hwf : HostWF n H) (N : ℕ) :
    ((Finset.range N).filter ztsxx).card ≤ 4 * H.length := by
  classical
  refine le_trans ztowz (card_brkSet n H)
  exact hostBreak_mem hn hwf (Finset.mem_filter.1 hu).2

/-! ## Tour positions -/
variable (C : Chain)

/-- The host point index of tour position `i`. -/
noncomputable def uOf (i : ℕ) : ℕ := zttx % C.P.n
theorem uOf_lt (i : ℕ) : uOf C i < C.P.n := Nat.mod_lt _ C.n_pos

/-- The tour coordinate is injective on the tour positions. -/
theorem tJ_inj {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m) (h : tJ C i = tJ C i') :
    i = i' := by
  unfold tJ at h
  zuec
  rcases (show C.sideS C.sideBeta + i < 2 * C.m ∨ 2 * C.m ≤ C.sideS C.sideBeta + i by omega)
    with h1 | h1 <;>
  rcases (show C.sideS C.sideBeta + i' < 2 * C.m ∨ 2 * C.m ≤ C.sideS C.sideBeta + i' by omega)
    with h2 | h2
  · zufmp
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt by_omega] at h; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt by_omega, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt by_omega, Nat.mod_eq_sub_mod h2,
      Nat.mod_eq_of_lt by_omega] at h; omega

/-- At most one tour position has a given tour coordinate. -/
theorem card_tJ_eq (j : ℕ) : ((Finset.range ztbb).filter fun i => tJ C i = j).card ≤ 1 := by
  refine Finset.card_le_one.2 fun i hi i' hi' => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi hi'
  exact tJ_inj C hi.1 hi'.1 (hi.2.trans hi'.2.symm)

/-- **At most two tour positions share a host point.** -/
theorem card_fiber_le (u : ℕ) :
    ((Finset.range ztbb).filter fun i => uOf C i = u).card ≤ 2 := by
  classical
  -- the chain index is determined by the host point
  have hk : ∀ i i', uOf C i = uOf C i' → sideE C.m ztdwj = sideE C.m (tJ C i') := by
    intro i i' h
    unfold uOf at h
    have h1 := Chazelle.Chain.sideE_le (m := C.m) (j := tJ C i) (tJ_lt C i).le
    have h2 := Chazelle.Chain.sideE_le (m := C.m) (j := tJ C i') (tJ_lt C i').le
    zumdy
    have e1 := Nat.div_add_mod zttx C.P.n
    have e2 := Nat.div_add_mod ztled C.P.n
    zvmwc at e1
    rcases le_total ztled zttx with hle | hle
    · zueum
      have hq0 : ztsle := by
        zuccr
        zuhvf

      grind
    · zueum
      have hq0 : ztsle := by
        zuccr
        zuhvf

      grind
  refine le_trans (Finset.card_le_card (t := ((Finset.range ztbb).filter fun i =>
      tJ C i = sideE C.m ztbnq) ∪
    ((Finset.range ztbb).filter fun i =>
      tJ C i = 2 * C.m - sideE C.m ztbnq))
    ?_) ((Finset.card_union_le _ _).trans (by
      have := card_tJ_eq C (sideE C.m ztbnq)
      have := card_tJ_eq C (2 * C.m -
        sideE C.m ztbnq)
      omega))
  zug
  zudld
  have hex : ∃ i, i < 2 * C.m ∧ uOf C i = u := ⟨i, hi.1, hi.2⟩
  have hsp := Classical.epsilon_spec hex
  have hki := hk _ _ (hi.2.trans hsp.2.symm)
  zuhpb
  zukdi
  unfold sideE at hki
  split_ifs at hki with h1 h2 h2
  · zumhy
  · zumhy
  · zuhjg
  · zuhjg

/-- **Few tour positions are breaks**: turns of the tour or break host points. -/
theorem card_brk_le (hn : 0 < n) (hwf : HostWF n H) :
    ((Finset.range ztbb).filter fun i =>
      tJ C i = 0 ∨ tJ C i = C.m ∨ HostBreak n H ztdim).card ≤ 2 + 8 * H.length := by
  classical
  have e : ((Finset.range ztbb).filter fun i =>
      tJ C i = 0 ∨ tJ C i = C.m ∨ HostBreak n H ztdim) ⊆
      ztxqc ∪
      (ztwvq ∪
      ztwxn) := by
    grind
  have hA := card_tJ_eq C 0
  have hB := card_tJ_eq C C.m
  have hC : ((Finset.range ztbb).filter fun i => HostBreak n H ztdim).card ≤
      2 * (((Finset.range ztbb).filter fun i => HostBreak n H ztdim).image
        ztwgy).card :=
    Finset.card_le_mul_card_image (f := uOf C) _ 2 fun u _ => by
      refine le_trans ztpyt (card_fiber_le C u)
      grind
  have hI : (((Finset.range ztbb).filter fun i => HostBreak n H ztdim).image
      ztwgy).card ≤ 4 * H.length := by
    refine le_trans ztowz (card_hostBreak_le hn hwf C.P.n)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_range.2 (uOf_lt C i), hi.2⟩
  have hU1 := Finset.card_union_le ztxqc
    (ztwvq ∪
      ztwxn)
  have hU2 := Finset.card_union_le ztwvq
    ztwxn
  have := Finset.card_le_card e
  omega
structure Pc where
  /-- The start. -/
  s : WPos
  /-- The end. -/
  e : WPos
  /-- The kind (`0` at most one counted edge, `1` a grade chain). -/
  kind : ℕ
  /-- The grade-table entry (kind `1`). -/
  entry : ℕ
  /-- The first edge of the chain of `Q` (kind `1`). -/
  x0 : ℕ
  /-- The direction (`1` upward). -/
  dir : ℕ
  /-- The number of edges `2^g` (kind `1`). -/
  pw : ℕ

/-- The walk of a kind-1 piece visits the chain `[x₀, x₀ + w]` of `Q` upward or downward. -/
def BlockWalk (W Q : Polygon) (p x0 w dir : ℕ) : Prop :=
  ∀ d, d ≤ w → W.vtx zttvc = Q.vtx (if dir = 1 then x0 + d else x0 + w - d)

/-- **A valid piece** of the chain model of `C`, for the grade table at `h` in the memory `m`
and the weight bound `γ`. -/
def PcOK (P : Polygon) (C : Chain) (m : ℕ → ℕ) (h γ : ℕ) (pc : Pc) : Prop :=
  ProperPos ztc zta P.n pc.s ∧ ProperPos ztc zta P.n pc.e ∧
    pc.s.edge < 2 * C.m + 7 ∧ pc.e.edge < 2 * C.m + 7 ∧ (pc.kind = 0 ∨ pc.kind = 1) ∧
    (pc.kind = 0 → (chainModel C).arcWt ztxjl
      ztxjk ≤ 1) ∧
    (pc.kind = 1 → ∃ g b, 1 ≤ g ∧ g < m h ∧ b < gradeCount P.n g ∧
      pc.entry = entryAddr m h g b ∧ pc.pw = 2 ^ g ∧ pc.x0 = b * 2 ^ g ∧
      b * 2 ^ g + 2 ^ g < P.n ∧ gradeGran g ≤ cutGran γ ∧
      pc.s.hgt = 0 ∧ pc.e.hgt = 0 ∧ 6 ≤ pc.s.edge ∧ pc.e.edge = pc.s.edge + 2 ^ g ∧
      pc.e.edge ≤ 2 * C.m + 6 ∧ (pc.dir = 1 ∨ pc.dir = 0) ∧
      BlockWalk (chainModel C).W zta pc.s.edge (b * 2 ^ g) ztgyk pc.dir)
theorem gradeLen_full {n g b : ℕ} (h : b * 2 ^ g + 2 ^ g < n) : gradeLen n g b = 2 ^ g := by
  unfold gradeLen; omega

/-- **The facts of a kind-1 piece** (`CutterOK`), read from the grade table in any memory `m'`
where it holds. -/
theorem kind1_facts {O : OracleIface} {P : Polygon} {C : Chain} {m m' : ℕ → ℕ} {h γ A : ℕ}
    {pc : Pc} (hok : PcOK P C m h γ pc) (hk : pc.kind = 1)
    (hR : Robust A m fun m'' => GradeRaw O P m'' h A) (hm' : ∀ a, a < A → m' a = m a)
    {A' : ℕ} (hA' : A ≤ A') :
    ChainWF P A' m' ztvyk ∧
      ∃ Hs Cα N, ChainDescAt m' ztvyk zta Hs Cα ∧
        NFWithin m' (m' ztoei) A' N ∧
        (∃ γ', γ' ≤ cutGran γ ∧ IsCanonicalNF ztbdc zta N γ' 4) ∧
        (chainModel C).arcSet ztxjl
          ztxjk = Cα.set ∧
        (chainModel C).arcWt ztxjl
          ztxjk = Cα.m ∧
        PieceWalk ztc Cα pc.s pc.e ∧ Cα.P = Qof P ∧
        ((∀ d, d ≤ Cα.m → (chainModel C).W.vtx ztyta =
            Cα.vertex d) ∨
          (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ztyta =
            Cα.vertex ztclf)) := by
  obtain ⟨hs, he, hsn, hen, -, -, h1⟩ := hok
  zukm

  have hΛ : ztuul := by
    have := (grade_low hR).1
    grind
  obtain ⟨Hs, Cα, N, hC, hwf, hP, -, -, hsC, hmC, hN, hcan, -⟩ := hR'.holds.2.2.2 g b hΛ hb
  have hPQ : Cα.P = Qof P := hP
  have hent : ztxth := by
    obtain ⟨h2, hr, -⟩ := grade_entry hR hgΛ hb
    zubtc

  rw [hent] at hC hwf hN
  zuc
  zuegz
  have hsα : Cα.s = b * 2 ^ g := by_tauto
  have hx : Cα.s + Cα.m < (Qof P).n := by_omega
  -- the walk agrees with the tour of `Cα`
  have hV : ∀ d, d ≤ Cα.m → (chainModel C).W.vtx zthjf =
      WalkEmbed.tourV Cα (if pc.dir = 1 then 0 else Cα.m) d := by
    zuip
    rw [hW d by_omega]
    split_ifs with hd1
    · rw [tourV_up Cα hd, grade_vertex hP hx hd, hsα]
    · rw [tourV_down Cα hd, grade_vertex hP hx by_omega, hsα, hlen]
      grind
  zubgg
  have hsP : pc.s = ztkmk := by zunwt
  have heP : pc.e = ⟨pc.s.edge + Cα.m, 0⟩ := by rw [hlen, ← hee, ← he0]
  refine ⟨hwf.mono hA', Hs, Cα, N, hC, hN.mono hA', ⟨gradeGran g, hgran, hcan⟩, ?_, ?_, ?_⟩
  · zugvn
    refine arcSet_tour (J := if pc.dir = 1 then 0 else Cα.m) by_grind by_omega
      hV
  · zugvn
    exact arcWt_chain_nat C by_grind h6 by_omega
  · rw [hsP, heP]
    have hmod : (pc.s.edge + Cα.m) % (chainModel C).W.n = pc.s.edge + Cα.m :=
      Nat.mod_eq_of_lt by_omega
    have := pieceWalk_tour (M := chainModel C) (Cα := Cα) (p₀ := pc.s.edge)
      (J := if pc.dir = 1 then 0 else Cα.m) by_omega (fun d hd => by
        zvmyc; grind)
    rw [hmod] at this
    refine ⟨this, hPQ, ?_⟩
    zubvt
    rcases hdir with hd1 | hd0
    · left
      zuip
      rw [Nat.mod_eq_of_lt by_omega, hV d hd, ite_eq_left hd1, tourV_up Cα hd]
    · right
      zuip
      rw [Nat.mod_eq_of_lt by_omega, hV d hd, ite_eq_right by_omega, tourV_down Cα hd]
variable {P : Polygon} {C : Chain} {m : ℕ → ℕ} {h γ : ℕ}
theorem proper_vtx' (P : Polygon) (C : Chain) (p : ℕ) :
    ProperPos ztc zta P.n ztcye := proper_vtx _ _ _ _

/-- **A single edge** between two walk vertices is a valid kind-0 piece. -/
theorem single_ok (e x0 dir pw : ℕ) {c : ℕ} (hc : c + 1 < 2 * C.m + 7) :
    PcOK P C m h γ ⟨ztexx, ztrax, 0, e, x0, dir, pw⟩ := by
  refine ⟨proper_vtx' P C _, proper_vtx' P C _, by_grind, by_omega, Or.inl rfl,
    fun _ => ?_, fun h1 => by_simp_all⟩
  simp only [key_hgt0]
  exact wt_within ztc (e := c) by_simp le_rfl by_simp

/-- **The grade of a block of weight at most `γ ≤ cap`** is processed and its granularity is
at most `cutGran γ`. -/
theorem block_grade {g Λ : ℕ} (hg : 1 ≤ g) (hγ : 2 ^ g ≤ γ) (hcap : γ ≤ 2 ^ ztufb) :
    g < Λ ∧ gradeGran g ≤ cutGran γ := by
  have h1 : g ≤ Λ - 1 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (hγ.trans hcap)
    omega
  have h2 : 2 ≤ 2 ^ g := by
    grind
  refine ⟨by
    omega, ?_⟩
  unfold cutGran
  apply gradeGran_mono
  have : 2 ^ g ≤ 2 ^ Nat.clog 2 γ := hγ.trans (Nat.le_pow_clog by_norm_num γ)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
variable {c q L g b e : ℕ}
/-- **A block of an upward stretch** `[q, q + L]` (walk vertices `c + d ↦ Q.vtx (q + d)`). -/
theorem blockUp_ok (hwalk : ∀ d, d ≤ L →
      (chainModel C).W.vtx ztjrg = (Qof P).vtx zttwp)
    (h6 : 6 ≤ c) (hcL : c + L ≤ 2 * C.m + 6) (hqL : q + L < P.n) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ ztlrg) (hlo : q ≤ b * 2 ^ g) (hhi : ztds * 2 ^ g ≤ q + L)
    (he : 1 ≤ g → e = entryAddr m h g b) :
    PcOK P C m h γ ⟨⟨c + ztnrk, 0⟩, ⟨c + ztnrk + 2 ^ g, 0⟩,
      if 0 < g then 1 else 0, e, b * 2 ^ g, 1, 2 ^ g⟩ := by
  zubdt
  zudmw
  zuevb
  · zuhpw
    exact single_ok e zttfg 1 1 by_omega
  · zuccl

    refine ⟨proper_vtx' P C _, proper_vtx' P C _, by_grind, by_grind, Or.inr rfl,
      fun h1 => by_simp_all, fun _ => ⟨g, b, hg, hΛ, ?_, he hg, rfl, rfl, by_omega, hgran,
        rfl, rfl, by_grind, rfl, by_grind, Or.inl rfl, fun d hd => ?_⟩⟩
    · zulbt
      have : b * 2 ^ g + 2 ^ g ≤ P.n - 1 := by_omega
      zulgp
      have := (Nat.le_div_iff_mul_le hp).2 this
      omega
    · zubvh
      zuhkb

/-- **A block of a downward stretch** from the top `q` (walk vertices `c + d ↦ Q.vtx (q - d)`). -/
theorem blockDn_ok (hwalk : ∀ d, d ≤ L →
      (chainModel C).W.vtx ztjrg = (Qof P).vtx zttwr)
    (h6 : 6 ≤ c) (hcL : c + L ≤ 2 * C.m + 6) (hq : q < P.n) (hLq : L ≤ q) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ ztlrg) (hlo : q - L ≤ b * 2 ^ g) (hhi : ztds * 2 ^ g ≤ q)
    (he : 1 ≤ g → e = entryAddr m h g b) :
    PcOK P C m h γ ⟨⟨c + ztyrn, 0⟩, ⟨c + ztyrn + 2 ^ g, 0⟩,
      if 0 < g then 1 else 0, e, b * 2 ^ g, 0, 2 ^ g⟩ := by
  zubdt
  zudmw
  zuevb
  · zuhpw
    exact single_ok e zttfg 0 1 by_omega
  · zuccl

    refine ⟨proper_vtx' P C _, proper_vtx' P C _, by_grind, by_grind, Or.inr rfl,
      fun h1 => by_simp_all, fun _ => ⟨g, b, hg, hΛ, ?_, he hg, rfl, rfl, by_omega, hgran,
        rfl, rfl, by_grind, rfl, by_grind, Or.inr rfl, fun d hd => ?_⟩⟩
    · zulbt
      zulgp
      have := (Nat.le_div_iff_mul_le hp).2 this
      omega
    · simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
      zuhkb
end ShootCut
open Metric
open Chazelle.Geometry (lerp point_ext)
namespace Sweep
section ChainModel
variable (C : Chain)

/-- The ray points from a later origin, backwards. -/
theorem rayPt_back (a : Point) (σ τ' s : ℝ) :
    rayPt (rayPt a σ τ') (-σ) s = rayPt a σ (τ' - s) := by
  zuhbh
end ChainModel
end Sweep
end
namespace Brute
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
inductive Src where
  | v (r : ℕ)
  | e (r₁ r₂ : ℕ)

/-- Load a source into the three kernel registers from `s`. -/
def Src.load (s : ℕ) : Src → Stmt
  | .v r => block [.constN s 0, .copyN ztbk r]
  | .e r₁ r₂ => block [.constN s 1, .copyN ztbk r₁, .copyN ztfp r₂]

/-- The symbolic point of a source in a configuration. -/
def Src.pt (c : Config) : Src → SymPt
  | .v r => .vtx ztfgx
  | .e r₁ r₂ => .onEdge (c.nreg r₁) (c.nreg r₂)

/-- The registers of a source are outside the kernel's registers. -/
def Src.Out : Src → Prop
  | .v r => r < 10000 ∨ 10500 ≤ r
  | .e r₁ r₂ => (r₁ < 10000 ∨ 10500 ≤ r₁) ∧ (r₂ < 10000 ∨ 10500 ≤ r₂)

/-- A sign test with its answer bit copied to register `d`. -/
def testS (op : ℕ) (x y z : Src) (d : ℕ) : Stmt :=
  .seq (x.load 10000) (.seq (y.load 10003) (.seq (z.load 10006)
    (.seq ztifn ztkps)))
variable {P : Polygon} {W : ℕ}
theorem load_exec (hW : 1 ≤ W) (s : ℕ) (hs : 10000 ≤ s ∧ s + 3 ≤ 10500)
    (x : Src) (hx : x.Out) (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (x.load s) c c' k ∧ k ≤ 3 ∧ SymPtIn c' s ztwia ∧
      (∀ r, (r < s ∨ s + 3 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  cases x with
  | v r =>
    simp only [Src.Out] at hx
    unfold Src.load
    exec_block
    · omega
    · refine ztgoc
      · zujob
        refine ztcp <;> simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other]
      · zup
  | e r₁ r₂ =>
    simp only [Src.Out] at hx
    unfold Src.load
    exec_block
    · omega
    · refine ztgoc
      · zujob
        refine ztcg <;> simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other]
      · zup
theorem src_pt_eq {x : Src} (hx : x.Out) {c c' : Config}
    (h : ∀ r, ztcu → c'.nreg r = c.nreg r) : x.pt c' = x.pt c := by
  cases x with
  | v r => simp only [Src.pt, Src.Out] at hx ⊢; rw [h r hx]
  | e r₁ r₂ => simp only [Src.pt, Src.Out] at hx ⊢; rw [h r₁ hx.1, h r₂ hx.2]

/-- The write set of a test: the kernel's registers and the destination. -/
def Bt (d : ℕ) (r : ℕ) : Bool := Bk r || decide (r = d)

/-- **A sign test into register `d`** (at most `245` steps). -/
theorem testS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {op : ℕ}
    (hop : op ≤ 3) {x y z : Src} (hx : x.Out) (hy : y.Out) (hz : z.Out) {d : ℕ}
    (c : Config) (hw : WordsBounded W c) (hlx : (x.pt c).Lt P.n) (hly : (y.pt c).Lt P.n)
    (hlz : (z.pt c).Lt P.n) :
    ∃ c' k, Exec P W ztpel c c' k ∧ k ≤ 245 ∧ FrameB ztjhb c c' ∧
      c'.nreg d ≤ 1 ∧
      (c'.nreg d = 1 ↔ SignTest op ((x.pt c).eval zta) ((y.pt c).eval zta)
        ((z.pt c).eval zta)) := by
  zudk
  obtain ⟨c₁, k₁, e₁, hk₁, s₁, r₁, rr₁, m₁, rm₁, o₁⟩ :=
    load_exec (P := P) hW1 10000 by_omega x hx c hw
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, r₂, rr₂, m₂, rm₂, o₂⟩ :=
    load_exec (P := P) hW1 10003 by_omega y hy c₁ e₁.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, rr₃, m₃, rm₃, o₃⟩ :=
    load_exec (P := P) hW1 10006 by_omega z hz c₂ e₂.wb_right
  have e₄ := Exec.constN (P := P) e₃.wb_right 10009 op by_omega
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 10009 op }
  have q₄ : ∀ r, r ≠ 10009 → c₄.nreg r = c₃.nreg r := fun r hr => by simp [c₄, hr]
  -- the points survive
  have hy₁ : y.pt c₁ = y.pt c := src_pt_eq hy fun r hr => r₁ r by_omega
  have hz₁ : z.pt c₂ = z.pt c := by
    rw [src_pt_eq hz fun r hr => r₂ r by_omega]
    exact src_pt_eq hz fun r hr => r₁ r by_omega
  have S₁ : SymPtIn c₄ 10000 ztwia := symPtIn_of_eq s₁ fun j h1 h2 => by
    grind
  have S₂ : SymPtIn c₄ 10003 (y.pt c) := by
    rw [← hy₁]
    exact symPtIn_of_eq s₂ fun j h1 h2 => by_grind
  have S₃ : SymPtIn c₄ 10006 (z.pt c) := by
    rw [← hz₁]
    tauto
  have hop₄ : ztusr := by_rfl
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, bit₅, sig₅⟩ := sig_exec (P := P) c₄ e₄.wb_right hG hW
    by_omega hlx hly hlz S₁ S₂ S₃
  rw [hop₄] at sig₅
  have e₆ := Exec.copyN (P := P) e₅.wb_right d 10010
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg d (c₅.nreg 10010) }
  have ex : Exec P W ztpel c c₆ (k₁ + (k₂ + (k₃ + (1 + ztett)))) :=
    .seq e₁ ztfv
  have hd : c₆.nreg d = c₅.nreg 10010 := by simp [c₆]
  refine ⟨c₆, _, ex, by_omega, ztcxw, by_omega,
    by simp_all⟩
  · have hr' : Bk r = false ∧ r ≠ d := by
      zulba
    have hnk : r < 10000 ∨ 10500 ≤ r := by
      have := hr'.1; unfold Bk at this; grind
    zulsa
    rw [upd_other _ _ _ hr'.2, f₅.1 r hr'.1, q₄ r by_omega, r₃ r by_omega, r₂ r by_omega,
      r₁ r by_omega]
  · have hr' : Bk r = false := by
      zulba
    zulsa
    rw [f₅.2.1 r hr', rr₃, rr₂, rr₁]
  · zunur; rw [f₅.2.2.1, m₃, m₂, m₁]
  · zunur; rw [f₅.2.2.2.1, rm₃, rm₂, rm₁]
  · zunur; rw [f₅.2.2.2.2, o₃, o₂, o₁]
theorem vertex_eq {C : Chain} {k : ℕ} (hk : C.s + k < C.P.n) : C.vertex k = C.P.vtx zttw := by
  unfold Chain.vertex Chain.edgeIdx; rw [Nat.mod_eq_of_lt hk]
theorem edgeIdx_eq {C : Chain} {k : ℕ} (hk : C.s + k < C.P.n) : C.edgeIdx k = C.s + k := by
  unfold Chain.edgeIdx; rw [Nat.mod_eq_of_lt hk]

/-- The write set of the brute-force procedure's own statements: the kernel's registers and
band `18`. -/
def Bm (r : ℕ) : Bool := Bk r || decide (180000 ≤ r ∧ r < 190000)
theorem frameB_mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B' r = false → B r = false) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_simp_all, fun r hr => h.2.1 r by_simp_all, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## Constants -/

/-- The constants. -/
def initS : Stmt :=
  block [.inputSize 180010, .constN 180011 1, .addN 180012 180001 180001, .copyN 180016 9999,
    .constN 180026 3, .constN 180027 6, .constN 180028 0, .addN 180023 180001 180011,
    .addN 180025 180012 180011]
variable {P : Polygon} {W : ℕ} (c : Config)
theorem initS_exec (hw : WordsBounded W c)
    (hW : P.n + 2 * c.nreg 180001 + 7 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 9 ∧ c'.nreg 180010 = P.n ∧ c'.nreg 180011 = 1 ∧
      c'.nreg 180012 = 2 * c.nreg 180001 ∧ c'.nreg 180016 = c.nreg 9999 ∧
      c'.nreg 180026 = 3 ∧ c'.nreg 180027 = 6 ∧ c'.nreg 180028 = 0 ∧
      c'.nreg 180023 = c.nreg 180001 + 1 ∧ c'.nreg 180025 = 2 * c.nreg 180001 + 1 ∧
      FrameB (fun r => decide (180010 ≤ r ∧ r < 180030)) c c' := by
  zujqm
  exec_block
  · omega
  · omega
  · config_simp; omega
  · omega
  · omega
  · omega
  · config_simp; omega
  · config_simp; omega
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ztgq⟩
    all_goals first
      | (simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]; omega)
      | simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      | skip
    zubzq
    zudw

/-! ## Boolean operations on bit registers (`180011` holds `1`) -/

/-- `d := x ∧ y` (`x + y - 1`). -/
def andS (d x y : ℕ) : Stmt := block [.addN d x y, .subN d d 180011]

/-- `d := x ∨ y` (`x + y - (x + y - 1)`), with scratch `t`. -/
def orS (d x y t : ℕ) : Stmt := block [.addN d x y, .subN t d 180011, .subN d d t]

/-- `d := ¬ x` (`1 - x`). -/
def notS (d x : ℕ) : Stmt := block [.subN d 180011 x]
theorem andS_exec (hW : 2 ≤ W) (c : Config) (hw : WordsBounded W c)
    {d x y : ℕ} (hd : d ≠ 180011) (h1 : c.nreg 180011 = 1) (hx : c.nreg x ≤ 1)
    (hy : c.nreg y ≤ 1) :
    ∃ c' k, Exec P W (andS d x y) c c' k ∧ k = 2 ∧ c'.nreg d = c.nreg x + c.nreg y - 1 ∧
      FrameB ztbaz c c' := by
  unfold andS
  exec_block
  · grind
  · zulox
    · zubs
      zuwv
    simp_all
theorem orS_exec (hW : 2 ≤ W) (c : Config) (hw : WordsBounded W c)
    {d x y t : ℕ} (hd : d ≠ 180011) (ht : t ≠ 180011) (hdt : d ≠ t) (h1 : c.nreg 180011 = 1)
    (hx : c.nreg x ≤ 1) (hy : c.nreg y ≤ 1) :
    ∃ c' k, Exec P W (orS d x y t) c c' k ∧ k = 3 ∧
      c'.nreg d = ztqjc - (c.nreg x + c.nreg y - 1) ∧
      FrameB ztbqe c c' := by
  unfold orS
  exec_block
  · omega
  · zulox
    · zubs
      zuwv
    simp_all
theorem notS_exec (hw : WordsBounded W c)
    {d x : ℕ} (_hd : d ≠ 180011) (h1 : c.nreg 180011 = 1) :
    ∃ c' k, Exec P W (notS d x) c c' k ∧ k = 1 ∧ c'.nreg d = 1 - c.nreg x ∧
      FrameB ztbaz c c' := by
  unfold notS
  exec_block
  zulox
  · simp_all
  simp_all

/-! ## The top index -/

/-- One step of the top-index scan: compare `v_best` with `v_k`, keep the higher. -/
def topBody : Stmt :=
  .seq ztiqi
    (.seq (testS 1 ztuvs (.v 180022) ztuvs 180029)
      (.seq ztipo
        (.instr (.addN 180020 180020 180011))))

/-- The top-index scan. -/
def topS : Stmt :=
  .seq ztkqy (.whileLtN 180020 180023 topBody)

/-- The write set of the scan. -/
def Btop (r : ℕ) : Bool :=
  Bk r || decide (r = 180013 ∨ (180020 ≤ r ∧ r < 180023) ∨ r = 180029)
theorem topBody_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {a b k : ℕ} (h0 : c.nreg 180000 = a) (h11 : c.nreg 180011 = 1)
    (h13 : c.nreg 180013 = b) (h20 : c.nreg 180020 = k) (hb : a + b < P.n) (hk : a + k < P.n) :
    ∃ c' k', Exec P W topBody c c' k' ∧ k' ≤ 253 ∧ FrameB Btop c c' ∧
      c'.nreg 180020 = k + 1 ∧
      c'.nreg 180013 = if ((Qof P).vtx ztth).2 < ((Qof P).vtx ztbzd).2 then k else b := by
  obtain ⟨c₁, k₁, e₁, hk₁, q21, q22, R₁, R₁'⟩ : ∃ c₁ k₁, Exec P W
      ztiqi c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180021 = a + b ∧ c₁.nreg 180022 = a + k ∧ FrameB Btop c c₁ ∧
      ∀ r, r ≠ 180021 → r ≠ 180022 → c₁.nreg r = c.nreg r := by
    exec_block
    · omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, ztgq, fun r h1 h2 => ?_⟩
      · simp_all
      · simp_all
      · zugzz
        zupg
        zudw
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, bit₂, sig₂⟩ := testS_exec (P := P) hG hW (op := 1) by_omega
    (x := .v 180021) (y := .v 180022) (z := .v 180021) (d := 180029) ztbh
    ztbh ztbh c₁ e₁.wb_right
    ztig ztig
    ztig
  simp only [Src.pt, SymPt.eval, SignTest, q21, q22] at sig₂
  have k2 := F₂.1
  have c11 : ztpnd := by
    rw [k2 _ by_decide, R₁' _ by_decide by_decide, h11]
  have c13 : c₂.nreg 180013 = b := by rw [k2 _ by_decide, R₁' _ by_decide by_decide, h13]
  have c20 : c₂.nreg 180020 = k := by rw [k2 _ by_decide, R₁' _ by_decide by_decide, h20]
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, q13, q20, R₃⟩ : ∃ c₃ k₃, Exec P W
      ztipo c₂ c₃ k₃ ∧ k₃ ≤ 3 ∧
      c₃.nreg 180013 = (if ((Qof P).vtx ztth).2 < ((Qof P).vtx ztbzd).2 then k else b) ∧
      c₃.nreg 180020 = k ∧ FrameB Btop c₂ c₃ := by
    by_cases ht : ((Qof P).vtx ztth).2 < ((Qof P).vtx ztbzd).2
    · have h1 := sig₂.2 ht
      refine ⟨_, _, .ifLtN_false by_omega (Exec.copyN w₂ 180013 180020), le_refl _,
        ?_, ?_, ztgq⟩
      · simp_all
      · simp_all
      · zugzz
        simp_all
    · have h1 : c₂.nreg 180029 = 0 := by_grind
      exact ⟨_, _, .ifLtN_true by_omega ztbun, by_omega,
        by simp_all, c20, FrameB.refl _ _⟩
  have e₄ := Exec.addN (P := P) e₃.wb_right 180020 180020 180011 (by
    zunrf; omega)
  refine ⟨_, _, .seq e₁ ztcb, by_omega, ?_, ?_, ?_⟩
  · refine (R₁.trans (frameB_mono F₂ ?_)).trans (R₃.trans ztgq)
    · zuz
      unfold Btop at hr; unfold Bt
      simp_all
    · zugzz
      zupg
      zudw
  · zubzl
    zunrf
  simp_all

/-- **The top-index scan**: register `180013` receives the index of the highest vertex among
`v_a, …, v_{a+m}` (at most `254 m + 256` steps). -/
theorem topS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {a m : ℕ} (h0 : c.nreg 180000 = a) (h11 : c.nreg 180011 = 1)
    (h23 : c.nreg 180023 = m + 1) (ham : a + m < P.n) :
    ∃ c' k', Exec P W topS c c' k' ∧ k' ≤ 255 * m + 257 ∧ FrameB Btop c c' ∧
      c'.nreg 180013 ≤ m ∧
      ∀ i, i ≤ m → ((Qof P).vtx zteon).2 ≤ ((Qof P).vtx (a + c'.nreg 180013)).2 := by
  obtain ⟨c₁, k₁, e₁, hk₁, q13, q20, R₁⟩ : ∃ c₁ k₁, Exec P W
      ztkqy c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180013 = 0 ∧ c₁.nreg 180020 = 1 ∧ FrameB Btop c c₁ := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, ztgq⟩
      zugzz
      zupg
      zudw
  let I : Config → Prop := fun d => WordsBounded W d ∧ FrameB Btop c d ∧
    1 ≤ d.nreg 180020 ∧ d.nreg 180020 ≤ m + 1 ∧ d.nreg 180013 < d.nreg 180020 ∧
    ∀ i, i < d.nreg 180020 → ((Qof P).vtx zteon).2 ≤ ((Qof P).vtx (a + d.nreg 180013)).2
  have hI₁ : ztkzz := ⟨e₁.wb_right, R₁, by_omega, by_omega, by_omega, by_simp_all⟩
  have keep : ∀ d r, FrameB Btop c d → Btop r = false → d.nreg r = c.nreg r := fun d r h hr =>
    h.1 r hr
  obtain ⟨c₂, k₂, e₂, ⟨w₂, F₂, h₁, h₂, h₃, h₄⟩, hex, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 180020) (b := 180023) (body := topBody) I
      (fun d => m + 1 - d.nreg 180020) 253 ztoe
      (by
        intro d ⟨wd, Fd, d1, d2, d3, d4⟩ hlt
        have d23 : d.nreg 180023 = m + 1 := by rw [keep d _ Fd by_decide, h23]
        rw [d23] at hlt
        obtain ⟨d', k', e', hk', F', q20', q13'⟩ := topBody_exec hG hW d wd
          (by rw [keep d _ Fd by_decide, h0]) (by rw [keep d _ Fd by_decide, h11]) rfl rfl
          by_omega by_omega
        refine ⟨d', k', e', ⟨e'.wb_right, Fd.trans F', by_omega, by_omega, ?_, ?_⟩, hk', by_omega⟩
        · grind
        · zug
          rw [q20'] at hi
          rw [q13']
          zujpo
          · zucyp
            · zubfo
            · exact le_rfl
          · zucyp
            · exact d4 i hi
            · exact not_lt.1 ht)
      hI₁
  have c23 : c₂.nreg 180023 = m + 1 := by rw [keep c₂ _ F₂ by_decide, h23]
  rw [c23] at hex
  refine ⟨c₂, _, .seq e₁ e₂, ?_, F₂, by_omega, by_grind⟩
  omega
end
end Brute
namespace DrvB
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (sideLeftOf sideCcw sideCross sideDot sideNonSpike)
open Chazelle.Visibility (DirInterior rayPt)
open Chazelle.Jordan (simple_three_le simple_vtx_ne simple_vtx_succ_ne)

/-! ## Directions in the left sector of a corner -/
variable {a v b : Point} {W : Polygon}
/-- A horizontal ray from the apex of a corner lies in its left sector at every parameter or at
none (the sector is a cone). -/
theorem sideLeftOf_rayPt_scale {σ s : ℝ} (hs : 0 < s) :
    sideLeftOf a v b ztrvb ↔ sideLeftOf a v b ztczx := by
  zucfg
  rw [FuseMath.rayPt_sub, FuseMath.rayPt_sub, one_smul, Chazelle.Chain.sideCcw_smul hs]

/-- **The corner test.**  For a simple polygon with the interior on its left, the horizontal
direction `σ = ±1` at vertex `p` is locally interior iff it lies in the open left sector of the
corner at `p`. -/
theorem dirInterior_iff_corner (hW : W.Simple) (hL : Mountain.orient W = 1)
    {p : ℕ} (hp : p < W.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    DirInterior W p σ ↔
      sideLeftOf ztbafn ztbbv ztbajj
        (rayPt ztbbv σ 1) := by
  obtain ⟨r, hr, hloc⟩ := FactsInterior.vertex_local hW hL hp
  have hball : ∀ s, 0 ≤ s → s < r → rayPt ztbbv σ s ∈ ball ztbbv r := fun s hs0 hsr => by
    rw [mem_ball, FuseMath.dist_rayPt _ hσ hs0]; omega
  constructor
  · zuq
    obtain ⟨s, hs, ⟨hs0, hsr⟩⟩ := (h.and ztmbi).exists
    have hx := hball s hs0.le hsr
    rcases (hloc _ hx).2.2 hs.2 with hl | hr'
    · exact (sideLeftOf_rayPt_scale hs0).1 hl
    grind
  · zuq
    zultr
    zuhuo
    exact (hloc _ (hball s hs.1.le hs.2)).1 ((sideLeftOf_rayPt_scale hs.1).2 h)

/-! ## The decision of the corner test -/

/-- **The corner decision** for the corner `a → v → b` and the horizontal direction `σ`: by the
heights of the neighbours (and their abscissae when one is at the height of `v`) and one
orientation test. -/
def emitG (a v b : Point) (σ : ℝ) : Prop :=
  if a.2 = v.2 then
    (if b.2 = v.2 then False
     else if v.2 < b.2 then σ = -1 ∧ v.1 < a.1 else σ = 1 ∧ a.1 < v.1)
  else if b.2 = v.2 then
    (if v.2 < a.2 then σ = 1 ∧ b.1 < v.1 else σ = -1 ∧ v.1 < b.1)
  else Brute.emitR a v b σ

/-- The four cases of `sideCcw`, spelled out. -/
theorem sideCcw_iff_raw (B X A : Point) : sideCcw B X A ↔
    ztgbt ∨
    ztfuo ∨
    ztgmc ∨
    ztecu := Iff.rfl

/-- **The corner decision is the left sector** (for a corner that is not a spike). -/
theorem sideLeftOf_iff_emitG (hav : a ≠ v) (hbv : b ≠ v)
    (hns : sideNonSpike ztfd ztgg) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    sideLeftOf a v b ztczx ↔ emitG a v b σ := by
  have eBX : sideCross ztfd (ztwn : Point) = -σ * ztcet := by
    unfold sideCross; simp only [Prod.snd_sub, Prod.fst_sub]; ring
  have eXA : sideCross (ztwn : Point) ztgg = σ * ztclz := by
    zubag
  have eBA : sideCross ztfd ztgg =
      ztry * ztclz - ztcet * ztcts := by
    rfl
  have eDBA : sideDot ztfd ztgg =
      ztry * ztcts + ztcet * ztclz := by
    rfl
  zucfg
  rw [FuseMath.rayPt_sub_one, sideCcw_iff_raw]
  unfold emitG
  by_cases ha : a.2 = v.2
  · zuhme
    have ha' : a.2 - v.2 = 0 := by_simp_all
    have ha1 : ztsdj := fun h => hav (Prod.ext by_linarith ha)
    have cXA : sideCross (ztwn : Point) ztgg = 0 := by_simp_all
    zufqy
    · -- both neighbours at the height of `v`: only a spike contains a horizontal direction
      zugeq

      zujww
      have cBA : ztzqq := by_simp_all
      rw [cBX, cBA]
      simp only [iff_false]
      rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, hd, -⟩)
      · simp_all
      · simp_all
      · simp_all
      tauto
    · zulqe
      have hb0 : b.2 - v.2 ≠ 0 := sub_ne_zero.2 hb
      have cBA : sideCross ztfd ztgg = -(ztcet * ztcts) := by
        simp_all
      have hne : ztcet * ztcts ≠ 0 := mul_ne_zero hb0 ha1
      rw [cXA, cBA, eBX]
      by_cases hvb : v.2 < b.2
      · rw [ite_eq_left hvb]
        have hbp : ztrzi := by_linarith
        constructor
        · zubjp
          · simp_all
          · zujx
            · zur
              · grind
              · rfl
            simp_all
          · simp_all
          · simp_all
          simp_all
        simp_all
      · rw [ite_eq_right hvb]
        have hbn : ztmud := by
          grind
        constructor
        · zubjp
          · simp_all
          · zujx
            · grind
            · zuca
              nlinarith
          · simp_all
          · simp_all
          simp_all
        · zugbk
          zuhl
          refine ⟨?_, Or.inl ?_⟩
          · have : 0 < ztcet * ztcts := mul_pos_of_neg_of_neg hbn by_linarith
            linarith
          simp_all
  · zuhmm
    have ha0 : ztsdl := sub_ne_zero.2 ha
    zufqy
    · zugeq

      have hb1 : b.1 - v.1 ≠ 0 := fun h => hbv (Prod.ext by_linarith hb)
      zujww
      have cBA : sideCross ztfd ztgg = ztry * ztclz := by
        simp_all
      have hne : ztry * ztclz ≠ 0 := mul_ne_zero hb1 ha0
      rw [cBX, cBA, eXA]
      by_cases hva : v.2 < a.2
      · rw [ite_eq_left hva]
        have hap : 0 < a.2 - v.2 := by_linarith
        constructor
        · zubjq
          · simp_all
          · simp_all
          · zujx
            · zur
              · rfl
              grind
            · zuca
              nlinarith
          · simp_all
          simp_all
        · zugbk
          zuhl
          refine ztryo
          · exact mul_neg_of_neg_of_pos by_linarith hap
          simp_all
      · rw [ite_eq_right hva]
        have han : a.2 - v.2 < 0 := by
          grind
        constructor
        · zubjq
          · simp_all
          · simp_all
          · zujx
            · grind
            · zuca
              nlinarith
          · simp_all
          simp_all
        · zugbk
          zuhl
          refine ztryo
          · exact mul_neg_of_pos_of_neg by_linarith han
          simp_all
    · zulqe
      have h := Brute.sideLeftOf_horiz ha hb hσ
      unfold sideLeftOf at h
      rw [FuseMath.rayPt_sub_one, sideCcw_iff_raw] at h
      zubh

/-- **The corner test by the decision.**  For a simple polygon with the interior on its left,
direction `σ = ±1` at vertex `p` is locally interior iff the corner decision holds. -/
theorem dirInterior_iff_emitG (hW : W.Simple) (hL : Mountain.orient W = 1)
    {p : ℕ} (hp : p < W.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    DirInterior W p σ ↔
      emitG ztbafn ztbbv ztbajj σ := by
  rw [dirInterior_iff_corner hW hL hp hσ]
  zuerq
  have hav : W.vtx ztnkf ≠ W.vtx p :=
    simple_vtx_ne hW (Chazelle.Jordan.prevIdx_lt W hp) hp (Chazelle.Jordan.prevIdx_ne W hn hp)
  have hbv : W.vtx ztwjb ≠ W.vtx p := (simple_vtx_succ_ne hW hp).symm
  exact sideLeftOf_iff_emitG hav hbv (FactsInterior.corner_nonSpike hW hp) hσ
end
end DrvB
namespace DownHost
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideSectorIn ChordSystem freeIn
  regionsIn TouchesIn)
open Chazelle.Geometry (lerp lerp_mem_segment)
variable (M : Model) (F : Set (Set Point)) (U : Set Point)

/-- The attachment keys of the exit chords of `U`. -/
def exitKeys : Set ℝ :=
  {x | ∃ c ∈ F, TouchesIn M.D c U ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ x = p + t}

/-- The keys of the walk vertices strictly inside the arcs of `U`. -/
def vtxKeys : Set ℝ :=
  {x | ∃ k : ℕ, k < M.W.n ∧ x = k ∧ ∃ a b : ℝ, M.IsArc F U a b ∧ sideInArc a b k}

/-- **The host keys of `U`**. -/
def hostKeys : Set ℝ := exitKeys M F U ∪ vtxKeys M F U
variable {M F U}
theorem exitKeys_subset_cuts : exitKeys M F U ⊆ {x | M.IsCut F x} := by
  rintro x ⟨c, hc, -, p, t, hA, rfl⟩
  exact ztcxr
theorem vtxKeys_finite : (vtxKeys M F U).Finite := by
  refine ((Finset.range M.W.n).finite_toSet.image (fun k : ℕ => (k : ℝ))).subset ?_
  rintro x ⟨k, hk, rfl, -⟩
  simp_all
theorem hostKeys_finite (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    (hostKeys M F U).Finite :=
  ((hM.finite_cuts hF hfin).subset exitKeys_subset_cuts).union vtxKeys_finite

/-- Host keys lie in `[0, n)`. -/
theorem hostKeys_bounds {x : ℝ} (hx : x ∈ hostKeys M F U) : 0 ≤ x ∧ x < M.W.n := by
  rcases hx with hx | ⟨k, hk, rfl, -⟩
  · exact WalkAx.cut_bounds ztqmp
  simp_all

/-- Distinct chords of a finite admissible family do not meet in the domain. -/
theorem chord_disj (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) (hne : c ≠ c') {z : Point} (hz : z ∈ c) (hz' : z ∈ c')
    (hzD : z ∈ M.D) : False := by
  zudr
  obtain ⟨y, a, b, h, rfl⟩ := hsys.hchord c hc
  obtain ⟨y', a', b', h', rfl⟩ := hsys.hchord c' hc'
  exact hne (SegObs.eq_of_common ztfxb ⟨y', a', b', h', rfl⟩ hz hz' hzD)
variable {a b : ℝ}
/-- Small positive numbers, as an eventual statement. -/
theorem ev_Ioo (h : a < b) : ∀ᶠ ε in 𝓝[>] a, ε ∈ Ioo a b := Ioo_mem_nhdsGT h

/-- Numbers just below `b`, as an eventual statement. -/
theorem ev_Ioo_lt (h : a < b) : ∀ᶠ ε in 𝓝[<] b, ε ∈ Ioo a b := Ioo_mem_nhdsLT h

/-- The start of a cyclic interval is not inside it. -/
theorem not_sideInArc_left (a b : ℝ) : ¬ sideInArc a b a := by
  zudcn

/-- The end of a cyclic interval is not inside it. -/
theorem not_sideInArc_right (a b : ℝ) : ¬ sideInArc a b b := by
  zudcn

/-- Keys strictly after a key inside an open cyclic interval stay inside it. -/
theorem eventually_in_arc {a b k : ℝ} (hk : sideInArc a b k) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b zthig := by
  unfold sideInArc at *
  split_ifs at * with h
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ztecr]
      with ε hε hε'
    grind
  · zucot
    · zulg
      grind
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ztecr]
        with ε hε hε'
      grind

/-- **Separation.**  If the positions strictly between the attachments `A`, `B` of `c ∈ F` have
their small left sectors in the component `K` of `D \ c` of `k₁`, a host key of `U` strictly
between `A` and `B` forces `U ⊆ K`. -/
theorem host_side (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hU : U ∈ M.regions F) {c : Set Point} (hc : c ∈ F) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {k₁ : Point}
    (hK : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbf ztbd ztk →
      SideSectorIn M.W ztzvl p t)
    {x : ℝ} (hx : x ∈ hostKeys M F U) (hxin : sideInArc ztbf ztbd x) :
    U ⊆ connectedComponentIn ztjq k₁ := by
  set K := connectedComponentIn ztjq k₁ with hKdef
  have hUfree : ztscu := fun y hy =>
    ⟨(Chazelle.Chain.regionsIn_subset hU hy).1,
      fun hyc => (Chazelle.Chain.regionsIn_subset hU hy).2 ⟨c, hc, hyc⟩⟩
  have hUpre := Chazelle.Chain.regionsIn_isPreconnected hU
  have hKo : IsOpen K :=
    (hM.isOpen.sdiff ((hM.sys F hF hfin).isClosed_chord hc)).connectedComponentIn
  -- a point of `U` in `K` suffices
  have hmeet : ∀ u ∈ U, u ∈ K → U ⊆ K := fun u hu huK => by
    rw [hKdef, connectedComponentIn_eq huK]
    exact hUpre.subset_connectedComponentIn hu hUfree
  rcases hx with ⟨c', hc', htouch, p, t, hA', rfl⟩ | ⟨k, hk, rfl, a, b, harc, hkab⟩
  · -- an exit chord `c'` attached strictly between `A` and `B`
    have hcc' : c' ≠ c := by
      zunq
      zubbw
      rcases hM.attach_endpoint hopen (hcab ▸ hA') with h | h
      · zufkq
        exact not_sideInArc_left _ _ hxin
      · obtain ⟨rfl, rfl⟩ := hM.attach_unique ztlz hA' hB h
        exact not_sideInArc_right _ _ hxin
    obtain ⟨e, he, -, hce, hopen, heD, -⟩ := hM.attach_other_end ztesy hA'
    obtain ⟨r, hr, hsec⟩ := hK p hA'.1 t hA'.2.1 hA'.2.2.1 hxin
    obtain ⟨s, hs0, hs1, hsd, hsl⟩ := WalkAx.exists_left_on_chord hA' hce he hr
    have hyK : lerp ztbp e s ∈ K := hsec _ by_tauto hsl
    -- the open part of `c'` lies in `K`
    have hopenK : ∀ s' ∈ Ioo (0 : ℝ) 1, lerp ztbp e s' ∈ K := by
      have hpre : IsPreconnected (ztzww '' Ioo (0 : ℝ) 1) :=
        isPreconnected_Ioo.image _ (Chazelle.Geometry.continuous_lerp _ _).continuousOn
      have hsub : ztzww '' Ioo (0 : ℝ) 1 ⊆ M.D \ c := by
        zuvn
        refine ⟨hopen s' hs', fun hmem => chord_disj hM hF hfin hc' hc hcc' ?_ hmem (hopen s' hs')⟩
        zvnme; exact lerp_mem_segment _ _ hs'.1.le hs'.2.le
      intro s' hs'
      rw [hKdef, connectedComponentIn_eq hyK]
      exact hpre.subset_connectedComponentIn ⟨s, ztdxi, rfl⟩ hsub ztrel
    -- the touching point is in the open part, hence in `K`
    obtain ⟨z, ⟨hzc, hzD⟩, hzcl⟩ := htouch
    zvnme at hzc
    obtain ⟨s', hs'0, hs'1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzc
    have hs'0' : ztrzk := by
      rcases hs'0.lt_or_eq with h | h
      · zubh
      · subst h; rw [Chazelle.Geometry.lerp_zero] at hzD
        exact absurd hzD (hM.trace p hA'.1 t hA'.2.1 hA'.2.2.1.le)
    have hs'1' : s' < 1 := by
      rcases hs'1.lt_or_eq with h | h
      · zubh
      · subst h; rw [Chazelle.Geometry.lerp_one] at hzD
        grind
    have hzK := hopenK s' ⟨hs'0', hs'1'⟩
    obtain ⟨u, huK, hu⟩ := mem_closure_iff.1 hzcl K hKo hzK
    grind
  · -- a walk vertex inside an arc of `U`: positions just after it face `U`
    obtain ⟨ε, ⟨hε0, hε1⟩, hin1, hin2⟩ := ((ev_Ioo ztja).and
      ((eventually_in_arc hxin).and (eventually_in_arc hkab))).exists
    have hfac := harc.2.2.2.2.2.2 k ε hk hε0 hε1 hin2
    exact hM.region_subset_of_sector hc hU hk ⟨hε0, hε1⟩ hfac
      (hK k hk ε hε0.le hε1 hin1)
end
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideSectorIn ChordSystem freeIn
  regionsIn TouchesIn)
open Chazelle.Geometry (lerp lerp_mem_segment point_ext)
open Chazelle.Jordan (offset nrm)
variable {M : Model} {F : Set (Set Point)} {U : Set Point}

/-! ## Cyclic facts -/
theorem cyc_first {a b f : ℝ} (hab : a ≠ b) (haf : a ≠ f) (h1 : ¬ sideInArc a f b)
    (h2 : ¬ sideInArc a b f) : b = f := by
  by_contra hbf
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne haf
  have := lt_or_gt_of_ne hbf
  unfold sideInArc at *
  grind
theorem cyc_sub_in {a b a' b' x : ℝ} (ha : sideInArc a' b' a) (h1 : ¬ sideInArc a b a')
    (h2 : ¬ sideInArc a b b') (hx : sideInArc a b x) : sideInArc a' b' x := by
  unfold sideInArc at *
  grind

/-! ## Regions next to an attachment -/

/-- A region with an arc inside the side `(pa + ta, pb + tb)` of a chord `c` lies in the
component of that side. -/
theorem arc_in_side (hM : WalkAx M) (hne : F.Nonempty) {X : Set Point}
    (hX : X ∈ M.regions F) {u v : ℝ} (harc : M.IsArc F X u v) {c : Set Point} (hc : c ∈ F)
    {pa pb : ℕ} {ta tb : ℝ} (hsub : ∀ x, sideInArc u v x → sideInArc ztbf ztbd x)
    {k₁ : Point}
    (hK : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbf ztbd ztk →
      SideSectorIn M.W ztzvl p t) :
    X ⊆ connectedComponentIn ztjq k₁ := by
  obtain ⟨p, hp, t, ht, hin, -, hfac⟩ := WalkAx.exists_pos_in_arc hne harc
  exact hM.region_subset_of_sector hc hX hp ht hfac by_grind

/-- **Two distinct regions touching a chord lie in different components of the domain minus
the chord.** -/
theorem touch_sep (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) {c : Set Point}
    (hc : c ∈ F) {X Z : Set Point} (hX : X ∈ M.regions F) (hZ : Z ∈ M.regions F) (hXZ : X ≠ Z)
    (htX : TouchesIn M.D c X) (htZ : TouchesIn M.D c Z) {k : Point}
    (hXk : X ⊆ connectedComponentIn ztjq k) (hZk : Z ⊆ connectedComponentIn ztjq k) :
    False := by
  obtain ⟨Up, Dn, hUp, hDn, -, hside, htouch⟩ := chordSides_of_system ztbip hc
  have hUDk : Up ⊆ connectedComponentIn ztjq k ∧ Dn ⊆ connectedComponentIn ztjq k := by
    rcases (htouch X hX).1 htX with rfl | rfl <;> rcases (htouch Z hZ).1 htZ with rfl | rfl
    · simp_all
    · simp_all
    · simp_all
    simp_all
  obtain ⟨a, b, hab, hcab, hy, hopen, -, -⟩ := hM.ends c ztlz
  have hs := hM.hsep ztlz hcab hab hy hopen
  rw [← hcab] at hs
  set z := lerp a b ztcn with hz
  have hzc : z ∈ c := by zvmyh; exact lerp_mem_segment _ _ by_norm_num by_norm_num
  zukhj
  set d := b.1 - a.1 with hd
  have hd0 : ztpnz := by
    grind
  have hdpos := abs_pos.2 hd0
  obtain ⟨ε₀, hε₀, hs'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hs
  obtain ⟨ε₁, hε₁, hside'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ztlpv
  rw [mem_Ioi] at hε₀ hε₁
  set δ := min ε₀ (ε₁ / |d|) / 2 with hδ
  zukhr
  have hδ1 : δ < ε₀ := by have := min_le_left ε₀ (ε₁ / |d|); grind
  have hδ2 : δ * |d| < ε₁ := by
    have h1 : δ < ε₁ / |d| := by
      grind
    rwa [lt_div_iff₀ hdpos] at h1
  have hneq := hs' ⟨hδ0, hδ1⟩
  have e1 : offset a b ztcn δ = (z.1, z.2 + δ * d) := by
    apply point_ext <;> zunip
  have e2 : offset b a ztcn δ = (z.1, z.2 - δ * d) := by
    apply point_ext <;> zunip <;> ring
  have hmem : ∀ w, w ∈ Up ∨ w ∈ Dn →
      connectedComponentIn ztjq w = connectedComponentIn ztjq k := by
    rintro w (hw | hw)
    · exact (connectedComponentIn_eq (hUDk.1 hw)).symm
    · exact (connectedComponentIn_eq (hUDk.2 hw)).symm
  have hpt := hside' ⟨mul_pos hδ0 hdpos, hδ2⟩
  simp only [mem_ofPred_eq] at hpt
  apply hneq
  zuea
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · rw [abs_of_neg hneg] at hpt
    grind
  · rw [abs_of_pos hpos] at hpt
    grind

/-- The region with a given side relation to a chord (`AboveOf`) is the upper side region. -/
theorem eq_up_of_above (hM : WalkAx M) (hF : F ⊆ M.Adm) (_hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {Up Dn X : Set Point} (hUp : Up ∈ M.regions F)
    (hside : ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztcxe : Point) ∈ Up ∧
      (ztcxf : Point) ∈ Dn)
    (hX : X ∈ M.regions F) (hA : M.AboveOf c X) : X = Up := by
  zutb
  have hzc : ztxmn := by
    zubij
  zukhk
  obtain ⟨δ, h1, h2⟩ := ((hA _ hzc hzD).and ztrsc).exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hUp with h | h
  · zubh
  grind

/-- The region below a chord (`BelowOf`) is the lower side region. -/
theorem eq_dn_of_below (hM : WalkAx M) (hF : F ⊆ M.Adm) (_hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {Up Dn X : Set Point} (hDn : Dn ∈ M.regions F)
    (hside : ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztcxe : Point) ∈ Up ∧
      (ztcxf : Point) ∈ Dn)
    (hX : X ∈ M.regions F) (hB : M.BelowOf c X) : X = Dn := by
  zutb
  have hzc : ztxmn := by
    zubij
  zukhk
  obtain ⟨δ, h1, h2⟩ := ((hB _ hzc hzD).and ztrsc).exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hDn with h | h
  · zubh
  grind

/-- Keys just before a walk vertex `p`: the position `((p + n - 1) mod n, t')` for `t'` close to
`1` lies in every open interval `(l, p)`. -/
theorem eventually_before_vertex {n p : ℕ} (hp : p < n) {l : ℝ} (hl0 : 0 ≤ l)
    (hln : l < n) (hlp : l ≠ p) :
    ∀ᶠ t' in 𝓝[<] (1 : ℝ), sideInArc l p ((ztzp % n : ℕ) + t') := by
  zucym
  · zufsw
    zui
    have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by_simp_all
    filter_upwards [Ioo_mem_nhdsLT (show l - ztkl < (1 : ℝ) by linarith)] with t ht
    zuiq

  · have e : ztxfl := by
      zuxw
    zui
    have hp1 : zticy := by_simp_all
    zuowo
    zufdq
    zus
    · filter_upwards [Ioo_mem_nhdsLT (show l - ztoq < (1 : ℝ) by linarith),
        self_mem_nhdsWithin] with t ht ht1
      grind
    · filter_upwards [self_mem_nhdsWithin] with t ht
      grind

/-! ## The dichotomy -/

/-- **Consecutive host keys** `a ≠ b` of `U` (no host key strictly between them) are joined
inside an arc of `U` (A), or by one chord of `F` attached at `a` and at `b` (B). -/
theorem gap (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (hne : F.Nonempty)
    (hU : U ∈ M.regions F) {a b : ℝ} (ha : a ∈ hostKeys M F U) (hb : b ∈ hostKeys M F U)
    (hab : a ≠ b) (hgap : ∀ x ∈ hostKeys M F U, ¬ sideInArc a b x) :
    (∃ a' b' : ℝ, M.IsArc F U a' b' ∧ ∀ x, sideInArc a b x → sideInArc a' b' x) ∨
    (∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
      a = p + t ∧ b = p' + t' ∧ sidePt M.W p t ≠ sidePt M.W p' t') := by
  have hstart : ∀ {a' b' : ℝ}, M.IsArc F U a' b' → a' ∈ hostKeys M F U := fun harc => by
    zubow

  have hend : ∀ {a' b' : ℝ}, M.IsArc F U a' b' → b' ∈ hostKeys M F U := fun harc => by
    zubov

  by_cases hacut : M.IsCut F a
  swap
  · rcases ha with hx | ⟨k, hk, rfl, a', b', harc, hkin⟩
    · exact absurd ztqmp hacut
    · exact Or.inl ⟨a', b', harc, fun x hx =>
        cyc_sub_in hkin by_grind by_grind hx⟩
  obtain ⟨c₁, hc₁, p₀, t₀, hA₁, hak⟩ := hacut
  subst hak
  obtain ⟨X, Y, l, r, hX, hY, hXY, harcX, harcY, hsoleT⟩ := hM.attach_face hF hfin hc₁ hA₁
  by_cases hXU : X = U
  · zulsx
    exact Or.inl ⟨_, r, harcX, fun x hx =>
      cyc_sub_start hx by_grind (WalkAx.arc_cuts hne harcX).2.2.symm⟩
  right
  have haex : (p₀ : ℝ) + t₀ ∈ exitKeys M F U := by
    rcases ha with hx | ⟨k, hk, hkeq, a', b', harc, hkin⟩
    · zufsg
    · rw [← hkeq] at hkin
      exact absurd ⟨c₁, hc₁, p₀, t₀, hA₁, rfl⟩ (harc.2.2.2.2.2.1 _ hkin)
  obtain ⟨c₀, hc₀, ht₀, p₁, t₁, hA₀, ha₀⟩ := haex
  obtain ⟨rfl, rfl⟩ := key_inj hA₁.2.1 hA₁.2.2.1 hA₀.2.1 hA₀.2.2.1 ha₀
  have hUne := Chazelle.Chain.regionsIn_nonempty hU
  -- the finishing argument, for a suitable exit chord `c` at `a`
  have finish : ∀ c ∈ F, TouchesIn M.D c U → SideAttach M.W c p₀ t₀ →
      (∀ k₁ k₂ : Point, X ⊆ connectedComponentIn ztjq k₁ →
        Y ⊆ connectedComponentIn ztjq k₂ →
        connectedComponentIn ztjq k₁ ≠ connectedComponentIn ztjq k₂ →
        ¬ U ⊆ connectedComponentIn ztjq k₁) →
      ∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
        (p₀ : ℝ) + t₀ = p + t ∧ b = p' + t' ∧ sidePt M.W p t ≠ sidePt M.W p' t' := by
    intro c hc htc hA hoff
    zuejc
    have hAB : sidePt M.W p₀ t₀ ≠ sidePt M.W pb tb := by_grind
    zubji
    have hfa : (pb : ℝ) + tb ≠ p₀ + t₀ := fun h => WalkAx.key_ne_of_pt_ne hA hB hAB h.symm
    have hfcut : ztidq := ztcxs
    have hXs : X ⊆ connectedComponentIn _ k₁ :=
      arc_in_side hM hne hX harcX hc (fun x hx =>
        cyc_sub_start hx (fun h => harcX.2.2.2.2.2.1 _ h hfcut) hfa) hK₁
    have hYs : Y ⊆ connectedComponentIn _ k₂ :=
      arc_in_side hM hne hY harcY hc (fun x hx =>
        cyc_sub hx (fun h => harcY.2.2.2.2.2.1 _ h hfcut) hfa) hK₂
    have hnot := hoff k₁ k₂ hXs hYs hK12
    have hfh : ztknk := Or.inl ztioc
    have hnone : ∀ x ∈ hostKeys M F U, ¬ sideInArc _ _ x :=
      fun x hx hin => hnot (host_side hM hF hfin hU hc hA hB hAB hK₁ hx hin)
    have hbf := cyc_first hab ztvbe by_grind by_grind
    grind
  -- components met by a nonempty region are equal
  have hcomp : ∀ (c : Set Point) (k₁ k₂ : Point), U ⊆ connectedComponentIn ztjq k₁ →
      U ⊆ connectedComponentIn ztjq k₂ →
      connectedComponentIn ztjq k₁ = connectedComponentIn ztjq k₂ := by
    intro c k₁ k₂ h₁ h₂
    obtain ⟨u, hu⟩ := hUne
    rw [connectedComponentIn_eq (h₁ hu), connectedComponentIn_eq (h₂ hu)]
  by_cases hUY : U = Y
  · subst hUY
    exact finish c₀ hc₀ ht₀ hA₀ by_grind
  by_cases hsole : ∀ c' ∈ F, SideAttach M.W c' p₀ t₀ → c' = c₀
  · exfalso
    obtain rfl := hsole c₁ hc₁ hA₁
    obtain ⟨htX, htY⟩ := hsoleT hsole
    obtain ⟨Up, Dn, -, -, -, -, htouch⟩ := chordSides_of_system ztbip hc₁
    rcases (htouch X hX).1 htX with rfl | rfl <;> rcases (htouch Y hY).1 htY with rfl | rfl <;>
      rcases (htouch U hU).1 ht₀ with rfl | rfl <;> simp_all
  zumiu
  obtain ⟨c', hc', hA', hc'0⟩ := hsole
  -- the tie at the vertex `a`
  have tie : ∀ ce cw : Set Point, ce ∈ F → cw ∈ F → SideAttach M.W ce p₀ t₀ →
      SideAttach M.W cw p₀ t₀ → (∀ z ∈ ce, (sidePt M.W p₀ t₀).1 ≤ z.1) →
      (∀ z ∈ cw, z.1 ≤ (sidePt M.W p₀ t₀).1) → (c₀ = ce ∨ c₀ = cw) →
      ∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
        (p₀ : ℝ) + t₀ = p + t ∧ b = p' + t' ∧ sidePt M.W p t ≠ sidePt M.W p' t' := by
    intro ce cw hce hcw hAe hAw hE hW hc0
    zudix
    zudlw
    have hp₀ := hAe.1
    have hl0 := harcY.1
    have hln := harcY.2.1
    have hlp := (WalkAx.arc_cuts hne harcY).2.2
    -- the region faced just after `a` is `X`, just before is `Y`
    have hafter : ∀ Z ∈ M.regions F, (∃ δ > (0 : ℝ), ∀ t', 0 < t' → t' < δ → M.Faces p₀ t' Z) →
        Z = X := by
      zugte
      have hra := (WalkAx.arc_cuts hne harcX).2.2
      obtain ⟨ε, ⟨hε0, hε1⟩, hin⟩ := ((ev_Ioo (lt_min hδ one_pos)).and
        (WalkAx.eventually_after_start hra)).exists
      have hin' : sideInArc ztmzl r (p₀ + ε) := by_grind
      exact WalkAx.faces_unique hZ hX by_grind
        (harcX.2.2.2.2.2.2 p₀ ε hp₀ hε0 (lt_of_lt_of_le hε1 ztgh) hin')
    have hbefore : ∀ Z ∈ M.regions F, (∃ δ > (0 : ℝ), ∀ t', 1 - δ < t' → t' < 1 →
        M.Faces (ztkcp % M.W.n) t' Z) → Z = Y := by
      zugte
      have hlp' : l ≠ (p₀ : ℝ) := by_grind
      obtain ⟨t', ⟨ht'1, ht'2⟩, ht'3, hin⟩ := ((ev_Ioo_lt (show 1 - min δ 1 < (1 : ℝ) by
        linarith [lt_min hδ one_pos])).and ((ev_Ioo_lt (show (0 : ℝ) < 1 by norm_num)).and
        (eventually_before_vertex hp₀ hl0 hln hlp'))).exists
      have hq : ztkcp % M.W.n < M.W.n := Nat.mod_lt _ by_omega
      have hin' : sideInArc l ztmzl ((ztkcp % M.W.n : ℕ) + t') := by
        grind
      exact WalkAx.faces_unique hZ hY
        (hf t' (by linarith [min_le_left δ 1]) ht'2)
        (harcY.2.2.2.2.2.2 _ t' hq ht'3.1 ht'3.2 hin')
    obtain ⟨Upe, Dne, hUpe, hDne, hUDe, hsidee, htouche⟩ := chordSides_of_system ztbip hce
    obtain ⟨Upw, Dnw, hUpw, hDnw, hUDw, hsidew, htouchw⟩ := chordSides_of_system ztbip hcw
    zujei
    · obtain ⟨-, Ua, Vb, R, hUa, hVb, hR, hBe, hBw, hAe', hAw', hfa, hfb, -⟩ :=
        hM.tie_down hF hfin hce hcw hAe hAw hE hW hdown
      zuegr

      have e1 := eq_dn_of_below hM hF hfin hce hDne hsidee hUa hBe
      have e2 := eq_up_of_above hM hF hfin hce hUpe hsidee hR hAe'
      have e3 := eq_dn_of_below hM hF hfin hcw hDnw hsidew hVb hBw
      have e4 := eq_up_of_above hM hF hfin hcw hUpw hsidew hR hAw'
      subst hUaX hVbY
      have hUR : ztmtw := by
        zukla
        · zuflh
          · grind
          grind
        · zufli
          · grind
          grind
      have htU : TouchesIn M.D ce U := by_grind
      have htX : TouchesIn M.D ce Ua := by_grind
      exact finish ce hce htU hAe fun k₁ k₂ hXs _ _ hU₁ =>
        touch_sep hM hF hfin hce hUa hU hXU htX htU hXs hU₁
    · obtain ⟨-, Ua, Vb, R, hUa, hVb, hR, hAw', hAe', hBe, hBw, hfa, hfb, -⟩ :=
        hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
      zuegr

      have e1 := eq_up_of_above hM hF hfin hcw hUpw hsidew hUa hAw'
      have e2 := eq_dn_of_below hM hF hfin hcw hDnw hsidew hR hBw
      have e3 := eq_up_of_above hM hF hfin hce hUpe hsidee hVb hAe'
      have e4 := eq_dn_of_below hM hF hfin hce hDne hsidee hR hBe
      subst hUaX hVbY
      have hUR : ztmtw := by
        zukla
        · zuflh
          · grind
          grind
        · zufli
          · grind
          grind
      have htU : TouchesIn M.D cw U := by_grind
      have htX : TouchesIn M.D cw Ua := by_grind
      exact finish cw hcw htU hAw fun k₁ k₂ hXs _ _ hU₁ =>
        touch_sep hM hF hfin hcw hUa hU hXU htX htU hXs hU₁
  rcases hM.tie_pair hF hc₀ hc' (Ne.symm hc'0) hA₀ hA' with ⟨hE, hW⟩ | ⟨hW, hE⟩
  · exact tie c₀ c' hc₀ hc' hA₀ hA' hE hW ztp
  · exact tie c' c₀ hc' hc₀ hA' hA₀ hE hW ztbt
end
end DownHost
namespace Gran
open Machine Machine.Stmt Programs SignK
@[expose] public section
def hv : SymPt → ℕ
  | .vtx i => i
  | .onEdge _ h => h
theorem eval_snd (Q : Polygon) (sp : SymPt) : (sp.eval Q).2 = (Q.vtx (hv sp)).2 := by
  cases sp <;> rfl
theorem hv_lt {n : ℕ} {sp : SymPt} (h : sp.Lt n) : hv sp < n := by
  cases sp with
  | vtx i => exact h
  | onEdge e k => exact h.2

/-- **Interior model**: a position has a nonzero parameter iff its code names a vertex other than
the start of its walk edge. -/
theorem pz_int {Q : Polygon} (hQ : Q.Simple) (hdh : DistinctHeights Q) {e h : ℕ} (he : e < Q.n)
    (hh : h ≤ Q.n) :
    (interiorModel Q).param Q ztcq ≠ 0 ↔
      (h ≠ 0 ∧ h - 1 ≠ OutWalk.wv (OutWalk.revOf Q) Q.n e) := by
  cases h with
  | zero => zuoyk
  | succ k =>
    zufbu
    constructor
    · intro hne hk
      zufqo
      rw [OutNF.param_eq hQ hdh he k, OutNF.wa_eq he, ← hk, sub_self, zero_div]
    · zuibt
      exact OutNF.param_ne_zero hQ hdh he by_omega fun h' => hk h'.symm
variable (C : Chain)
/-- The walk vertices of a tour edge of the chain model. -/
theorem chain_wa_wb {i : ℕ} (hi : i < 2 * C.m) :
    (chainModel C).wa ztcy = C.vertex ztlx ∧
      (chainModel C).wb ztcy = C.vertex ztwlt := by
  zubzo
  rw [C.sideWalk_n, Nat.mod_eq_of_lt by_omega, show i + 6 + 1 = ztg + 6 by ring,
    C.sideWalk_vtx_tour _ by_omega, C.sideWalk_vtx_tour _ by_omega]
  tauto

/-- **Chain model, tour edge**: a position has a nonzero parameter iff its code is nonzero, the
edge is not horizontal and the code names another height than the start of the edge. -/
theorem pz_chain {Q : Polygon} (hdh : DistinctHeights Q) {i h : ℕ} (hi : i < 2 * C.m)
    (hh : h ≤ Q.n) {sp₁ sp₂ : SymPt} (h1 : C.vertex ztlx = sp₁.eval Q)
    (h2 : C.vertex ztwlt = sp₂.eval Q) (l1 : sp₁.Lt Q.n)
    (l2 : sp₂.Lt Q.n) :
    (chainModel C).param Q ⟨i + 6, h⟩ ≠ 0 ↔ (h ≠ 0 ∧ hv sp₁ ≠ hv sp₂ ∧ h - 1 ≠ hv sp₁) := by
  obtain ⟨ea, eb⟩ := chain_wa_wb C hi
  have ya : ((chainModel C).wa ztcy).2 = (Q.vtx (hv sp₁)).2 := by rw [ea, h1, eval_snd]
  have yb : ((chainModel C).wb ztcy).2 = (Q.vtx (hv sp₂)).2 := by rw [eb, h2, eval_snd]
  have a1 := hv_lt l1
  have a2 := hv_lt l2
  have hinj : ∀ a b, a < Q.n → b < Q.n → ((Q.vtx a).2 = (Q.vtx b).2 ↔ a = b) := fun a b ha hb =>
    ⟨fun e => by by_contra hne; exact hdh a b ha hb hne e, fun e => by zvmwe⟩
  cases h with
  | zero => zuoyk
  | succ k =>
    zufbu
    zulrt
    rw [ya, yb]
    by_cases hab : hv sp₁ = hv sp₂
    · simp_all
    · grind
open WalkKey NFLoc
open Chazelle.Chain (sideE)
def chPts : Stmt :=
  .seq chIdx (.seq cntStmt (.seq ztdca
    (.seq hostPt (.seq (block [.copyN 50040 50046, .copyN 50041 50047, .copyN 50042 50048,
        .copyN 50091 50079])
      (.seq hostPt ztccn)))))
theorem wr_chPts : wr Bdir chPts = true := by_decide
variable {P : Polygon} {W : ℕ} {a b : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
/-- **The two walk vertices of a tour edge.** -/
theorem chPts_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {H : Host} {Hh s m T b i : ℕ} (hH : HostAt c.nmem Hh H)
    (hwf : HostWF P.n H) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hNW : 2 * (H.pts P.n).length ≤ W) (hs : s < (H.pts P.n).length)
    (hmN : m < (H.pts P.n).length) (hT : T ≤ m) (hi : i < 2 * m)
    (h32 : c.nreg 50032 = 1) (h60 : c.nreg 50060 = Hh) (h52 : c.nreg 50052 = s)
    (h53 : c.nreg 50053 = m) (h54 : c.nreg 50054 = T) (h55 : c.nreg 50055 = b)
    (h56 : c.nreg 50056 = i) :
    ∃ c' k, Exec P W chPts c c' k ∧ k ≤ 70 * H.length + 500 ∧ FrameB Bdir c c' ∧
      ∃ sp₁ sp₂ : SymPt,
        ztbkj[ztyfo %
          (H.pts P.n).length]? = some sp₁ ∧
        ztbkj[ztxxx %
          (H.pts P.n).length]? = some sp₂ ∧
        SymPtIn c' 50040 sp₁ ∧ SymPtIn c' 50043 sp₂ ∧ sp₁.Lt P.n ∧ sp₂.Lt P.n := by
  zubsq

  obtain ⟨c₁, k₁, e₁, hk₁, k78, k79, f₁⟩ := chIdx_exec (P := P) c hw h32 h53 h54 h55 h56 hi hT
    by_omega
  zud
  zubju

  have g₁ := fun r (hr : Bl [50058, 50059, 50089, 50077, 50078, 50090, 50079] r = false) =>
    f₁.1 r hr
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, n63, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ w₁
    ztmdh ztmyz haW by_omega
  zubdn
  obtain ⟨c₃, k₃, e₃, hk₃, q87, q91, r₃⟩ : ∃ c₃ k₃, Exec P W
      ztdca c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 50087 = N ∧ c₃.nreg 50091 = sideE m j ∧
      ∀ r, r ≠ 50087 → r ≠ 50091 → c₃.nreg r = c₂.nreg r := by
    zuja
    exec_block
    refine ⟨rfl, by_simp_all, ?_, fun r h1 h2 => by_simp_all⟩
    config_simp; rw [g₂ _ by_decide, k78]
  have E₃ : ztrfn :=
    ⟨e₃.wb_right, by zunvp,
      by zunvq, by zunvr,
      by zunvs, by zunvt,
      by rw [(exec_frameB e₃ (B := Bl [50087, 50091]) by_decide).2.2.1, E₂.mem,
        f₁.2.2.1]⟩
  have s₃ : ztusd := by
    zudkk
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, E₄, sp₁, hsp₁, in₁⟩ := hostPt_exec (P := P) c₃ E₃ hH hwf
    by_omega haW hNW s₃ q87 q91 hs by_omega
  zudha
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, q91', r₅⟩ : ∃ c₅ k₅, Exec P W
      ztfxz
      c₄ c₅ k₅ ∧ k₅ = 4 ∧ SymPtIn c₅ 50040 sp₁ ∧ c₅.nreg 50091 = sideE m ztl ∧
      ∀ r, r ≠ 50040 → r ≠ 50041 → r ≠ 50042 → r ≠ 50091 → c₅.nreg r = c₄.nreg r := by
    zubwq
    exec_block
    refine ⟨rfl, symPtIn_copy in₁ (by config_simp) (by config_simp) (by config_simp), ?_,
      fun r h1 h2 h3 h4 => by zunaf⟩
    config_simp
    rw [g₄ _ by_decide, r₃ _ by_omega by_omega, g₂ _ by_decide, k79]
  have E₅ : ztrfo :=
    ⟨e₅.wb_right, by zunpd,
      by zunpe,
      by zunpf,
      by zunpg,
      by zunph,
      by rw [(exec_frameB e₅ (B := Bl [50040, 50041, 50042, 50091]) by_decide).2.2.1,
        E₄.mem]⟩
  have s₅ : ztutc := by
    zuedv
  have n₅ : ztutd := by
    zuedu
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, sp₂, hsp₂, in₂⟩ := hostPt_exec (P := P) c₅ E₅ hH hwf
    by_omega haW hNW s₅ n₅ q91' hs by_omega
  have a₆ : SymPtIn c₆ 50040 sp₁ := symPtIn_copy a₅ ztfrw ztfrw
    ztfrw
  obtain ⟨c₇, k₇, e₇, hk₇, a₇, b₇⟩ : ∃ c₇ k₇, Exec P W
      ztccn c₆ c₇ k₇ ∧ k₇ = 3 ∧
      SymPtIn c₇ 50040 sp₁ ∧ SymPtIn c₇ 50043 sp₂ := by
    zuizr
    exec_block
    exact ⟨rfl, symPtIn_copy a₆ (by config_simp) (by config_simp) (by config_simp),
      symPtIn_copy in₂ (by config_simp) (by config_simp) (by config_simp)⟩
  have l₁ : sp₁.Lt P.n := hLt _ ztnmn
  have l₂ : sp₂.Lt P.n := hLt _ ztnmo
  have ex : Exec P W chPts c c₇ _ := .seq e₁ ztfc
  exact ⟨c₇, _, ex, by_omega, exec_frameB ex wr_chPts, sp₁, sp₂, hsp₁, hsp₂, a₇, b₇, l₁, l₂⟩

/-! ## Height-vertex indices and bit tests -/

/-- `dst := hv` of the symbolic point at `r` (`r50032 = 1`). -/
def hvS (dst r : ℕ) : Stmt :=
  .ifLtN r 50032 (.instr (.copyN dst ztgu)) (.instr (.copyN dst ztbcu))
theorem hvS_exec (c : Config) (hw : WordsBounded W c) {dst r : ℕ}
    {sp : SymPt} (h32 : c.nreg 50032 = 1) (hsp : SymPtIn c r sp) :
    ∃ c' k, Exec P W (hvS dst r) c c' k ∧ k ≤ 3 ∧ c'.nreg dst = hv sp ∧
      ztedc ∧ c'.nmem = c.nmem := by
  unfold hvS
  cases sp with
  | vtx i =>
    obtain ⟨h0, h1⟩ := hsp
    exact ⟨_, _, .ifLtN_true by_omega ztbim, by_omega,
      by simp [upd, h1, hv], fun q hq => by_simp_all, rfl⟩
  | onEdge e k =>
    obtain ⟨h0, -, h2⟩ := hsp
    exact ⟨_, _, .ifLtN_false by_omega ztbim, by_omega,
      by simp [upd, h2, hv], fun q hq => by_simp_all, rfl⟩

/-- `s` if `r a ≠ r b`, else `t`. -/
def ifNe (a b : ℕ) (s t : Stmt) : Stmt := .ifLtN a b s (.ifLtN b a s t)
theorem ifNe_ne
    (h : c.nreg a ≠ c.nreg b) (e : Exec P W s c c' k) :
    ∃ k', Exec P W ztqrl c c' k' ∧ k' ≤ k + 3 := by
  zuhtf
  · tauto
  · exact ⟨_, .ifLtN_false hlt ztdrx, by_omega⟩
theorem ifNe_eq
    (h : c.nreg a = c.nreg b) (e : Exec P W t c c' k) :
    Exec P W ztqrl c c' ztqsd :=
  .ifLtN_false by_omega ztejp

/-- `r112 := 1` if `r111 ≠ 0`, `r ra ≠ r rb` and `r rc ≠ r rd` (else unchanged). -/
def tail3 (ra rb rc rd : ℕ) : Stmt :=
  .ifLtN 90111 90019 .skip (ifNe ra rb (ifNe rc rd ztzam .skip) .skip)
theorem tail3_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    (ra rb rc rd : ℕ) (h19 : c.nreg 90019 = 1) (h112 : c.nreg 90112 = 0) :
    ∃ c' k, Exec P W (tail3 ra rb rc rd) c c' k ∧ k ≤ 10 ∧
      c'.nreg 90112 ≤ 1 ∧
      (c'.nreg 90112 = 1 ↔ (c.nreg 90111 ≠ 0 ∧ c.nreg ra ≠ c.nreg rb ∧ c.nreg rc ≠ c.nreg rd)) ∧
      (∀ q, q ≠ 90112 → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem := by
  unfold tail3
  by_cases h0 : c.nreg 90111 = 0
  · exact ⟨c, _, .ifLtN_true by_omega ztjd, by_omega, by_omega,
      by omega, fun _ _ => rfl, rfl⟩
  have e0 : ¬ c.nreg 90111 < c.nreg 90019 := by_omega
  by_cases h1 : c.nreg ra = c.nreg rb
  · exact ⟨c, _, .ifLtN_false e0 (ifNe_eq h1 ztjd), by_omega, by_omega,
      by omega, fun _ _ => rfl, rfl⟩
  by_cases h2 : c.nreg rc = c.nreg rd
  · obtain ⟨k', e', hk'⟩ := ifNe_ne (s := ifNe rc rd ztzam .skip)
      (t := .skip) h1 (ifNe_eq (P := P) (W := W) (s := .instr ztgwp) h2 ztjd)
    exact ⟨c, _, .ifLtN_false e0 e', by_omega, by_omega, by_omega,
      fun _ _ => rfl, rfl⟩
  · obtain ⟨k₁, e₁, hk₁⟩ := ifNe_ne (s := .instr ztgwp) (t := .skip) h2
      (Exec.constN (P := P) hw 90112 1 hW)
    obtain ⟨k', e', hk'⟩ := ifNe_ne (s := ifNe rc rd ztzam .skip)
      (t := .skip) h1 e₁
    exact ⟨_, _, .ifLtN_false e0 e', by_omega, by_simp, by_simp_all,
      fun q hq => by_simp_all, rfl⟩

/-! ## The procedure -/

/-- The chain model (after `chHead`). -/
def pzChain : Stmt :=
  .ifLtN 50002 50081 ztouk
    (.seq ztbin
      (.ifLtN 50057 50053
        (.seq chPts (.seq (hvS 90113 50040) (.seq (hvS 90114 50043)
          (.seq ztjpg
            (tail3 90113 90114 90115 90113)))))
        ztouk))

/-- The interior model. -/
def pzInt : Stmt :=
  .seq intIdx (.seq ztjpg
    (tail3 90115 50041 90115 50041))

/-- **The bit `pz`** of the position `⟨r110, r111⟩` into `r112`. -/
def pzStmt : Stmt :=
  .seq (.instr (.copyN 50002 90110)) (.ifLtN 90023 90019 (.seq chHead pzChain) pzInt)

/-- The registers `pzStmt` writes. -/
def Bpz (r : ℕ) : Bool := Bdir r || decide (r = 50002) || decide (90110 ≤ r ∧ r < 90120)
theorem wr_pzStmt : wr Bpz pzStmt = true := by_decide

/-- The registers `chPts` writes. -/
def Bpts (r : ℕ) : Bool := decide (50040 ≤ r ∧ r < 50049) || decide (50056 ≤ r ∧ r < 50100)
theorem wr_chPts_fine : wr Bpts chPts = true := by_decide
theorem wr_intIdx : wr Bdir intIdx = true := by_decide
theorem pz_exec {P : Polygon} {W : ℕ} {M : Model} (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (c : Config) (hw : WordsBounded W c) {MD e h : ℕ} (h50 : c.nreg 50000 = MD)
    (hMD : ModelDescAt c.nmem MD zta M) (h23 : c.nreg 90023 = c.nmem MD)
    (h19 : c.nreg 90019 = 1) (h110 : c.nreg 90110 = e) (h111 : c.nreg 90111 = h)
    (he : e < M.W.n) (hh : h ≤ P.n) (hDW : MD + 6 ≤ W) (hCW : LocChainWF P W c.nmem MD) :
    ∃ c' k, Exec P W pzStmt c c' k ∧ k ≤ 6000 ∧ FrameB Bpz c c' ∧ c'.nreg 90112 ≤ 1 ∧
      ztxqt := by
  suffices hh' : ∃ c' k, Exec P W pzStmt c c' k ∧ k ≤ 6000 ∧ c'.nreg 90112 ≤ 1 ∧
      ztxqt by
    obtain ⟨c', k, ex, hk, h1, h2⟩ := hh'
    exact ⟨c', k, ex, hk, exec_frameB ex wr_pzStmt, h1, h2⟩
  zuc
  have hgs := goodShear_epsOf hG.2
  have hdh : ztxpn := hgs.2.1
  zudk
  -- copy the edge
  have e₀ := Exec.copyN (P := P) hw 50002 90110
  set c₀ : Config := { c with nreg := upd c.nreg 50002 (c.nreg 90110) } with hc₀
  have w₀ : ztsdd := e₀.wb_right
  have r₀ : ∀ r, r ≠ 50002 → c₀.nreg r = c.nreg r := fun r hr => by zunad; zumwy
  have x₀ : c₀.nreg 50002 = e := by zunad; simp [h110]
  have m₀ : ztsfv := rfl
  have d₀ : c₀.nreg 50000 = MD := by rw [r₀ _ by_omega, h50]
  rcases hMD with ⟨hk0, H, C, hC, rfl⟩ | ⟨hk1, hbit, rfl⟩
  · -- the chain model
    obtain ⟨hlen, hwf, hHW, hs, hNW⟩ := hCW hk0 H C hC
    zubhc
    have hNlen : ztehu := by
      zujif
      show ((H.pts (Qof P).n).map ztbafl).length = _
      zujgs
    zubnw
    zuwi
    have hen : ztpoj := by simpa [chainModel, C.sideWalk_n] using he
    have t0 : c₀.nreg 90023 < c₀.nreg 90019 := by
      rw [r₀ _ by_omega, r₀ _ by_omega, h23, h19, hk0]; omega
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W chHead c₀ c₁ k₁ ∧ k₁ = 16 ∧
        (c₁.nreg 50032 = 1 ∧ c₁.nreg 50060 = c.nmem ztki ∧ c₁.nreg 50052 = C.s ∧
          c₁.nreg 50053 = C.m ∧ c₁.nreg 50054 = C.topIdx ∧ c₁.nreg 50055 = c.nmem ztnmy ∧
          c₁.nreg 50081 = 6 ∧ c₁.nreg 50002 = e ∧ c₁.nreg 90111 = h ∧ c₁.nreg 90019 = 1 ∧
          c₁.nmem = c.nmem) := by
      unfold chHead
      exec_block
      all_goals try omega
      all_goals try (config_simp; zuofe; omega)
      zubee
      config_simp
      zuofe
      refine ⟨rfl, hs', hm', hT', rfl, x₀, ?_, ?_, m₀⟩
      · rw [r₀ _ by_omega, h111]
      · rw [r₀ _ by_omega, h19]
    obtain ⟨q32, q60, q52, q53, q54, q55, q81, q02, q111, q19, qm⟩ := q
    zud
    zubta
    · refine ⟨_, _, .seq e₀ (.ifLtN_true t0 (.seq e₁ (.ifLtN_true ztkuf
        (Exec.constN w₁ 90112 0 by_omega)))), by_omega, by simp [upd], ?_⟩
      zugzt

      · zujaz
      · rintro ⟨⟨h6, -⟩, -⟩; omega
    obtain ⟨c₂, k₂, e₂, hk₂, q56, q57, r₂⟩ : ∃ c₂ k₂, Exec P W
        ztbin c₁ c₂ k₂ ∧ k₂ = 2 ∧
        c₂.nreg 50056 = e - 6 ∧ c₂.nreg 50057 = e - 6 - C.m ∧
        ∀ r, r ≠ 50056 → r ≠ 50057 → c₂.nreg r = c₁.nreg r := by
      exec_block
      refine ⟨rfl, by config_simp; zuolb, by config_simp; rw [q02, q81, q53],
        fun r h1 h2 => by zungi⟩
    zue
    have p53 : ztpnh := by rw [r₂ _ by_omega by_omega, q53]
    have ns : ¬ c₁.nreg 50002 < c₁.nreg 50081 := by zuolb; exact hsm
    zucus
    · zufuu
      zubfs
      have hH₂ : HostAt c₂.nmem (c.nmem ztki) H := by zungj; exact hHost
      obtain ⟨c₃, k₃, e₃, hk₃, -, sp₁, sp₂, hsp₁, hsp₂, a₃, b₃, l₁, l₂⟩ := chPts_exec (P := P) hG
        hW c₂ w₂ hH₂ hwf hHW (by zunuq; exact hNW) ztljg
        (by zunuq; exact hmN) hT hi (by rw [r₂ _ by_omega by_omega, q32])
        (by rw [r₂ _ by_omega by_omega, q60]) (by rw [r₂ _ by_omega by_omega, q52]) p53
        ztkup ztkuq q56
      have F₃ := exec_frameB e₃ wr_chPts_fine
      have g₃ : ∀ r, Bpts r = false → c₃.nreg r = c₂.nreg r := F₃.1
      have c32 : ztusc := by
        rw [g₃ _ by_decide, r₂ _ by_omega by_omega, q32]
      obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄, m₄⟩ := hvS_exec (P := P) (dst := 90113) c₃ e₃.wb_right
        c32 a₃
      obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅, m₅⟩ := hvS_exec (P := P) (dst := 90114) c₄ e₄.wb_right
        (by rw [r₄ _ by_omega, c32])
        (symPtIn_copy b₃ ztohd ztohd ztohd)
      have h111₅ : c₅.nreg 90111 = h := by
        rw [r₅ _ by_omega, r₄ _ by_omega, g₃ _ by_decide, r₂ _ by_omega by_omega,
          q111]
      have h19₅ : c₅.nreg 90019 = 1 := by
        rw [r₅ _ by_omega, r₄ _ by_omega, g₃ _ by_decide, r₂ _ by_omega by_omega,
          q19]
      obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W (block [.constN 90112 0,
          .subN 90115 90111 90019]) c₅ c₆ k₆ ∧ k₆ = 2 ∧ (c₆.nreg 90112 = 0 ∧
          c₆.nreg 90115 = h - 1 ∧ c₆.nreg 90111 = h ∧ c₆.nreg 90113 = hv sp₁ ∧
          c₆.nreg 90114 = hv sp₂ ∧ c₆.nreg 90019 = 1) := by
        zudpp
        exec_block
        · omega
        · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
          · rw [h111₅, h19₅]
          · exact h111₅
          · rw [r₅ _ by_omega, v₄]
          · exact v₅
          · exact h19₅
      obtain ⟨q112, q115, q111', q113, q114, q19'⟩ := q
      obtain ⟨c₇, k₇, e₇, hk₇, b₇, i₇, -, -⟩ := tail3_exec (P := P) c₆ e₆.wb_right hW1
        90113 90114 90115 90113 q19' q112
      refine ⟨c₇, _, .seq e₀ (.ifLtN_true t0 (.seq e₁ (.ifLtN_false ns (.seq e₂
        (.ifLtN_true ztfbp
          ztyoi))))), ?_, b₇, ?_⟩
      · have : H.length ≤ 64 := hlen
        omega
      rw [i₇, q111', q113, q114, q115]
      -- the mathematics
      have hS : (if c.nmem ztnmy = 1 then C.topIdx else 2 * C.m - C.topIdx) =
          C.sideS C.sideBeta := by
        zueeu

        · zuikz
        · rw [ite_eq_right (mt hb'.1 hb), ite_eq_right hb]
      obtain ⟨i1, i2⟩ := sideIdx_pair C ztbcs
      zupw

      have v1 := chain_vertex_host C hP _ (by zvmxg; exact hsp₁)
      have v2 := chain_vertex_host C hP _ (by zvmxg; exact hsp₂)
      have key := pz_chain C hdh hi (h := h) ztgfs v1 v2
        (by zvmxg; exact l₁) (by zvmxg; exact l₂)
      rw [show e - 6 + 6 = e by omega] at key
      zueyw
      simp only [chainModel]
      constructor
      · intro h'; exact ⟨⟨by_omega, by_omega⟩, h'⟩
      · intro h'; exact h'.2
    · zufvg
      refine ⟨_, _, .seq e₀ (.ifLtN_true t0 (.seq e₁ (.ifLtN_false ns (.seq e₂
        (.ifLtN_false ztfbp (Exec.constN w₂ 90112 0 by_omega)))))),
        by omega, by simp [upd], ?_⟩
      zugzt

      · zujaz
      · rintro ⟨⟨-, h6⟩, -⟩; omega
  · -- the interior model
    zucm
    have hen : ztmvo := by
      have := interiorWalk_n zta
      zujom
      rw [this, hQn] at he
      zulyv
    have t0 : ¬ c₀.nreg 90023 < c₀.nreg 90019 := by
      rw [r₀ _ by_omega, r₀ _ by_omega, h23, h19, hk1]; omega
    obtain ⟨c₁, k₁, e₁, hk₁, i41, -⟩ := intIdx_exec (P := P) hW c₀ w₀ (by rw [x₀]; exact hen)
      (by zuofe; omega)
    have F₁ := exec_frameB e₁ wr_intIdx
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (block [.constN 90112 0,
        .subN 90115 90111 90019]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ (c₂.nreg 90112 = 0 ∧
        c₂.nreg 90115 = h - 1 ∧ c₂.nreg 90111 = h ∧ c₂.nreg 50041 = c₁.nreg 50041 ∧
        c₂.nreg 90019 = 1) := by
      zuka
      have a : c₁.nreg 90111 = h := by
        rw [F₁.1 _ by_decide, r₀ _ by_omega, h111]
      have b : ztgas := by rw [F₁.1 _ by_decide, r₀ _ by_omega, h19]
      exec_block
      · omega
      · refine ztbob <;> config_simp
        · rw [a, b]
        · exact a
        · exact b
    obtain ⟨q112, q115, q111', q41, q19'⟩ := q
    obtain ⟨c₃, k₃, e₃, hk₃, b₃, i₃, -, -⟩ := tail3_exec (P := P) c₂ e₂.wb_right hW1
      90115 50041 90115 50041 q19' q112
    refine ⟨c₃, _, .seq e₀ (.ifLtN_false t0 ztwrj), by_omega, b₃, ?_⟩
    rw [i₃, q111', q115, q41, i41, x₀, d₀, m₀]
    have key := pz_int hQ hdh (e := e) (h := h) (by zvmxg; exact hen) ztgfs
    have hwv : OutWalk.wv (OutWalk.revOf zta) (Qof P).n e =
        (if c.nmem ztki = 1 then e else P.n - 1 - e) := by
      unfold OutWalk.wv OutWalk.revOf
      zujih
      by_cases hl : Mountain.LeftInside zta
      · rw [ite_eq_left (hbit.2 hl)]; zuoff
      · rw [ite_eq_right (fun h' => hl (hbit.1 h'))]; zuoff
    rw [hwv] at key
    zueyw
    simp only [interiorModel, true_and, and_self]
open SearchR
def posStmt : Stmt := .seq locDir (.seq locSetup (searchStmt keyCmp))

/-- The partition point is one past the position of the key. -/
theorem pos_pick {M : Model} {Q : Polygon} {N : NF} (hNF : IsNF M Q N) (hne : (N.F M Q).Nonempty)
    (hGM : GoodModel M) {x : WPos} (hx1 : x.hgt ≠ 0) (hcut : M.IsCut ztdu ztbys)
    {t : ℕ} (ht : t ≤ N.arcs.length)
    (hpre : ∀ i, i < t → KeyPred M Q x (N.arc ztdfs).s)
    (hpost : t < N.arcs.length → ¬ KeyPred M Q x (N.arc ztnnf).s) :
    0 < t ∧ t - 1 < N.arcs.length ∧ pk M Q N ztso = M.key Q x := by
  obtain ⟨j, hj, hjk⟩ := cut_pk hNF hGM hcut
  have kp : ∀ i, KeyPred M Q x (N.arc ztdfs).s ↔ pk M Q N i ≤ M.key Q x := by
    intro i; unfold KeyPred pk; simp_all
  have htj : t = j + 1 := by
    zubvm

    · -- `t ≤ j`
      have := hpost by_omega
      rw [kp] at this
      zulvx
      rw [← hjk]
      rcases Nat.lt_or_eq_of_le (show t ≤ j by omega) with h' | h'
      · exact (pk_strict hNF hne h' hj).le
      simp_all
    · have := (kp _).1 (hpre ztl h)
      rw [← hjk] at this
      exact absurd this (not_le.2 (pk_strict hNF hne ztffs by_omega))
  simp_all
theorem pos_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hD : LocDPre P W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    {M : Model} {N : NF} (hM : ModelDescAt c.nmem zthut zta M) (hGM : GoodModel M)
    (hN : NFAt c.nmem ztvii N) (hNF : IsNF M zta N) (hne : (N.F M zta).Nonempty)
    (hx : ProperPos M zta P.n ztbig) (hx1 : c.nreg 50003 ≠ 0)
    (hcut : M.IsCut ztwiv ztxvk)
    (hst : ∀ j, j < N.arcs.length → ProperPos M zta P.n (N.arc j).s)
    (hB : c.nreg 50001 + 7 ≤ c.nreg ALLOC)
    (hAB : c.nmem ztrme + 5 * N.arcs.length ≤ c.nreg ALLOC)
    (hSB : c.nmem ztrmf + N.arcs.length ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + locCost 5100 N.arcs.length ≤ W) :
    ∃ c' k, Exec P W posStmt c c' k ∧ k ≤ locCost 5100 N.arcs.length ∧
      Frame {bLocate, bSign} c c' k ∧ 0 < c'.nreg 50105 ∧ c'.nreg 50105 - 1 < N.arcs.length ∧
      pk M zta N (c'.nreg 50105 - 1) = M.key zta ztbig := by
  zubce

  zuce
  zudyc

  have hseq : ztguz := fun i hi =>
    hN.2.2.2.2.2.2.2.2.1 i by_omega
  have hA0 : ztrzd := by
    obtain ⟨j, hj, -⟩ := cut_pk hNF hGM hcut
    omega
  have hL : 1 ≤ Nat.clog 2 A + 1 := by_omega
  have hcostW : c.nreg ALLOC + (5100 + 20 + searchCost 275 A) ≤ W := by
    have : ztkzr := by
      zumtk

    omega
  -- 1. the direction
  zubrh

  zud
  zucal

  have al₁ : ztpmy := f₁.1 _ by_decide
  zudqa
  -- 2. the setup
  obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W locSetup c₁ c₂ k₂ ∧ k₂ = 14 ∧
      (c₂.nreg 10500 = c.nreg 50002 ∧ c₂.nreg 10501 = c.nreg 50003 ∧
        c₂.nreg 10502 = c₁.nreg 10502 ∧ c₂.nreg 10503 = AB ∧ c₂.nreg 10504 = A ∧
        c₂.nreg 10505 = SB ∧ c₂.nreg 50103 = SB ∧ c₂.nreg 50104 = A) := by
    unfold locSetup
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · zubee
      config_simp
      grind
  zucsz
  zue
  zujxq
  have al₂ : ztlyc := (f₂.1 _ by_decide).trans al₁
  zucxa
  -- 3. the search
  zuioe
  have hJ₂ : CmpJ x d AB A SB A₀ c.nmem c₂ :=
    ⟨q500, q501, by_omega, q503, q504, q505, fun a _ => by zunbg⟩
  have hcmp := keyCmp_predOK hG hW x hx.2.2 d AB A SB A₀ c.nmem hAB by_omega
  have hpr : ∀ i, i < A → (cmpPr P x d AB A c.nmem ztbagf = true ↔
      KeyPred M zta x (N.arc ztdfs).s) := fun i hi => by
    zueyi

  obtain ⟨c₃, k₃, e₃, hk₃, hJ₃, hF₃, ht₃, hpre₃, hpost₃⟩ := searchStmt_exec hcmp
    by_decide w₂ hJ₂ (by rw [al₂]; exact cmpJ_stable x d AB A SB A₀ c.nmem)
    by_omega
    (fun i j hij hj hprj => by
      zueds

      exact (hpr i by_omega).2 ztgqo)
    by_grind
  rw [q104] at ht₃ hk₃ hpost₃
  zuhng
  zujnc
  obtain ⟨tpos, tlt, tpk⟩ := pos_pick hNF hne hGM (x := x) hx1 hcut ht₃
    zthgz
    (fun hi hk => by
      grind)
  have F₁ := frame_of_frameB f₁ Bdir_band k₁
  have F₂ := frame_of_frameB f₂ Bloc_band k₂
  refine ⟨_, k₁ + zttl, .seq e₁ ztcr, ?_,
    (F₁.trans (F₂.trans hF₃)).mono by_simp le_rfl, tpos, tlt, tpk⟩
  have : ztkzr := by
    zumtk

  omega
open Set
open Chazelle.Chain (SideAttach)
variable {M : Model} {Q : Polygon} {N : NF}
theorem ncard_F (hN : IsNF M Q N) : (N.F M Q).ncard = N.nChords := by
  have e : N.F M Q = zteaa '' {i | i < N.nChords} := by
    zubcj
    zumoq
    grind
  have hinj : Set.InjOn zteaa {i | i < N.nChords} :=
    fun i hi i' hi' h => cs_inj hN hi hi' h
  rw [e, hinj.ncard_image, show {i | i < N.nChords} = ((Finset.range N.nChords : Finset ℕ) :
    Set ℕ) by ext; simp, Set.ncard_coe_finset, Finset.card_range]

/-- **A valid normal form has `K + 1` regions.** -/
theorem nRegions_eq (hN : IsNF M Q N) (hM : WalkAx M) : N.nRegions = N.nChords + 1 := by
  obtain ⟨-, -, -, reg, hRC, -⟩ := id hN
  have hsys := hM.sys _ ztuyg (F_finite hN)
  have hcard := hsys.ncard_regionsIn hM.preconn hM.nonempty ztibe
  rw [ncard_F hN] at hcard
  have e : M.regions ztdu = reg '' {r | r < N.nRegions} := by
    zulge
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · zulmt
      zufko
      grind
    · zuewj
  have hinj : Set.InjOn reg {r | r < N.nRegions} := fun r hr r' hr' h => hRC.2.1 r r' hr hr' h
  have : ztyxv := by
    rw [e, hinj.ncard_image, show {r | r < N.nRegions} = ((Finset.range N.nRegions : Finset ℕ) :
      Set ℕ) by ext; simp, Set.ncard_coe_finset, Finset.card_range]
  unfold Model.regions at this
  omega

/-- **At most two arcs per chord.** -/
theorem arcs_le (hN : IsNF M Q N) (hM : WalkAx M) (hne : (N.F M Q).Nonempty) :
    N.arcs.length ≤ 2 * N.nChords := by
  classical
  zugyb
  set K := N.nChords
  have hsub : (Finset.range A).image ztruj ⊆
      (Finset.range K).image ztkwb ∪
        (Finset.range K).image ztkwc := by
    zugf
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    have hcut := pk_cut hN hne ztpyw
    rw [← fam_univ, isCut_fam_iff hN hM] at hcut
    grind
  have h1 : ((Finset.range A).image ztruj).card = A := by
    rw [Finset.card_image_of_injOn fun j hj j' hj' h =>
      pk_inj hN hne ztpyw (Finset.mem_range.1 hj') h, Finset.card_range]
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_union_le ((Finset.range K).image ztkwb)
    ((Finset.range K).image ztkwc)
  have h4 := Finset.card_image_le (s := Finset.range K) (f := fun i => M.key Q (N.chord i).lpos)
  have h5 := Finset.card_image_le (s := Finset.range K) (f := fun i => M.key Q (N.chord i).rpos)
  rw [Finset.card_range] at h4 h5
  omega

/-- The regions of a normal form with degrees `≤ D` have at most `D` exit chords. -/
theorem chords_le {reg : ℕ → Set Point} (hN : IsNF M Q N) (hRC : RegionCorr M Q N reg)
    (hRO : RegionsOK M Q N reg) {D : ℕ} (hD : M.DegLe ztdu D) {r : ℕ}
    (hr : r < N.nRegions) : (N.region r).chords.length ≤ D := by
  rw [← deg_region hN hRC hRO hr]
  exact hD _ ztdhm

/-- The left end of a chord record is a position of the walk proper. -/
theorem lpos_proper (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    ProperPos M Q Q.n (N.chord i).lpos := by
  obtain ⟨-, h0, h1, -⟩ := attach_l hN hi
  zubon
theorem rpos_proper (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    ProperPos M Q Q.n (N.chord i).rpos := by
  obtain ⟨-, h0, h1, -⟩ := attach_r hN hi
  zubon

/-- The ends of a chord record are cut keys. -/
theorem lkey_cut (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    M.IsCut ztdu (M.key Q (N.chord i).lpos) :=
  ⟨cs M Q N i, cs_mem hi, _, _, attach_l hN hi, rfl⟩
theorem rkey_cut (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    M.IsCut ztdu (M.key Q (N.chord i).rpos) :=
  ⟨cs M Q N i, cs_mem hi, _, _, attach_r hN hi, rfl⟩

/-- The start of a listed arc lies on a walk edge. -/
theorem edge_lt' (hN : IsNF M Q N) (hne : (N.F M Q).Nonempty) {j : ℕ} (hj : j < N.arcs.length) :
    (N.arc ztnnd).s.edge < M.W.n := by
  have hcut := pk_cut hN hne hj
  obtain ⟨c, -, p, t, hA, hk⟩ := hcut
  obtain ⟨hp, ht0, ht1, -⟩ := hA
  zubrg
  obtain ⟨hs0, hs1, -⟩ := (hpp _ (NFLoc.seq_lt hN hj)).1
  unfold pk Model.key at hk
  have hfl : ((N.arc ztnnd).s.edge : ℝ) < p + 1 := by_linarith
  have : (N.arc ztnnd).s.edge < p + 1 := by exact_mod_cast hfl
  omega
def hdrBlock : Stmt := block [.constN 90019 1, .constN 90020 3, .constN 90021 2,
  .copyN 90014 90003, .loadN 90010 90001, .addN 90060 90001 90019, .loadN 90011 90060,
  .addN 90060 90060 90019, .loadN 90012 90060, .addN 90060 90060 90019, .loadN 90013 90060,
  .addN 90060 90060 90019, .loadN 90015 90060, .addN 90060 90060 90019, .loadN 90016 90060,
  .addN 90060 90060 90019, .loadN 90017 90060, .addN 90060 90060 90019, .loadN 90022 90060,
  .loadN 90023 90000, .addN 90060 90000 90020, .loadN 90024 90060, .copyN 50000 90000,
  .copyN 50001 90001]

/-- The number of counted edges: `2 m` (chain) or `n` (interior). -/
def szStmt : Stmt := .ifLtN 90023 90019 (.instr (.addN 90018 90024 90024)) (.instr (.inputSize 90018))

/-- The header. -/
def hdrStmt : Stmt := .seq hdrBlock szStmt

/-- The registers of the header. -/
def Bhdr (r : ℕ) : Bool := decide (90010 ≤ r ∧ r < 90025) || decide (r = 90060) ||
  decide (r = 50000) || decide (r = 50001)
theorem wr_hdrStmt : wr Bhdr hdrStmt = true := by_decide

/-- The number of counted edges computed by `szStmt`. -/
def szOf (P : Polygon) (kind m : ℕ) : ℕ := if kind = 0 then 2 * m else P.n
variable {P : Polygon} {W : ℕ}
theorem hdr_exec (c : Config) (hw : WordsBounded W c) {MD B : ℕ}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = B) (hB : B + 7 ≤ W) (hMD : MD + 3 ≤ W)
    (hn : P.n ≤ W) (hm : c.nmem MD = 0 → 2 * c.nmem ztua ≤ W) :
    ∃ c' k, Exec P W hdrStmt c c' k ∧ k ≤ 30 ∧
      c'.nreg 90010 = c.nmem B ∧ c'.nreg 90011 = c.nmem ztvf ∧
      c'.nreg 90012 = c.nmem zthb ∧ c'.nreg 90013 = c.nmem ztkh ∧
      c'.nreg 90015 = c.nmem ztow ∧ c'.nreg 90016 = c.nmem zter ∧
      c'.nreg 90017 = c.nmem ztcsw ∧ c'.nreg 90022 = c.nmem ztlw ∧
      c'.nreg 90023 = c.nmem MD ∧ c'.nreg 90024 = c.nmem ztua ∧
      c'.nreg 90018 = szOf P zteqv ztyih ∧
      c'.nreg 90014 = c.nreg 90003 ∧ c'.nreg 90019 = 1 ∧ c'.nreg 90020 = 3 ∧
      c'.nreg 90021 = 2 ∧ c'.nreg 50000 = MD ∧ c'.nreg 50001 = B ∧ FrameB Bhdr c c' := by
  suffices hh : ∃ c' k, Exec P W hdrStmt c c' k ∧ k ≤ 30 ∧
      c'.nreg 90010 = c.nmem B ∧ c'.nreg 90011 = c.nmem _ ∧
      c'.nreg 90012 = c.nmem _ ∧ c'.nreg 90013 = c.nmem _ ∧
      c'.nreg 90015 = c.nmem _ ∧ c'.nreg 90016 = c.nmem _ ∧
      c'.nreg 90017 = c.nmem _ ∧ c'.nreg 90022 = c.nmem _ ∧
      c'.nreg 90023 = c.nmem MD ∧ c'.nreg 90024 = c.nmem _ ∧
      c'.nreg 90018 = szOf P _ _ ∧
      c'.nreg 90014 = c.nreg 90003 ∧ c'.nreg 90019 = 1 ∧ c'.nreg 90020 = 3 ∧
      c'.nreg 90021 = 2 ∧ c'.nreg 50000 = MD ∧ c'.nreg 50001 = B by
    obtain ⟨c', k, e, hk, q⟩ := hh
    exact ⟨c', k, e, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
      q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      exec_frameB e wr_hdrStmt⟩
  zukaq
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W hdrBlock c c₁ k₁ ∧ k₁ = 24 ∧
      (c₁.nreg 90010 = c.nmem B ∧ c₁.nreg 90011 = c.nmem ztvf ∧
      c₁.nreg 90012 = c.nmem zthb ∧ c₁.nreg 90013 = c.nmem ztkh ∧
      c₁.nreg 90015 = c.nmem ztow ∧ c₁.nreg 90016 = c.nmem zter ∧
      c₁.nreg 90017 = c.nmem ztcsw ∧ c₁.nreg 90022 = c.nmem ztlw ∧
      c₁.nreg 90023 = c.nmem MD ∧ c₁.nreg 90024 = c.nmem ztua ∧
      c₁.nreg 90014 = c.nreg 90003 ∧ c₁.nreg 90019 = 1 ∧ c₁.nreg 90020 = 3 ∧
      c₁.nreg 90021 = 2 ∧ c₁.nreg 50000 = MD ∧ c₁.nreg 50001 = B ∧ c₁.nmem = c.nmem) := by
    unfold hdrBlock
    exec_block
    all_goals try omega
    all_goals try (config_simp; zvmwp; omega)
    all_goals try (config_simp; zvmzn; omega)
    zubee
    config_simp
    grind
  obtain ⟨q10, q11, q12, q13, q15, q16, q17, q22, q23, q24, q14, q19, q20, q21, q50, q51,
    qm⟩ := q
  zud
  by_cases hk : c.nmem MD = 0
  · have t : c₁.nreg 90023 < c₁.nreg 90019 := by_omega
    have e₂ := Exec.addN (P := P) w₁ 90018 90024 90024 by_omega
    refine ⟨_, _, .seq e₁ ztspo, by_omega, ?_⟩
    config_simp
    refine ztdbi
    rw [q24]; unfold szOf; grind
  · have t : ¬ c₁.nreg 90023 < c₁.nreg 90019 := by_omega
    have e₂ := Exec.inputSize w₁ 90018 hn
    refine ⟨_, _, .seq e₁ ztnaf, by_omega, ?_⟩
    config_simp
    refine ztdbi
    unfold szOf; simp_all

/-! ## Products -/

/-- `dst := r a * r b` (counter `cnt`). -/
def mulS (dst a b cnt : ℕ) : Stmt :=
  .seq (block [.constN dst 0, .constN cnt 0])
    (.whileLtN cnt a (block [.addN dst dst b, .addN cnt cnt 90019]))
theorem mul_exec (c : Config) (hw : WordsBounded W c) {dst a b cnt : ℕ}
    (h1 : dst ≠ cnt) (h2 : dst ≠ a) (h3 : dst ≠ b) (h4 : cnt ≠ a) (h5 : cnt ≠ b)
    (h6 : dst ≠ 90019) (h7 : cnt ≠ 90019) (h19 : c.nreg 90019 = 1)
    (hW : c.nreg a * c.nreg b ≤ W) (ha : c.nreg a ≤ W) :
    ∃ c' k, Exec P W ztqtr c c' k ∧ k ≤ 4 * c.nreg a + 4 ∧
      c'.nreg dst = c.nreg a * c.nreg b ∧
      (∀ r, r ≠ dst → r ≠ cnt → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      FrameB (fun r => decide ztogo || decide zttxy) c c' := by
  suffices hh : ∃ c' k, Exec P W ztqtr c c' k ∧ k ≤ 4 * c.nreg a + 4 ∧
      c'.nreg dst = c.nreg a * c.nreg b by
    obtain ⟨c', k, e, hk, hd⟩ := hh
    have F := exec_frameB e (B := fun r => decide ztogo || decide zttxy)
      (by simp [mulS, wr, block, wrOK])
    exact ⟨c', k, e, hk, hd, fun r a1 a2 => F.1 r by_simp_all, F.2.2.1, F⟩
  have hW0 : 0 ≤ W := Nat.zero_le _
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN dst 0, .constN cnt 0]) c c₁ k₁ ∧
      k₁ = 2 ∧ (c₁.nreg dst = 0 ∧ c₁.nreg cnt = 0 ∧
        ∀ r, r ≠ dst → r ≠ cnt → c₁.nreg r = c.nreg r) := by
    refine spec_step (Exec.constN hw dst 0 hW0) fun hw₁ => ?_
    refine spec_step (Exec.constN hw₁ cnt 0 hW0) fun hw₂ => ?_
    refine spec_nil hw₂ by_simp_all
  obtain ⟨q1, q2, qr⟩ := q
  obtain ⟨c', k, e, ⟨hw', hc', hd', hr'⟩, hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := cnt)
    (b := a) (body := block [.addN dst dst b, .addN cnt cnt 90019])
    (fun d => WordsBounded W d ∧ d.nreg cnt ≤ c.nreg a ∧ d.nreg dst = d.nreg cnt * c.nreg b ∧
      ∀ r, r ≠ dst → r ≠ cnt → d.nreg r = c.nreg r)
    (fun d => c.nreg a - d.nreg cnt) 2 ztsa
    (fun d ⟨hwd, hle, hdd, hrd⟩ ht => by
      rw [hrd a ztvam ztvan] at ht
      have hb : d.nreg b = c.nreg b := by_grind
      have h19' : ztutm := by_grind
      have hmul : (d.nreg cnt + 1) * c.nreg b ≤ c.nreg a * c.nreg b :=
        Nat.mul_le_mul_right _ by_omega
      have hsum : d.nreg dst + d.nreg b ≤ W := by
        grind
      refine spec_step (Exec.addN hwd dst dst b hsum) fun hw₁ => ?_
      refine spec_step (Exec.addN hw₁ cnt cnt 90019 (by
        simp [upd, h1.symm, show (90019 : ℕ) ≠ dst from Ne.symm h6]; omega))
        fun hw₂ => ?_
      refine spec_nil hw₂ ⟨⟨hw₂, ?_, ?_, fun r a1 a2 => ?_⟩, by_omega, ?_⟩
      · zundh; omega
      · simp [upd, h1, h1.symm, show (90019 : ℕ) ≠ dst from Ne.symm h6, h19', hdd, hb]; ring
      · simp_all
      · zundh; omega)
    ⟨e₁.wb_right, by_omega, by_simp_all, qr⟩
  rw [hr' a ztvam ztvan] at hx
  have hfull : c'.nreg cnt = c.nreg a := by_omega
  refine ⟨c', _, .seq e₁ e, ?_, by_simp_all⟩
  omega

/-! ## The layout -/

/-- The products, the bases and the allocation. -/
def baseBlock : Stmt := block [.copyN 90030 9999, .addN 90031 90030 90010,
  .addN 90032 90031 90010, .addN 90033 90032 90010, .addN 90034 90033 90010,
  .addN 90035 90034 90010, .addN 90036 90035 90012, .addN 90037 90036 90012,
  .addN 90027 90037 90012, .addN 90038 90027 90025, .addN 90039 90038 90011,
  .addN 90040 90039 90011, .addN 90041 90040 90011, .addN 90042 90041 90011,
  .addN 90043 90042 90011, .addN 90044 90043 90010, .addN 90044 90044 90026,
  .addN 90028 90044 90002, .addN 90028 90028 90019, .addN 90029 90028 90010,
  .addN 90029 90029 90010, .addN 90029 90029 90010]

/-- The allocation loop. -/
def allocLoop : Stmt := .whileLtN 9999 90029 (.instr ztrhu)

/-- Products, bases, allocation. -/
def baseStmt : Stmt :=
  .seq (mulS 90025 90012 90002 90061) (.seq (mulS 90026 90002 90010 90061)
    (.seq baseBlock allocLoop))

/-- The registers of `baseStmt`. -/
def Bbase (r : ℕ) : Bool := decide (90025 ≤ r ∧ r < 90062) || decide ztyc
theorem wrS_baseStmt : wrS Bbase baseStmt = true := by_decide

/-- The dimensions of the layout. -/
def dmOf (K A R D b0 : ℕ) : Dm := ⟨K, A, R, D, b0⟩

/-- The base registers of the layout. -/
structure Bases (c : Config) (d : Dm) : Prop where
  bLive : c.nreg 90030 = d.b0
  bS0 : c.nreg 90031 = d.b0 + d.oS0
  bS1 : c.nreg 90032 = d.b0 + d.oS1
  bNd0 : c.nreg 90033 = d.b0 + d.oNd0
  bNd1 : c.nreg 90034 = d.b0 + d.oNd1
  bDeg : c.nreg 90035 = d.b0 + d.oDeg
  bWt : c.nreg 90036 = d.b0 + d.oWt
  bExb : c.nreg 90037 = d.b0 + d.oExb
  bCnt : c.nreg 90038 = d.b0 + d.oCnt
  bNxt : c.nreg 90039 = d.b0 + d.oNxt
  bPrv : c.nreg 90040 = d.b0 + d.oPrv
  bEg : c.nreg 90041 = d.b0 + d.oEg
  bPz : c.nreg 90042 = d.b0 + d.oPz
  bStk : c.nreg 90043 = d.b0 + d.oStk
  bTmp : c.nreg 90044 = d.b0 + d.oTmp
theorem Bases.frame {c c' : Config} {d : Dm} (h : Bases c d)
    (hr : ∀ r, 90030 ≤ r → r < 90045 → c'.nreg r = c.nreg r) : Bases c' d := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
  refine ztcl <;>
    (rw [hr _ by_norm_num by_norm_num]; assumption)

/-- The constants and the bases give `Cst`. -/
theorem Cst.of_bases {c : Config} {E : Env} {d : Dm} (h : Bases c d) (hγ : c.nreg 90014 = E.γ)
    (hsz : c.nreg 90018 = E.sz) (h1 : c.nreg 90019 = 1) (h3 : c.nreg 90020 = 3)
    (h2 : c.nreg 90021 = 2) : Cst c E d :=
  ⟨hγ, hsz, h1, h3, h2, h.bLive, h.bS0, h.bS1, h.bNd0, h.bNd1, h.bDeg, h.bWt, h.bExb, h.bCnt,
    h.bNxt, h.bPrv, h.bEg, h.bPz, h.bStk, h.bTmp⟩
theorem dmOf_oEnd (K A R D b0 : ℕ) : (dmOf K A R D b0).oEnd =
    9 * K + 3 * R + R * D + 5 * A + D * K + D + 1 := by
  simp only [dmOf, Dm.oEnd, Dm.oList, Dm.oTmp, Dm.cap, Dm.oStk, Dm.oPz, Dm.oEg, Dm.oPrv, Dm.oNxt,
    Dm.oCnt, Dm.oEx]
  ring
set_option maxHeartbeats 4000000 in
/-- The bases. -/
theorem baseBlock_exec (c₂ : Config) (w₂ : WordsBounded W c₂)
    {K A R D b0 : ℕ} (g10 : c₂.nreg 90010 = K) (g11 : c₂.nreg 90011 = A)
    (g12 : c₂.nreg 90012 = R) (g02 : c₂.nreg 90002 = D) (g19 : c₂.nreg 90019 = 1)
    (g25 : c₂.nreg 90025 = R * D) (d₂ : c₂.nreg 90026 = D * K) (gA : c₂.nreg 9999 = b0)
    (hroom : b0 + (9 * K + 3 * R + R * D + 5 * A + D * K + D + 1) ≤ W) :
    ∃ c₃ k₃, Exec P W baseBlock c₂ c₃ k₃ ∧ k₃ = 22 ∧
      (Bases c₃ (dmOf K A R D b0) ∧ c₃.nreg 90027 = b0 + (dmOf K A R D b0).oEx ∧
        c₃.nreg 90028 = b0 + (dmOf K A R D b0).oList ∧
        c₃.nreg 90029 = b0 + (dmOf K A R D b0).oEnd) := by
  zuhec
  have o0 : (dmOf K A R D b0).b0 = b0 := rfl
  have o1 : (dmOf K A R D b0).oS0 = K := rfl
  have o2 : (dmOf K A R D b0).oS1 = 2 * K := rfl
  have o3 : (dmOf K A R D b0).oNd0 = 3 * K := rfl
  have o4 : (dmOf K A R D b0).oNd1 = 4 * K := rfl
  have o5 : (dmOf K A R D b0).oDeg = 5 * K := rfl
  have o6 : (dmOf K A R D b0).oWt = 5 * K + R := rfl
  have o7 : (dmOf K A R D b0).oExb = 5 * K + 2 * R := rfl
  have o8 : (dmOf K A R D b0).oEx = 5 * K + 3 * R := rfl
  have o9 : (dmOf K A R D b0).oCnt = 5 * K + 3 * R + R * D := rfl
  have o10 : (dmOf K A R D b0).oNxt = 5 * K + 3 * R + R * D + A := rfl
  have o11 : (dmOf K A R D b0).oPrv = 5 * K + 3 * R + R * D + A + A := rfl
  have o12 : (dmOf K A R D b0).oEg = 5 * K + 3 * R + R * D + A + A + A := rfl
  have o13 : (dmOf K A R D b0).oPz = 5 * K + 3 * R + R * D + A + A + A + A := rfl
  have o14 : (dmOf K A R D b0).oStk = 5 * K + 3 * R + R * D + A + A + A + A + A := rfl
  have o15 : (dmOf K A R D b0).oTmp = 5 * K + 3 * R + R * D + A + A + A + A + A + ztpzh :=
    rfl
  have o16 : (dmOf K A R D b0).oList =
      5 * K + 3 * R + R * D + A + A + A + A + A + ztpzh + D + 1 := rfl
  unfold baseBlock
  exec_block
  all_goals try (config_simp; simp only [gA, g10, g11, g12, g02, g19, g25, d₂]; omega)
  refine ⟨rfl, ztcl, ?_, ?_, ?_⟩ <;>
    config_simp <;> simp only [gA, g10, g11, g12, g02, g19, g25, d₂, o0, o1, o2, o3, o4, o5,
      o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, hE] <;> omega
theorem base_exec (c : Config) (hw : WordsBounded W c) {K A R D : ℕ}
    (h10 : c.nreg 90010 = K) (h11 : c.nreg 90011 = A) (h12 : c.nreg 90012 = R)
    (h02 : c.nreg 90002 = D) (h19 : c.nreg 90019 = 1)
    (hroom : c.nreg ALLOC + (dmOf K A R D ztm).oEnd ≤ W) :
    ∃ c' k, Exec P W baseStmt c c' k ∧
      k ≤ 4 * R + 4 * D + 32 + 3 * (dmOf K A R D ztm).oEnd ∧
      Bases c' (dmOf K A R D ztm) ∧
      c'.nreg ALLOC = c.nreg ALLOC + (dmOf K A R D ztm).oEnd ∧
      c'.nreg 90027 = c.nreg ALLOC + (dmOf K A R D ztm).oEx ∧
      c'.nreg 90028 = c.nreg ALLOC + (dmOf K A R D ztm).oList ∧
      c'.nreg 90026 = D * K ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∀ r, ztoga → r ≠ 90061 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ FrameS Bbase c c' := by
  set b0 := c.nreg ALLOC with hb0
  zuhec
  rw [hE] at hroom ⊢
  have hRD : R * D ≤ W := by_omega
  have hDK : D * K ≤ W := by_omega
  -- the products
  obtain ⟨c₁, k₁, e₁, hk₁, d₁, r₁, m₁, F₁⟩ := mul_exec (P := P) (dst := 90025) (a := 90012)
    (b := 90002) (cnt := 90061) c hw by_decide by_decide by_decide by_decide by_decide
    by_decide by_decide h19 by_simp_all by_omega
  rw [h12, h02] at d₁
  rw [h12] at hk₁
  obtain ⟨c₂, k₂, e₂, hk₂, d₂, r₂, m₂, F₂⟩ := mul_exec (P := P) (dst := 90026) (a := 90002)
    (b := 90010) (cnt := 90061) c₁ e₁.wb_right by_decide by_decide by_decide by_decide
    by_decide by_decide by_decide by_simp_all
    by_simp_all
    by_grind
  rw [r₁ _ by_decide by_decide, r₁ _ by_decide by_decide, h02, h10] at d₂
  rw [r₁ _ by_decide by_decide, h02] at hk₂
  have g : ∀ r, r ≠ 90025 → r ≠ 90026 → r ≠ 90061 → c₂.nreg r = c.nreg r := by_simp_all
  zue
  have g10 : zturm := by_simp_all
  have g11 : c₂.nreg 90011 = A := by_simp_all
  have g12 : c₂.nreg 90012 = R := by_simp_all
  have g02 : zturl := by_simp_all
  have g19 : ztizn := by_simp_all
  have g25 : c₂.nreg 90025 = R * D := by_simp_all
  have gA : c₂.nreg 9999 = b0 := by rw [g _ by_decide by_decide by_decide]; rfl
  -- the bases
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ := baseBlock_exec (P := P) c₂ w₂ g10 g11 g12 g02 g19 g25 d₂ gA
    hroom
  have F₃ := exec_frameB e₃ (B := fun r => decide (90027 ≤ r ∧ r < 90045))
    by_rfl
  have r₃ : ∀ r, ztoga → c₃.nreg r = c₂.nreg r := fun r hr =>
    F₃.1 r by_grind
  have m₃ := F₃.2.2.1
  obtain ⟨B₃, q27, q28, q29⟩ := q
  zubj
  -- the allocation
  have t29 := q29
  rw [hE] at t29
  obtain ⟨c₄, k₄, e₄, ⟨hw₄, hle₄, hr₄, hm₄, hrr₄, hrm₄, ho₄⟩, hx, hk₄, hlb⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 9999) (b := 90029)
    (body := .instr ztrhu)
    (fun d => WordsBounded W d ∧ d.nreg 9999 ≤ c₃.nreg 90029 ∧
      (∀ r, r ≠ 9999 → d.nreg r = c₃.nreg r) ∧ d.nmem = c₃.nmem ∧ d.rreg = c₃.rreg ∧
      d.rmem = c₃.rmem ∧ d.output = c₃.output)
    (fun d => 3 * (c₃.nreg 90029 - d.nreg 9999)) ztqno ztesk
    (fun d ⟨hwd, hled, hrd, hmd, hrrd, hrmd, hod⟩ ht => by
      have h1d : ztutm := by
        grind
      have h29 : d.nreg 90029 = c₃.nreg 90029 := by_grind
      rw [h29] at ht
      zujfj
      refine ⟨⟨hw2, by config_simp; omega, fun r hr => ?_, hmd, hrrd, hrmd, hod⟩, ?_, ?_⟩
      · config_simp; rw [Machine.upd_other _ _ _ hr]; grind
      · config_simp; omega
      · config_simp; rw [h1d])
    ⟨w₃, by_simp_all, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have h29 : c₄.nreg 90029 = c₃.nreg 90029 := by_grind
  rw [h29] at hx
  refine ⟨c₄, _, .seq e₁ ztcb, ?_, B₃.frame by_grind,
    ?_, ?_, ?_, ?_, ?_, fun r hr a1 a2 => ?_, ?_, exec_frameS ztwri
      wrS_baseStmt⟩
  · grind
  · have h1 := hle₄
    rw [t29] at h1 hx
    show c₄.nreg 9999 = _
    grind
  · grind
  · grind
  · rw [hr₄ _ by_decide, F₃.1 _ by_decide, d₂]
  · rw [r₃ 9999 by_omega, gA] at hlb
    show c₄.nreg 9999 ≤ b0 + _
    omega
  · rw [hr₄ r a2, r₃ r hr, g r by_omega by_omega a1]
  grind
def chBody : Stmt := block [.addN 90072 90030 90070, .constN 90073 1, .storeN 90072 90073,
  .addN 90074 90071 90020, .loadN 90075 90074, .addN 90072 90031 90070, .storeN 90072 90075,
  .addN 90074 90074 90019, .loadN 90075 90074, .addN 90072 90032 90070, .storeN 90072 90075,
  .addN 90071 90071 90076, .addN 90070 90070 90019]

/-- The chord loop. -/
def chLoop : Stmt := .seq zthso
  (.whileLtN 90070 90010 chBody)

/-- Registers written by the init loops. -/
def Binit (r : ℕ) : Bool := decide ztnib
theorem wrS_chLoop : wrS Binit chLoop = true := by_decide

/-- The chord-loop invariant. -/
structure ChI (W K CB : ℕ) (d : Dm) (chords : ℕ → CRec) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 90070 ≤ K
  ptr : c.nreg 90071 = CB + 5 * c.nreg 90070
  c76 : c.nreg 90076 = 5
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  live : ∀ u, u < c.nreg 90070 → c.nmem ztnxm = 1
  s0 : ∀ u, u < c.nreg 90070 → c.nmem ztjtm = (chords u).up
  s1 : ∀ u, u < c.nreg 90070 → c.nmem ztjtn = (chords u).dn
  mem : ∀ a, (a < d.b0 ∨ d.b0 + d.oNd0 ≤ a) → c.nmem a = c₀.nmem a
variable {P : Polygon}
set_option maxHeartbeats 1000000 in
theorem chBody_exec {W K CB : ℕ} {d : Dm} {chords : ℕ → CRec} {c₀ c : Config}
    (hI : ChI W K CB d chords c₀ c) (hB : Bases c₀ d) (hK : d.K = K)
    (h10 : c₀.nreg 90010 = K) (h19 : c₀.nreg 90019 = 1) (h20 : c₀.nreg 90020 = 3)
    (hrec : ∀ i, i < K → c₀.nmem ztdfl = (chords i).up ∧
      c₀.nmem ztdfm = (chords i).dn)
    (hCB : CB + 5 * K ≤ d.b0) (hW : d.b0 + d.oEnd ≤ W) (ht : c.nreg 90070 < K) :
    ∃ c' k, Exec P W chBody c c' k ∧ ChI W K CB d chords c₀ c' ∧ k ≤ 13 ∧
      c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hi, hp, h76, hr, hl, hs0, hs1, hm⟩ := hI
  zudex
  zufxf
  have b30 : c.nreg 90030 = d.b0 := by rw [hr _ by_decide, hB.bLive]
  have b31 : c.nreg 90031 = d.b0 + d.oS0 := by rw [hr _ by_decide, hB.bS0]
  have b32 : c.nreg 90032 = d.b0 + d.oS1 := by rw [hr _ by_decide, hB.bS1]
  zuefx
  have c20 : c.nreg 90020 = 3 := by zunyz
  obtain ⟨rup, rdn⟩ := hrec _ ht
  have mup : c.nmem ztman = (chords zterb).up := by
    grind
  have mdn : c.nmem (CB + 5 * c.nreg 90070 + 4) = (chords zterb).dn := by
    grind
  have hEnd : d.oNd0 ≤ d.oEnd := by dm_simp; omega
  have v1 : upd c.nmem ztroi 1 ztman =
      (chords zterb).up := by
    rw [Machine.upd_other _ _ _ by_omega, mup]
  have v2 : upd (upd c.nmem ztroi 1) (d.b0 + d.oS0 + c.nreg 90070)
      (chords zterb).up (CB + 5 * c.nreg 90070 + 3 + 1) = (chords zterb).dn := by
    zucw
    omega
  unfold chBody
  exec_block
  all_goals try (have : d.oNd0 ≤ d.oEnd := hEnd; omega)
  all_goals try (config_simp; simp only [b30, b31, b32, c19, c20, hp, h76]; omega)
  refine ⟨⟨by assumption, ?_, ?_, ?_, fun r hr' => ?_, fun u hu => ?_, fun u hu => ?_,
    fun u hu => ?_, fun a ha => ?_⟩, by_omega, ?_⟩ <;>
    config_simp <;> simp only [b30, b31, b32, c19, c20, hp, h76, v1] <;>
    (try simp only [v2])
  · omega
  · omega
  · have := hr r hr'
    zuhor
    zuby
    grind
  · config_simp at hu; simp only [c19] at hu
    by_cases hui : u = c.nreg 90070
    · zulth
      zucw
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      grind
  · config_simp at hu; simp only [c19] at hu
    by_cases hui : u = c.nreg 90070
    · zulth
      zubc
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      grind
  · config_simp at hu; simp only [c19] at hu
    by_cases hui : u = c.nreg 90070
    · zulth
      simp
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      grind
  · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega]
    grind
theorem chLoop_exec {P : Polygon} {W K CB : ℕ} {d : Dm} {chords : ℕ → CRec} {c₀ : Config}
    (hw : WordsBounded W c₀) (hB : Bases c₀ d) (hK : d.K = K)
    (h10 : c₀.nreg 90010 = K) (h13 : c₀.nreg 90013 = CB) (h19 : c₀.nreg 90019 = 1)
    (h20 : c₀.nreg 90020 = 3)
    (hrec : ∀ i, i < K → c₀.nmem ztdfl = (chords i).up ∧
      c₀.nmem ztdfm = (chords i).dn)
    (hCB : CB + 5 * K ≤ d.b0) (hW : d.b0 + d.oEnd ≤ W) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W chLoop c₀ c' k ∧ k ≤ 15 * K + 5 ∧
      (∀ u, u < K → c'.nmem ztnxm = 1 ∧ c'.nmem ztjtm = (chords u).up ∧
        c'.nmem ztjtn = (chords u).dn) ∧
      ztfjf ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W chLoop c₀ c' k ∧ k ≤ 15 * K + 5 ∧
      (∀ u, u < K → c'.nmem ztnxm = 1 ∧ c'.nmem ztjtm = (chords u).up ∧
        c'.nmem ztjtn = (chords u).dn) ∧
      ztfjf by
    zubgz
    exact ⟨c', k, e, h1, h2, h3, exec_frameS e wrS_chLoop⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90013,
      .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 3 ∧ ChI W K CB d chords c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, fun r hr => ?_, fun u hu => ?_, fun u hu => ?_,
        fun u hu => ?_, fun a _ => rfl⟩, ?_⟩
      · simp
      · simp_all
      · config_simp
      · zubzi
        config_simp; simp only [upd]; grind
      · simp_all
      · simp_all
      · simp_all
      simp
  zuidc
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90010)
    (body := chBody) (ChI W K CB d chords c₀) ztnyn 13 ztpf
    (fun c I ht => by
      have t : ztuol := by rw [I.regs 90010 by_decide, h10] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := chBody_exec (P := P) I hB hK h10 h19 h20 hrec hCB hW t
      grind) q
  have hK' : ztung := by
    rw [I'.regs 90010 by_decide, h10] at hx; have := I'.i_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun u hu => ⟨I'.live u by_omega, I'.s0 u by_omega,
    I'.s1 u by_omega⟩, I'.mem⟩
  omega

/-! ## The worklist -/

/-- One stack entry (`r70 = t`). -/
def stkBody : Stmt := block [.addN 90072 90043 90070, .storeN 90072 90070, .addN 90070 90070 90019]

/-- `stk t := t` for `t < K + D K` (`r77`). -/
def stkLoop : Stmt := .seq (block [.constN 90070 0, .addN 90077 90010 90026])
  (.whileLtN 90070 90077 stkBody)
theorem wrS_stkLoop : wrS Binit stkLoop = true := by_decide

/-- The stack-loop invariant. -/
structure StkI (W : ℕ) (d : Dm) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90070 ≤ d.cap
  cap : c.nreg 90077 = d.cap
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  stk : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oStk + u) = u
  mem : ∀ a, zteou → c.nmem a = c₀.nmem a
theorem stkLoop_exec {W : ℕ} {d : Dm} {c₀ : Config}
    (hw : WordsBounded W c₀) (hB : Bases c₀ d) (h10 : c₀.nreg 90010 = d.K)
    (h26 : c₀.nreg 90026 = d.D * d.K) (h19 : c₀.nreg 90019 = 1) (hW : d.b0 + d.oEnd ≤ W) :
    ∃ c' k, Exec P W stkLoop c₀ c' k ∧ k ≤ 5 * d.cap + 4 ∧
      ztgnp ∧
      ztybl ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W stkLoop c₀ c' k ∧ k ≤ 5 * d.cap + 4 ∧
      ztgnp ∧
      ztybl by
    zubgz
    exact ⟨c', k, e, h1, h2, h3, exec_frameS e wrS_stkLoop⟩
  obtain ⟨y1, y2, y3, y4, -⟩ := d.lay
  have hcap : d.cap = d.K + d.D * d.K := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0,
      .addN 90077 90010 90026]) c₀ c₁ k₁ ∧ k₁ = 2 ∧ StkI W d c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · config_simp; omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, fun r hr => ?_, fun u hu => ?_, fun a _ => rfl⟩, ?_⟩
      · simp
      · simp_all
      · zubzi
        config_simp; simp only [upd]; grind
      · simp_all
      simp
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90077)
    (body := stkBody) (StkI W d c₀) (fun c => d.cap - c.nreg 90070) 3 ztpf
    (fun c I ht => by
      obtain ⟨hwc, hle, hc77, hr, hs, hm⟩ := I
      rw [hc77] at ht
      have b43 : c.nreg 90043 = d.b0 + d.oStk := by rw [hr _ by_decide, hB.bStk]
      zuefx
      unfold stkBody
      exec_block
      · omega
      · config_simp; omega
      · refine ⟨⟨by assumption, ?_, ?_, fun r hr' => ?_, fun u hu => ?_, fun a ha => ?_⟩, by_omega,
          ?_⟩
        · simp_all
        · simp_all
        · zuhor
          config_simp; zvmwf; split_ifs <;> first | omega | exact hr r ztbjn
        · config_simp at hu; rw [c19] at hu
          config_simp; rw [b43]
          by_cases hut : u = c.nreg 90070
          · simp_all
          · zugtv
        · config_simp; rw [b43, Machine.upd_other _ _ _ by_omega]; simp_all
        · config_simp; omega) q
  have hfull : c'.nreg 90070 = d.cap := by rw [I'.cap] at hx; have := I'.t_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun u hu => I'.stk u by_omega, I'.mem⟩
  omega
