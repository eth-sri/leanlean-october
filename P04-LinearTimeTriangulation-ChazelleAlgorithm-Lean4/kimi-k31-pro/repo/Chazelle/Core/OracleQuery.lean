module

public import Chazelle.Core.OracleCand
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# Lemma 3.6 (WP-H), part 9: correctness of the query from the quantities it computes

The query program of Lemma 3.6 computes, for the ray from `z` in direction `σ`:
* a stopping parameter `T` (the first hit on the scanned edges of the regions of `D*`, the first
  point of a chord ahead of `z`, or the side of the box, whichever comes first);
* candidate nodes at the stopping point (the arcs located by double identification at the walk
  positions of the stopping point, with their neighbours in the table);
* the first hit `best` on the scanned edges of the regions of the nodes of `D*` and of the
  clusters of the candidates.

`query_main` proves that `best` is the answer (`FirstHit` / `NoHit` on the chain), from exactly
these facts; the RAM establishes them.
-/

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
theorem mem_nodeScan (hN : IsNF (chainModel C) Q N) {reg : ℕ → Set Point}
    (_hR : RegionCorr (chainModel C) Q N reg) (hA : ArcsOK (chainModel C) Q N reg)
    {v : ℕ} (hv : v < N.arcs.length) {x : Point} (hxC : x ∈ C.set)
    (hx : ArcHit C (N.F (chainModel C) Q) (reg (rgi N v)) x) : x ∈ nodeScan C Q N v := by
  obtain ⟨a, b, harc, hmem⟩ := hx
  have hrv := (hA.1 _ (NFLoc.seq_lt hN hv)).1
  obtain ⟨j, hj, hjr, hja, hjb⟩ := hA.2.2.1 _ hrv a b harc
  obtain ⟨p, hp, hpj⟩ := NFLoc.seq_surj hN hj
  have hsk : sk (chainModel C) Q N p = a := by
    show (chainModel C).key Q (N.arc (N.seq.getD p 0)).s = a
    rw [hpj, hja]
  have hek : ek (chainModel C) Q N p = b := by
    show (chainModel C).key Q (N.arc (N.seq.getD p 0)).e = b
    rw [hpj, hjb]
  refine ⟨hv, p, hp, ?_, ?_⟩
  · show (N.arc (N.seq.getD p 0)).reg = rgi N v
    rwr [hpj, hjr]
  · -- the ends of the arc record are proper positions on walk edges
    obtain ⟨-, -, -, reg', -, -, -, -, -, -, hprop⟩ := id hN
    obtain ⟨hs, he⟩ := hprop _ (NFLoc.seq_lt hN hp)
    have hkey : ∀ (w : WPos), ProperPos (chainModel C) Q Q.n w →
        (chainModel C).key Q w < (chainModel C).W.n → w.edge < (chainModel C).W.n := by
      intro w hw hk
      have : (w.edge : ℝ) < (chainModel C).W.n := by
        have := hw.1
        unfold Model.key at hk
        linarith
      exact_mod_cast this
    have hsk' : (chainModel C).key Q (N.arc (sj N p)).s < (chainModel C).W.n := by
      have e : (chainModel C).key Q (N.arc (sj N p)).s = sk (chainModel C) Q N p := rfl
      rw [e, hsk]; exact harc.2.1
    have hek' : (chainModel C).key Q (N.arc (sj N p)).e < (chainModel C).W.n := by
      have e : (chainModel C).key Q (N.arc (sj N p)).e = ek (chainModel C) Q N p := rfl
      rw [e, hek]; exact harc.2.2.2.1
    have hsn := hkey _ hs hsk'
    have hen := hkey _ he hek'
    exact mem_scan C Q N hs he hsn hen hxC (by rwx [hsk, hek])

/-- A ray point in the open box at height at most the top that lies on an arc is on the chain. -/
theorem mem_set_of_arcSet {x : Point} (hbox : x ∈ Chain.box C.radius) (hy : x.2 ≤ C.top.2)
    {a b : ℝ} (hx : x ∈ (chainModel C).arcSet a b) (hP : C.P.Simple) : x ∈ C.set := by
  have hnd  := Sweep.arcSet_subset_compl_dom C hP a b hx
  rcases (Merge.not_mem_dom_iff C hy).1 hnd with h | h
  · exact absurd hbox h
  · exact h

/-- Near `0`, the points of a finite set are only `0`. -/
theorem eventually_not_mem_of_finite {X : Set ℝ} (hX : X.Finite) : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∉ X := by
  have hc : IsClosed (X \ {0}) := (hX.sdiff).isClosed
  have ho : (X \ {0})ᶜ ∈ 𝓝 (0 : ℝ) := hc.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds ho, self_mem_nhdsWithin] with t h1 h2
  intro ht
  exact h1 ⟨ht, by simp [Set.mem_singleton_iff]; exact ne_of_gt h2⟩

/-- No point lies on an arc of the empty set (arcs face their region at their inner keys). -/
theorem not_arcHit_empty {F : Set (Set Point)} {x : Point} : ¬ ArcHit C F ∅ x := by
  rintro ⟨a, b, harc, -⟩
  obtain ⟨ha0, han, -, -, hends, -, hfac⟩ := harc
  -- a non-vertex key inside the arc
  have hn : 0 < (chainModel C).W.n := by rwo [walk_n]
  obtain ⟨p, t, hp, ht0, ht1, hin⟩ : ∃ p : ℕ, ∃ t : ℝ, p < (chainModel C).W.n ∧ 0 < t ∧ t < 1 ∧
      sideInArc a b (p + t) := by
    rcases hends with ⟨-, -, hab⟩ | ⟨-, rfl, rfl⟩
    · -- just after `a`
      obtain ⟨q, hq, hqa⟩ : ∃ q : ℕ, q < (chainModel C).W.n ∧ (q : ℝ) ≤ a ∧ a < q + 1 := by
        refine ⟨⌊a⌋₊, ?_, Nat.floor_le ha0, Nat.lt_floor_add_one a⟩
        have : (⌊a⌋₊ : ℝ) < (chainModel C).W.n := lt_of_le_of_lt (Nat.floor_le ha0) han
        exact_mod_cast this
      set ε := (if a < b then min (q + 1 - a) (b - a) else q + 1 - a) / 2 with hε
      have hε0 : 0 < ε := by
        rw [hε]; split_ifs with h
        · have := lt_min (show 0 < (q : ℝ) + 1 - a by linarith [hqa.2]) (sub_pos.2 h); linarith
        · linarith [hqa.2]
      have hεq : a + ε < q + 1 := by
        rw [hε]; split_ifs with h
        · have := min_le_left ((q : ℝ) + 1 - a) (b - a); linarith
        · linarith [hqa.2]
      refine ⟨q, a + ε - q, hq, by linarith [hqa.1], by linarith, ?_⟩
      rw [show (q : ℝ) + (a + ε - q) = a + ε by ring]
      unfold sideInArc
      split_ifs with h
      · have := min_le_right ((q : ℝ) + 1 - a) (b - a)
        have e : ε = min ((q : ℝ) + 1 - a) (b - a) / 2 := by rw [hε, BookData.ite_t h]
        constructor <;> linarith
      · left; linarith
    · refine ⟨0, 1 / 2, hn, by norm_num, by norm_num, ?_⟩
      ufn sideInArc
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
    (hN : IsNF (chainModel C) Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr (chainModel C) Q N reg) (hA : ArcsOK (chainModel C) Q N reg)
    {B : BookData} (hB : GraphOK C Q N B)
    (Dm : Fin B.N → Prop) (ℓ : Fin B.N → ℕ)
    (hlab : ∀ u v (w : (bookGraph B).Walk u v), (∀ x ∈ w.support, ¬ Dm x) → ℓ u = ℓ v)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 0 < T)
    (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ (N.F (chainModel C) Q))
    (hnoD : ∀ i : Fin B.N, Dm i → ∀ s, 0 < s → s < T → rayPt z σ s ∉ nodeScan C Q N i)
    (hstop : rayPt z σ T ∉ C.dom)
    (Cand : Fin B.N → Prop)
    (hcand : ∀ v : Fin B.N, v.1 < N.arcs.length →
      rayPt z σ T ∈ (chainModel C).arcSet (sk (chainModel C) Q N v) (ek (chainModel C) Q N v) →
        Cand v)
    (SN : Fin B.N → Prop)
    (hSN : ∀ i, (Dm i ∨ ∃ c, Cand c ∧ ℓ i = ℓ c) → SN i)
    {S : Set Point} (hS1 : ∀ i, SN i → nodeScan C Q N i ⊆ S) (hSC : S ⊆ C.set)
    {best : Option ℝ} (hbest : Sweep.FirstHitOpt S z σ best) :
    (∀ t, best = some t → FirstHit C.set z σ t) ∧ (best = none → NoHit C.set z σ) := by
  set F := N.F (chainModel C) Q with hFdef
  have hFam  := hN.1
  have hfin := finite_crossings C (fun k _ => vertex_snd_ne C hD) z hσ
  -- the initial part of the ray is free
  have hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ freeIn C.dom F := by
    filter_upwards [eventually_not_mem_of_finite hfin, Ioo_mem_nhdsGT hT] with t h1 h2
    exact mem_freeIn_of_ray C hz (hbox t h2.1 h2.2) h1 (hnoF t h2.1 h2.2)
  have hfree : Merge.FreeAt C z σ := hini.mono fun t ht => ht.1
  obtain ⟨hT0, hnd, hdom⟩ := Merge.hit_of_freeAt C hz hσ hfree
  set t₀ := C.hitParam z σ
  by_cases hon : rayPt z σ t₀ ∈ C.set
  · -- the true hit is on the chain: it is scanned
    have hfirst := firstHit_chain_of_hit C hz hσ hfree hon
    obtain ⟨U, hU, hUi⟩ := exists_initial_region C hfree (hini.mono fun t ht => ht.2)
    obtain ⟨R, hRr, hRi⟩ := exists_final_region C hz hT hbox hfin hnoF
    -- the node of `R` at the stopping point
    obtain ⟨a₀, ha₀, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hRi
    have hRhit : ArcHit C F R (rayPt z σ T) :=
      arcHit_left C hP hFam hRr hz hσ ha₀ (fun t h1 h2 => hsub ⟨h1, h2⟩) hstop
    obtain ⟨a, b, harc, hmem⟩ := hRhit
    obtain ⟨r, hr, rfl⟩ := hR.2.2 R hRr
    obtain ⟨j, hj, hjr, hja, hjb⟩ := hA.2.2.1 r hr a b harc
    obtain ⟨p, hp, hpj⟩ := NFLoc.seq_surj hN hj
    have hpN  := lt_of_lt_of_le hp hB.arcs_le
    have hrp : rgi N p = r := by
      show (N.arc (N.seq.getD p 0)).reg = r
      rw [hpj, hjr]
    let iR : Fin B.N := ⟨p, hpN⟩
    have hrgR : rgNode reg N B iR = reg r := by
      show (if p < N.arcs.length then reg (rgi N p) else ∅) = reg r
      rw [BookData.ite_t hp, hrp]
    have hcandR : Cand iR := by
      refine hcand iR hp ?_
      have hsk : sk (chainModel C) Q N p = a := by
        show (chainModel C).key Q (N.arc (N.seq.getD p 0)).s = a
        rw [hpj, hja]
      have hek : ek (chainModel C) Q N p = b := by
        show (chainModel C).key Q (N.arc (N.seq.getD p 0)).e = b
        rw [hpj, hjb]
      show rayPt z σ T ∈ (chainModel C).arcSet (sk (chainModel C) Q N p) (ek (chainModel C) Q N p)
      rwx [hsk, hek]
    -- no node of `D*` is hit before `T`
    have hDh : ∀ i, Dm i → ∀ s, 0 < s → s < T →
        ¬ ArcHit C F (rgNode reg N B i) (rayPt z σ s) := by
      intro i hi s hs0 hsT hh
      by_cases hiA : i.1 < N.arcs.length
      · have e : rgNode reg N B i = reg (rgi N i) := by
          show (if i.1 < N.arcs.length then reg (rgi N i) else ∅) = _
          rw [BookData.ite_t hiA]
        rw [e] at hh
        obtain ⟨a', b', harc', hmem'⟩ := hh
        have hxC := mem_set_of_arcSet (hbox s hs0 hsT) (by simpa using hz) hmem' hP
        exact hnoD i hi s hs0 hsT (mem_nodeScan hN hR hA hiA hxC ⟨a', b', harc', hmem'⟩)
      · have e : rgNode reg N B i = ∅ := by
          show (if i.1 < N.arcs.length then reg (rgi N i) else ∅) = _
          rw [BookData.ite_f hiA]
        rw [e] at hh
        exact not_arcHit_empty hh
    obtain ⟨iU, hiU, hsel⟩ := cluster_query_nodes C hP hFam (rgNode reg N B) (bookGraph B)
      (conn_of_graphOK hN hR hA hB) (cross_of_graphOK hP hN hR hA hB) Dm ℓ hlab hz hσ hT hbox
      hfin hnoF hDh hU hUi (iR := iR) (by rw [hrgR]; exact hR.1 r hr) (by rwx [hrgR])
    have hSN : SN iU := hSN iU (by
      rcases hsel with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨iR, hcandR, h⟩)
    -- the true hit is on an arc of `U`, hence scanned
    obtain ⟨a₁, b₁, harc₁, hmem₁⟩ := Sweep.local_shoot C hP hFam hU hz hσ hUi
    have hiUA : iU.1 < N.arcs.length := by
      by_contra hc
      have e : rgNode reg N B iU = ∅ := by
        show (if iU.1 < N.arcs.length then reg (rgi N iU) else ∅) = _
        rw [BookData.ite_f hc]
      rw [e] at hiU
      rw [← hiU] at hU
      exact (Chazelle.Chain.regionsIn_nonempty (D := C.dom) hU).ne_empty rfl
    have hiU' : reg (rgi N iU) = U := by
      rw [← hiU]
      show reg (rgi N iU) = (if iU.1 < N.arcs.length then reg (rgi N iU) else ∅)
      rw [BookData.ite_t hiUA]
    have hinS : rayPt z σ t₀ ∈ S :=
      hS1 iU hSN (mem_nodeScan hN hR hA hiUA hon (by rw [hiU']; exact ⟨a₁, b₁, harc₁, hmem₁⟩))
    have hSfirst  := Sweep.firstHit_of_subset hSC hfirst hinS
    refine ⟨fun t ht => ?_, fun hn => ?_⟩
    · subst ht
      rwx [Sweep.firstHit_unique hbest hSfirst]
    · subst hn
      exact absurd hinS (hbest t₀ hT0)
  · -- the true hit is the side of the box: no hit at all
    have hno := noHit_chain_of_hit C hz hσ hfree hon
    refine ⟨fun t ht => ?_, fun _ => hno⟩
    subst ht
    exact absurd (hSC hbest.2.1) (hno t hbest.1)

end OracleQ

end

end Chazelle.Core
