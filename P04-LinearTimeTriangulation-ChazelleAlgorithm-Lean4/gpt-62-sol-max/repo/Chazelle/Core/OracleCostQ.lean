module

public import Chazelle.Core.OracleQueryExec

/-!
# Lemma 3.6 (WP-H), part 25: the sizes behind the query cost

For a `γ`-canonical normal form of a chain (degree cap `4`):

* `gamma_pos`: `γ ≥ 1` (the walk has counted edges, and some arc meets one);
* `arcWt_le_gamma`: an arc of a region meets at most `γ` counted edges;
* `scanLen_le`: the walk edges scanned for an arc are at most `γ + 10` (and `2 m + 9`) — all but
  the seven box and slit edges among them are counted edges met by the arc;
* `region_arcs_le`: a region lists at most `5` arcs (`arcsPerRegion`, degree `≤ 4`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

variable {C : Chain} {Q : Polygon} {N : NF} {γ : ℕ}

/-- An arc of a region of a `γ`-semigranular family meets at most `γ` counted edges. -/
theorem arcWt_le_gamma {M : Model} (hGM : GoodModel M) {F : Set (Set Point)}
    (hF : M.ChordFamily Q F) (hsg : M.Semigranular F γ) {U : Set Point} (hU : U ∈ M.regions F)
    {a b : ℝ} (harc : M.IsArc F U a b) : M.arcWt a b ≤ γ := by
  have hM := walkAx_of_goodModel hGM
  have hbdd : BddAbove ((fun ab : ℝ × ℝ => M.arcWt ab.1 ab.2) '' {ab | M.IsArc F U ab.1 ab.2}) :=
    ((hM.arcs_bound hF.2.1 hF.1 hU).1.image _).bddAbove
  have hle : M.arcWt a b ≤ M.weight F U := le_csSup hbdd ⟨(a, b), harc, rfl⟩
  exact hle.trans (hsg U hU)

/-- A finite set of counted edges met by an interval bounds its weight from below. -/
theorem card_le_arcWt {M : Model} {a b : ℝ} (T : Finset ℕ)
    (hT : ∀ q ∈ T, q < M.W.n ∧ M.counted q ∧ sideInArc a b ((q : ℝ) + 1 / 2)) :
    T.card ≤ M.arcWt a b := by
  unfold Model.arcWt
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun q hq => ?_) ((Set.finite_Iio M.W.n).subset fun p hp => hp.1)
  obtain ⟨h1, h2, h3⟩ := hT q hq
  exact ⟨h1, h2, 1 / 2, by norm_num, by norm_num, h3⟩

/-- **`γ ≥ 1`** for a `γ`-canonical normal form of a chain. -/
theorem gamma_pos (hP : C.P.Simple) (hC : IsCanonicalNF (chainModel C) Q N γ 4) : 1 ≤ γ := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hM := walkAx_of_goodModel hGM
  have hF := hC.1.1
  have hsg := hC.2.2.1.semigranular
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  have hm1 := C.one_le
  by_contra h0
  have hγ : γ = 0 := by omega
  subst hγ
  by_cases hne : (N.F (chainModel C) Q).Nonempty
  · exact hM.not_semigranular_zero hF.2.1 hF.1 hne (p₀ := 6) (by rw [hnW]; omega)
      (show 6 ≤ 6 ∧ 6 < 2 * C.m + 6 by omega) hsg
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨U, hU, a, b, harc⟩ := (arcCover (chainModel C) Q _ hGM hF).1
    have hab : a = 0 ∧ b = 0 := by
      rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1, h2⟩
      · rw [hne] at hc; exact absurd hc (Set.notMem_empty _)
      · exact ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := hab
    have := card_le_arcWt (M := chainModel C) (a := 0) (b := 0) {6} (by
      intro q hq
      rw [Finset.mem_singleton] at hq; subst hq
      refine ⟨by rw [hnW]; omega, show 6 ≤ 6 ∧ 6 < 2 * C.m + 6 by omega, ?_⟩
      unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; left; norm_num)
    have := arcWt_le_gamma hGM hF hsg hU harc
    simp at *; omega

/-- All but at most seven walk edges of a set are counted edges. -/
theorem card_counted_ge (m : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q < 2 * m + 7) :
    S.card ≤ (S.filter fun q => 6 ≤ q ∧ q < 2 * m + 6).card + 7 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := S)
    (fun q => 6 ≤ q ∧ q < 2 * m + 6)
  have hsub : S.filter (fun q => ¬ (6 ≤ q ∧ q < 2 * m + 6)) ⊆ Finset.range 6 ∪ {2 * m + 6} := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have := hS q hq.1
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
    omega
  have hc := Finset.card_le_card hsub
  have hc2 : (Finset.range 6 ∪ {2 * m + 6}).card ≤ 7 :=
    (Finset.card_union_le _ _).trans (by simp)
  omega

/-- **The walk edges scanned for an arc.** -/
theorem scanLen_le (hP : C.P.Simple) (hC : IsCanonicalNF (chainModel C) Q N γ 4) {p : ℕ}
    (hp : p < N.arcs.length) :
    scanLenR N (2 * C.m + 7) N.arcs.length p ≤ γ + 10 ∧
      scanLenR N (2 * C.m + 7) N.arcs.length p ≤ 2 * C.m + 9 := by
  classical
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hN := hC.1
  have hsg := hC.2.2.1.semigranular
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  obtain ⟨reg, hR, hA, harc⟩ := isArc_sj hN hp
  have hU : reg (N.arc (sj N p)).reg ∈ (chainModel C).regions (N.F (chainModel C) Q) :=
    hR.1 _ (hA.1 _ (NFLoc.seq_lt hN hp)).1
  have hwt := arcWt_le_gamma hGM hN.1 hsg hU harc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := id hN
  obtain ⟨⟨hs0, hs1, -⟩, ⟨he0, he1, -⟩⟩ := hpp _ (NFLoc.seq_lt hN hp)
  set se := (N.arc (sj N p)).s.edge
  set ee := (N.arc (sj N p)).e.edge
  have hsk : sk (chainModel C) Q N p = se + (chainModel C).param Q (N.arc (sj N p)).s := rfl
  have hek : ek (chainModel C) Q N p = ee + (chainModel C).param Q (N.arc (sj N p)).e := rfl
  have hts0 : 0 ≤ (chainModel C).param Q (N.arc (sj N p)).s := hs0
  have hts1 : (chainModel C).param Q (N.arc (sj N p)).s < 1 := hs1
  have hte0 : 0 ≤ (chainModel C).param Q (N.arc (sj N p)).e := he0
  have hte1 : (chainModel C).param Q (N.arc (sj N p)).e < 1 := he1
  have ha1 := harc.2.1
  have hb1 := harc.2.2.2.1
  rw [hnW] at ha1 hb1
  have hse : se < 2 * C.m + 7 := by
    have : (se : ℝ) < 2 * C.m + 7 := by rw [hsk] at ha1; push_cast at ha1; linarith
    exact_mod_cast this
  have hee : ee < 2 * C.m + 7 := by
    have : (ee : ℝ) < 2 * C.m + 7 := by rw [hek] at hb1; push_cast at hb1; linarith
    exact_mod_cast this
  have hw := wrap_iff hN hGM hp
  unfold scanLenR
  by_cases hwr : p + 1 < N.arcs.length
  · rw [ite_eq_left hwr]
    have hab := hw.2 hwr
    rw [hsk, hek] at hab
    have hT := card_le_arcWt (M := chainModel C) (a := sk (chainModel C) Q N p)
      (b := ek (chainModel C) Q N p) ((Finset.Ioo se ee).filter fun q => 6 ≤ q ∧ q < 2 * C.m + 6) (by
        intro q hq
        rw [Finset.mem_filter, Finset.mem_Ioo] at hq
        refine ⟨by rw [hnW]; omega, hq.2, ?_⟩
        rw [hsk, hek]; unfold sideInArc; rw [ite_eq_left hab]
        have h1 : (se : ℝ) + 1 ≤ q := by exact_mod_cast hq.1.1
        have h2 : (q : ℝ) + 1 ≤ ee := by exact_mod_cast hq.1.2
        constructor <;> linarith)
    have hc := card_counted_ge C.m (Finset.Ioo se ee) (fun q hq => by
      rw [Finset.mem_Ioo] at hq; omega)
    rw [Nat.card_Ioo] at hc
    constructor <;> omega
  · rw [ite_eq_right hwr]
    have hab : ¬ (sk (chainModel C) Q N p < ek (chainModel C) Q N p) := fun h => hwr (hw.1 h)
    have hab' := hab
    rw [hsk, hek] at hab'
    have hes : ee ≤ se := by
      have : (ee : ℝ) < se + 1 := by push Not at hab'; linarith
      have : ee < se + 1 := by exact_mod_cast this
      omega
    have hT := card_le_arcWt (M := chainModel C) (a := sk (chainModel C) Q N p)
      (b := ek (chainModel C) Q N p) ((Finset.Ioo se (2 * C.m + 7) ∪ Finset.range ee).filter
      fun q => 6 ≤ q ∧ q < 2 * C.m + 6) (by
        intro q hq
        rw [Finset.mem_filter, Finset.mem_union, Finset.mem_Ioo, Finset.mem_range] at hq
        refine ⟨by rw [hnW]; omega, hq.2, ?_⟩
        unfold sideInArc; rw [ite_eq_right hab, hsk, hek]
        rcases hq.1 with h | h
        · left
          have h1 : (se : ℝ) + 1 ≤ q := by exact_mod_cast h.1
          linarith
        · right
          have h2 : (q : ℝ) + 1 ≤ ee := by exact_mod_cast h
          linarith)
    have hdis : Disjoint (Finset.Ioo se (2 * C.m + 7)) (Finset.range ee) := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      rw [Finset.mem_Ioo] at h1; rw [Finset.mem_range] at h2; omega
    have hc := card_counted_ge C.m (Finset.Ioo se (2 * C.m + 7) ∪ Finset.range ee) (fun q hq => by
      rw [Finset.mem_union, Finset.mem_Ioo, Finset.mem_range] at hq; omega)
    rw [Finset.card_union_of_disjoint hdis, Nat.card_Ioo, Finset.card_range] at hc
    constructor <;> omega

/-- **A region lists at most five arcs.** -/
theorem region_arcs_le (hP : C.P.Simple) (hC : IsCanonicalNF (chainModel C) Q N γ 4) {r : ℕ}
    (hr : r < N.regions.length) : (N.region r).arcs.length ≤ 5 := by
  classical
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hM := walkAx_of_goodModel hGM
  obtain ⟨hF, -, -, reg, hR, -, hA, hRs, -⟩ := hC.1
  have hU : reg r ∈ (chainModel C).regions (N.F (chainModel C) Q) := hR.1 r hr
  have hnd := (hRs r hr).2.2.1
  set L := (N.region r).arcs
  set f : ℕ → ℝ × ℝ := fun j => ((chainModel C).key Q (N.arc j).s, (chainModel C).key Q (N.arc j).e)
  have hmem : ∀ j ∈ L, j < N.arcs.length ∧ (N.arc j).reg = r := fun j hj => (hA.2.2.2 r hr j).1 hj
  have hinj : Set.InjOn f {j | j ∈ L} := by
    intro j hj j' hj' hjj
    obtain ⟨h1, h2⟩ := hmem j hj
    obtain ⟨h1', h2'⟩ := hmem j' hj'
    exact hA.2.1 j j' h1 h1' (h2.trans h2'.symm) (congrArg Prod.fst hjj)
  have hsub : f '' {j | j ∈ L} ⊆ {ab : ℝ × ℝ | (chainModel C).IsArc (N.F (chainModel C) Q) (reg r) ab.1 ab.2} := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := hmem j hj
    have := (hA.1 j h1).2
    rw [h2] at this; exact this
  obtain ⟨hfin, hcard⟩ := hM.arcs_bound hF.2.1 hF.1 hU
  have hdeg := hC.2.1 _ hU
  have hL : L.length = ({j | j ∈ L} : Set ℕ).ncard := by
    rw [show ({j | j ∈ L} : Set ℕ) = ↑L.toFinset by ext; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  have h1 : ({j | j ∈ L} : Set ℕ).ncard = (f '' {j | j ∈ L}).ncard := (Set.InjOn.ncard_image hinj).symm
  have h2 := Set.ncard_le_ncard hsub hfin
  omega

/-- **At most five arcs per region.** -/
theorem arcs_le_regions (hP : C.P.Simple) (hC : IsCanonicalNF (chainModel C) Q N γ 4) :
    N.arcs.length ≤ 5 * N.regions.length := by
  classical
  obtain ⟨reg, hR, hA, -⟩ := NFLoc.isNF_arcs hC.1
  have := Finset.card_le_mul_card_image_of_maps_to (s := Finset.range N.arcs.length)
    (t := Finset.range N.regions.length) (f := fun j => (N.arc j).reg)
    (fun j hj => Finset.mem_range.2 (hA.1 j (Finset.mem_range.1 hj)).1) 5 (by
      intro r hr
      have hr' := Finset.mem_range.1 hr
      calc ((Finset.range N.arcs.length).filter fun j => (N.arc j).reg = r).card
          ≤ (N.region r).arcs.toFinset.card := by
            apply Finset.card_le_card
            intro j hj
            rw [Finset.mem_filter, Finset.mem_range] at hj
            rw [List.mem_toFinset]
            exact (hA.2.2.2 r hr' j).2 hj
        _ ≤ (N.region r).arcs.length := List.toFinset_card_le _
        _ ≤ 5 := region_arcs_le hP hC hr')
  simpa using this

/-- **The regions of a normal form are one more than its chords.** -/
theorem regions_eq (hP : C.P.Simple) (hN : IsNF (chainModel C) Q N) :
    N.regions.length = N.chords.length + 1 := by
  classical
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨hF, hinj, -, reg, hR, -⟩ := hN
  obtain ⟨-, hcard, -⟩ := regionTree (chainModel C) Q _ hGM hF
  -- the regions
  have hRn : (chainModel C).regions (N.F (chainModel C) Q) = reg '' Set.Iio N.regions.length := by
    ext U; constructor
    · intro hU; obtain ⟨r, hr, rfl⟩ := hR.2.2 U hU; exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact hR.1 r hr
  have hRc : ((chainModel C).regions (N.F (chainModel C) Q)).ncard = N.regions.length := by
    rw [hRn, Set.InjOn.ncard_image (s := Set.Iio N.regions.length) (f := reg)
      (fun a ha b hb h => hR.2.1 a b ha hb h), ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  -- the chords
  have hFn : N.F (chainModel C) Q = (fun i => (N.chord i).toSet (chainModel C) Q) ''
      Set.Iio N.chords.length := by
    ext c; constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      refine ⟨i, hi, ?_⟩
      show (N.chord i).toSet _ _ = _
      unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨N.chord i, ?_, rfl⟩
      unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]; exact List.getElem_mem hi
  have hFc : (N.F (chainModel C) Q).ncard = N.chords.length := by
    rw [hFn, Set.InjOn.ncard_image (s := Set.Iio N.chords.length)
      (f := fun i => (N.chord i).toSet (chainModel C) Q) (fun a ha b hb h => hinj a b ha hb h),
      ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  omega

end

end OracleR

end Chazelle.Core
