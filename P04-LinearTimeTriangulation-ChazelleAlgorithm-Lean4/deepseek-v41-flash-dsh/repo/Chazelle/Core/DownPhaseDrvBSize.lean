module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBArc
public import Chazelle.Core.FactsArcs
public import Chazelle.Core.DownPhaseDrvCount

/-!
# Down-phase base (D9): sizes of the regions

The base case costs a constant per region when the regions are small (`λ < 16`, or `n < n₀`):
a region of an interior family of degree `≤ D` and weight `≤ γ` has

* at most `D + 1` arcs (`arcs_length_le`, `ArcsPerRegionSpec`);
* a host of at most `(D + 1) γ + 2 D` points (`regPts_length_le`: `nk ≤ #inner vertices + 2 deg`,
  `DownDrv.nk_le`, and an arc has at most its weight of inner vertices, `vertsIn_le_arcWt`);
* at most `γ + 2` walk edges per arc (`arcCnt_le`).

For `K = 0` the whole walk is one arc of weight `n`, so `n ≤ γ` (`n_le_of_empty`).
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc)
open BuildNF (codeLe wposOf gapStarts)
open DrvR (regHost walkItems)

/-! ## Inner vertices and weights -/

/-- **An interval has at most its weight of inner walk vertices** (interior model: every edge is
counted). -/
theorem vertsIn_le_arcWt (Q : Polygon) (a b : ℝ) :
    (WalkAx.vertsIn (interiorModel Q) a b).ncard ≤ (interiorModel Q).arcWt a b := by
  have hfin : {p : ℕ | p < (interiorModel Q).W.n ∧ (interiorModel Q).counted p ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}.Finite :=
    (Set.finite_lt_nat _).subset fun p hp => hp.1
  refine Set.ncard_le_ncard ?_ hfin
  rintro p ⟨hp, hin⟩
  refine ⟨hp, trivial, ?_⟩
  obtain ⟨t, h1, h2⟩ := ((cyc_open hin).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  exact ⟨t, h2.1, h2.2, h1⟩

/-- **An arc weighs at most the weight of its region.** -/
theorem arcWt_le_weight {Q : Polygon} (hQ : Q.Simple) {S : Set (Set Point)}
    (hFam : (interiorModel Q).ChordFamily Q S) {R : Set Point}
    (hR : R ∈ (interiorModel Q).regions S) {a b : ℝ} (harc : (interiorModel Q).IsArc S R a b) :
    (interiorModel Q).arcWt a b ≤ (interiorModel Q).weight S R := by
  have hfin := (arcsPerRegion (interiorModel Q) Q S (Or.inr ⟨Q, hQ, rfl⟩) hFam R hR).1
  unfold Model.weight
  apply le_csSup ((hfin.image _).bddAbove)
  exact ⟨(a, b), harc, rfl⟩

/-! ## The arcs of a region of `buildNF` -/

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

theorem region_arcs_nodup (r : ℕ) :
    ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs.Nodup := by
  unfold NF.region
  by_cases hr : r < L.length + 1
  · Ξ List.getD_eq_getElem?_getD
    simp only [BuildNF.buildNF, List.getElem?_map, List.getElem?_range hr, Option.map_some,
      Option.getD_some]
    exact List.nodup_range.filter _
  · Ξ List.getD_eq_getElem?_getD
    ϴ BuildNF.buildNF, List.getElem?_map
    Ξ List.getElem?_eq_none (by simp; omega)
    simp

/-- **A region has at most `deg + 1` arcs.** -/
theorem arcs_length_le (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) :
    ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs.length ≤
      (interiorModel Q).deg ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q)
        (reg r) + 1 := by
  set N := BuildNF.buildNF (interiorModel Q) Q L E with hN
  set S := N.F (interiorModel Q) Q with hS
  have hR := B.hregs.1.1 r hr
  obtain ⟨hfin, hcard⟩ := arcsPerRegion (interiorModel Q) Q S (Or.inr ⟨Q, B.hQ, rfl⟩) B.fam _ hR
  set f : ℕ → ℝ × ℝ := fun j => ((interiorModel Q).key Q (N.arc j).s,
    (interiorModel Q).key Q (N.arc j).e) with hf
  have hmem : ∀ j ∈ (N.region r).arcs, f j ∈ {ab : ℝ × ℝ | (interiorModel Q).IsArc S (reg r) ab.1 ab.2} := by
    intro j hj
    obtain ⟨hjA, hjr⟩ := (B.hregs.2.2.1.2.2.2 r hr j).1 hj
    have := (B.hregs.2.2.1.1 j hjA).2
    rw [hjr] at this
    exact this
  have hinj : Set.InjOn f {j | j ∈ (N.region r).arcs} := by
    intro j hj j' hj' he
    obtain ⟨hjA, hjr⟩ := (B.hregs.2.2.1.2.2.2 r hr j).1 hj
    obtain ⟨hjA', hjr'⟩ := (B.hregs.2.2.1.2.2.2 r hr j').1 hj'
    exact B.hregs.2.2.1.2.1 j j' hjA hjA' (hjr.trans hjr'.symm) (Prod.ext_iff.1 he).1
  have h1 : ((N.region r).arcs.toFinset.image f).card = (N.region r).arcs.length := by
    rw [Finset.card_image_of_injOn (fun j hj j' hj' h => hinj (by simpa using hj)
      (by simpa using hj') h), List.toFinset_card_of_nodup (region_arcs_nodup r)]
  have h2 : (((N.region r).arcs.toFinset.image f : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ⊆
      {ab : ℝ × ℝ | (interiorModel Q).IsArc S (reg r) ab.1 ab.2} := by
    intro ab hab
    simp only [Finset.coe_image, List.coe_toFinset, Set.mem_image, mem_ofPred_eq] at hab
    obtain ⟨j, hj, rfl⟩ := hab
    exact hmem j hj
  have h3 := Set.ncard_le_ncard h2 hfin
  rw [Set.ncard_coe_finset, h1] at h3
  exact h3.trans hcard

/-- A union of a finite family of sets of bounded size. -/
theorem ncard_biUnion_le_mul {α β : Type*} {T : Set α} (hT : T.Finite) (f : α → Set β) {m : ℕ}
    (hf : ∀ x ∈ T, (f x).ncard ≤ m) (hfin : ∀ x ∈ T, (f x).Finite) :
    (⋃ x ∈ T, f x).ncard ≤ m * T.ncard := by
  induction T, hT using Set.Finite.induction_on with
  | empty => simp
  | @insert c T hcT hT ih =>
    Ξ Set.biUnion_insert, Set.ncard_insert_of_notMem hcT hT
    refine (Set.ncard_union_le _ _).trans ?_
    have h1 := hf c (Set.mem_insert c T)
    have h2 := ih (fun x hx => hf x (Set.mem_insert_of_mem c hx))
      (fun x hx => hfin x (Set.mem_insert_of_mem c hx))
    Ξ Nat.mul_succ
    omega

/-- **A region has at most `(deg + 1) γ + 2 deg` host points.** -/
theorem regPts_length_le (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) γ) :
    (regPts li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r).length ≤
      ((interiorModel Q).deg ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q)
          (reg r) + 1) * γ +
        2 * (interiorModel Q).deg ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q)
          (reg r) := by
  have hR := B.hregs.1.1 r hr
  obtain ⟨-, -, -, hlen, -⟩ := DownMath.walk_rep (B.rc hr) B.hli
  have hlenP : (regPts li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r).length =
      DownHost.nk (interiorModel Q)
        ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) := by
    unfold regPts
    Ξ wlist_length, DownMath.regHost_pts
    split_ifs
    · exact hlen
    · rw [List.length_reverse]; exact hlen
  Ξ hlenP
  have hM := walkAx_interiorModel B.hQ
  have hnk := DownDrv.nk_le hM B.fam.2.1 B.fam.1 (reg r)
  obtain ⟨hfin, hcard⟩ := arcsPerRegion (interiorModel Q) Q _ (Or.inr ⟨Q, B.hQ, rfl⟩) B.fam _ hR
  have hsub : DownDrv.vtxIdx (interiorModel Q)
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) ⊆
      ⋃ ab ∈ {ab : ℝ × ℝ | (interiorModel Q).IsArc
          ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) ab.1 ab.2},
        WalkAx.vertsIn (interiorModel Q) ab.1 ab.2 := by
    rintro k ⟨hk, a, b, harc, hin⟩
    exact Set.mem_iUnion₂.2 ⟨(a, b), harc, hk, hin⟩
  have hv := (Set.ncard_le_ncard hsub (Set.Finite.biUnion hfin fun _ _ =>
      (Set.finite_lt_nat _).subset fun p hp => hp.1)).trans
    (ncard_biUnion_le_mul hfin _ (m := γ)
      (fun ab hab => (vertsIn_le_arcWt Q _ _).trans ((arcWt_le_weight B.hQ B.fam hR hab).trans
        (hwt _ hR)))
      (fun _ _ => (Set.finite_lt_nat _).subset fun p hp => hp.1))
  have hmul := Nat.mul_le_mul_left γ hcard
  have e1 : ((interiorModel Q).deg ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q)
      (reg r) + 1) * γ = γ * ((interiorModel Q).deg
        ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) + 1) :=
    mul_comm _ _
  omega

/-- **An arc of a region has at most its weight plus two walk edges.** -/
theorem arcCnt_le (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) γ) {j : ℕ}
    (hj : j ∈ ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs) :
    arcCnt Q.n ((BuildNF.buildNF (interiorModel Q) Q L E).arc j) ≤ γ + 2 := by
  have hR := B.hregs.1.1 r hr
  obtain ⟨hjA, hjr⟩ := (B.hregs.2.2.1.2.2.2 r hr j).1 hj
  have harc := (B.hregs.2.2.1.1 j hjA).2
  rw [hjr] at harc
  have hbound := (vertsIn_le_arcWt Q _ _).trans ((arcWt_le_weight B.hQ B.fam hR harc).trans
    (hwt _ hR))
  have hE : 0 < E.length := by rw [B.hperm.length_eq, List.length_range]; have := B.hK; omega
  have hA := DrvD.arcs_length (M := interiorModel Q) (Q := Q) (E := E) B.hK
  have hjA' : j < (gapStarts (interiorModel Q) Q L E).length := by rw [← hA]; exact hjA
  obtain ⟨sn, s0, s1⟩ := evPos_ok B (DrvD.gs_lt_len hjA')
  obtain ⟨en, e0, e1⟩ := evPos_ok B (Nat.mod_lt (DrvD.gs (interiorModel Q) Q L E j + 1) hE)
  rw [← DrvD.arc_s B.hK hjA'] at sn s0 s1
  rw [← DrvD.arc_e B.hK hjA'] at en e0 e1
  generalize hsg : ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s = s at *
  generalize heg : ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e = e at *
  have ka : (interiorModel Q).key Q s = s.edge + (interiorModel Q).param Q s := rfl
  have kb : (interiorModel Q).key Q e = e.edge + (interiorModel Q).param Q e := rfl
  have hn : (interiorModel Q).W.n = Q.n := DownMath.walk_n Q
  unfold arcCnt
  rw [hsg, heg]
  by_cases hlt : j + 1 < (gapStarts (interiorModel Q) Q L E).length
  · have hk := DrvD.key_s_lt_e (M := interiorModel Q) (Q := Q) B.hK hE hlt
    rw [hsg, heg] at hk
    have hse : s.edge ≤ e.edge := by
      have : (s.edge : ℝ) < e.edge + 1 := by linarith
      have : s.edge < e.edge + 1 := by exact_mod_cast this
      omega
    rw [show e.edge + Q.n - s.edge = (e.edge - s.edge) + Q.n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    have hsub : ((Finset.Ioo s.edge e.edge : Finset ℕ) : Set ℕ) ⊆
        WalkAx.vertsIn (interiorModel Q) ((interiorModel Q).key Q s)
          ((interiorModel Q).key Q e) := by
      intro v hv
      simp only [Finset.coe_Ioo, Set.mem_Ioo] at hv
      refine ⟨by rw [hn]; omega, ?_⟩
      unfold sideInArc; rw [ite_eq_left hk]
      have h1 : (s.edge : ℝ) + 1 ≤ v := by exact_mod_cast hv.1
      have h2 : (v : ℝ) + 1 ≤ e.edge := by exact_mod_cast hv.2
      constructor <;> linarith
    have := Set.ncard_le_ncard hsub ((Set.finite_lt_nat _).subset fun p hp => hp.1)
    rw [Set.ncard_coe_finset, Nat.card_Ioo] at this
    omega
  · have hjl : j = (gapStarts (interiorModel Q) Q L E).length - 1 := by omega
    have hks := DrvD.key_s_last (M := interiorModel Q) (Q := Q) B.hK hE
    have hke := DrvD.key_e_last (M := interiorModel Q) (Q := Q) B.hK hE
    rw [← hjl, hsg] at hks
    rw [← hjl, heg] at hke
    have hge : (interiorModel Q).key Q e ≤ (interiorModel Q).key Q s := by
      rw [hks, hke]; exact DrvD.kE_mono B.hsort (Nat.zero_le _) (by omega)
    have hne := last_arc_edges B
    rw [hA, ← hjl, hsg, heg] at hne
    have hse : e.edge < s.edge := by
      have : (e.edge : ℝ) < s.edge + 1 := by linarith
      have : e.edge < s.edge + 1 := by exact_mod_cast this
      omega
    rw [Nat.mod_eq_of_lt (by omega)]
    have hsub : ((Finset.Ioo s.edge Q.n ∪ Finset.Ico 0 e.edge : Finset ℕ) : Set ℕ) ⊆
        WalkAx.vertsIn (interiorModel Q) ((interiorModel Q).key Q s)
          ((interiorModel Q).key Q e) := by
      intro v hv
      simp only [Finset.coe_union, Finset.coe_Ioo, Finset.coe_Ico, Set.mem_union, Set.mem_Ioo,
        Set.mem_Ico] at hv
      refine ⟨by rw [hn]; omega, ?_⟩
      unfold sideInArc; rw [ite_eq_right (not_lt.2 hge)]
      rcases hv with hv | hv
      · left
        have h1 : (s.edge : ℝ) + 1 ≤ v := by exact_mod_cast hv.1
        linarith
      · right
        have h2 : (v : ℝ) + 1 ≤ e.edge := by exact_mod_cast hv.2
        linarith
    have := Set.ncard_le_ncard hsub ((Set.finite_lt_nat _).subset fun p hp => hp.1)
    rw [Set.ncard_coe_finset] at this
    have hd : Disjoint (Finset.Ioo s.edge Q.n) (Finset.Ico 0 e.edge) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_Ioo, Finset.mem_Ico] at h1 h2
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ioo, Nat.card_Ico] at this
    omega

/-! ## The empty family -/

/-- The whole walk weighs `n`. -/
theorem arcWt_zero (Q : Polygon) : (interiorModel Q).arcWt 0 0 = Q.n := by
  have hn : (interiorModel Q).W.n = Q.n := DownMath.walk_n Q
  unfold Model.arcWt
  have : {p : ℕ | p < (interiorModel Q).W.n ∧ (interiorModel Q).counted p ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc 0 0 (p + t)} = {p | p < Q.n} := by
    ext p
    ϴ mem_ofPred_eq, hn
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, trivial, 1 / 2, ⊛, by norm_num, ?_⟩
      unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; left; positivity
  rw [this, show {p : ℕ | p < Q.n} = ((Finset.range Q.n : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, Finset.card_range]

/-- **With no chords, the walk is one arc**: `n` is at most the weight bound. -/
theorem n_le_of_empty {Q : Polygon} (hQ : Q.Simple) {E : List ℕ} (hE : E = []) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ((BuildNF.buildNF (interiorModel Q) Q [] E).F (interiorModel Q) Q) γ) : Q.n ≤ γ := by
  subst hE
  set I := interiorModel Q with hI
  set N := BuildNF.buildNF I Q [] [] with hN
  have hL : ChordTriplesOK I Q [] := ⟨⟨✓, by simp, by simp⟩, by simp, by simp, by simp⟩
  have hNF : IsNF I Q N := DownMath.isNF_build hQ hL (✓) (by simp)
  obtain ⟨-, -, -, reg, hRC, -, hAO, -⟩ := id hNF
  have hA : N.arcs = [⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩] := by
    show BuildNF.arcList I Q [] [] = _
    unfold BuildNF.arcList
    Ξ ite_eq_left (show ([] : List (ℕ × ℕ × ℕ)).length = 0 from rfl)
  have h0 : 0 < N.arcs.length := by rw [hA]; simp
  obtain ⟨hreg, harc⟩ := hAO.1 0 h0
  have ha : N.arc 0 = ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by unfold NF.arc; rw [hA]; rfl
  rw [ha] at hreg harc
  have hk : I.key Q ⟨0, 0⟩ = 0 := by
    unfold Model.key Model.param; simp
  rw [hk] at harc
  have hR := hRC.1 _ hreg
  have := (arcWt_le_weight hQ hNF.1 hR harc).trans (hwt _ hR)
  rwa [arcWt_zero] at this

end

end DrvB

end Chazelle.Core
