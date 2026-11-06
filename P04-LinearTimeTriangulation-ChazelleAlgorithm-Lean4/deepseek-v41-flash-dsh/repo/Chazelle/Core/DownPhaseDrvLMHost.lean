module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBSize
public import Chazelle.Core.DownPhaseDrvRLvlSpec
public import Chazelle.Core.DownPhaseMathRec2

/-!
# Down-phase level math (D7), part 1: the sizes of the region hosts

For region `r` of the interior normal form `N = buildNF I Q L E` (degree `≤ 4`, weight `≤ γ`),
the host description `regHost li n N r` written by the host RAM has

* at most `4` items per arc of `r`, hence at most `20` items (`regHost_length_le`);
* runs of at most `γ` edges (`run_le`): a run lists the walk vertices strictly inside an arc,
  at most its number of walk edges (`DrvB.arcCnt_le`) less two;
* between `3` and `5 γ + 8` points (`DownHost.three_le_nk`, `DrvB.regPts_length_le`).
-/

namespace Chazelle.Core

namespace DrvLM

@[expose] public section

open DrvR (regHost walkItems arcItems runItems runCnt atVtx ptI)
open BuildNF (codeLe wposOf gapStarts)

/-! ## Item counts -/

theorem runItems_length (li : Bool) (n : ℕ) (s e : WPos) : (runItems li n s e).length ≤ 1 := by
  unfold runItems; split_ifs <;> simp

theorem arcItems_length (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).length ≤ 4 := by
  unfold arcItems
  have := runItems_length li n (N.arc j).s (N.arc j).e
  ϴ List.length_append, List.length_singleton
  split_ifs <;> simp <;> omega

theorem walkItems_length (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    (walkItems li n N r).length ≤ 4 * (N.region r).arcs.length := by
  unfold walkItems
  Ξ List.length_flatMap
  have : ∀ x ∈ (List.range (N.region r).arcs.length).map (fun t => (arcItems li n N r
      ((N.region r).arcs.getD t 0) ((N.region r).arcs.getD ((t + 1) %
        (N.region r).arcs.length) 0)).length), x ≤ 4 := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact arcItems_length _ _ _ _ _ _
  have h := List.sum_le_length_nsmul _ 4 this
  simp only [List.length_map, List.length_range, smul_eq_mul] at h
  omega

theorem regHost_length (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    (regHost li n N r).length ≤ 4 * (N.region r).arcs.length := by
  unfold regHost
  split_ifs
  · exact walkItems_length _ _ _ _
  · rw [List.length_reverse]; exact walkItems_length _ _ _ _

/-! ## Runs -/

theorem run_mem_runItems {li : Bool} {n : ℕ} {s e : WPos} {a ℓ : ℕ}
    (h : HostItem.run a ℓ ∈ runItems li n s e) : runCnt li n s e ≠ 0 ∧ ℓ = runCnt li n s e - 1 := by
  unfold runItems at h
  split_ifs at h with h0 h1
  · simp at h
  · simp only [List.mem_singleton, HostItem.run.injEq] at h
    exact ⟨h0, h.2⟩
  · simp only [List.mem_singleton, HostItem.run.injEq] at h
    exact ⟨h0, h.2⟩

theorem run_mem_arcItems {li : Bool} {n : ℕ} {N : NF} {r jp j a ℓ : ℕ}
    (h : HostItem.run a ℓ ∈ arcItems li n N r jp j) :
    runCnt li n (N.arc j).s (N.arc j).e ≠ 0 ∧ ℓ = runCnt li n (N.arc j).s (N.arc j).e - 1 := by
  unfold arcItems at h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with ((h | h) | h) | h
  · split_ifs at h with h'
    · simp at h
    · simp only [List.mem_singleton] at h; unfold ptI at h; cases h
  · unfold ptI at h; cases h
  · exact run_mem_runItems h
  · unfold ptI at h; cases h

/-- A run of the host comes from an arc of the region. -/
theorem run_mem_regHost {li : Bool} {n : ℕ} {N : NF} {r a ℓ : ℕ}
    (h : HostItem.run a ℓ ∈ regHost li n N r) :
    ∃ j ∈ (N.region r).arcs,
      runCnt li n (N.arc j).s (N.arc j).e ≠ 0 ∧ ℓ = runCnt li n (N.arc j).s (N.arc j).e - 1 := by
  have hw : HostItem.run a ℓ ∈ walkItems li n N r := by
    unfold regHost at h
    split_ifs at h
    · exact h
    · exact List.mem_reverse.1 h
  unfold walkItems at hw
  obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.1 hw
  rw [List.mem_range] at ht
  refine ⟨_, ?_, run_mem_arcItems hmem⟩
  have hk : (t + 1) % (N.region r).arcs.length < (N.region r).arcs.length :=
    Nat.mod_lt _ (⋄)
  Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some
  exact List.getElem_mem hk

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

/-- **The run of an arc has at most `γ + 1` walk vertices.** -/
theorem runCnt_le (B : DrvB.BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) γ) {j : ℕ}
    (hj : j ∈ ((BuildNF.buildNF (interiorModel Q) Q L E).region r).arcs)
    (hne : runCnt li Q.n ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s
      ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e ≠ 0) :
    runCnt li Q.n ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).s
      ((BuildNF.buildNF (interiorModel Q) Q L E).arc j).e ≤ γ + 1 := by
  set N := BuildNF.buildNF (interiorModel Q) Q L E with hN
  have hac := DrvB.arcCnt_le B hr hwt hj
  obtain ⟨hjA, -⟩ := (B.hregs.2.2.1.2.2.2 r hr j).1 hj
  have hE : 0 < E.length := by rw [B.hperm.length_eq, List.length_range]; have := B.hK; omega
  have hA := DrvD.arcs_length (M := interiorModel Q) (Q := Q) (E := E) B.hK
  have hjA' : j < (gapStarts (interiorModel Q) Q L E).length := by rw [← hA]; exact hjA
  obtain ⟨sn, s0, s1⟩ := DrvB.evPos_ok B (DrvD.gs_lt_len hjA')
  obtain ⟨en, e0, e1⟩ := DrvB.evPos_ok B (Nat.mod_lt (DrvD.gs (interiorModel Q) Q L E j + 1) hE)
  rw [← DrvD.arc_s B.hK hjA'] at sn s0 s1
  rw [← DrvD.arc_e B.hK hjA'] at en e0 e1
  obtain ⟨-, hpe⟩ := DownMath.arc_pos B.hQ B.hL B.hperm B.hsort B.hK hjA
  have hNF := (BuildNF.isNF_goodModel (Or.inr ⟨Q, B.hQ, rfl⟩) B.hL B.hperm B.hsort).1
  have hvtx := DownMath.atVtx_iff hNF B.hdh B.hli hpe
  unfold DrvB.arcCnt at hac
  unfold runCnt at hne ⊢
  generalize hsg : (N.arc j).s = s at *
  generalize heg : (N.arc j).e = e at *
  have kb : (interiorModel Q).key Q e = e.edge + (interiorModel Q).param Q e := rfl
  have ka : (interiorModel Q).key Q s = s.edge + (interiorModel Q).param Q s := rfl
  by_cases hv : atVtx li Q.n e = true
  · rw [ite_eq_left hv] at hne ⊢
    by_cases hxy : s.edge < e.edge
    · rw [show e.edge + 0 + Q.n - 1 - s.edge = (e.edge - s.edge - 1) + Q.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [show e.edge + Q.n - s.edge = (e.edge - s.edge) + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hac
      omega
    by_cases hyx : e.edge < s.edge
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)] at hac
      omega
    · -- the degenerate case: both ends on one walk edge, the end at its start vertex
      exfalso
      have hxe : s.edge = e.edge := by omega
      have hk : (interiorModel Q).key Q e = (e.edge : ℝ) := by
        have h1 := hvtx.1 hv
        rw [kb, DownHost.floor_add e0 e1] at h1
        rw [kb]; exact h1
      by_cases hlast : j + 1 < (gapStarts (interiorModel Q) Q L E).length
      · have hlt := DrvD.key_s_lt_e (M := interiorModel Q) (Q := Q) B.hK hE hlast
        rw [hsg, heg, hk, ka, hxe] at hlt
        linarith
      · have hne' := DrvB.last_arc_edges B
        have hjl : j = (BuildNF.buildNF (interiorModel Q) Q L E).arcs.length - 1 := by
          rw [hA]; omega
        rw [← hjl, hsg, heg] at hne'
        exact hne' hxe
  · rw [ite_eq_right hv] at hne ⊢
    by_cases hxy : s.edge < e.edge
    · rw [show e.edge + 1 + Q.n - 1 - s.edge = (e.edge - s.edge) + Q.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [show e.edge + Q.n - s.edge = (e.edge - s.edge) + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hac
      omega
    by_cases hyx : e.edge < s.edge
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)] at hac
      omega
    · exfalso
      rw [show e.edge + 1 + Q.n - 1 - s.edge = 0 + Q.n by omega, Nat.add_mod_right,
        Nat.zero_mod] at hne
      exact hne rfl

/-- The host has as many points as the region has host keys. -/
theorem pts_length (B : DrvB.BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions) :
    ((regHost li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r).pts Q.n).length =
      DownHost.nk (interiorModel Q)
        ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) := by
  obtain ⟨-, -, -, hlen, -⟩ := DownMath.walk_rep (B.rc hr) B.hli
  Ξ DownMath.regHost_pts
  split_ifs
  · exact hlen
  · rw [List.length_reverse]; exact hlen

/-- **The sizes of a region host** (degree `≤ 4`, weight `≤ γ`). -/
theorem host_facts (B : DrvB.BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF (interiorModel Q) Q L E).nRegions)
    (hdeg : (interiorModel Q).DegLe
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) 4) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) γ) :
    (regHost li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r).length ≤ 20 ∧
      (∀ a ℓ, HostItem.run a ℓ ∈ regHost li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r →
        ℓ ≤ γ) ∧
      3 ≤ ((regHost li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r).pts Q.n).length ∧
      ((regHost li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r).pts Q.n).length ≤
        5 * γ + 8 := by
  have hR := B.hregs.1.1 r hr
  have hd : (interiorModel Q).deg ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q)
      (reg r) ≤ 4 := hdeg _ hR
  have hnA := DrvB.arcs_length_le B hr
  refine ⟨?_, fun a ℓ h => ?_, ?_, ?_⟩
  · have := regHost_length li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r
    omega
  · obtain ⟨j, hj, hne, rfl⟩ := run_mem_regHost h
    have := runCnt_le B hr hwt hj hne
    omega
  · Ξ pts_length B hr
    have hne : ((BuildNF.buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q).Nonempty := by
      refine ⟨((BuildNF.buildNF (interiorModel Q) Q L E).chord 0).toSet (interiorModel Q) Q,
        (BuildNF.buildNF (interiorModel Q) Q L E).chord 0, ?_, rfl⟩
      unfold NF.chord
      have h0 : 0 < (BuildNF.buildNF (interiorModel Q) Q L E).chords.length := by
        simp [BuildNF.buildNF]; exact B.hK
      Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some
      exact List.getElem_mem h0
    exact DownHost.three_le_nk B.hQ B.fam hne hR
  · have h1 := DrvB.regPts_length_le B hr hwt
    rw [DrvB.regPts, DrvB.wlist_length] at h1
    have h2 : ((interiorModel Q).deg ((BuildNF.buildNF (interiorModel Q) Q L E).F
        (interiorModel Q) Q) (reg r) + 1) * γ ≤ 5 * γ :=
      Nat.mul_le_mul_right _ (⋄)
    omega

end

end DrvLM

end Chazelle.Core
