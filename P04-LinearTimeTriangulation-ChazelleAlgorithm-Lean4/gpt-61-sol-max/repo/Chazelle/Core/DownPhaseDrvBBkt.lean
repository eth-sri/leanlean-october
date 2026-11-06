module

public import Chazelle.Core.DownPhaseDrvBPieces
public import Chazelle.Core.DownPhaseDrvBFam
public import Chazelle.Core.DownPhaseDrvDRMath
public import Chazelle.Core.DownPhaseDrvDLoc

/-!
# Down-phase base (D9): the bucket mathematics of the region-loop output (`BktMathSpec`)

For the data of the region loop (`BEnv`, `BGood`) and buckets `bk` of the tagged records
`TL (K + 1)`:

* the new chords `newLB` are distinct vertex chords of `Q`, hence at most `2 n`
  (`length_le_of_chords`);
* the buckets are at most the number of arcs (`BktKey.le`) and ordered by the event comparator
  (`DrvD.codeLe_of_bkt`, as in `DrvD.round_ok`);
* the codes of one bucket `b > …` all come from one region (the arc `arcOfB b` lies in a unique
  region), whose records form one block of `TL` of at most `2 |pts r|` records (`TL_countP`,
  `regList_length_le`); hence at most `4 MX` codes (`countP_half`, `countP_range_getD`).

**`bktMath : BktMathSpec`**.
-/

namespace Chazelle.Core

namespace DrvB

open BuildNF (codeLe wposOf)

@[expose] public section

/-! ## Counting -/

/-- Counting the codes `q < 2 m` by the index `q / 2`. -/
theorem countP_half (P : ℕ → Bool) (m : ℕ) :
    (List.range (2 * m)).countP (fun q => P (q / 2)) = 2 * (List.range m).countP P := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.countP_append, List.countP_append, ih, List.range_succ, List.countP_append]
    grind

/-- Counting the indices of a list by a predicate on its entries. -/
theorem countP_range_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    (List.range l.length).countP (fun i => p (l.getD i d)) = l.countP p := by
  have e : (List.range l.length).map (fun i => l.getD i d) = l := by
    apply List.ext_getElem (by simp)
    simp_all
  conv_rhs => rw [← e]
  rw [List.countP_map]
  rfl

/-- The tagged records of region `r` among the regions `< s`. -/
theorem TL_countP (E : BEnv) (r s : ℕ) :
    (E.TL s).countP (fun x => decide (x.1 = r)) = if r < s then (E.recs r).length else 0 := by
  induction s with
  | zero => simp [BEnv.TL]
  | succ s ih =>
    rw [E.TL_succ, List.countP_append, ih, List.countP_map]
    by_cases hrs : r = s
    · simp_all
    · have : (List.countP ((fun x : ℕ × (ℕ × ℕ × ℕ) => decide (x.1 = r)) ∘ fun x => (s, x))
          (E.recs s)) = 0 := by
        aesop
      grind

/-- The tags of `TL s` are below `s`. -/
theorem TL_mem_lt (E : BEnv) {s : ℕ} {x : ℕ × (ℕ × ℕ × ℕ)} (hx : x ∈ E.TL s) : x.1 < s := by
  aesop (add simp [BEnv.TL]) (add safe (by omega))

/-- The bucket count as a count over the range. -/
theorem bcnt_eq (bk : ℕ → ℕ) (n b : ℕ) :
    DrvR.bcnt bk n b = (List.range n).countP (fun q => decide (bk q = b)) := by
  unfold DrvR.bcnt DrvR.bfilt
  grind

/-! ## The bucket mathematics -/

/-- **The splice preconditions of the region-loop output.** -/
theorem bktMath : BktMathSpec := by
  intro E hE bk MX hbk hbk0 hMX
  set TLk := E.TL (E.K + 1) with hTLk
  have hnew : newLB E.li E.Q E.L E.E = TLk.map Prod.snd := rfl
  have hlen : (newLB E.li E.Q E.L E.E).length = TLk.length := by simp_all
  rw [hlen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- at most `2 n` new chords
    rw [← hlen, ← hE.hQn]
    apply length_le_of_chords
    · rcases Nat.eq_zero_or_pos E.K with hK | hK
      · rw [newLB_zero _ _ _ hK]; exact (newL0_ok hE.hQ hE.hDH hE.hli).2.1
      · rw [newLB_pos _ _ _ hK]
        have := (newL_ok (hE.ctx hK)).2.1
        grind
    · intro x hx
      rw [newLB_eq_flatMap] at hx
      obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
      have hr' : r < E.K + 1 := List.mem_range.1 hr
      obtain ⟨S, R, hFam, hR⟩ := hE.regOK hr'
      exact (regList_sound hE.hQ hE.hDH hE.hli hFam hR (hE.pts_lt hr') hxr).1
  · -- the buckets are at most the number of arcs
    intro q hq
    rcases Nat.eq_zero_or_pos E.K with hK | hK
    · simp_all
    · exact ((hbk hK).key q hq).le
  · -- the buckets are ordered by the event comparator
    intro q q' hq hq' hbb
    rcases Nat.eq_zero_or_pos E.K with hK | hK
    · simp_all
    · have hB := hbk hK
      have hok' : ChordTriplesOK E.I E.Q (E.L ++ newLB E.li E.Q E.L E.E) := by
        rw [newLB_pos _ _ _ hK]; exact newL_ok (hE.ctx hK)
      have hM : WalkAx E.I := walkAx_interiorModel hE.hQ
      have hkey : ∀ q, q < 2 * TLk.length →
          E.I.key E.Q (wposOf (E.L ++ newLB E.li E.Q E.L E.E) (2 * E.L.length + q)) =
            E.I.key E.Q (DrvD.endPos (TLk.getD (q / 2) DrvD.dflt).2 (q % 2)) := by
        intro q hq
        rw [DrvD.wposOf_new (by rw [hlen]; exact hq), hnew, DrvD.getD_map_snd]
      have hlen' : (E.L ++ newLB E.li E.Q E.L E.E).length = E.L.length + TLk.length := by
        simp_all
      refine DrvD.codeLe_of_bkt hM hok' hK hE.hperm hE.hsort (by omega) (by rw [hlen']; omega)
        (by omega) (by rw [hlen']; omega) ?_ ?_ hbb
      · rw [hkey q hq]; exact hB.key q hq
      · rw [hkey q' hq']; exact hB.key q' hq'
  · -- at most `4 MX` codes per bucket
    intro b
    rcases Nat.eq_zero_or_pos E.K with hK | hK
    · -- one region: all codes
      have h1 : DrvR.bcnt bk (2 * TLk.length) b ≤ 2 * TLk.length := by
        rw [bcnt_eq]
        exact List.countP_le_length.trans (by rw [List.length_range])
      have h2 : TLk.length ≤ 2 * MX := by
        have e : TLk = (E.recs 0).map fun x => (0, x) := by
          rw [hTLk, hK, E.TL_succ]; simp [BEnv.TL]
        rw [e, List.length_map]
        exact (regList_length_le _ _).trans (by simp_all)
      omega
    · have hB := hbk hK
      rw [bcnt_eq]
      by_cases hex : ∃ q, q < 2 * TLk.length ∧ bk q = b
      · obtain ⟨q₀, hq₀, hb₀⟩ := hex
        set r₀ := (TLk.getD (q₀ / 2) DrvD.dflt).1 with hr₀
        have hmem : ∀ i, i < TLk.length → (TLk.getD i DrvD.dflt).1 < E.K + 1 := fun i hi =>
          TL_mem_lt E (s := E.K + 1) (DrvD.getD_mem' hi)
        have hreg : ∀ q, q < 2 * TLk.length → (TLk.getD (q / 2) DrvD.dflt).1 < E.N.nRegions := by
          intro q hq
          rw [hE.nRegions]
          grind
        -- the region of a code of bucket `b`
        have hone : ∀ q, q < 2 * TLk.length → bk q = b → (TLk.getD (q / 2) DrvD.dflt).1 = r₀ := by
          intro q hq hbq
          have ha := hB.arc q hq
          have ha₀ := hB.arc q₀ hq₀
          rw [hbq] at ha
          rw [hb₀] at ha₀
          have e1 := ((hE.hregs.2.2.1.2.2.2 _ (hreg q hq) _).1 ha).2
          have e2 := ((hE.hregs.2.2.1.2.2.2 _ (hreg q₀ hq₀) _).1 ha₀).2
          rw [← e1]; exact e2
        have hr₀K : r₀ < E.K + 1 := hmem _ (by omega)
        calc (List.range (2 * TLk.length)).countP (fun q => decide (bk q = b))
            ≤ (List.range (2 * TLk.length)).countP
                (fun q => decide ((TLk.getD (q / 2) DrvD.dflt).1 = r₀)) := by
              refine List.countP_mono_left fun q hq hbq => ?_
              grind
          _ = 2 * TLk.countP (fun x => decide (x.1 = r₀)) := by
              rw [countP_half (fun i => decide ((TLk.getD i DrvD.dflt).1 = r₀)),
                countP_range_getD TLk DrvD.dflt (fun x => decide (x.1 = r₀))]
          _ = 2 * (E.recs r₀).length := by rw [hTLk, TL_countP, ite_eq_left hr₀K]
          _ ≤ 4 * MX := by
              have := regList_length_le (Q := E.Q) E.li (E.pts r₀)
              have := hMX r₀ hr₀K
              unfold BEnv.recs
              omega
      · push Not at hex
        have : (List.range (2 * TLk.length)).countP (fun q => decide (bk q = b)) = 0 := by
          simp_all
        omega

end

end DrvB

end Chazelle.Core
