module

public import Chazelle.Core.DownPhaseDrvDLoc
public import Chazelle.Core.RestoreRound

/-!
# Down-phase restoration rounds (D8), part 3: the mathematics of one round

After the region loop of a round on `N = buildNF M Q L E`, the new chords `newL` (pairs of a high
region and the triple found for it, `Restore.NewOK`) are appended to `L`, and every new event code
`2 |L| + q` has a bucket `bk q` with the bucket condition on an arc of its own region (`BktOK`).

* `round_ok`: the list `L ++ L₂` is valid, the buckets are at most `A` (the number of arcs),
  ordered (`codeLe`), and of at most two codes each — the precondition of the splice;
* `round_family`: the normal form of `L ++ L₂` (for any sorted event list) has a family containing
  the old one, with degree `≤ max D (d - 1)`, still `γ`-semigranular, and
  `|L ++ L₂| + 1 ≤ 2 (|L| + 1)`.
-/

namespace Chazelle.Core

namespace DrvD

@[expose] public section

open BuildNF (codeLe wposOf buildNF)
open Restore (FoundOK NewOK newSet highList degOf oldL)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The walk position of end `s` (`0` left, `1` right) of a chord triple. -/
def endPos (t : ℕ × ℕ × ℕ) (s : ℕ) : WPos :=
  if s = 0 then ⟨t.2.1, t.1 + 1⟩ else ⟨t.2.2, t.1 + 1⟩

/-- The default pair of `newL`. -/
abbrev dflt : ℕ × (ℕ × ℕ × ℕ) := (0, 0, 0, 0)

theorem getD_map_snd {newL : List (ℕ × (ℕ × ℕ × ℕ))} (i : ℕ) :
    (newL.map Prod.snd).getD i (0, 0, 0) = (newL.getD i dflt).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases newL[i]? <;> rfl

/-- The positions of the new event codes. -/
theorem wposOf_new {L₂ : List (ℕ × ℕ × ℕ)} {q : ℕ} (_hq : q < 2 * L₂.length) :
    wposOf (L ++ L₂) (2 * L.length + q) = endPos (L₂.getD (q / 2) (0, 0, 0)) (q % 2) := by
  have e2 : (2 * L.length + q) / 2 = L.length + q / 2 := by omega
  have e3 : (2 * L.length + q) % 2 = q % 2 := by omega
  have hg : (L ++ L₂).getD (L.length + q / 2) (0, 0, 0) = L₂.getD (q / 2) (0, 0, 0) := by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  unfold wposOf endPos
  rw [e3, e2]
  simp only [BuildRegions.crec, hg]
  split_ifs <;> rfl

/-- **The buckets of the new events** written by the region loop: for every new code `q` the
bucket condition of its position, on an arc of the region of its chord. -/
structure BktOK (M : Model) (Q : Polygon) (N : NF) (newL : List (ℕ × (ℕ × ℕ × ℕ)))
    (bk : ℕ → ℕ) : Prop where
  key : ∀ q, q < 2 * newL.length →
    BktKey M Q N (M.key Q (endPos (newL.getD (q / 2) dflt).2 (q % 2))) (bk q)
  arc : ∀ q, q < 2 * newL.length →
    arcOfB N.arcs.length (bk q) ∈ (N.region (newL.getD (q / 2) dflt).1).arcs

theorem getD_mem' {newL : List (ℕ × (ℕ × ℕ × ℕ))} {i : ℕ} (hi : i < newL.length) :
    newL.getD i dflt ∈ newL := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- The region records of `buildNF`. -/
theorem region_buildNF {r : ℕ} (hr : r < L.length + 1) :
    (buildNF M Q L E).region r =
      ⟨BuildNF.regArcs M Q L E r, BuildNF.regChords M Q L E r, BuildNF.regWt M Q L E r⟩ := by
  unfold NF.region
  rw [List.getD_eq_getElem?_getD]
  simp [buildNF, hr]

/-- Without chords there are no high regions. -/
theorem newL_nil {reg : ℕ → Set Point} {D : ℕ} {newL : List (ℕ × (ℕ × ℕ × ℕ))}
    (hnew : NewOK M Q (buildNF M Q L E) reg D newL) (hK : L.length = 0) : newL = [] := by
  rcases newL with _ | ⟨p, newL⟩
  · rfl
  · exfalso
    have hp : p.1 ∈ (p :: newL).map Prod.fst := by simp
    rw [hnew.fst, Restore.mem_highList] at hp
    have hr : p.1 < L.length + 1 := by
      have := hp.1; simpa [NF.nRegions, buildNF] using this
    have h0 : degOf (buildNF M Q L E) p.1 = 0 := by
      unfold degOf
      rw [region_buildNF hr]
      simp [BuildNF.regChords, hK]
    omega

/-- **The precondition of the splice after the region loop of a round.** -/
theorem round_ok (hGM : GoodModel M) (hok : ChordTriplesOK M Q L)
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M Q L))
    {reg : ℕ → Set Point} (hregs : Restore.NFRegs M Q (buildNF M Q L E) reg) {D : ℕ}
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} (hnew : NewOK M Q (buildNF M Q L E) reg D newL)
    {bk : ℕ → ℕ} (hbk : BktOK M Q (buildNF M Q L E) newL bk) :
    ChordTriplesOK M Q (L ++ newL.map Prod.snd) ∧
    (∀ q, q < 2 * (newL.map Prod.snd).length → bk q ≤ (buildNF M Q L E).arcs.length) ∧
    (∀ q q', q < 2 * (newL.map Prod.snd).length → q' < 2 * (newL.map Prod.snd).length →
      bk q < bk q' →
      codeLe M Q (L ++ newL.map Prod.snd) (2 * L.length + q) (2 * L.length + q')) ∧
    (∀ b, DrvR.bcnt bk (2 * (newL.map Prod.snd).length) b ≤ 2) := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨hNF, hmap, -⟩ := BuildNF.isNF_goodModel hGM hok hperm hsort
  have holdL : oldL (buildNF M Q L E) = L := hmap
  have hok' : ChordTriplesOK M Q (L ++ newL.map Prod.snd) := by
    have := Restore.round_list_ok hM hNF hregs hnew
    rwa [holdL] at this
  rw [List.length_map]
  have hkey : ∀ q, q < 2 * newL.length →
      M.key Q (wposOf (L ++ newL.map Prod.snd) (2 * L.length + q)) =
        M.key Q (endPos (newL.getD (q / 2) dflt).2 (q % 2)) := by
    intro q hq
    rw [wposOf_new (by rwa [List.length_map]), getD_map_snd]
  refine ⟨hok', fun q hq => (hbk.key q hq).le, fun q q' hq hq' hbb => ?_, fun b => ?_⟩
  · rcases Nat.eq_zero_or_pos L.length with hK | hK
    · rw [newL_nil hnew hK] at hq; simp at hq
    · have hlen : (L ++ newL.map Prod.snd).length = L.length + newL.length := by simp
      refine codeLe_of_bkt hM hok' hK hperm hsort (by omega) (by rw [hlen]; omega) (by omega)
        (by rw [hlen]; omega) ?_ ?_ hbb
      · rw [hkey q hq]; exact hbk.key q hq
      · rw [hkey q' hq']; exact hbk.key q' hq'
  · refine bcnt_le_two fun q q' hq hq' hb hb' => ?_
    have hr : ∀ q, q < 2 * newL.length → (newL.getD (q / 2) dflt).1 < (buildNF M Q L E).nRegions :=
      fun q hq => hnew.lt (getD_mem' (by omega))
    have ha := hbk.arc q hq
    have ha' := hbk.arc q' hq'
    rw [hb] at ha
    rw [hb'] at ha'
    have e1 := ((hregs.2.2.1.2.2.2 _ (hr q hq) _).1 ha).2
    have e2 := ((hregs.2.2.1.2.2.2 _ (hr q' hq') _).1 ha').2
    have hfst : (newL.map Prod.fst)[q / 2]'(by rw [List.length_map]; omega) =
        (newL.map Prod.fst)[q' / 2]'(by rw [List.length_map]; omega) := by
      rw [List.getElem_map, List.getElem_map]
      have g1 : newL[q / 2]'(by omega) = newL.getD (q / 2) dflt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have g2 : newL[q' / 2]'(by omega) = newL.getD (q' / 2) dflt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [g1, g2, ← e1, ← e2]
    exact (hnew.nodup_fst.getElem_inj_iff).1 hfst

/-- **The family after a round.** -/
theorem round_family (hGM : GoodModel M) (hok : ChordTriplesOK M Q L)
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M Q L))
    {reg : ℕ → Set Point} (hregs : Restore.NFRegs M Q (buildNF M Q L E) reg) {D : ℕ}
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} (hnew : NewOK M Q (buildNF M Q L E) reg D newL) {d γ : ℕ}
    (hdeg : M.DegLe ((buildNF M Q L E).F M Q) d)
    (hsg : M.Semigranular ((buildNF M Q L E).F M Q) γ) (E' : List ℕ)
    (hperm' : E'.Perm (List.range (2 * (L ++ newL.map Prod.snd).length)))
    (hsort' : E'.Pairwise (codeLe M Q (L ++ newL.map Prod.snd))) :
    (buildNF M Q L E).F M Q ⊆ (buildNF M Q (L ++ newL.map Prod.snd) E').F M Q ∧
      M.DegLe ((buildNF M Q (L ++ newL.map Prod.snd) E').F M Q) (max D (d - 1)) ∧
      M.Semigranular ((buildNF M Q (L ++ newL.map Prod.snd) E').F M Q) γ ∧
      (L ++ newL.map Prod.snd).length + 1 ≤ 2 * (L.length + 1) := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨hNF, hmap, -⟩ := BuildNF.isNF_goodModel hGM hok hperm hsort
  have holdL : oldL (buildNF M Q L E) = L := hmap
  have hok' : ChordTriplesOK M Q (L ++ newL.map Prod.snd) := by
    have := Restore.round_list_ok hM hNF hregs hnew
    rwa [holdL] at this
  obtain ⟨-, hmap', -⟩ := BuildNF.isNF_goodModel hGM hok' hperm' hsort'
  have hF' : (buildNF M Q (L ++ newL.map Prod.snd) E').F M Q =
      (buildNF M Q L E).F M Q ∪ newSet M Q newL := by
    rw [Gran.F_of_map hmap', ← Restore.round_lset (N := buildNF M Q L E), holdL]
  have hSa : (buildNF M Q L E).F M Q ⊆ M.Adm := hNF.1.2.1
  have hSf : ((buildNF M Q L E).F M Q).Finite := hNF.1.1
  have hdata := Restore.round_data hM hNF hregs hnew
  have hdeg' := Restore.round_degLe hM hSa hSf hdata hdeg (Restore.round_all hNF hregs hnew)
  have hlenNew : newL.length ≤ L.length + 1 := by
    have := congrArg List.length hnew.fst
    rw [List.length_map] at this
    rw [this]
    refine (Restore.highList_length_le _ _ _).trans ?_
    simp [NF.nRegions, buildNF]
  rw [hF']
  refine ⟨Set.subset_union_left, hdeg', Restore.semigranular_mono hM Set.subset_union_left
    (Set.union_subset hSa hdata.adm) (hSf.union hdata.fin) hsg, ?_⟩
  rw [List.length_append, List.length_map]
  omega

end

end DrvD

end Chazelle.Core
