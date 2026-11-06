module

public import Chazelle.Core.DownPhaseDrvXRamI

/-!
# Down phase, extraction (D6), RAM part 10: the loop over the chord records

`xL P v NR i`: the interior triples of the kept chord records among the first `i`.
`loopS_exec`: after the loop, the triples of all kept records are stored (`ChordListAt`) and the
buckets of their ends (`keyBkt … (endPos …)`); memory below the entry allocator is unchanged.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE keyBkt endPos)

@[expose] public section

/-- The kept chord records among the first `i`. -/
noncomputable def kl (P : Polygon) (v : XV) (NR : NF) (i : ℕ) : List ℕ :=
  (List.range i).filter fun t => decide (kR P v (NR.chord t))

/-- The interior triple of chord record `t`. -/
noncomputable def xT (P : Polygon) (v : XV) (NR : NF) (t : ℕ) : ℕ × ℕ × ℕ :=
  xTriple (Qof P).n v.H v.li v.m v.T v.β (NR.chord t).h (NR.chord t).lp (NR.chord t).rp

/-- **The triples of the kept records** among the first `i`. -/
noncomputable def xL (P : Polygon) (v : XV) (NR : NF) (i : ℕ) : List (ℕ × ℕ × ℕ) :=
  (kl P v NR i).map (xT P v NR)

theorem kl_succ (P : Polygon) (v : XV) (NR : NF) (i : ℕ) :
    kl P v NR (i + 1) = kl P v NR i ++ (if kR P v (NR.chord i) then [i] else []) := by
  unfold kl
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : kR P v (NR.chord i) <;> simp [h]

theorem xL_kept {P : Polygon} {v : XV} {NR : NF} {i : ℕ} (h : kR P v (NR.chord i)) :
    xL P v NR (i + 1) = xL P v NR i ++ [xT P v NR i] := by
  unfold xL; rw [kl_succ, ite_eq_left h, List.map_append]; rfl

theorem xL_not {P : Polygon} {v : XV} {NR : NF} {i : ℕ} (h : ¬ kR P v (NR.chord i)) :
    xL P v NR (i + 1) = xL P v NR i := by
  unfold xL; rw [kl_succ, ite_eq_right h, List.append_nil]

theorem xL_length_le (P : Polygon) (v : XV) (NR : NF) (i : ℕ) : (xL P v NR i).length ≤ i := by
  unfold xL kl
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by rw [List.length_range])

theorem endPos_append {L M : List (ℕ × ℕ × ℕ)} {q : ℕ} (hq : q < 2 * L.length) :
    endPos (L ++ M) q = endPos L q := by
  unfold endPos
  rw [List.getD_append _ _ _ _ (by omega)]

theorem endPos_last_l (L : List (ℕ × ℕ × ℕ)) (x : ℕ × ℕ × ℕ) :
    endPos (L ++ [x]) (2 * L.length) = (recOf x).lpos := by
  unfold endPos
  rw [ite_eq_left (by omega), show 2 * L.length / 2 = L.length by omega,
    List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem endPos_last_r (L : List (ℕ × ℕ × ℕ)) (x : ℕ × ℕ × ℕ) :
    endPos (L ++ [x]) (2 * L.length + 1) = (recOf x).rpos := by
  unfold endPos
  rw [ite_eq_right (by omega), show (2 * L.length + 1) / 2 = L.length by omega,
    List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem stMem_apply (P : Polygon) (v : XV) (N : NF) (mm : ℕ → ℕ) (cnt : ℕ) (c : CRec) (a : ℕ) :
    stMem P v N mm cnt c a =
      if a = v.BkB + 2 * cnt + 1 then keyBkt (Qof P) N (xP P v c.h c.rp)
      else if a = v.BkB + 2 * cnt then keyBkt (Qof P) N (xP P v c.h c.lp)
      else if a = v.LxB + 3 * cnt + 2 then (xP P v c.h c.rp).edge
      else if a = v.LxB + 3 * cnt + 1 then (xP P v c.h c.lp).edge
      else if a = v.LxB + 3 * cnt then c.h else mm a := by
  unfold stMem
  simp only [Machine.upd_apply]

section loop

variable {P : Polygon} {W : ℕ} {v : XV} {N NR : NF} {ras : ℕ → ℕ} {A0 : ℕ} {mem0 : ℕ → ℕ}

set_option maxHeartbeats 8000000 in
/-- **The loop over the chord records.** -/
theorem loopS_exec (E : XE P W v N NR ras A0 mem0) (d : Config) (hw : WordsBounded W d)
    (hmem : ∀ a, a < A0 → d.nmem a = mem0 a) (hg : XG P v d) (h39 : d.nreg 217039 = 0)
    (h40 : d.nreg 217040 = v.CB) (h38 : d.nreg 217038 = 0) (h45 : d.nreg 217045 = v.LxB)
    (h46 : d.nreg 217046 = v.BkB) :
    ∃ d' k, Exec P W loopS d d' k ∧ k ≤ 24002 * v.K + 2 ∧ XG P v d' ∧
      d'.nreg 217038 = (xL P v NR v.K).length ∧ (∀ a, a < A0 → d'.nmem a = mem0 a) ∧
      ChordListAt d'.nmem v.LxB (xL P v NR v.K) ∧
      (∀ q, q < 2 * (xL P v NR v.K).length →
        d'.nmem (v.BkB + q) = keyBkt (Qof P) N (endPos (xL P v NR v.K) q)) ∧
      FrameM Bch d d' := by
  have hLx := E.hLx
  have hBk := E.hBk
  let Inv : ℕ → Config → Prop := fun i c => WordsBounded W c ∧ c.nreg 217039 = i ∧
    c.nreg 217028 = v.K ∧ XG P v c ∧ c.nreg 217040 = v.CB + 5 * i ∧
    c.nreg 217038 = (xL P v NR i).length ∧ c.nreg 217045 = v.LxB + 3 * (xL P v NR i).length ∧
    c.nreg 217046 = v.BkB + 2 * (xL P v NR i).length ∧ (∀ a, a < A0 → c.nmem a = mem0 a) ∧
    ChordListAt c.nmem v.LxB (xL P v NR i) ∧
    (∀ q, q < 2 * (xL P v NR i).length →
      c.nmem (v.BkB + q) = keyBkt (Qof P) N (endPos (xL P v NR i) q)) ∧ FrameM Bch d c
  have hI0 : Inv 0 d := ⟨hw, h39, hg.r28, hg, by simp [h40],
    by simp [h38, xL, kl], by simp [h45, xL, kl], by simp [h46, xL, kl], hmem,
    fun q hq => by simp [xL, kl] at hq, fun q hq => by simp [xL, kl] at hq, FrameM.refl _ _⟩
  obtain ⟨d', k', e', ⟨-, -, -, g', -, c38, -, -, cm, cl, cb, f'⟩, hk'⟩ := DrvR.forLoop (P := P)
    (W := W) (ir := 217039) (nr := 217028) (body := chS) Inv 24000 v.K
    (fun i c hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩)
    (fun i c hi hc => by
      obtain ⟨hwc, c39, c28, cg, c40, c38, c45, c46, cmem, clist, cbkt, cf⟩ := hc
      have hlen := xL_length_le P v NR i
      obtain ⟨c', kc, ec, hkc, b39, b40, bk, bn, bf⟩ := chS_exec E c hwc cmem cg hi hlen c39 c40
        c38 c45 c46
      have cg' : XG P v c' := cg.frameM bf (by decide)
      refine ⟨c', kc, ec, ⟨ec.wb_right, b39, by rw [bf.1 _ (by decide), c28], cg', b40, ?_⟩, hkc⟩
      by_cases hk : kR P v (NR.chord i)
      · obtain ⟨m', d38, d45, d46⟩ := bk hk
        rw [xL_kept hk]
        simp only [List.length_append, List.length_singleton]
        have hK := E.hK
        have hA0 := E.hA0
        refine ⟨d38, d45, d46, fun a ha => ?_, fun q hq => ?_, fun q hq => ?_, cf.trans bf⟩
        · rw [m', stMem_apply]
          split_ifs <;> first | omega | exact cmem a ha
        · rw [m']
          simp only [List.length_append, List.length_singleton] at hq
          rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq' | hq'
          · rw [List.getD_append _ _ _ _ hq']
            obtain ⟨x1, x2, x3⟩ := clist q hq'
            refine ⟨?_, ?_, ?_⟩
            · rw [stMem_apply]; split_ifs <;> first | omega
            · rw [stMem_apply]; split_ifs <;> first | omega
            · rw [stMem_apply]; split_ifs <;> first | omega
          · subst hq'
            rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
            refine ⟨?_, ?_, ?_⟩
            · rw [stMem_apply]; split_ifs <;> first | omega | rfl
            · rw [stMem_apply]; split_ifs <;> first | omega | rfl
            · rw [stMem_apply]; split_ifs <;> first | omega | rfl
        · rw [m']
          by_cases hq' : q < 2 * (xL P v NR i).length
          · rw [endPos_append hq', ← cbkt q hq', stMem_apply]
            split_ifs <;> first | omega
          · rcases (show q = 2 * (xL P v NR i).length ∨ q = 2 * (xL P v NR i).length + 1 by omega)
              with hq'' | hq''
            · subst hq''
              rw [endPos_last_l, stMem_apply]
              split_ifs <;> first | omega | rfl
            · subst hq''
              rw [endPos_last_r, stMem_apply]
              split_ifs <;> first | omega | rfl
      · obtain ⟨m', d38, d45, d46⟩ := bn hk
        rw [xL_not hk]
        exact ⟨d38, d45, d46, fun a ha => by rw [m']; exact cmem a ha, by rw [m']; exact clist,
          fun q hq => by rw [m']; exact cbkt q hq, cf.trans bf⟩)
    hI0 (Nat.zero_le _)
  have hk : k' ≤ 24002 * v.K + 2 := by
    have : v.K - 0 = v.K := Nat.sub_zero _
    rw [this] at hk'; omega
  exact ⟨d', k', e', hk, g', c38, cm, cl, cb, f'⟩

end loop

end

end DrvX

end Chazelle.Core
