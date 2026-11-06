module

public import Chazelle.Core.ClusterStageD2
public import Chazelle.Core.ClusterPlace

/-!
# WP-I, part 55: stage D2 — the placement scan

`placeS` scans the preorder positions `p < N` and places the tail `v` of the dart `INV[p]` when
`FIRST[v] = INV[p]` (so `p` is the key of `v`) and `v` is not light. The result: the counters
`CNT[b]` are the ends of the blocks, `POS[v] = plPos v` and `ACT[plPos v] = v`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The placement scan.** -/
theorem placeS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {inv vert first lev hl blk key : ℕ → ℕ}
    (hinv : ∀ p, p < g.N → c.nmem (g.base 32 + p) = inv p)
    (hvW : ∀ p, p < g.N → g.bV + inv p < g.A0)
    (hvert : ∀ p, p < g.N → c.nmem (g.bV + inv p) = vert (inv p))
    (hvlt : ∀ p, p < g.N → vert (inv p) < g.μ)
    (hfst : ∀ v, v < g.μ → c.nmem (g.base 0 + v) = first v)
    (hlev : ∀ v, v < g.μ → c.nmem (g.base 3 + v) = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ) (hhl : ∀ l, l < g.μ → c.nmem (g.base 36 + l) = hl l)
    (hhl1 : ∀ l, l < g.μ → hl l ≤ 1) (hblk : ∀ l, l < g.μ → c.nmem (g.base 35 + l) = blk l)
    (hblt : ∀ l, l < g.μ → hl l ≠ 1 → blk l < g.μ)
    (hk1 : ∀ v, v < g.μ → key v < g.N ∧ inv (key v) = first v ∧ vert (first v) = v)
    (hk2 : ∀ p, p < g.N → first (vert (inv p)) = inv p → key (vert (inv p)) = p)
    (hcnt : ∀ b, b < g.μ → c.nmem (g.base 42 + b) = cntLt (blkOf g.μ lev hl blk) g.μ b)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W placeS c c' k ∧ k ≤ 32 * g.N + 4 ∧ WordsBounded W c' ∧
      PFr StDRG (PlMem g) c c' ∧
      PlInv g.μ (blkOf g.μ lev hl blk) key (g.base 42) (g.base 43) (g.base 44) c.nmem g.N
        c'.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have b42 := g.base_eq 42; have b43 := g.base_eq 43
  have b44 := g.base_eq 44; have b45 := g.base_eq 45; have b0 := g.base_eq 0
  have b3 := g.base_eq 3; have b32 := g.base_eq 32; have b35 := g.base_eq 35
  have b36 := g.base_eq 36
  set bo := blkOf g.μ lev hl blk with hbo
  have hinj : ∀ v w, v < g.μ → w < g.μ → key v = key w → v = w := fun v w hv hw h => by
    have h1 := hk1 v hv; have h2 := hk1 w hw
    rw [← h1.2.2, ← h2.2.2, ← h1.2.1, ← h2.2.1, h]
  have hbo_lt : ∀ v, v < g.μ → (bo v < g.μ ↔ hl (lev v) ≠ 1) := fun v hv => by
    simp only [hbo, blkOf]
    split_ifs with h
    · simp [h]
    · simp only [h, ne_eq, not_false_eq_true, iff_true]; exact hblt _ (hlt v hv) h
  unfold placeS
  have e1 := Exec.constN (P := P) hw 130860 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130860 0 }
  have f1 : PFr StDRG (PlMem g) c c1 :=
    ⟨fun r hr => by simp only [c1, Machine.upd_other _ _ _ (show r ≠ 130860 by
        unfold StDRG at hr; omega)], rfl, rfl, rfl, fun a _ => rfl⟩
  have hG1 : GR g c1 := hG.frame (fun r hr => f1.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130860) (rn := 130014) (body := placeBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130860 = j ∧ c'.nreg 130014 = g.N ∧
      PFr StDRG (PlMem g) c c' ∧
      PlInv g.μ bo key (g.base 42) (g.base 43) (g.base 44) c.nmem j c'.nmem)
    g.N 30 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hI3⟩ => by
      have hG3 : GR g c3 := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; unfold StDRG; omega))
      have keep : ∀ a, a < g.base 42 → c3.nmem a = c.nmem a := fun a ha =>
        hf3.2.2.2.2 a (by unfold PlMem; omega)
      set v := vert (inv j) with hv
      have hvμ : v < g.μ := hvlt j hj
      have hlv := hlt v hvμ
      set b := blk (lev v) with hb
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, hi4, hm4⟩ := placeBody_exec (P := P) hw3 hG3
        (gg := inv j) (v := v) (f := first v) (l := lev v) (h := hl (lev v)) (b := b)
        (q := c3.nmem (g.base 42 + b)) hi3 hj
        (by rw [keep _ (by omega)]; exact hinv j hj) (by have := hvW j hj; omega)
        (by have := hvW j hj; rw [keep _ (by omega)]; exact hvert j hj) hvμ
        (by rw [keep _ (by omega)]; exact hfst v hvμ)
        (fun _ => by rw [keep _ (by omega)]; exact hlev v hvμ) (fun _ => hlv)
        (fun _ => by rw [keep _ (by omega)]; exact hhl _ hlv) (fun _ => hhl1 _ hlv)
        (fun _ => by rw [keep _ (by omega)]; exact hblk _ hlv) (fun _ h => hblt _ hlv h)
        (fun _ => rfl) (fun hf hh => by
          have hkv : key v = j := hk2 j hj hf
          have hbv : bo v = b := by simp only [hbo, blkOf, ite_eq_right hh, hb]
          have hbμ : b < g.μ := hblt _ hlv hh
          rw [hI3.cnt b hbμ, ← hbv, ← hkv, ← rk_eq_cB]
          have := rk_lt (bo := bo) (key := key) hvμ
          have := cntLt_succ bo g.μ (bo v); have := cntLt_le bo g.μ (bo v + 1)
          omega) hW
      refine ⟨c4, k4, e4, hk4, hw4, hi4, by
        rwa [hf4.1 _ (by unfold PLRG; omega)],
        hf3.trans (hf4.mono (fun r h => by unfold PLRG at h; unfold StDRG; omega)
          (fun a h => h)), ?_⟩
      rw [hm4]
      split_ifs with hc
      · have hkv : key v = j := hk2 j hj hc.1
        have hbv : bo v = b := by simp only [hbo, blkOf, ite_eq_right hc.2, hb]
        have hbμ : bo v < g.μ := (hbo_lt v hvμ).2 hc.2
        have hq : c3.nmem (g.base 42 + b) = plPos g.μ bo key v := by
          rw [← hbv, hI3.cnt _ hbμ]; unfold plPos; rw [rk_eq_cB, hkv]
        have := hI3.step hinj (by omega) (by omega) hvμ hkv hbμ
        rw [hq, ← hbv]; exact this
      · refine hI3.skip (fun w hw hkw hbw => hc ?_)
        have h1 := hk1 w hw
        have hwv : v = w := by rw [hv, ← hkw, h1.2.1, h1.2.2]
        rw [← hwv] at hbw
        refine ⟨?_, (hbo_lt v hvμ).1 hbw⟩
        rw [hwv, ← h1.2.1, hkw])
    (j₀ := 0) ⟨e1.wb_right, by simp [c1], hG1.rN, f1, PlInv.zero hcnt⟩ (Nat.zero_le _)
  exact ⟨c', 1 + k, .seq e1 e, by omega, hw', hf', hm'⟩

end proofs

end

end Chazelle.Core.Cluster
