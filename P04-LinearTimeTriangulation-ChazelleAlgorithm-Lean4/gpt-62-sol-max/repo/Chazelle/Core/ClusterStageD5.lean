module

public import Chazelle.Core.ClusterInit

/-!
# WP-I, part 58: stage D — the placement, composed

`stageD`: `POS := μ` everywhere; `INV := FPRE⁻¹` (slot 32); the block sizes and starts
(`bcS`, `pfxS`); the placement scan `placeS`; `DF := 0`. The key of a vertex `v` is
`FPRE[FIRST[v]]`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- **Stage D.** -/
def stageD : Stmt := .seq (fillWith 130074 130011 130011)
  (.seq (block [.copyN 130800 130059, .copyN 130801 130062, .copyN 130802 130014])
  (.seq invStmt (.seq bcS (.seq pfxS (.seq placeS (fillWith 130078 130011 130009))))))

/-- The memory written by stage D. -/
def DMem (g : GV) (a : ℕ) : Prop :=
  (g.base 32 ≤ a ∧ a < g.base 33) ∨ (g.base 42 ≤ a ∧ a < g.base 45) ∨
    (g.base 48 ≤ a ∧ a < g.base 49)

/-- An injective self-map of `[0, N)` is onto. -/
theorem surj_range {N : ℕ} {f : ℕ → ℕ} (hlt : ∀ i, i < N → f i < N)
    (hinj : ∀ i j, i < N → j < N → f i = f j → i = j) : ∀ p, p < N → ∃ i, i < N ∧ f i = p := by
  intro p hp
  have := Finset.surjOn_of_injOn_of_card_le f (s := Finset.range N) (t := Finset.range N)
    (fun i hi => by simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢; exact hlt i hi)
    (fun i hi j hj h => by
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj; exact hinj i j hi hj h) le_rfl
  obtain ⟨i, hi, hfi⟩ := this (by simp [hp] : p ∈ (Finset.range N : Set ℕ))
  simp only [Finset.coe_range, Set.mem_Iio] at hi
  exact ⟨i, hi, hfi⟩

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **Stage D.** -/
theorem stageD_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {lev hl blk : ℕ → ℕ}
    (hpre_lt : ∀ i, i < g.N → c.nmem (g.base 29 + i) < g.N)
    (hpre_inj : ∀ i j, i < g.N → j < g.N → c.nmem (g.base 29 + i) = c.nmem (g.base 29 + j) →
      i = j)
    (hfst_lt : ∀ v, v < g.μ → c.nmem (g.base 0 + v) < g.N)
    (hvf : ∀ v, v < g.μ → c.nmem (g.bV + c.nmem (g.base 0 + v)) = v)
    (hvlt : ∀ i, i < g.N → c.nmem (g.bV + i) < g.μ) (hVA : g.bV + g.N ≤ g.A0)
    (hlev : ∀ v, v < g.μ → c.nmem (g.base 3 + v) = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ) (hhl : ∀ l, l < g.μ → c.nmem (g.base 36 + l) = hl l)
    (hhl1 : ∀ l, l < g.μ → hl l ≤ 1) (hblk : ∀ l, l < g.μ → c.nmem (g.base 35 + l) = blk l)
    (hblt : ∀ l, l < g.μ → hl l ≠ 1 → blk l < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageD c c' k ∧ k ≤ 40 * (g.μ + g.N) + 40 ∧ WordsBounded W c' ∧
      PFr StDRG (DMem g) c c' ∧
      (∀ b, b < g.μ → c'.nmem (g.base 42 + b) = cntLt (blkOf g.μ lev hl blk) g.μ (b + 1)) ∧
      (∀ v, v < g.μ → c'.nmem (g.base 44 + v) = if blkOf g.μ lev hl blk v < g.μ then
        plPos g.μ (blkOf g.μ lev hl blk) (fun v => c.nmem (g.base 29 + c.nmem (g.base 0 + v))) v
        else g.μ) ∧
      (∀ v, v < g.μ → blkOf g.μ lev hl blk v < g.μ → c'.nmem (g.base 43 + plPos g.μ
        (blkOf g.μ lev hl blk) (fun v => c.nmem (g.base 29 + c.nmem (g.base 0 + v))) v) = v) ∧
      (∀ v, v < g.μ → c'.nmem (g.base 48 + v) = 0) := by
  have hU := g.U_ge; have hE := g.END_eq
  have b0 := g.base_eq 0; have b3 := g.base_eq 3; have b29 := g.base_eq 29
  have b32 := g.base_eq 32; have b33 := g.base_eq 33; have b35 := g.base_eq 35
  have b36 := g.base_eq 36; have b42 := g.base_eq 42; have b43 := g.base_eq 43
  have b44 := g.base_eq 44; have b45 := g.base_eq 45; have b48 := g.base_eq 48
  have b49 := g.base_eq 49
  have hA0 : g.A0 = g.base 0 := by omega
  set bo := blkOf g.μ lev hl blk with hbo
  set key : ℕ → ℕ := fun v => c.nmem (g.base 29 + c.nmem (g.base 0 + v)) with hkey
  -- the memory reads survive every step
  have rd : ∀ c' : Config, PFr StDRG (DMem g) c c' →
      (∀ a, a < g.base 32 → c'.nmem a = c.nmem a) ∧
      (∀ a, g.base 33 ≤ a → a < g.base 42 → c'.nmem a = c.nmem a) := fun c' h =>
    ⟨fun a ha => h.2.2.2.2 a (by unfold DMem; omega),
     fun a h1 h2 => h.2.2.2.2 a (by unfold DMem; omega)⟩
  unfold stageD
  -- POS := μ
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 44 (by omega)) hG.rμ hG.rμ (by unfold FillRG; omega) (by unfold FillRG; omega)
    (by unfold FillRG; omega) (by omega) (by omega)
  have f1 : PFr StDRG (DMem g) c c1 := hf1.mono (fun r h => by unfold FillRG at h; unfold StDRG; omega)
    (fun a h => by unfold DMem; omega)
  have hG1 : GR g c1 := hG.frame (fun r hr => f1.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  -- the inversion
  obtain ⟨c2, k2, e2, hk2, hw2, h800, h801, h802, hf2, hm2⟩ : ∃ c2 k2, Exec P W
      (block [.copyN 130800 130059, .copyN 130801 130062, .copyN 130802 130014]) c1 c2 k2 ∧
      k2 = 3 ∧ WordsBounded W c2 ∧ c2.nreg 130800 = g.base 29 ∧ c2.nreg 130801 = g.base 32 ∧
      c2.nreg 130802 = g.N ∧ PFr StDRG (DMem g) c1 c2 ∧ c2.nmem = c1.nmem := by
    have r59 := hG1.rbase 29 (by omega); have r62 := hG1.rbase 32 (by omega); have rN := hG1.rN
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact r59, by config_simp; exact r62, by config_simp; exact rN,
      ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, rfl⟩
    simp only; unfold StDRG at hr
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have f2 := f1.trans hf2
  have hG2 : GR g c2 := hG.frame (fun r hr => f2.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  have rd2 := rd c2 f2
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hinv3⟩ := invStmt_exec (P := P) hw2 hG2.one h800 h801 h802
    (fun i hi => by rw [rd2.1 _ (by omega)]; exact hpre_lt i hi)
    (fun i j hi hj h => hpre_inj i j hi hj (by rwa [rd2.1 _ (by omega), rd2.1 _ (by omega)] at h))
    (by omega) (by omega) (by omega) (by omega)
  have f3 : PFr StDRG (DMem g) c c3 := f2.trans (hf3.mono (fun r h => by
    unfold InvRG at h; unfold StDRG; omega) (fun a h => by unfold DMem; omega))
  have hG3 : GR g c3 := hG.frame (fun r hr => f3.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  have rd3 := rd c3 f3
  set inv : ℕ → ℕ := fun p => c3.nmem (g.base 32 + p) with hinvd
  have hinvpre : ∀ i, i < g.N → inv (c.nmem (g.base 29 + i)) = i := fun i hi => by
    have := hinv3 i hi; rw [rd2.1 _ (by omega)] at this; exact this
  have hsurj := surj_range hpre_lt hpre_inj
  have hinv_lt : ∀ p, p < g.N → inv p < g.N ∧ c.nmem (g.base 29 + inv p) = p := fun p hp => by
    obtain ⟨i, hi, rfl⟩ := hsurj p hp
    rw [hinvpre i hi]; exact ⟨hi, rfl⟩
  -- block sizes and starts
  have hlev3 : ∀ v, v < g.μ → c3.nmem (g.base 3 + v) = lev v := fun v hv => by
    rw [rd3.1 _ (by omega)]; exact hlev v hv
  have hhl3 : ∀ l, l < g.μ → c3.nmem (g.base 36 + l) = hl l := fun l hl' => by
    rw [rd3.2 _ (by omega) (by omega)]; exact hhl l hl'
  have hblk3 : ∀ l, l < g.μ → c3.nmem (g.base 35 + l) = blk l := fun l hl' => by
    rw [rd3.2 _ (by omega) (by omega)]; exact hblk l hl'
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hcnt4⟩ := bcS_exec (P := P) hw3 hG3 hlev3 hlt hhl3 hhl1 hblk3
    hblt hW
  have f4 : PFr StDRG (DMem g) c c4 := f3.trans (hf4.mono (fun r h => h)
    (fun a h => by unfold DMem; omega))
  have hG4 : GR g c4 := hG.frame (fun r hr => f4.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hcnt5⟩ := pfxS_exec (P := P) hw4 hG4 hcnt4 hW
  have f45 : PFr StDRG (fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ) c3 c5 := hf4.trans hf5
  have f5 : PFr StDRG (DMem g) c c5 := f3.trans (f45.mono (fun r h => h)
    (fun a h => by unfold DMem; omega))
  have hG5 : GR g c5 := hG.frame (fun r hr => f5.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  have rd5 := rd c5 f5
  have k35 : ∀ a, (a < g.base 42 ∨ g.base 42 + g.μ ≤ a) → c5.nmem a = c3.nmem a := fun a ha =>
    f45.2.2.2.2 a (by omega)
  -- the placement
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, hI6⟩ := placeS_exec (P := P) hw5 hG5 (inv := inv)
    (vert := fun i => c.nmem (g.bV + i)) (first := fun v => c.nmem (g.base 0 + v)) (key := key)
    (fun p hp => by rw [k35 _ (by omega)])
    (fun p hp => by have := (hinv_lt p hp).1; omega)
    (fun p hp => by have := (hinv_lt p hp).1; rw [rd5.1 _ (by omega)])
    (fun p hp => hvlt _ (hinv_lt p hp).1)
    (fun v hv => by rw [rd5.1 _ (by omega)])
    (fun v hv => by rw [rd5.1 _ (by omega)]; exact hlev v hv) hlt
    (fun l hl' => by rw [rd5.2 _ (by omega) (by omega)]; exact hhl l hl') hhl1
    (fun l hl' => by rw [rd5.2 _ (by omega) (by omega)]; exact hblk l hl') hblt
    (fun v hv => ⟨hpre_lt _ (hfst_lt v hv), hinvpre _ (hfst_lt v hv), hvf v hv⟩)
    (fun p hp h => by
      simp only [hkey]; rw [h]; exact (hinv_lt p hp).2)
    hcnt5 hW
  have f6 : PFr StDRG (DMem g) c c6 := f5.trans (hf6.mono (fun r h => h)
    (fun a h => by unfold PlMem at h; unfold DMem; omega))
  have hG6 : GR g c6 := hG.frame (fun r hr => f6.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  -- DF := 0
  obtain ⟨c7, k7, x7, hk7, hw7, hf7, hz7⟩ := fillWith_exec (P := P) hw6 hG6.one
    (hG6.rbase 48 (by omega)) hG6.rμ hG6.zero (by unfold FillRG; omega) (by unfold FillRG; omega)
    (by unfold FillRG; omega) (by omega) (by omega)
  have f7 : PFr StDRG (DMem g) c c7 := f6.trans (hf7.mono (fun r h => by
    unfold FillRG at h; unfold StDRG; omega) (fun a h => by unfold DMem; omega))
  have k67 : ∀ a, a < g.base 48 → c7.nmem a = c6.nmem a := fun a ha =>
    hf7.2.2.2.2 a (by omega)
  have hnk : ∀ w, w < g.μ → key w < g.N := fun w hw => hpre_lt _ (hfst_lt w hw)
  refine ⟨c7, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + k7))))),
    .seq x1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 x7))))), by omega, hw7, f7,
    fun b hb => ?_, fun v hv => ?_, fun v hv hbv => ?_, fun v hv => hz7 v hv⟩
  · rw [k67 _ (by omega)]; exact hI6.full hnk hb
  · rw [k67 _ (by omega), hI6.pos v hv]
    by_cases h : bo v < g.μ
    · rw [ite_eq_left ⟨h, hnk v hv⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right h, k35 _ (by omega)]
      rw [hf3.2.2.2.2 _ (by omega), hm2]
      exact hz1 v hv
  · have := plPos_lt_μ (key := key) hv hbv
    rw [k67 _ (by omega)]; exact hI6.act v hv hbv (hnk v hv)

end proofs

end

end Chazelle.Core.Cluster
