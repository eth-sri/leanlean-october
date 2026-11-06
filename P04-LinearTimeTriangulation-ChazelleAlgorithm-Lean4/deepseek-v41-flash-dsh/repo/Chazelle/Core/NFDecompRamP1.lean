module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompRamBfs

/-!
# Tree decomposition (WP-C), part 15: the size pass on the RAM

`p1S_exec`: the size pass leaves in field `7` the fold of `p1` over all `R` search positions
(the component subtree sizes, `p1_full`), starting from the all-ones field.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

section p1ram

variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}

/-- The last instruction of every pass body: `i := i + 1`. -/
theorem incr_exec {c : Config} (hw : WordsBounded W c) (o : c.nreg 60011 = 1) (hW : c.nreg 60020 + 1 ≤ W) :
    ∃ c' k, Exec P W (.instr (.addN 60020 60020 60011)) c c' k ∧ k = 1 ∧ c'.nmem = c.nmem ∧
      Same [60020] c c' ∧ c'.nreg 60020 = c.nreg 60020 + 1 := by
  refine spec_instr (Exec.addN hw _ _ _ (by rw [o]; exact hW)) fun _ => ⟨rfl, rfl, Same.upd1 (✓), ?_⟩
  config_simp; Ξ o

/-- The addition of the size of `r` into its parent's. -/
theorem p1Add_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r q : ℕ} (h40 : c.nreg 60040 = r) (hr : r < R) (hq : q < R)
    (hprg : fv c.nmem A R 3 r = q)
    (hsum : fv c.nmem A R 7 q + fv c.nmem A R 7 r ≤ W) :
    ∃ c' k, Exec P W p1Add c c' k ∧ k = 8 ∧
      c'.nmem = upd c.nmem (A + 12 + 7 * R + q) (fv c.nmem A R 7 q + fv c.nmem A R 7 r) ∧
      Same [60030, 60043, 60044, 60031, 60045] c c' := by
  have b3 := hR.b 3 (⊛); have b7 := hR.b 7 (⊛)
  ϴ' Nat.reduceAdd at b3 b7
  have hq' : c.nmem (A + 12 + 3 * R + r) = q := hprg
  unfold fv at hsum
  unfold p1Add
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b3, b7, h40, hq']; omega)
    | skip
  refine ⟨rfl, ?_, ⟨fun x hx => ?_, rfl, rfl, rfl⟩⟩
  · config_simp; simp only [b3, b7, h40, hq']; unfold fv; Ξ Nat.add_comm (c.nmem _)
  · ϴ' List.mem_cons, List.not_mem_nil, or_false, not_or at hx
    config_simp
    simp only [Machine.upd_other _ _ _ hx.1, Machine.upd_other _ _ _ hx.2.1,
      Machine.upd_other _ _ _ hx.2.2.1, Machine.upd_other _ _ _ hx.2.2.2.1,
      Machine.upd_other _ _ _ hx.2.2.2.2]

/-- **One step of the size pass** realises `p1` on field `7`. -/
theorem p1Body_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {j : ℕ} (h20 : c.nreg 60020 = j) (hj : j < R)
    (hr : fv c.nmem A R 1 (R - 1 - j) < R)
    (hpch : fv c.nmem A R 1 (R - 1 - j) ≠ 0 → fv c.nmem A R 4 (fv c.nmem A R 1 (R - 1 - j)) < R)
    (hprg : fv c.nmem A R 1 (R - 1 - j) ≠ 0 → fv c.nmem A R 3 (fv c.nmem A R 1 (R - 1 - j)) < R)
    (hsum : fv c.nmem A R 1 (R - 1 - j) ≠ 0 →
      fv c.nmem A R 7 (fv c.nmem A R 3 (fv c.nmem A R 1 (R - 1 - j))) +
        fv c.nmem A R 7 (fv c.nmem A R 1 (R - 1 - j)) ≤ W) :
    ∃ c' k, Exec P W p1Body c c' k ∧ k ≤ 25 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      c'.nreg 60020 = j + 1 ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 7 then p1 R (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
          (fv c.nmem A R 7) j u else fv c.nmem A R f u := by
  have b1 := hR.b 1 (⊛); have b4 := hR.b 4 (⊛)
  have b11 := hR.b 11 (⊛)
  simp only [Nat.reduceAdd] at b1 b4 b11
  have z := hR.zero; have o := hR.one; have r1 := hR.rR1
  set r := fv c.nmem A R 1 (R - 1 - j) with hrdef
  have hr' : c.nmem (A + 12 + 1 * R + (R - 1 - j)) = r := rfl
  -- the first block
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [.subN 60039 60019 60020,
      .addN 60030 60101 60039, .loadN 60040 60030]) c c1 k1 ∧ k1 = 3 ∧
      c1 = { c with nreg := upd (upd (upd c.nreg 60039 (R - 1 - j)) 60030
        (A + 12 + 1 * R + (R - 1 - j))) 60040 r } := by
    exec_block
    · config_simp; rw [b1, r1, h20]; omega
    · refine ⟨rfl, ?_⟩
      Ξ b1, r1, h20, hr'
  have s1 : Same [60039, 60030, 60040] c c1 := by
    rw [hc1]; exact ((Same.upd1 (✓)).trans (Same.upd1 (by simp))).trans (Same.upd1 (by simp))
  have m1 : c1.nmem = c.nmem := Ρ hc1
  have hw1 := e1.wb_right
  have hR1 : DRegs A R K CB RB LB c1 := hR.of_same s1 (⊚ Prot)
  have r40 : c1.nreg 60040 = r := by rw [hc1]; config_simp
  unfold p1Body
  -- the middle
  have hmid : ∃ c2 k2, Exec P W (.ifLtN 60010 60040
        (.seq (ldF 60041 4 60040) (.seq (ldF 60042 11 60041) (ifEqN 60042 60011 .skip p1Add)))
        .skip) c1 c2 k2 ∧ k2 ≤ 20 ∧ Same [60041, 60042, 60030, 60043, 60044, 60031, 60045] c1 c2 ∧
      (∀ a, (a < A + 12 ∨ A + 12 + 19 * R ≤ a) → c2.nmem a = c.nmem a) ∧
      ∀ f u, f < 19 → u < R → fv c2.nmem A R f u =
        if f = 7 then p1 R (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
          (fv c.nmem A R 7) j u else fv c.nmem A R f u := by
    by_cases h0 : r = 0
    · have hp1 : p1 R (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
          (fv c.nmem A R 7) j = fv c.nmem A R 7 := by
        unfold p1; rw [← hrdef, ite_eq_right (fun hh => hh.1 h0)]
      refine spec_ifLtN_false (by rw [hR1.zero, r40, h0]; omega) (spec_skip hw1 ?_)
      refine ⟨⋄, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun a _ => by rw [m1], fun f u _ _ => ?_⟩
      rw [hp1, m1]; split_ifs with hf <;> [rw [hf]; rfl]
    · refine spec_ifLtN_true (by rw [hR1.zero, r40]; omega) ?_
      have hpr := hpch h0; have hpg := hprg h0
      obtain ⟨c2, k2, e2, rfl, m2, s2, r41⟩ := ldF_rel (P := P) hw1 60041 4 60040
        (by rw [show fb 4 = 60104 from rfl, hR1.b 4 (⊛), r40]; omega)
      rw [show fb 4 = 60104 from rfl, hR1.b 4 (⊛), r40, m1] at r41
      have hR2 : DRegs A R K CB RB LB c2 := hR1.of_same s2 (⊚ Prot)
      obtain ⟨c3, k3, e3, rfl, m3, s3, r42⟩ := ldF_rel (P := P) e2.wb_right 60042 11 60041
        (by
          rw [show fb 11 = 60111 from rfl, hR2.b 11 (⊛), r41]
          have : fv c.nmem A R 4 r < R := hpr
          unfold fv at this
          omega)
      rw [show fb 11 = 60111 from rfl, hR2.b 11 (⊛), r41, m2, m1] at r42
      have hR3 : DRegs A R K CB RB LB c3 := hR2.of_same s3 (⊚ Prot)
      have s23 : Same [60041, 60042, 60030, 60043, 60044, 60031, 60045] c1 c3 :=
        (s2.mono (✓)).trans (s3.mono (by simp))
      refine spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, 2, e3, ?_⟩⟩
      by_cases hrem : fv c.nmem A R 11 (fv c.nmem A R 4 r) = 1
      · have hp1 : p1 R (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
            (fv c.nmem A R 7) j = fv c.nmem A R 7 := by
          unfold p1; rw [← hrdef, ite_eq_right (fun hh => hh.2 hrem)]
        refine ifEqN_eq (by rw [r42, hR3.one]; exact hrem) (spec_skip e3.wb_right ?_)
        refine ⟨⋄, s23, fun a _ => by rw [m3, m2, m1], fun f u _ _ => ?_⟩
        rw [hp1, m3, m2, m1]; split_ifs with hf <;> [rw [hf]; rfl]
      · have hp1 : p1 R (fv c.nmem A R 1) (fv c.nmem A R 3) (fv c.nmem A R 4) (fv c.nmem A R 11)
            (fv c.nmem A R 7) j = Function.update (fv c.nmem A R 7) (fv c.nmem A R 3 r)
              (fv c.nmem A R 7 (fv c.nmem A R 3 r) + fv c.nmem A R 7 r) := by
          unfold p1; rw [← hrdef, ite_eq_left ⟨h0, hrem⟩]
        refine ifEqN_ne (by rw [r42, hR3.one]; exact hrem) ?_
        obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := p1Add_exec (P := P) e3.wb_right hR3 hAW (r := r)
          (q := fv c.nmem A R 3 r) (by rw [s23.1 _ (✓), r40]) hr hpg
          (Ρ m3, m2, m1) (by rw [m3, m2, m1]; exact hsum h0)
        refine ⟨c4, 8, e4, fun k' hk' => ⟨⋄, s23.trans (s4.mono (by simp)),
          fun a ha => ?_, fun f u hf hu => ?_⟩⟩
        · rw [m4, m3, m2, m1]; exact fv_store_out (⊛) hpg ha
        · Ξ hp1, m4, m3, m2, m1
          have := fv_store (m := c.nmem) (A := A) (R := R) (f := 7) (i := fv c.nmem A R 3 r)
            (v := fv c.nmem A R 7 (fv c.nmem A R 3 r) + fv c.nmem A R 7 r) (g := f) hpg hu
          Ξ this
          by_cases hf7 : f = 7
          · subst hf7
            ϴ true_and, ite_true, Function.update_apply
          · Θ hf7
  obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := hmid
  have hR2 : DRegs A R K CB RB LB c2 := hR1.of_same s2 (⊚ Prot)
  obtain ⟨c3, k3, e3, rfl, m3, s3, r20⟩ := incr_exec (P := P) e2.wb_right hR2.one
    (by rw [s2.1 _ (✓), s1.1 _ (by simp), h20]; omega)
  have s13 : Same [60039, 60030, 60040, 60041, 60042, 60043, 60044, 60031, 60045, 60020] c c3 :=
    ((s1.mono (✓)).trans (s2.mono (by simp))).trans (s3.mono (by simp))
  refine ⟨c3, 3 + (k2 + 1), .seq e1 (.seq e2 e3), ⋄, ?_, by
    rw [r20, s2.1 _ (✓), s1.1 _ (by simp), h20], fun f u hf hu => by rw [m3, hv2 f u hf hu]⟩
  exact DFr.of_same s13 (by simp [Prot]) (fun a ha => Ρ m3, hm2 a ha)

/-- `p1` depends only on the entries it reads. -/
theorem p1_congr {R j u : ℕ} {o o' p p' q q' rm rm' s s' : ℕ → ℕ} (hu : u < R)
    (ho : o (R - 1 - j) = o' (R - 1 - j)) (hp : p (o' (R - 1 - j)) = p' (o' (R - 1 - j)))
    (hq : q (o' (R - 1 - j)) = q' (o' (R - 1 - j)))
    (hrm : o' (R - 1 - j) ≠ 0 → rm (q' (o' (R - 1 - j))) = rm' (q' (o' (R - 1 - j))))
    (hs : ∀ v, v < R → s v = s' v) (hr : o' (R - 1 - j) < R) (hpR : o' (R - 1 - j) ≠ 0 → p' (o' (R - 1 - j)) < R) :
    p1 R o p q rm s j u = p1 R o' p' q' rm' s' j u := by
  unfold p1
  Ξ ho, hp, hq
  by_cases h0 : o' (R - 1 - j) = 0
  · rw [ite_eq_right (fun hh => hh.1 h0), ite_eq_right (fun hh => hh.1 h0)]; exact hs u hu
  · Ξ hrm h0
    split_ifs
    · ϴ Function.update_apply
      Ξ hs _ (hpR h0), hs _ hr
      split_ifs <;> [rfl; exact hs u hu]
    · exact hs u hu

/-- **The size pass**: field `7` ends with the subtree sizes of the components. -/
theorem p1S_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn ord pos prg pch rem : ℕ → ℕ}
    (h : Rooted R K up dn ord pos prg pch)
    (hord : ∀ j, j < R → fv c.nmem A R 1 j = ord j) (hprg : ∀ j, j < R → fv c.nmem A R 3 j = prg j)
    (hpch : ∀ j, j < R → fv c.nmem A R 4 j = pch j) (hrem : ∀ j, j < R → fv c.nmem A R 11 j = rem j)
    (hsize : ∀ j, j < R → fv c.nmem A R 7 j = 1) :
    ∃ c' k, Exec P W p1S c c' k ∧ k ≤ 27 * R + 3 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 7 then sz R prg pch rem u else fv c.nmem A R f u := by
  have hKR : K < R := by have := h.hR; omega
  let S : ℕ → ℕ → ℕ := fun j => (List.range j).foldl (p1 R ord prg pch rem) ones
  -- the values stay below `R`
  have hSle : ∀ j, j ≤ R → ∀ u, u < R → S j u ≤ R := by
    intro j hj u hu
    show ((List.range j).foldl (p1 R ord prg pch rem) ones) u ≤ R
    Ξ p1_fold h hj hu
    have h1 := sz_rec h (rem := rem) hu
    have h2 : sz R prg pch rem u ≤ R := by
      classical
      unfold sz sub
      exact (Finset.card_filter_le _ _).trans (Ρ Finset.card_range)
    have h3 : ∑ c ∈ (kids R prg pch rem u).filter (fun c => R - j ≤ pos c), sz R prg pch rem c ≤
        ∑ c ∈ kids R prg pch rem u, sz R prg pch rem c :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  have hS : ∀ j, S (j + 1) = p1 R ord prg pch rem (S j) j := fun j => by
    ϴ S, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil
  unfold p1S
  refine spec_seq (spec_instr (Exec.constN hw 60020 0 (Nat.zero_le _)) fun hw1 => ?_)
  set c1 := { c with nreg := upd c.nreg 60020 0 } with hc1
  have hf1 : DFr (A + 12) (A + 12 + 19 * R) c c1 :=
    DFr.nreg _ fun r hr _ => by
      unfold Prot at hr; Ξ Machine.upd_other _ _ _ (⋄)
  obtain ⟨c', k, e, ⟨hw', hf', hj', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := p1Body)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ d.nreg 60020 ≤ R ∧
      ∀ f u, f < 19 → u < R → fv d.nmem A R f u = if f = 7 then S (d.nreg 60020) u else fv c.nmem A R f u)
    (fun d => 27 * (R - d.nreg 60020)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, hjd, hvd⟩ htest => by
      have hRd := hR.frame hfd
      Ξ' hRd.rR at htest
      obtain ⟨j, hjdef⟩ : ∃ j, d.nreg 60020 = j := ⟨_, rfl⟩
      Ξ' hjdef at htest hjd
      have hp : R - 1 - j < R := ⋄
      have hv1 : ∀ v, v < R → fv d.nmem A R 1 v = ord v := fun v hv => by
        Ξ hvd 1 v (⊛) hv, ite_eq_right (⊛), hord v hv
      have hv3 : ∀ v, v < R → fv d.nmem A R 3 v = prg v := fun v hv => by
        Ξ hvd 3 v (⊛) hv, ite_eq_right (⊛), hprg v hv
      have hv4 : ∀ v, v < R → fv d.nmem A R 4 v = pch v := fun v hv => by
        Ξ hvd 4 v (⊛) hv, ite_eq_right (⊛), hpch v hv
      have hv11 : ∀ v, v < R → fv d.nmem A R 11 v = rem v := fun v hv => by
        Ξ hvd 11 v (⊛) hv, ite_eq_right (⊛), hrem v hv
      have hv7 : ∀ v, v < R → fv d.nmem A R 7 v = S j v := fun v hv => by
        Ξ hvd 7 v (⊛) hv, ite_eq_left rfl, hjdef
      have hrR := h.ord_lt _ hp
      Ξ' ← hv1 _ hp at hrR
      obtain ⟨d', k', e', hk', hf'', h20', hv''⟩ := p1Body_exec (P := P) hwd hRd hAW hjdef htest hrR
        (fun h0 => by rw [hv1 _ hp] at h0 ⊢; rw [hv4 _ (h.ord_lt _ hp)]; have := h.pch_lt _ (h.ord_lt _ hp) h0; omega)
        (fun h0 => by rw [hv1 _ hp] at h0 ⊢; rw [hv3 _ (h.ord_lt _ hp)]; exact h.prg_lt _ (h.ord_lt _ hp) h0)
        (fun h0 => by
          Ξ' hv1 _ hp at h0 ⊢
          have hr := h.ord_lt _ hp
          Ξ hv3 _ hr, hv7 _ (h.prg_lt _ hr h0), hv7 _ hr
          have := hSle j (⋄) _ (h.prg_lt _ hr h0)
          have := hSle j (⋄) _ hr
          omega)
      have hr := h.ord_lt _ hp
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', ⋄, fun f u hf hu => ?_⟩, by
        rw [h20', hjdef]; omega⟩
      Ξ hv'' f u hf hu, h20', hS j
      split_ifs with h7
      · subst h7
        refine p1_congr hu (hv1 _ hp) (hv3 _ hr) (hv4 _ hr) (fun h0 => hv11 _ ?_) hv7 hr
          (fun h0 => h.prg_lt _ hr h0)
        have := h.pch_lt _ hr h0; omega
      · rw [hvd f u hf hu, ite_eq_right h7])
    ⟨hw1, hf1, by simp only [hc1]; config_simp; omega, fun f u hf hu => by
      simp only [hc1]; config_simp
      split_ifs with h7
      · rw [h7]; exact hsize u hu
      · rfl⟩
  have hR' := hR.frame hf'
  Ξ' hR'.rR at htest
  have hjR : c'.nreg 60020 = R := ⋄
  have h0 : c1.nreg 60020 = 0 := by simp only [hc1]; config_simp
  Ξ' h0 at hk
  refine ⟨c', k, e, ⋄, hw', hf', fun f u hf hu => ?_⟩
  Ξ hv' f u hf hu, hjR
  split_ifs
  · exact p1_full h hu
  · rfl

end p1ram

end

end Chazelle.Core.DecR
