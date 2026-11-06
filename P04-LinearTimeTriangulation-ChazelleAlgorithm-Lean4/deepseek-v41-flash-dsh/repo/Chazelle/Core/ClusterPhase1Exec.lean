module

public import Chazelle.Golf

public import Chazelle.Core.ClusterPhase1

/-!
# WP-I, part 68: the first phase, executed

`phase1_exec`: from the input facts, `phase1` reaches `PostD`, writing only band-13 registers
and memory above `A0`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The first phase.** -/
theorem phase1_exec {c : Config} (hw : WordsBounded W c) {g : GV} (hg : gOf c = g)
    {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} (hpl : M.Planar)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M)
    (hμ : 0 < g.μ) (hμN : g.μ ≤ g.N) (hB2 : c.nreg 130000 + 2 ≤ W)
    (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0) (hk : 1 ≤ g.k)
    (hEND : g.END ≤ W) :
    ∃ c' k, Exec P W phase1 c c' k ∧ k ≤ cost1 g ∧ WordsBounded W c' ∧ GR g c' ∧
      (∀ r, ¬ (130000 ≤ r ∧ r < 131000) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ (∀ a, a < g.A0 → c'.nmem a = c.nmem a) ∧
      ∃ (T : SpanTree M) (a : F → Fin g.N) (ha : ∀ f, M.face (a f) = f)
        (C : CoTree (starTree T a ha)) (R : BTree) (first : Fin g.μ → Fin g.N)
        (preE slot : ℕ → ℕ) (ρ : ℕ), PostD g M T a ha C R first preE slot ρ W c'.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have hLU := g.L_le_U; have hP := g.two_pow_L
  have hL : 0 < g.L := by
    by_contra h0
    have : g.L = 0 := by omega
    rw [this] at hP; simp at hP; omega
  have hk' : 0 < g.k' := by show 0 < min g.k g.μ; omega
  have hkμ : g.k' ≤ g.μ := min_le_right _ _
  have hN : 0 < g.N := by omega
  have b37 := g.base_eq 37; have b38 := g.base_eq 38; have b39 := g.base_eq 39
  have b40 := g.base_eq 40; have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3; have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7; have b24 := g.base_eq 24; have b26 := g.base_eq 26; have b29 := g.base_eq 29
  have b30 := g.base_eq 30; have b32 := g.base_eq 32; have b33 := g.base_eq 33; have b35 := g.base_eq 35; have b36 := g.base_eq 36; have b41 := g.base_eq 41; have b42 := g.base_eq 42; have b45 := g.base_eq 45; have b48 := g.base_eq 48; have b49 := g.base_eq 49
  unfold phase1
  -- setup
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hG1, hr1, hrr1, hrm1, ho1⟩ :=
    setupStmt_exec (P := P) hw hB2 (hg ▸ hEND)
  rw [hg] at hk1 hG1
  -- stage A
  obtain ⟨c2, k2, e2, hk2, hw2, hG2, hf2, T, hA2⟩ := stageA_exec (P := P) hw1 hG1
    (by rw [hm1]; exact hmap) hpl.1 hμ hμN hO hR hV hL hEND
  -- stage B1
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, a, ha, hB3⟩ := stageB1_exec (P := P) hw2 hG2 hA2 hμ hO hR
    hV hEND
  have hG3 : GR g c3 := hG2.frame (fun r hr => hf3.1 r (by unfold GRReg at hr; unfold StBRG; omega))
  have hA3 : AF g M T c3.nmem := hA2.congr ⟨hO, hR, hV⟩ (fun x hx => hf3.2.2.2.2 x (by
    unfold KeepA at hx; omega))
  -- stage B2
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, C, R, preE, slot, hB4⟩ := stageB2_exec (P := P) hw3 hG3 hA3
    hB3 hpl.1 hN hL hO hR hV hEND
  have hG4 : GR g c4 := hG3.frame (fun r hr => hf4.1 r (by unfold GRReg at hr; unfold StBRG; omega))
  have hLU' : g.L * g.U ≥ 0 := Nat.zero_le _
  have hA4 : AF g M T c4.nmem := hA3.congr ⟨hO, hR, hV⟩ (fun x hx => hf4.2.2.2.2 x (by
    unfold KeepA at hx; omega))
  have hB14 : B1F g M T a ha c4.nmem := hB3.congr (fun x h1 h2 => hf4.2.2.2.2 x (by omega))
  -- stage C
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hhalf5, hpow5, ρ, hρ, hlv5, hmin5⟩ := stageC_exec (P := P)
    hw4 hG4 hk' hkμ (lev := fun v => c4.nmem (g.base 3 + v)) (fun v hv => rfl)
    (fun v hv => by have := hA4.lev ⟨v, hv⟩; have := hA4.lev_lt ⟨v, hv⟩; simp_all) hEND
  have hG5 : GR g c5 := hG4.frame (fun r hr => hf5.1 r (by unfold GRReg at hr; unfold StCRG; omega))
  have k45 : ∀ x, ¬ CMem g x → c5.nmem x = c4.nmem x := fun x hx => hf5.2.2.2.2 x hx
  have hA5 : AF g M T c5.nmem := hA4.congr ⟨hO, hR, hV⟩ (fun x hx => k45 x (by
    unfold KeepA at hx; unfold CMem; omega))
  have hB15 : B1F g M T a ha c5.nmem := hB14.congr (fun x h1 h2 => k45 x (by unfold CMem; omega))
  have hB25 : B2F g C R preE slot c5.nmem := hB4.congr (fun x hx => k45 x (by
    unfold CMem; omega))
  have hlev5 : ∀ v, v < g.μ → c5.nmem (g.base 3 + v) = c4.nmem (g.base 3 + v) := fun v hv =>
    k45 _ (by unfold CMem; omega)
  -- stage D
  have hRn := hB25.R_n
  have hpre_lt : ∀ i, i < g.N → c5.nmem (g.base 29 + i) < g.N := fun i hi => by
    rw [hB25.pre i hi, ← hRn]; exact hB25.R_pre.pre_lt hB25.R_ok (by rw [hRn]; exact hi)
  have hpre_inj : ∀ i j, i < g.N → j < g.N → c5.nmem (g.base 29 + i) = c5.nmem (g.base 29 + j) →
      i = j := fun i j hi hj h => by
    rw [hB25.pre i hi, hB25.pre j hj] at h
    exact BTree.PreInv.pre_inj hB25.R_ok hB25.R_pre (by rw [hRn]; exact hi) (by rw [hRn]; exact hj) h
  have hlvx : ∀ l, l < g.μ → LvOK g c5.nmem (g.k' - 1 - ρ) l := hlv5
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, hcnt6, hpos6, hact6, hdf6⟩ := stageD_exec (P := P) hw5 hG5
    (lev := fun v => c5.nmem (g.base 3 + v)) (hl := fun l => c5.nmem (g.base 36 + l))
    (blk := fun l => c5.nmem (g.base 35 + l)) hpre_lt hpre_inj
    (fun v hv => hA5.first_lt v hv) (fun v hv => hA5.first_v v hv)
    (fun i hi => by rw [(hA5.map ⟨i, hi⟩).2.2]; exact (M.vert ⟨i, hi⟩).2) hV
    (fun v hv => rfl) (fun v hv => by have := hA5.lev ⟨v, hv⟩; have := hA5.lev_lt ⟨v, hv⟩; simp_all)
    (fun l hl => rfl)
    (fun l hl => by obtain ⟨-, -, -, h36⟩ := hlvx l hl; rw [h36]; split_ifs <;> omega)
    (fun l hl => rfl)
    (fun l hl hne => by
      obtain ⟨-, -, h35, h36⟩ := hlvx l hl
      rw [h35]
      rw [h36] at hne
      exact shift_div_lt hk' (by omega) hkμ hl) hEND
  have hG6 : GR g c6 := hG5.frame (fun r hr => hf6.1 r (by unfold GRReg at hr; unfold StDRG; omega))
  have k56 : ∀ x, ¬ DMem g x → c6.nmem x = c5.nmem x := fun x hx => hf6.2.2.2.2 x hx
  have hA6 : AF g M T c6.nmem := hA5.congr ⟨hO, hR, hV⟩ (fun x hx => k56 x (by
    unfold KeepA at hx; unfold DMem; omega))
  have hB16 : B1F g M T a ha c6.nmem := hB15.congr (fun x h1 h2 => k56 x (by unfold DMem; omega))
  have hB26 : B2F g C R preE slot c6.nmem := hB25.congr (fun x hx => k56 x (by
    unfold DMem; omega))
  have hlv6 : ∀ l, l < g.μ → LvOK g c6.nmem (g.k' - 1 - ρ) l := fun l hl => by
    obtain ⟨h1, h2, h3, h4⟩ := hlvx l hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [k56 _ (by unfold DMem; omega)]; exact h1
    · rw [k56 _ (by unfold DMem; omega)]; exact h2
    · rw [k56 _ (by unfold DMem; omega)]; exact h3
    · rw [k56 _ (by unfold DMem; omega)]; exact h4
  have hSF := sfacts_of (W := W) hA6 hB16 hB26 hpl hμN hO hV hEND hL
    (fun w hw' => by rw [k56 _ (by unfold DMem; omega)]; exact hhalf5 w hw')
    (fun j hj => by rw [k56 _ (by unfold DMem; omega)]; exact hpow5 j hj) hk' hlv6
  have hbo : ∀ w, w < g.μ → blkOf g.μ (fun v => c5.nmem (g.base 3 + v))
      (fun l => c5.nmem (g.base 36 + l)) (fun l => c5.nmem (g.base 35 + l)) w =
      boOf g c6.nmem w := fun w hw => by
    have hl := hA5.lev_lt ⟨w, hw⟩; have e := hA5.lev ⟨w, hw⟩
    simp only at e
    have hlw : c5.nmem (g.base 3 + w) < g.μ := by rw [e]; exact hl
    simp only [boOf, blkOf]
    rw [k56 (g.base 3 + w) (by unfold DMem; omega), k56 (g.base 36 + c5.nmem (g.base 3 + w))
      (by unfold DMem; omega), k56 (g.base 35 + c5.nmem (g.base 3 + w)) (by unfold DMem; omega)]
  have hkey : ∀ w, w < g.μ → c5.nmem (g.base 29 + c5.nmem (g.base 0 + w)) =
      keyOf' g c6.nmem w := fun w hw => by
    have := hA5.first_lt w hw
    simp only [keyOf']
    rw [k56 (g.base 0 + w) (by unfold DMem; omega), k56 (g.base 29 + c5.nmem (g.base 0 + w))
      (by unfold DMem; omega)]
  have hm06 : ∀ x, x < g.A0 → c6.nmem x = c.nmem x := fun x hx => by
    rw [k56 x (by unfold DMem; omega), k45 x (by unfold CMem; omega),
      hf4.2.2.2.2 x (by omega), hf3.2.2.2.2 x (by omega), hf2.2.2.2.2 x (by unfold WrA; omega), hm1]
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + k6)))),
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6)))), by unfold cost1; omega, hw6, hG6,
    fun r hr => ?_, by rw [hf6.2.1, hf5.2.1, hf4.2.1, hf3.2.1, hf2.2.1, hrr1],
    by rw [hf6.2.2.1, hf5.2.2.1, hf4.2.2.1, hf3.2.2.1, hf2.2.2.1, hrm1],
    by rw [hf6.2.2.2.1, hf5.2.2.2.1, hf4.2.2.2.1, hf3.2.2.2.1, hf2.2.2.2.1, ho1], hm06,
    T, a, ha, C, R, _, preE, slot, ρ, ⟨hSF, hA6.head_le, hlv6, hρ, fun r hr => ?_,
    fun b hb => ?_, fun v hv => ?_, fun v hv hbv => ?_, hdf6, hA6.map,
    fun u hu => ⟨hA6.first_lt u hu, hA6.first_v u hu⟩, hA6.zero⟩⟩
  · rw [hf6.1 r (by unfold StDRG; omega), hf5.1 r (by unfold StCRG; omega),
      hf4.1 r (by unfold StBRG; omega), hf3.1 r (by unfold StBRG; omega),
      hf2.1 r (by unfold StARG; omega), hr1 r (by unfold SetRG; omega)]
  · have h1 : ∀ v, v < g.μ → c6.nmem (g.base 3 + v) % g.k' = c4.nmem (g.base 3 + v) % g.k' :=
      fun v hv => by rw [k56 _ (by unfold DMem; omega), hlev5 v hv]
    rw [cntBelow_congr h1, cntBelow_congr h1]; exact hmin5 r hr
  · rw [hcnt6 b hb]; exact cntLt_congr hbo
  · rw [hpos6 v hv, hbo v hv, plPos_congr hbo hkey hv]
  · have := hact6 v hv (by rw [hbo v hv]; exact hbv)
    rw [plPos_congr hbo hkey hv] at this; exact this

end proofs

end

end Chazelle.Core.Cluster
