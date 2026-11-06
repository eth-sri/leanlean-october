module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvStopSort5

/-!
# The sweep (WP-D), stage 2: sorting the raw stop records, part 6 (task S)

**`sortTask : SortTask`**: the program `ssSrt` with the constant `κ = 40000`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
open SortL

@[expose] public section

set_option hygiene false in
/-- Register arithmetic with the hypotheses. -/
macro "sshSrt" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only [srA0, srIB, srI, srA, srSB, srJ, srX,
                srP, srT, srS, srD, srE, srV, sr1, sr2, sr3, sr4, sB, sC, aB, gRB, gRC, K0, K1, ALLOC,
                sw, Nat.reduceAdd, ne_eq] at *; omega))

theorem ss_seg_range {m : ℕ → ℕ} {A S : ℕ} (h : ∀ i, i < S → m (A + i) = i) :
    seg m A S = List.range S := by
  unfold seg
  Ξ List.map_congr_left (g := id) (fun i hi => h i (List.mem_range.1 hi)), List.map_id

theorem ss_seg_getD {m : ℕ → ℕ} {A S i : ℕ} (hi : i < S) : (seg m A S).getD i 0 = m (A + i) :=
  seg_getD i hi

theorem ss_clog_mono (S : ℕ) : S * (Nat.clog 2 S + 1) ≤ (S + 1) * (Nat.clog 2 (S + 1) + 1) :=
  Nat.mul_le_mul (⋄) (by have := Nat.clog_mono_right 2 (show S ≤ S + 1 by omega); omega)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **Task S: sort and dedupe the raw stop records.** -/
theorem sortTask : SortTask := by
  refine ⟨ssSrt, 40000, fun sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hrec hRB hroom => ?_⟩
  set S := c.nreg gRC with hSd
  set A := c.nreg ALLOC with hAd
  set RB := c.nreg gRB with hRBd
  set m₀ := c.nmem with hm₀
  set d2 := c.nreg (sw 2) with hd2
  have hY : S * (Nat.clog 2 S + 1) ≤ (S + 1) * (Nat.clog 2 (S + 1) + 1) := ss_clog_mono S
  have hX1 : S + 1 ≤ (S + 1) * (Nat.clog 2 (S + 1) + 1) := Nat.le_mul_of_pos_right _ (⋄)
  have hsc : sortCost 12000 S = 12030 * (S * (Nat.clog 2 S + 1) + 1) := rfl
  rw [Nat.mul_assoc] at hroom ⊢
  generalize hXd : (S + 1) * (Nat.clog 2 (S + 1) + 1) = XX at hY hX1 hroom ⊢
  generalize hYd : S * (Nat.clog 2 S + 1) = Y at hY hsc
  clear hXd hYd
  have hw := hI.hw
  obtain ⟨k0, k1, -, -, -, -, -⟩ := E.hK.fix hI
  have hgw : c.nreg cGW = gW J := E.gw' hI
  obtain ⟨hG, hWh, hwf, ⟨H, hC, -⟩, -, hWm⟩ := E.ctxW' hI
  have hgn : gW J < (chainModel J.whole).W.n := by
    unfold gW; rw [cm_n]; have := tpos_lt J.whole J.m₁; omega
  have h11 : A + 11000 ≤ W := ⋄
  have hcmp : CmpOK P W ssCmp ssBc (SsCtx J d2 RB S A m₀) (ssLe P J m₀ RB S) 12000 :=
    ssCmp_ok hG hWh hwf hC hWm h11 hRB (fun i hi => (hrec i hi).1) hgn
  -- 1. the indices
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, q0₁, qB₁, t₁, m₁, r₁, rr₁, rm₁, o₁⟩ :=
    ssIdx_exec (P := P) hw k1 (⋄)
  have kr₁ : ∀ r, 240000 ≤ r → r < 250000 → r < sw 3000 ∨ sw 3003 < r →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    r₁ r (by unfold ALLOC; omega) (by sshSrt) (by sshSrt) (by sshSrt) (by sshSrt)
  -- 2. the inputs of the sort
  have e₂ := exec_regB (P := P) ssSortIn e₁.wb_right (by
    simp only [ssSortIn, okW, okWI]; exact ⟨trivial, trivial, trivial⟩)
  set c₂ : Config := { c₁ with nreg := regB c₁.nmem ssSortIn c₁.nreg } with hc₂
  have r₂ : ∀ r, r ≠ 30003 → r ≠ 30004 → c₂.nreg r = c₁.nreg r := fun r a b => by
    simp only [hc₂, ssSortIn, regB, regI]; rw [upd_other _ _ _ b, upd_other _ _ _ a]
  have v3 : c₂.nreg 30003 = A := by
    simp only [hc₂, ssSortIn, regB, regI]; rw [upd_other _ _ _ (⊛), upd_same, qB₁]
  have v4 : c₂.nreg 30004 = S := by
    ϴ hc₂, ssSortIn, regB, regI, upd_same
    Ξ upd_other _ _ _ (by ssoSrt), kr₁ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have kr₂ : ∀ r, 240000 ≤ r → r < 250000 → r < sw 3000 ∨ sw 3003 < r →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [r₂ r (⋄) (by omega)]; exact kr₁ r h1 h2 h3
  have A₂ : c₂.nreg ALLOC = A + S := by rw [r₂ ALLOC (by ssoSrt) (by ssoSrt)]; exact a₁
  have ctx₂ : SsCtx J d2 RB S A m₀ c₂ := by
    refine ⟨kr₂ (sw 2) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₂ cGW (⊚ cGW, sw) (by simp [cGW, sw]) (by simp [cGW, sw])).trans hgw,
      kr₂ gRB (by ssoSrt) (by ssoSrt) (by ssoSrt), kr₂ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₂ K0 (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k0, (kr₂ K1 (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k1,
      (r₂ srA0 (by ssoSrt) (by ssoSrt)).trans q0₁, fun a ha => m₁ a ha⟩
  -- 3. the sort
  have hsortroom : c₂.nreg ALLOC + sortCost 12000 (rd c₂ bSort 4) ≤ W := by
    show c₂.nreg ALLOC + sortCost 12000 (c₂.nreg 30004) ≤ W
    Ξ A₂, v4, hsc
    clear * - hroom hY hX1
    omega
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨p1, p2, pperm, ppair⟩, fr₃⟩ :=
    sort_meets (cmp := ssCmp) bSort_not_ssBc 12000 (fun _ _ _ d => SsCtx J d2 RB S A m₀ d)
      (fun _ _ => ssLe P J m₀ RB S) P W c₂ e₂.wb_right
      ⟨ctx₂, hcmp, ssCtx_stable (by rw [A₂]; omega), ssLe_trans, ssLe_total,
        by show c₂.nreg 30003 + c₂.nreg 30004 ≤ c₂.nreg ALLOC; rw [v3, v4, A₂]⟩ hsortroom
  have hk₃' : k₃ ≤ 12030 * (Y + 1) := by
    have : k₃ ≤ sortCost 12000 (c₂.nreg 30004) := hk₃
    rw [v4, hsc] at this; omega
  set SBv := c₃.nreg 30005 with hSBv
  have p1' : A + S ≤ SBv := by have := p1; rw [A₂] at this; exact this
  have p2' : SBv + S ≤ c₃.nreg ALLOC := by have := p2; rw [show rd c₂ bSort 4 = S from v4] at this
                                           exact this
  set L := seg c₃.nmem SBv S with hL
  have hLr : seg c₂.nmem (rd c₂ bSort 3) S = List.range S := by
    Ξ show rd c₂ bSort 3 = A from v3
    exact ss_seg_range (fun i hi => t₁ i hi)
  have pperm' : L.Perm (List.range S) := by
    have := pperm; rw [show rd c₂ bSort 4 = S from v4] at this; rw [hLr] at this; exact this
  have ppair' : L.Pairwise fun a b => ssLe P J m₀ RB S a b = true := by
    have := ppair; rw [show rd c₂ bSort 4 = S from v4] at this; exact this
  have hLm : ∀ x ∈ L, x < S := fun x hx => List.mem_range.1 (pperm'.mem_iff.1 hx)
  have hLlen : L.length = S := Ρ hL, seg_length
  have hLs : L.Pairwise (fun x y => KLe (ssKey P J m₀ RB x) (ssKey P J m₀ RB y)) :=
    ppair'.imp_of_mem fun hx hy h => (ssLe_in (hLm _ hx) (hLm _ hy)).1 h
  -- frame of the sort
  have fb : ∀ r, 240000 ≤ r → r < 250000 → bandOf r ∉ insert bSort ssBc := fun r h1 h2 => by
    rw [band_sw h1 h2]; decide
  have kr₃ : ∀ r, 240000 ≤ r → r < 250000 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    fr₃.1 r (fb r h1 h2) (by unfold ALLOC; omega)
  have hB1 : A + S ≤ c₃.nreg ALLOC := le_trans (Ρ A₂) fr₃.2.2.2.2.2.1
  have hB1' : c₃.nreg ALLOC ≤ A + S + k₃ := by have := fr₃.2.2.2.2.2.2; rw [A₂] at this; exact this
  set B1 := c₃.nreg ALLOC with hB1d
  -- 4. the output arrays
  have e₄ := exec_regB (P := P) ssAllocL e₃.wb_right (ssAllocL_ok c₃.nmem c₃.nreg (by
    rw [kr₃ gRC (by ssoSrt) (by ssoSrt), kr₂ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega))
  set c₄ : Config := { c₃ with nreg := regB c₃.nmem ssAllocL c₃.nreg } with hc₄
  obtain ⟨vSB, vsB, vaB, vAl, vsC, vqJ, vo⟩ := ssAllocL_val c₃.nmem c₃.nreg
  have gS₃ : c₃.nreg gRC = S := by
    Ξ kr₃ gRC (by ssoSrt) (by ssoSrt), kr₂ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt)
  rw [gS₃] at vaB vAl
  have k₄ : ∀ r, r ≠ srSB → r ≠ sB → r ≠ srT → r ≠ aB → r ≠ ALLOC → r ≠ sC → r ≠ srJ →
      c₄.nreg r = c₃.nreg r := vo
  have kr₄ : ∀ r, 240000 ≤ r → r < 250000 → (r < sw 2600 ∨ sw 2602 < r) →
      (r < sw 3000 ∨ sw 3016 < r) → c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [k₄ r (by sshSrt) (by sshSrt) (by sshSrt) (by sshSrt) (by unfold ALLOC; omega) (by sshSrt) (by sshSrt),
      kr₃ r h1 h2, kr₂ r h1 h2 (by sshSrt)]
  have q0₄ : c₄.nreg srA0 = A := by
    rw [k₄ srA0 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      kr₃ srA0 (by ssoSrt) (by ssoSrt), r₂ srA0 (by ssoSrt) (by ssoSrt), q0₁]
  have mA₄ : ∀ a, a < A → c₄.nmem a = m₀ a := fun a ha => by
    show c₃.nmem a = _
    rw [fr₃.2.2.1 a (by rw [A₂]; omega)]; exact m₁ a ha
  have ctx₄ : SsCtx J d2 RB S A m₀ c₄ :=
    ⟨kr₄ (sw 2) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₄ cGW (⊚ cGW, sw) (by simp [cGW, sw]) (by simp [cGW, sw])
        (⊚ cGW, sw)).trans hgw,
      kr₄ gRB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), kr₄ gRC (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt),
      (kr₄ K0 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k0,
      (kr₄ K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans k1, q0₄, mA₄⟩
  have hw₄ := e₄.wb_right
  have I₀ : SsDI P W J d2 RB S A m₀ L SBv B1 c₄ 0 c₄ :=
    { wb := hw₄, qj := vqJ, ctx := ctx₄, sb := vSB, b1 := vsB,
      b2 := by show regB _ _ _ aB = _; rw [vaB]; omega,
      mem := fun _ _ => rfl,
      recs := ⟨[], DInv.start L, vsC, le_rfl, fun h => absurd h (lt_irrefl 0),
        fun i hi => absurd hi (✓), fun i hi => absurd hi (by simp)⟩,
      regs := fun _ _ _ _ => rfl, rr := fun _ _ => rfl, rm := rfl, out := rfl }
  have hLmem : ∀ i, i < S → c₄.nmem (SBv + i) = L.getD i 0 := fun i hi => by
    show c₃.nmem _ = _
    Ξ hL, ss_seg_getD hi
  -- 5. the dedupe pass
  obtain ⟨c₅, k₅, e₅, hk5a, hk5b, I5⟩ := ssDedup_exec hcmp hLlen hLm hLs hLmem p2' hRB
    (⋄) (by omega) I₀
  obtain ⟨w₅, -, -, -, b1₅, b2₅, mem₅, ⟨O, hD, hC₅, hO, -, hst, hax⟩, regs₅, rr₅, rm₅, out₅⟩ := I5
  have A₄ : c₄.nreg ALLOC = B1 + 10 * S := by show regB _ _ _ ALLOC = _; rw [vAl]; omega
  have A₅ : c₅.nreg ALLOC = B1 + 10 * S := by
    rw [regs₅ _ (⌖) (by unfold ALLOC sw; omega) (by unfold ALLOC sC sw; omega), A₄]
  -- registers of the band of the sweep outside the writes, through all steps
  have kr₅ : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → ¬ SoR r → c₅.nreg r = c.nreg r := by
    intro r ho hA hS
    unfold SoR at hS
    simp only [sw] at hS
    have hn : r ≠ sC := by rintro rfl; exact hS (Or.inr (Or.inl (by simp only [sC, sw]; omega)))
    Ξ regs₅ r ho (by simp only [sw]; omega) hn
    by_cases hb : 240000 ≤ r ∧ r < 250000
    · exact kr₄ r hb.1 hb.2 (by simp only [sw]; omega) (by simp only [sw]; omega)
    · have nb : ∀ q, 240000 ≤ q → q < 250000 → r ≠ q := fun q h1 h2 h => hb ⟨h ▸ h1, h ▸ h2⟩
      rw [k₄ r (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt))
          (nb _ (by ssoSrt) (by ssoSrt)) hA (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt)),
        fr₃.1 r (by
          intro h
          simp only [Finset.mem_insert, ssBc, bSign, bLocate, bOQuery, bSort,
            Finset.mem_singleton] at h
          apply ho
          rcases h with h | h | h | h <;> rw [h] <;> decide) hA,
        r₂ r (by intro h; subst h; exact ho (⌖)) (by intro h; subst h; exact ho (by decide)),
        r₁ r hA (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt)) (nb _ (by ssoSrt) (by ssoSrt))
          (nb _ (by ssoSrt) (by ssoSrt))]
  -- memory below the entry allocator
  have mem₅' : ∀ a, a < A → c₅.nmem a = m₀ a := fun a ha => by
    rw [mem₅ a (⋄)]; exact mA₄ a ha
  have hk₁' : k₁ = 5 * S + 6 := hk₁
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ⟨w₅, fun q hq => ?_, ?_,
    fun a ha => ?_, fun a ha => ?_⟩, ⟨fun r hr hrA => ?_, fun r hr => ?_, ?_, ?_, ?_⟩,
    ⟨O, fun i hi => hLm i (hD.sub i hi), hD.inc, fun i hi => ?_, hC₅, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha => mem₅' a ha, fun r h1 h2 h3 => kr₅ r h1 h3 h2⟩⟩
  · ϴ ssSortIn, ssAllocL, List.length_cons, List.length_nil
    clear * - hk₁' hk₃' hk5b hY hX1
    omega
  · unfold IFix at hq
    rw [kr₅ q (not_oracle_sw (⋄) (by omega)) (by unfold ALLOC; omega) (by
      unfold SoR; simp only [sw]; omega)]
    exact hI.hin q (by unfold IFix; omega)
  · rw [A₅]; have := hI.hA; omega
  · rw [mem₅' a (by have := hI.hA; omega)]; exact hI.hm a ha
  · Ξ rm₅
    show c₃.rmem a = _
    Ξ fr₃.2.2.2.1 a (by rw [A₂]; have := hI.hA; omega)
    show c₁.rmem a = _
    rw [rm₁]; exact hI.hrm a ha
  · exact kr₅ r (fun h => hr (oracle_sub h)) hrA (by
      intro h
      apply hr
      unfold SoR at h
      simp only [sw] at h
      exact sw_io (⋄) (by omega))
  · Ξ rr₅ r (fun h => hr (oracle_sub h))
    show c₃.rreg r = _
    rw [fr₃.2.1 r (fun h => hr (by
      have : insert bSort ssBc ⊆ ioBands := ssBc_oracle.trans oracle_sub
      exact this h))]
    show c₁.rreg r = _
    Ξ rr₁
  · rw [out₅]; show c₃.output = _; rw [fr₃.2.2.2.2.1]; show c₁.output = _; rw [o₁]
  · rw [A₅]; omega
  · rw [A₅]; simp only [ssSortIn, ssAllocL, List.length_cons, List.length_nil]
    clear * - hk₁' hB1' hk5a
    omega
  · -- covering
    have hiL : i ∈ L := pperm'.mem_iff.2 (List.mem_range.2 hi)
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hiL
    have hnL : n < L.length := by
      by_contra h; rw [List.getElem?_eq_none (⋄)] at hn; cases hn
    obtain ⟨y, hy, hk⟩ := hD.cov n (⋄) i hn
    exact ⟨y, hy, hk⟩
  · rw [b1₅]; exact hst
  · rw [b2₅]; exact hax
  · rw [b1₅]; omega
  · rw [b1₅, A₅]; omega
  · rw [b2₅]; omega
  · rw [b2₅, A₅]; omega

end

end SweepEv

end Chazelle.Core
