module

public import Chazelle.Core.NFDecompRamRound

/-!
# Tree decomposition (WP-C), part 20: the loop of rounds on the RAM

* `rinv_start`: the round invariant at round `0` for any state with nothing removed or pending,
  the root active with the root slot, and no finished leaf;
* `rounds_le_self`: at most `K` rounds;
* `roundsS_exec`: the loop of rounds ends with the round invariant and no active component.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

section start

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}

/-- With nothing removed, the root is the only top. -/
theorem istop_start (h : Rooted R K up dn ord pos prg pch) {rem : ℕ → ℕ}
    (hrem : ∀ e, e < K → rem e = 0) {t : ℕ} (ht : t < R) : IsTop pch rem t ↔ t = 0 := by
  constructor
  · rintro (h0 | h1)
    · exact h0
    · by_contra h0
      have := hrem _ (h.pch_lt t ht h0)
      omega
  · intro h0; exact Or.inl h0

/-- **The invariant at the start**, for any state agreeing with `rs0` where it matters. -/
theorem rinv_start (h : Rooted R K up dn ord pos prg pch) {σ : RS}
    (hrem : ∀ e, e < K → σ.rem e = 0) (hpend : ∀ e, e < K → σ.pend e = 0)
    (hact : σ.act 0 = 1) (hside : σ.side 0 = 2) (hfin : σ.fin = 0)
    (gc : ℕ → Finset ℕ) (cr : ℕ → ℕ) :
    RInv R K D prg pch isdn chOf 0 σ gc cr where
  i0 e he hp := by rw [hpend e he] at hp; omega
  i1 e he hr := by rw [hrem e he] at hr; omega
  i2 e he hr := by rw [hrem e he] at hr; omega
  i3 e he hp := by rw [hpend e he] at hp; omega
  i4 t ht htop _ := by
    rw [istop_start h hrem ht] at htop
    subst htop
    exact Or.inl ⟨hside, rfl, rfl⟩
  i5 t ht htop hact' := by
    rw [istop_start h hrem ht] at htop
    subst htop
    exact absurd hact hact'
  i6 t _ _ _ := by
    refine ⟨?_, Or.inl rfl⟩
    have : sz R prg pch σ.rem t ≤ R := by
      classical
      unfold sz sub
      exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have := h.hR
    simp only [Function.iterate_zero, id]
    omega
  i7 _ := ⟨fun e he => by rw [hrem e he]; omega, hact, hside⟩
  i8 hj := absurd hj (by norm_num)
  i9 := by
    rw [hfin]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht ⟨htop, hact'⟩
    rw [Finset.mem_range] at ht
    rw [istop_start h hrem ht] at htop
    subst htop
    exact hact' hact

/-- At most `K` rounds. -/
theorem rounds_le_self (D K : ℕ) : rounds D K ≤ K := by
  have key : ∀ i, (hstep D)^[i] K + i ≤ K ∨ (hstep D)^[i] K = 0 := by
    intro i
    induction i with
    | zero => left; simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases Nat.eq_zero_or_pos ((hstep D)^[i] K) with h0 | hpos
      · right; rw [h0]; have := hstep_le D 0; omega
      · rcases ih with ih | ih
        · left; have := hstep_lt D _ hpos; omega
        · omega
  have hK : (hstep D)^[K] K = 0 := by
    rcases key K with h | h
    · omega
    · exact h
  exact Nat.find_min' _ hK

end start

section loopram

variable {P : Polygon} {W : ℕ} {A R K D CB RB LB : ℕ}

/-- **The loop of rounds.** -/
theorem roundsS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn pos : ℕ → ℕ} {mB : ℕ → ℕ}
    (h : Rooted R K up dn (tv mB A R 1) pos (tv mB A R 3) (tv mB A R 4))
    (hch : ∀ e, e < K → tv mB A R 6 e < R ∧ tv mB A R 6 e ≠ 0 ∧ tv mB A R 4 (tv mB A R 6 e) = e)
    (hdeg : ∀ v, v < R →
      (kids R (tv mB A R 3) (tv mB A R 4) rem0 v).card + (if v = 0 then 0 else 1) ≤ D)
    (hst : Stat mB c.nmem A R) (h7 : ∀ u, u < R → fv c.nmem A R 7 u = 1)
    (h11 : ∀ u, u < R → fv c.nmem A R 11 u = 0) (h12 : ∀ u, u < R → fv c.nmem A R 12 u = 0)
    (h13 : fv c.nmem A R 13 0 = 1) (h15 : fv c.nmem A R 15 0 = 2) :
    ∃ c' k, Exec P W roundsS c c' k ∧ k ≤ (175 * R + 45) * (rounds D K + 1) + 5 ∧
      WordsBounded W c' ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧ Stat mB c'.nmem A R ∧
      ∃ j gc cr, RInv R K D (tv mB A R 3) (tv mB A R 4) (tv mB A R 5) (tv mB A R 6) j
        (rsOf c'.nmem A R (c'.nreg 60024) (c'.nreg 60023)) gc cr ∧
      ∀ t, t < R → IsTop (tv mB A R 4) (rsOf c'.nmem A R (c'.nreg 60024) (c'.nreg 60023)).rem t →
        (rsOf c'.nmem A R (c'.nreg 60024) (c'.nreg 60023)).act t ≠ 1 := by
  have hKR : K < R := by have := h.hR; omega
  have hR0 : 0 < R := by omega
  have hrK := rounds_le_self D K
  unfold roundsS
  -- the three counters
  have e1 := Exec.constN (P := P) hw 60022 0 (Nat.zero_le _)
  set c1 := { c with nreg := upd c.nreg 60022 0 } with hc1
  have e2 := Exec.constN (P := P) e1.wb_right 60023 0 (Nat.zero_le _)
  set c2 := { c1 with nreg := upd c1.nreg 60023 0 } with hc2
  have e3 := Exec.constN (P := P) e2.wb_right 60024 0 (Nat.zero_le _)
  set c3 := { c2 with nreg := upd c2.nreg 60024 0 } with hc3
  have eB : Exec P W (block [.constN 60022 0, .constN 60023 0, .constN 60024 0]) c c3 3 :=
    .seq e1 (.seq e2 (.seq e3 (.skip e3.wb_right)))
  have hf3 : DFr (A + 12) (A + 12 + 19 * R) c c3 :=
    DFr.nreg _ fun r hr _ => by
      unfold Prot at hr
      simp only [hc2, hc1]
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
  have m3 : c3.nmem = c.nmem := rfl
  have r22 : c3.nreg 60022 = 0 := by simp only [hc3, hc2, hc1]; config_simp
  have r23 : c3.nreg 60023 = 0 := by simp only [hc3, hc2, hc1]; config_simp
  have hI0 : RInv R K D (tv mB A R 3) (tv mB A R 4) (tv mB A R 5) (tv mB A R 6) 0
      (rsOf c3.nmem A R (c3.nreg 60024) (c3.nreg 60023)) (fun _ => ∅) (fun _ => 0) :=
    rinv_start h (fun e he => by
        show tv c3.nmem A R 11 e = 0
        rw [tv_lt (by omega), m3]; exact h11 e (by omega))
      (fun e he => by
        show tv c3.nmem A R 12 e = 0
        rw [tv_lt (by omega), m3]; exact h12 e (by omega))
      (by show tv c3.nmem A R 13 0 = 1; rwa [tv_lt hR0, m3])
      (by show tv c3.nmem A R 15 0 = 2; rwa [tv_lt hR0, m3])
      (by show c3.nreg 60023 = 0; exact r23) _ _
  -- the loop
  obtain ⟨c', k, e, ⟨hw', hf', hst', h7', hjr, j, hjd, gc, cr, hI'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 60023) (b := 60013) (body := roundBody)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ Stat mB d.nmem A R ∧
      (∀ u, u < R → fv d.nmem A R 7 u = 1) ∧ d.nreg 60022 ≤ rounds D K + 1 ∧
      ∃ j, d.nreg 60022 = j ∧ ∃ gc cr, RInv R K D (tv mB A R 3) (tv mB A R 4) (tv mB A R 5)
        (tv mB A R 6) j (rsOf d.nmem A R (d.nreg 60024) (d.nreg 60023)) gc cr)
    (fun d => (175 * R + 45) * (rounds D K + 1 - d.nreg 60022)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, hstd, h7d, hjd, j, hjdef, gc, cr, hId⟩ ht => by
      have hRd := hR.frame hfd
      rw [hRd.rR] at ht
      obtain ⟨t, ht1, ht2, ht3⟩ := (fin_lt_iff h hId).1 ht
      have hjr := le_rounds_of_active h hId ht1 ht2 ht3
      obtain ⟨d', k', e', hk', hw'', hf'', hst'', h7'', hj'', gc', cr', hI''⟩ :=
        roundBody_exec (P := P) hwd hRd hAW h hch hdeg hstd h7d hId hjdef (by omega) ht
      refine ⟨d', k', e', ⟨hw'', hfd.trans hf'', hst'', h7'', by omega, j + 1, hj'', gc', cr',
        hI''⟩, ?_⟩
      rw [hj'', hjdef]
      have : rounds D K + 1 - j = (rounds D K + 1 - (j + 1)) + 1 := by omega
      rw [this, Nat.mul_add]
      omega)
    ⟨e3.wb_right, hf3, by rwa [m3], by rwa [m3], by omega, 0, r22, _, _, hI0⟩
  have hR' := hR.frame hf'
  rw [hR'.rR] at htest
  subst hjd
  refine ⟨c', 3 + k, .seq eB e, ?_, hw', hf', hst', _, gc, cr, hI', fun t ht htop hact => ?_⟩
  · rw [r22] at hk
    have : (175 * R + 45) * (rounds D K + 1 - 0) = (175 * R + 45) * (rounds D K + 1) := by
      rw [Nat.sub_zero]
    omega
  · exact htest ((fin_lt_iff h hI').2 ⟨t, ht, htop, hact⟩)

end loopram

end

end Chazelle.Core.DecR
