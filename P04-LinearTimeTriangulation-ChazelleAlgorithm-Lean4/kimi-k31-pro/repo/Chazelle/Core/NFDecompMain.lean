module

public import Chazelle.Core.NFDecompRamOut
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ConfigTactics

/-!
# Tree decomposition (WP-C), part 23: `DecompSpec`

* `allocS_exec'`: the allocation loop, with the allocator raised by at most the step count;
* `decomp_cost`: the arithmetic of the cost bound;
* `decomp_run`: the whole procedure `decompStmt` on the RAM;
* `decomp : DecompSpec`.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec Relation

@[expose] public section

section helpers

variable {P : Polygon} {W : ℕ}

/-- **The allocation loop**, with the growth of the allocator bounded by the cost. -/
theorem allocS_exec' {c : Config} (hw : WordsBounded W c) (h1 : c.nreg 60011 = 1)
    (hle : c.nreg ALLOC ≤ c.nreg 60086) :
    ∃ c' k, Exec P W allocS c c' k ∧ k ≤ 3 * (c.nreg 60086 - c.nreg ALLOC) + 2 ∧
      c'.nreg ALLOC = c.nreg 60086 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hT := WordsBounded.nreg hw 60086
  obtain ⟨c', k, e, ⟨hw', hle', hr, hm, hrr, hrm, ho⟩, htest, hk, hlb⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 9999) (b := 60086)
    (body := .instr (.addN 9999 9999 60011))
    (fun d => WordsBounded W d ∧ d.nreg 9999 ≤ c.nreg 60086 ∧
      (∀ r, r ≠ 9999 → d.nreg r = c.nreg r) ∧ d.nmem = c.nmem ∧ d.rreg = c.rreg ∧
      d.rmem = c.rmem ∧ d.output = c.output)
    (fun d => 3 * (c.nreg 60086 - d.nreg 9999)) (fun d => d.nreg 9999) (fun d h => h.1)
    (fun d ⟨hwd, hled, hrd, hmd, hrrd, hrmd, hod⟩ ht => by
      have h1d : d.nreg 60011 = 1 := by rwx [hrd _ (by decide)]
      have h86 : d.nreg 60086 = c.nreg 60086 := hrd _ (by decide)
      rw [h86] at ht
      refine spec_instr (Exec.addN hwd _ _ _ (by rwo [h1d])) fun hw2 => ?_
      refine ⟨⟨hw2, by cso, fun r hr => ?_, hmd, hrrd, hrmd, hod⟩, ?_, ?_⟩
      · config_simp; rw [Machine.upd_other _ _ _ hr]; exact hrd r hr
      · config_simp; rwo [h1d]
      · cso)
    ⟨hw, hle, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have h86 : c'.nreg 60086 = c.nreg 60086 := hr _ (by decide)
  rw [h86] at htest
  exact ⟨c', k, e, by ufo ALLOC at hle ⊢, by ufo ALLOC, hlb,
    hr, hm, hrr, hrm, ho⟩

/-- The stages after the allocation do not write the allocator. -/
theorem noWr_stmts : NoWr 9999 initS = true ∧ NoWr 9999 bfsS = true ∧ NoWr 9999 roundsS = true ∧
    NoWr 9999 fcS = true ∧ NoWr 9999 hdrS = true ∧ NoWr 60024 fcS = true := by decide

/-- The sequence table has one entry per arc. -/
theorem seq_length' {M : Model} {Q : Polygon} {N : NF} (h : IsNF M Q N) :
    N.seq.length = N.arcs.length := by
  obtain ⟨_, _, _, _, _, _, _, _, hS, _⟩ := h
  rw [hS.1.length_eq, List.length_range]

/-- The layout (with the length) determines the sequence table. -/
theorem nfAt_seq_eq' {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N')
    (hl : N'.seq.length = N.seq.length) : N'.seq = N.seq :=
  list_ext_getD hl fun t ht => by
    rw [← h.2.2.2.2.2.2.2.2.1 t ht, ← h'.2.2.2.2.2.2.2.2.1 t (by omega)]

/-- `clog` grows by at most one from `K` to `K + 1`. -/
theorem clog_succ_le (K : ℕ) : Nat.clog 2 (K + 1) ≤ Nat.clog 2 K + 1 := by
  apply Nat.clog_le_of_le_pow
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) K
  have h2 : 1 ≤ 2 ^ Nat.clog 2 K := Nat.one_le_two_pow
  rw [pow_succ]
  omega

/-- **The cost of the procedure.** -/
theorem decomp_cost (D K : ℕ) (hD : K = 0 ∨ 1 ≤ D) :
    38 + (3 * (12 + 19 * (K + 1) + 3 * K) + 2) + (11 * (K + 1) + 11) +
      ((42 * D + 16) * (K + 1) + 6) + ((175 * (K + 1) + 45) * (rounds D K + 1) + 5) +
      (17 * K + 3) + 40 ≤ 1000 * (D + 1) * (K * (Nat.clog 2 K + 1) + 1) ∧
    12 + 20 * (K + 1) + 3 * K ≤ 1000 * (D + 1) * (K * (Nat.clog 2 K + 1) + 1) := by
  set L := Nat.clog 2 K with hL
  have hr : rounds D K ≤ D * (L + 1) := by
    rcases hD with h0 | h1
    · subst h0; rw [rounds_zero]; exact Nat.zero_le _
    · exact (rounds_le h1 K).trans (Nat.mul_le_mul_left _ (clog_succ_le K))
  set X := K * (L + 1) + 1 with hX
  have hX1 : K + 1 ≤ X := by
    have : K ≤ K * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hX2 : (K + 1) * (L + 1) ≤ 2 * X := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · subst h0
      have : L = 0 := by rws [hL]
      rws [this, hX]
    · have : L + 1 ≤ K * (L + 1) := Nat.le_mul_of_pos_left _ hpos
      rwo [Nat.add_mul, Nat.one_mul, hX]
  have hR1 : rounds D K + 1 ≤ (D + 1) * (L + 1) := by
    have : D * (L + 1) + 1 ≤ (D + 1) * (L + 1) := by rwo [Nat.add_mul]
    omega
  set Y := (D + 1) * X with hY
  have hXY : X ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : (175 * (K + 1) + 45) * (rounds D K + 1) ≤ 440 * Y := by
    calc (175 * (K + 1) + 45) * (rounds D K + 1) ≤ (220 * (K + 1)) * ((D + 1) * (L + 1)) :=
          Nat.mul_le_mul (by omega) hR1
      _ = 220 * (D + 1) * ((K + 1) * (L + 1)) := by ring
      _ ≤ 220 * (D + 1) * (2 * X) := Nat.mul_le_mul_left _ hX2
      _ = 440 * Y := by rwring [hY]
  have e2 : (42 * D + 16) * (K + 1) ≤ 58 * Y := by
    calc (42 * D + 16) * (K + 1) ≤ (58 * (D + 1)) * X := Nat.mul_le_mul (by omega) hX1
      _ = 58 * Y := by rwring [hY]
  have e4 : 1000 * (D + 1) * X = 1000 * Y := by rwring [hY]
  rw [e4]
  constructor <;> omega

end helpers

section run

variable {P : Polygon} {W : ℕ}

/-- **The procedure on the RAM**: from a normal form `N₀` readable below the allocator at `B`,
whose record tree has degree cap `D`, `decompStmt` writes at the old allocator a copy of `N₀`
with a decomposition of depth `decDepth D K`. -/
theorem decomp_run {c : Config} (hw : WordsBounded W c) {B D : ℕ} {N₀ : NF}
    (hB : c.nreg 60001 = B) (hNW : NFWithin c.nmem B (c.nreg ALLOC) N₀) (hRT : RecTree N₀ D)
    (hroom : c.nreg ALLOC + 12 + 20 * N₀.nRegions + 3 * N₀.nChords ≤ W) :
    ∃ c' k, ∃ σ : RS, Exec P W decompStmt c c' k ∧
      k ≤ 38 + (3 * (12 + 19 * N₀.nRegions + 3 * N₀.nChords) + 2) + (11 * N₀.nRegions + 11) +
        ((42 * D + 16) * N₀.nRegions + 6) +
        ((175 * N₀.nRegions + 45) * (rounds D N₀.nChords + 1) + 5) + (17 * N₀.nChords + 3) + 40 ∧
      Frame {bDecomp} c c' k ∧ c'.nreg 60003 = c.nreg ALLOC ∧
      NFWithin c'.nmem (c.nreg ALLOC) (c'.nreg ALLOC) (withDec N₀ N₀.nChords N₀.nRegions σ) ∧
      IsDecomp (withDec N₀ N₀.nChords N₀.nRegions σ) (decDepth D N₀.nChords) := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := noWr_stmts
  set A := c.nreg ALLOC with hA
  set K := N₀.nChords with hK
  set R := N₀.nRegions with hRdef
  have hN0 := hNW.nfAt
  have hcount : R = K + 1 := hRT.count
  have hKR : K < R := by omega
  have hB9 : B + 9 < A := rb_addr (fun m' hm' => (hNW m' hm').2.2.2.1)
  have hroom' : c.nreg ALLOC + 12 + 20 * N₀.regions.length + 3 * N₀.chords.length ≤ W := hroom
  -- setup
  obtain ⟨c1, k1, e1, hk1, hR1, hA1, h86, hm1, hrr1, hrm1, ho1, hregs1⟩ :=
    setupS_exec (P := P) hw hB (hN0.1 : c.nmem B = K) (hN0.2.2.1 : c.nmem (B + 2) = R) rfl rfl rfl
      (by omega) (by omega)
  -- allocation
  obtain ⟨c2, k2, e2, hk2, hA2, hlb2, hregs2, hm2, hrr2, hrm2, ho2⟩ :=
    allocS_exec' (P := P) e1.wb_right hR1.one (by rwo [h86, hA1])
  have hR2 : DRegs A R K (c.nmem (B + 3)) (c.nmem (B + 5)) (c.nmem (B + 7)) c2 :=
    hR1.of_regs fun r _ hr => hregs2 r hr
  -- initialisation
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hv3, hord3, h13, h15⟩ :=
    initS_exec (P := P) e2.wb_right hR2 (by omega) (by omega)
  have hR3 := hR2.frame hf3
  have hm3 : ∀ a, a < A → c3.nmem a = c.nmem a := fun a ha => by
    rw [hf3.2.2.2.2 a (Or.inl (by omega)), hm2, hm1]
  -- the search
  have hends : ∀ i, i < K → (N₀.chord i).up < R ∧ (N₀.chord i).dn < R ∧
      (N₀.chord i).up ≠ (N₀.chord i).dn :=
    fun i hi => ⟨(hRT.ends_lt i hi).1, (hRT.ends_lt i hi).2, hRT.ends_ne i hi⟩
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hfix4, st, hbinv, henc⟩ :=
    bfsS_exec (P := P) hw3 hR3 (by omega) ((inEnv_of hNW).transport hm3) hends hRT.lists hKR
      hRT.deg (fun j hj => (hv3 j hj).1) hord3
  have hR4 := hR3.frame hf4
  obtain ⟨hroot, hchst, hisdnst⟩ := bfs_rooted hends hRT.lists hcount
    (fun r hr => hRT.conn 0 r (by omega) hr) hbinv
  -- the static fields, read through the truncated views
  have t1 : ∀ j, j < R → tv c4.nmem A R 1 j = st.ord j := fun j hj => by
    rw [tv_lt hj]; exact (henc j hj).1
  have t3 : ∀ j, j < R → tv c4.nmem A R 3 j = st.prg j := fun j hj => by
    rw [tv_lt hj]; exact (henc j hj).2.2.1
  have t4 : ∀ j, j < R → tv c4.nmem A R 4 j = st.pch j := fun j hj => by
    rw [tv_lt hj]; exact (henc j hj).2.2.2.1
  have t5 : ∀ j, j < R → tv c4.nmem A R 5 j = st.isdn j := fun j hj => by
    rw [tv_lt hj]; exact (henc j hj).2.2.2.2.1
  have t6 : ∀ j, j < R → tv c4.nmem A R 6 j = st.chOf j := fun j hj => by
    rw [tv_lt hj]; exact (henc j hj).2.2.2.2.2
  have hRo := Rooted.congr hroot t1 t3 t4
  have hch : ∀ e, e < K → tv c4.nmem A R 6 e < R ∧ tv c4.nmem A R 6 e ≠ 0 ∧
      tv c4.nmem A R 4 (tv c4.nmem A R 6 e) = e := fun e he => by
    obtain ⟨a1, a2, a3⟩ := hchst e he
    rw [t6 e (by omega), t4 _ a1]; exact ⟨a1, a2, a3⟩
  have hisdn : ∀ s, s < R → s ≠ 0 →
      (tv c4.nmem A R 5 s = 1 ↔ (N₀.chord (tv c4.nmem A R 4 s)).dn = s) := fun s hs hs0 => by
    rw [t5 s hs, t4 s hs]; exact hisdnst s hs hs0
  have hdeg : ∀ v, v < R →
      (kids R (tv c4.nmem A R 3) (tv c4.nmem A R 4) rem0 v).card + (if v = 0 then 0 else 1) ≤ D :=
    fun v hv => (kids_deg hRo hRT.lists hRT.nodup hv).trans (hRT.deg v hv)
  have fx : ∀ f j, f < 19 → ¬ BFields f → j < R → fv c4.nmem A R f j = fv c3.nmem A R f j :=
    fun f j hf hb hj => hfix4 f hf hb j hj
  -- the rounds
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hst5, jj, gc, cr, hI, hna⟩ :=
    roundsS_exec (P := P) hw4 hR4 (by omega) hRo hch hdeg (fun _ _ _ _ => rfl)
      (fun u hu => by rw [fx 7 u (by norm_num) (by ufo BFields) hu]; exact (hv3 u hu).2.1)
      (fun u hu => by rw [fx 11 u (by norm_num) (by ufo BFields) hu]; exact (hv3 u hu).2.2.1)
      (fun u hu => by rw [fx 12 u (by norm_num) (by ufo BFields) hu]; exact (hv3 u hu).2.2.2)
      (by rwx [fx 13 0 (by norm_num) (by ufo BFields) (by omega)])
      (by rwx [fx 15 0 (by norm_num) (by ufo BFields) (by omega)])
  have hR5 := hR4.frame hf5
  -- the node table and the header
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, hv6⟩ := fcS_exec (P := P) hw5 hR5 (by omega) hKR
  have hR6 := hR5.frame hf6
  have hB6 : c6.nreg 60001 = B := by
    rw [hf6.1 _ (by ufo Prot) (by decide), hf5.1 _ (by ufo Prot) (by decide),
      hf4.1 _ (by ufo Prot) (by decide), hf3.1 _ (by ufo Prot) (by decide),
      hregs2 _ (by decide), hregs1 _ (Or.inl (by norm_num)) (by decide), hB]
  obtain ⟨c7, k7, e7, hk7, h03, hregs7, hrr7, hrm7, ho7, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
    x10, x11, xo⟩ := hdrS_exec (P := P) hw6 hR6 hB6 hB9 (by omega)
  -- registers and memory through the stages
  have h86' : c1.nreg 60086 = A + 12 + 19 * R + 3 * K := h86
  have hAl2 : c2.nreg ALLOC = A + 12 + 19 * R + 3 * K := by rw [hA2, h86']
  have hAl7 : c7.nreg ALLOC = A + 12 + 19 * R + 3 * K := by
    show c7.nreg 9999 = _
    rw [nreg_of_noWr e7 w5, nreg_of_noWr e6 w4, nreg_of_noWr e5 w3, nreg_of_noWr e4 w2,
      nreg_of_noWr e3 w1]
    exact hAl2
  have h24 : c6.nreg 60024 = c5.nreg 60024 := nreg_of_noWr e6 w6
  have M1' : ∀ a, a < A → c6.nmem a = c.nmem a := fun a ha => by
    rw [hv6 a, ite_eq_right (by omega), hf5.2.2.2.2 a (Or.inl (by omega)),
      hf4.2.2.2.2 a (Or.inl (by omega)), hm3 a ha]
  have M1 : ∀ a, a < A → c7.nmem a = c.nmem a := fun a ha => by
    rw [xo a (Or.inl ha), M1' a ha]
  have M3 : ∀ a, A + 12 ≤ a → a < A + 12 + 19 * R → c7.nmem a = c5.nmem a := fun a h1 h2 => by
    rw [xo a (Or.inr h1), hv6 a, ite_eq_right (by omega)]
  have M4 : ∀ k t, k < K → t < 3 → c7.nmem (A + 12 + 19 * R + 3 * k + t) =
      fv c5.nmem A R (16 + t) k := fun k t hk ht => by
    rw [xo _ (Or.inr (by omega)), hv6, ite_eq_left (by omega)]
    unfold ntv
    rw [show A + 12 + 19 * R + 3 * k + t - (A + 12 + 19 * R) = 3 * k + t by omega,
      show (3 * k + t) % 3 = t by omega, show (3 * k + t) / 3 = k by omega]
  set σ := rsOf c5.nmem A R (c5.nreg 60024) (c5.nreg 60023) with hσ
  have hD : K = 0 ∨ 1 ≤ D := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · exact Or.inl h0
    · right
      have hu := (hRT.ends_lt 0 hpos).1
      have hmem : 0 ∈ (N₀.region (N₀.chord 0).up).chords :=
        (hRT.lists _ hu 0).2 ⟨hpos, Or.inl rfl⟩
      have := hRT.deg _ hu
      have := List.length_pos_of_mem hmem
      omega
  refine ⟨c7, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + k7))))), σ,
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 e7))))), ?_, ?_, h03, ?_, ?_⟩
  · rw [h86', hA1] at hk2
    omega
  · refine ⟨fun r hr hra => ?_, fun r hr => ?_, M1, ?_, ?_, ?_, ?_⟩
    · have hb : r < 60000 ∨ 70000 ≤ r := by
        simp [Finset.mem_singleton, bandOf, bDecomp] at hr
        omega
      rw [hregs7 r (by omega) (by omega) (by omega) (by omega),
        hf6.1 r (by ufo Prot) hra, hf5.1 r (by ufo Prot) hra,
        hf4.1 r (by ufo Prot) hra, hf3.1 r (by ufo Prot) hra, hregs2 r hra,
        hregs1 r (by omega) hra]
    · rw [hrr7, hf6.2.1, hf5.2.1, hf4.2.1, hf3.2.1, hrr2, hrr1]
    · intro a _
      rw [hrm7, hf6.2.2.1, hf5.2.2.1, hf4.2.2.1, hf3.2.2.1, hrm2, hrm1]
    · rw [ho7, hf6.2.2.2.1, hf5.2.2.2.1, hf4.2.2.2.1, hf3.2.2.2.1, ho2, ho1]
    · rwo [hAl7]
    · rw [hAl7]
      have := hlb2
      rw [hAl2, hA1] at this
      omega
  · intro m' hm'
    rw [hAl7] at hm'
    have hmB : NFAt m' B N₀ := hNW m' (fun a ha => (hm' a (by omega)).trans (M1 a ha))
    have eqB : ∀ t, 1 ≤ t → t ≤ 7 → m' (A + t) = c.nmem (B + t) → m' (A + t) = m' (B + t) :=
      fun t _ _ h => by rw [h, hm' (B + t) (by omega), M1 _ (by omega)]
    have e3 := eqB 3 (by norm_num) (by norm_num) (by rw [hm' _ (by omega), x3, M1' _ (by omega)])
    have e4 := eqB 4 (by norm_num) (by norm_num) (by rw [hm' _ (by omega), x4, M1' _ (by omega)])
    have e5 := eqB 5 (by norm_num) (by norm_num) (by rw [hm' _ (by omega), x5, M1' _ (by omega)])
    have e6 := eqB 6 (by norm_num) (by norm_num) (by rw [hm' _ (by omega), x6, M1' _ (by omega)])
    have e7 := eqB 7 (by norm_num) (by norm_num) (by rw [hm' _ (by omega), x7, M1' _ (by omega)])
    have hR0 : 0 < R := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwr [hm' _ (by omega), x0]
    · rw [hm' _ (by omega), x1, M1' _ (by omega)]; exact hN0.2.1
    · rwr [hm' _ (by omega), x2]
    · rwr [hm' _ (by omega), x9, h24]
    · rw [hm' _ (by omega), x11]; simp [withDec]
    · intro i hi; rw [e3]; exact hmB.2.2.2.2.2.1 i hi
    · intro j hj; rw [e4]; exact hmB.2.2.2.2.2.2.1 j hj
    · intro r hr; rw [e5, e7]; exact hmB.2.2.2.2.2.2.2.1 r hr
    · intro j hj; rw [e6]; exact hmB.2.2.2.2.2.2.2.2.1 j hj
    · intro k hk
      have hk' : k < K := by simpa [withDec] using hk
      have hkR : k < R := by omega
      have hx8 : m' (A + 8) = A + 12 + 19 * R := by rw [hm' _ (by omega), x8]
      have hdn : (withDec N₀ K R σ).dnode k = ⟨σ.dpar k, σ.dlo k, σ.dhi k⟩ := by
        simp [withDec, NF.dnode, List.getD_eq_getElem?_getD, hk']
      rw [hdn, hx8]
      refine ⟨?_, ?_, ?_⟩
      · rw [hm' _ (by omega), show A + 12 + 19 * R + 3 * k = A + 12 + 19 * R + 3 * k + 0 by rfl,
          M4 k 0 hk' (by norm_num)]
        show _ = tv c5.nmem A R 16 k
        rw [tv_lt hkR]
      · rw [hm' _ (by omega), M4 k 1 hk' (by norm_num)]
        show _ = tv c5.nmem A R 17 k
        rw [tv_lt hkR]
      · rw [hm' _ (by omega), M4 k 2 hk' (by norm_num)]
        show _ = tv c5.nmem A R 18 k
        rw [tv_lt hkR]
    · intro r hr
      have hr' : r < R := by simpa [withDec] using hr
      have hx10 : m' (A + 10) = A + 12 := by rw [hm' _ (by omega), x10]
      have hlp : (withDec N₀ K R σ).lpar.getD r 0 = σ.lpar r := by
        simp [withDec, List.getD_eq_getElem?_getD, hr']
      clear hr
      have ha2 : A + 12 + r < A + 12 + 19 * R := by
        have : r < 19 * R := by omega
        exact Nat.add_lt_add_left this _
      have ha1 : A + 12 + r < A + 12 + 19 * R + 3 * K := Nat.lt_add_right _ ha2
      have hl : σ.lpar r = fv c5.nmem A R 0 r := tv_lt hr'
      rw [hlp, hx10, hm' (A + 12 + r) ha1, M3 (A + 12 + r) (Nat.le_add_right _ _) ha2, hl]
      unfold fv
      rw [Nat.zero_mul, Nat.add_zero]
  · exact isDecomp_final (N := N₀) rfl rfl hRo hch hisdn hI hna hD

/-- A record tree with a chord has a positive degree cap. -/
theorem recTree_hD {N : NF} {D : ℕ} (hRT : RecTree N D) : N.nChords = 0 ∨ 1 ≤ D := by
  rcases Nat.eq_zero_or_pos N.nChords with h0 | hpos
  · exact Or.inl h0
  · right
    have hu := (hRT.ends_lt 0 hpos).1
    have hmem : 0 ∈ (N.region (N.chord 0).up).chords := (hRT.lists _ hu 0).2 ⟨hpos, Or.inl rfl⟩
    have := hRT.deg _ hu
    have := List.length_pos_of_mem hmem
    omega

/-- **WP-C: the tree decomposition meets `DecompSpec`** (constant `κ = 1000`). -/
theorem decomp : DecompSpec := by
  refine ⟨decompStmt, 1000, ?_⟩
  intro P W c hw ⟨_, _, _, M, N₀, _, hGM, hNW, hNF, hdeg⟩ hroom
  beta_reduce at hroom ⊢
  have hRT : RecTree N₀ (rd c bDecomp 2) := recTree_of hGM hNF hdeg
  have hN0 := hNW.nfAt
  have hKc : c.nmem (rd c bDecomp 1) = N₀.nChords := hN0.1
  have hcount := hRT.count
  obtain ⟨hc1, hc2⟩ := decomp_cost (rd c bDecomp 2) N₀.nChords (recTree_hD hRT)
  rw [hKc] at hroom
  obtain ⟨c', k, σ, e, hk, hF, h03, hNW', hdec⟩ := decomp_run (P := P) hw rfl hNW hRT
    (by rwo [hcount])
  refine ⟨c', k, e, ?_, ?_, hF⟩
  · rw [hKc]
    rw [hcount] at hk
    omega
  · intro M' N _ hN hNF'
    have hch : N₀.chords = N.chords := nfAt_chords_eq' hN hN0
    have har : N₀.arcs = N.arcs := nfAt_arcs_eq' hN hN0
    have hrg : N₀.regions = N.regions := nfAt_regions_eq' hN hN0
    have hsq : N₀.seq = N.seq := nfAt_seq_eq' hN hN0 (by
      rw [seq_length' hNF, seq_length' hNF', har])
    have h3 : rd c' bDecomp 3 = c.nreg ALLOC := h03
    have hnc : N.nChords = N₀.nChords := by unfold NF.nChords; rw [hch]
    refine ⟨withDec N₀ N₀.nChords N₀.nRegions σ, by rw [h3], by rwx [h3], hch, har,
      hrg, hsq, by rwx [hnc]⟩

end run

end

end Chazelle.Core.DecR
