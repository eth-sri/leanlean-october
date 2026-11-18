module

public import Chazelle.Core.UpPhase7

/-!
# WP-J up phase, part 8: the normal form of a chain

`nfU`: grade `g < 7`: brute force; `2^(g-1) < len`: Lemma 4.1; otherwise (a short last chain of
grade `g ≥ 7`): coarsen the child's normal form (the entry `2i` of the row of grade `g - 1`).
One exec lemma per case (`nfU_brute`, `nfU_l41`, `nfU_gran`).

Constants: `170037 = 7`; `170019 = 2^(g-1)`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The child's NF, then coarsening. -/
def granU (sG : Stmt) : Stmt := .seq (block [.addN 170034 170014 170035,
  .addN 170034 170034 170020, .loadN 170031 170034]) (granCall sG)

/-- **The normal form of chain `(g, i)`.** -/
def nfU (sB sL sG : Stmt) : Stmt :=
  .ifLtN 170007 170037 (bruteCall sB) (.ifLtN 170019 170017 (l41Call sL) (granU sG))

/-- The bands written by the three packages. -/
def pkgBands : Finset ℕ := bruteBands ∪ l41Bands

theorem not_brute_of {r : ℕ} (h : bandOf r ∉ pkgBands) : bandOf r ∉ bruteBands := fun h' =>
  h (Finset.mem_union_left _ h')

theorem not_l41_of {r : ℕ} (h : bandOf r ∉ pkgBands) : bandOf r ∉ l41Bands := fun h' =>
  h (Finset.mem_union_right _ h')

theorem not_gran_of {r : ℕ} (h : bandOf r ∉ pkgBands) : bandOf r ∉ granBands := fun h' =>
  h (Finset.mem_union_left _ (Finset.mem_union_left _ h'))

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
/-- **Grades below `7`: brute force.** -/
theorem nfU_brute {sB sL sG : Stmt} {κB : ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        (rd c bBrute 1 = 1 ∨ 2 ≤ rd c bBrute 2))
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bBrute 3) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (rd c bBrute 2) 4)
      (fun _ c => κB * (rd c bBrute 1 + 1) ^ 3))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {s len γ g : ℕ} (h07 : c.nreg 170007 = g) (h37 : c.nreg 170037 = 7) (hg : g < 7)
    (h16 : c.nreg 170016 = s) (h17 : c.nreg 170017 = len)
    (h11 : c.nreg 170011 = γ) (hl : 1 ≤ len) (hsl : s + len + 1 ≤ P.n) (hγ : 1 ≤ γ)
    (hlγ : len = 1 ∨ 2 ≤ γ) (hbud : c.nreg ALLOC + κB * (len + 1) ^ 3 ≤ W) :
    ∃ c' k, Exec P W (nfU sB sL sG) c c' k ∧ k ≤ κB * (len + 1) ^ 3 + 5 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N ∧
        IsCanonicalNF (chainModel C) (Qof P) N γ 4) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ pkgBands → ¬ MdRG r → r ≠ 170031 → r ≠ 170034 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ pkgBands → c'.rreg r = c.rreg r) := by
  obtain ⟨c', k, e, hk, hw', a1, a2, hpost, m1, m2, o, fr, frr⟩ :=
    bruteCall_exec hB hG hWh hw h16 h17 h11 hl hsl hγ hlγ hbud
  exact ⟨c', k + 1, .ifLtN_true (by rw [h07, h37]; exact hg) e, by omega, hw', a1, by omega,
    hpost, m1, m2, o, fun r h1 _ h3 _ h5 => fr r (not_brute_of h1) h3 h5,
    fun r h1 => frr r (not_brute_of h1)⟩

set_option maxHeartbeats 16000000 in
/-- **Full chains of grade `≥ 7`: Lemma 4.1.** -/
theorem nfU_l41 {O : OracleIface} {sB sL sG : Stmt} {κL : ℕ}
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem (rd c bL41 0) (c.nreg ALLOC) ∧
        rd c bL41 3 ≤ c.nmem (rd c bL41 0) ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ (rd c bL41 3 - 1) < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bL41 4) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran (rd c bL41 3)) 4)
      (fun _ c => κL * (lemma41Nat (rd c bL41 3) + 1)))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {h s len g : ℕ} (h07 : c.nreg 170007 = g) (h37 : c.nreg 170037 = 7) (h7 : 7 ≤ g)
    (h19 : c.nreg 170019 = 2 ^ (g - 1)) (h05 : c.nreg 170005 = h) (h16 : c.nreg 170016 = s)
    (h17 : c.nreg 170017 = len)
    (hX : (gradeCtx O).holds P c.nmem h (c.nreg ALLOC)) (hgΛ : g ≤ c.nmem h)
    (hsl : s + len + 1 ≤ P.n) (hl1 : 2 ^ (g - 1) < len) (hl2 : len ≤ 2 ^ g)
    (hbud : c.nreg ALLOC + κL * (lemma41Nat g + 1) ≤ W) :
    ∃ c' k, Exec P W (nfU sB sL sG) c c' k ∧ k ≤ κL * (lemma41Nat g + 1) + 8 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran g) 4) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ pkgBands → ¬ MdRG r → r ≠ 170031 → r ≠ 170034 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ pkgBands → c'.rreg r = c.rreg r) := by
  obtain ⟨c', k, e, hk, hw', a1, a2, hpost, m1, m2, o, fr, frr⟩ :=
    l41Call_exec hL hG hWh hw h05 h16 h17 h07 hX hgΛ h7 hsl hl1 hl2 hbud
  exact ⟨c', k + 1 + 2, .ifLtN_false (by rw [h07, h37]; omega)
      (.ifLtN_true (by rw [h19, h17]; exact hl1) e), by omega, hw', a1, by omega,
    hpost, m1, m2, o, fun r h1 _ h3 _ h5 => fr r (not_l41_of h1) h3 h5,
    fun r h1 => frr r (not_l41_of h1)⟩

set_option maxHeartbeats 16000000 in
/-- **Short chains of grade `≥ 7`: coarsen the child's normal form.** The child's NF pointer is
the word `R + q + 1` of the row of grade `g - 1` (`R` in `170014`, `q = 6i` in `170035`). -/
theorem nfU_gran {sB sL sG : Stmt} {κG : ℕ → ℕ}
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bGran 0) ∧
        ∃ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M ∧ GoodModel M ∧
          NFWithin c.nmem (rd c bGran 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
          M.DegLe (N.F M (Qof P)) (rd c bGran 2) ∧
          M.Semigranular (N.F M (Qof P)) (rd c bGran 3))
      (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M →
        NFAt c.nmem (rd c bGran 1) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N' ∧
          N'.F M (Qof P) ⊆ N.F M (Qof P) ∧
          IsCanonicalNF M (Qof P) N' (rd c bGran 3) (rd c bGran 2))
      (fun _ c => κG (rd c bGran 2) *
        (c.nmem (rd c bGran 1) * (Nat.clog 2 (c.nmem (rd c bGran 1)) + 1) + 1)))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {MD B F γ γ0 hp g len R q : ℕ} {C : Chain} {N : NF}
    (h07 : c.nreg 170007 = g) (h37 : c.nreg 170037 = 7) (h7 : 7 ≤ g)
    (h19 : c.nreg 170019 = 2 ^ (g - 1)) (h17 : c.nreg 170017 = len) (hl : len ≤ 2 ^ (g - 1))
    (h14 : c.nreg 170014 = R) (h35 : c.nreg 170035 = q) (hRW : R + q + 1 < W)
    (hF : c.nmem (R + q + 1) = F)
    (hA : c.nreg ALLOC = MD) (h30 : c.nreg 170030 = B)
    (h11 : c.nreg 170011 = γ) (h20 : c.nreg 170020 = 1) (h25 : c.nreg 170025 = 4)
    (h26 : c.nreg 170026 = 6) (h29 : c.nreg 170029 = 0)
    (hd : ChainDescAt c.nmem B (Qof P) (Host.whole P.n) C) (hBh : c.nmem B = hp)
    (hB5 : B + 5 ≤ MD) (hhp : hp + 7 ≤ MD) (hCP : C.P = Qof P) (hCn : C.s + C.m + 1 ≤ P.n)
    (hNW : NFWithin c.nmem F MD N) (hc : IsCanonicalNF (chainModel C) (Qof P) N γ0 4)
    (hγ : γ0 ≤ γ)
    (hbud : MD + 6 + κG 4 * (c.nmem F * (Nat.clog 2 (c.nmem F) + 1) + 1) ≤ W) :
    ∃ c' k, Exec P W (nfU sB sL sG) c c' k ∧
      k ≤ κG 4 * (c.nmem F * (Nat.clog 2 (c.nmem F) + 1) + 1) + 37 ∧
      WordsBounded W c' ∧ MD ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ MD + k ∧
      (∃ N', NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N' ∧
        IsCanonicalNF (chainModel C) (Qof P) N' γ 4) ∧
      (∀ a, a < MD → c'.nmem a = c.nmem a) ∧
      (∀ a, a < MD → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ pkgBands → ¬ MdRG r → r ≠ 170031 → r ≠ 170034 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ pkgBands → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, l34, l31, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 170034 170014 170035, .addN 170034 170034 170020, .loadN 170031 170034])
      c c1 k1 ∧ k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 170034 = R + q + 1 ∧
      c1.nreg 170031 = F ∧ (∀ r, r ≠ 170034 → r ≠ 170031 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h14, h35, h20]); omega)
    refine ⟨rfl, ‹_›, by config_simp; simp only [h14, h35, h20],
      by config_simp; simp only [h14, h35, h20, hF], fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have g1 : ∀ r, r ≠ 170034 → r ≠ 170031 → c1.nreg r = c.nreg r := fr1
  obtain ⟨c', k, e, hk, hw', a1, a2, hpost, m1, m2, o, fr, frr⟩ :=
    granCall_exec (P := P) (C := C) (N := N) (γ0 := γ0) (hp := hp) hGr hG hWh hw1
      (by rw [g1 _ (by rw [hAl]; decide) (by rw [hAl]; decide)]; exact hA)
      (by rw [g1 _ (by decide) (by decide)]; exact h30) l31
      (by rw [g1 _ (by decide) (by decide)]; exact h11)
      (by rw [g1 _ (by decide) (by decide)]; exact h20)
      (by rw [g1 _ (by decide) (by decide)]; exact h25)
      (by rw [g1 _ (by decide) (by decide)]; exact h26)
      (by rw [g1 _ (by decide) (by decide)]; exact h29)
      (by rw [hm1]; exact hd) (by rw [hm1]; exact hBh) hB5 hhp hCP hCn
      (by rw [hm1]; exact hNW) hc hγ (by rw [hm1]; exact hbud)
  rw [hm1] at hk
  refine ⟨c', (k1 + k) + 2 + 2, .ifLtN_false (by rw [h07, h37]; omega)
      (.ifLtN_false (by rw [h19, h17]; omega) (.seq e1 e)), by omega, hw', a1, by omega,
    hpost, fun a ha => by rw [m1 a ha, hm1], fun a ha => by rw [m2 a ha, hrm1], by rw [o, ho1],
    fun r h1 h2 h3 h4 h5 => ?_, fun r h1 => by rw [frr r (not_gran_of h1), hrr1]⟩
  rw [fr r (not_gran_of h1) h2 h3 h5, g1 r h4 h3]

end proofs

end

end Chazelle.Core.Up
