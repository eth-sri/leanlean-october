module

public import Chazelle.Core.GranInitA

/-!
# WP-F, init part 14: the second half of the initialisation

`initB = positions; chord ends and counts; top := K, nlive := K, r52 := 0` (`initB_exec`), from
the intermediate state `InitMid`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- `top := K`, `nlive := K`, `r52 := 0`. -/
def finStmt : Stmt := block [.copyN 90050 90010, .copyN 90051 90010, .constN 90052 0]

/-- The second half. -/
def initB : Stmt := .seq posLoop (.seq ndLoop finStmt)

/-- The start edge of position `u`. -/
def edgeOf (N : NF) (u : ℕ) : ℕ := (N.arc (N.seq.getD u 0)).s.edge

/-- The start height code of position `u`. -/
def hgtOf (N : NF) (u : ℕ) : ℕ := (N.arc (N.seq.getD u 0)).s.hgt

/-- Reading an array. -/
def rdArr (m : ℕ → ℕ) (base : ℕ) : ℕ → ℕ := fun i => m (base + i)

/-- The state after the initialisation (layout `dmOf K A R D b0`, `b0` the entry allocator). -/
structure InitEnd (P : Polygon) (W MD NFH D γ : ℕ) (M : Model) (N : NF) (c₀ c : Config) :
    Prop where
  wb : WordsBounded W c
  r00 : c.nreg 90000 = MD
  r01 : c.nreg 90001 = NFH
  r02 : c.nreg 90002 = D
  r03 : c.nreg 90003 = γ
  r10 : c.nreg 90010 = N.nChords
  r13 : c.nreg 90013 = c₀.nmem (NFH + 3)
  r18 : c.nreg 90018 = szOf P (c₀.nmem MD) (c₀.nmem (MD + 3))
  r14 : c.nreg 90014 = γ
  r19 : c.nreg 90019 = 1
  r20 : c.nreg 90020 = 3
  r21 : c.nreg 90021 = 2
  r28 : c.nreg 90028 =
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oList
  r50 : c.nreg 90050 = N.nChords
  r51 : c.nreg 90051 = N.nChords
  r52 : c.nreg 90052 = 0
  bases : Bases c (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC))
  alloc : c₀.nreg ALLOC +
    (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oEnd ≤ c.nreg ALLOC
  live : ∀ u, u < N.nChords → c.nmem (c₀.nreg ALLOC + u) = 1 ∧
    c.nmem (c₀.nreg ALLOC + N.nChords + u) = (N.chord u).up ∧
    c.nmem (c₀.nreg ALLOC + 2 * N.nChords + u) = (N.chord u).dn
  stk : ∀ u, u < (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).cap →
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oStk + u) =
      u
  cls : ∀ x, x < N.nRegions →
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oDeg + x) =
      (N.region x).chords.length ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oWt + x) =
      (N.region x).wt ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oExb + x) =
      c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oEx + D * x ∧
    ∀ t, t < D → c.nmem (c₀.nreg ALLOC +
      (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oEx + D * x + t) =
      (N.region x).chords.getD t 0
  ring : ∀ j, j < N.arcs.length →
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oNxt + j) =
      (if j + 1 < N.arcs.length then j + 1 else 0) ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oPrv + j) =
      (if 0 < j then j - 1 else N.arcs.length - 1) ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oEg + j) =
      bB (decide (c₀.nmem MD = 0)) (edgeOf N j) ∧
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oPz + j) ≤ 1 ∧
    (c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oPz + j) = 1 ↔
      M.counted (edgeOf N j) ∧ M.param (Qof P) ⟨edgeOf N j, hgtOf N j⟩ ≠ 0)
  cnt : ∀ j, j < N.arcs.length →
    c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oCnt + j) =
      cntInit N.nChords
        (rdArr c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D
          (c₀.nreg ALLOC)).oNd0))
        (rdArr c.nmem (c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D
          (c₀.nreg ALLOC)).oNd1)) j
  nd0 : ∀ u, u < N.nChords →
    c.nmem (c₀.nreg ALLOC + 3 * N.nChords + u) < N.arcs.length ∧
    pk M (Qof P) N (c.nmem (c₀.nreg ALLOC + 3 * N.nChords + u)) = M.key (Qof P) (N.chord u).lpos
  nd1 : ∀ u, u < N.nChords →
    c.nmem (c₀.nreg ALLOC + 4 * N.nChords + u) < N.arcs.length ∧
    pk M (Qof P) N (c.nmem (c₀.nreg ALLOC + 4 * N.nChords + u)) = M.key (Qof P) (N.chord u).rpos
  mem : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a

set_option maxHeartbeats 4000000 in
theorem initB_exec {P : Polygon} {W : ℕ} {c c₅ : Config} {MD NFH D γ : ℕ} {M : Model} {N : NF}
    (hI : InitMid P W MD NFH D γ N c c₅) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD) (hMD : ModelDescAt c.nmem MD (Qof P) M)
    (hGM : GoodModel M) (hNW : NFWithin c.nmem NFH (c.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hne : (N.F M (Qof P)).Nonempty)
    (hroom : c₅.nreg ALLOC + N.nChords * (2 * NFLoc.locCost 5100 N.arcs.length + 30) ≤ W) :
    ∃ c' k, Exec P W initB c₅ c' k ∧
      k ≤ 6052 * N.arcs.length + N.nChords * (2 * NFLoc.locCost 5100 N.arcs.length + 32) + 12 ∧
      InitEnd P W MD NFH D γ M N c c' ∧ GF (c.nreg ALLOC) c₅ c' k := by
  set b0 := c.nreg ALLOC with hb0
  set K := N.nChords with hKd
  set A := N.arcs.length with hAd
  set R := N.nRegions with hRd
  set d := dmOf K A R D b0 with hd
  have hdb : d.b0 = b0 := rfl
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have yN0 : d.oNd0 = 3 * d.K := rfl
  have yN1 : d.oNd1 = 4 * d.K := rfl
  have hdK : d.K = K := rfl
  have hdA : d.A = A := rfl
  have hdR : d.R = R := rfl
  have hdD : d.D = D := rfl
  have hN : NFAt c.nmem NFH N := hNW.holds
  obtain ⟨aB, aCh, aRg, aLst, aArc, aSeq⟩ := nf_areas hNW
  have hsl := NFLoc.seq_length hNF
  have hmem5 : ∀ a, a < b0 → c₅.nmem a = c.nmem a := fun a ha => hI.mem a (Or.inl ha)
  have al5 : c₅.nreg ALLOC = b0 + d.oEnd := hI.alloc
  have hbW : d.b0 + d.oEnd ≤ W := by omega
  have hW6 : 6 ≤ W := by unfold hostWords at hWh; omega
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨hdesc₅, hwf₅⟩ := desc_agree' hwf hMD hmem5
  -- 1. the positions
  have hPE : PosEnv P W A MD (c.nmem (NFH + 6)) (c.nmem (NFH + 4)) d M (edgeOf N) (hgtOf N) c₅ :=
    { hG := hG, hW := hWh, hA := rfl, bW := hbW, bases := hI.bases, h11 := hI.r11,
      h15 := hI.r15, h17 := hI.r17, h19 := hI.r19,
      h23 := by rw [hI.r23, hmem5 _ (by have := hwf.1; omega)],
      h50 := hI.l00, wf := hwf₅, desc := hdesc₅,
      arcs := fun u hu => by
        have hs := aSeq u (by omega)
        have ha := NFLoc.seq_lt hNF hu
        have hA4 := aArc _ ha
        have e1 : c₅.nmem (c.nmem (NFH + 6) + u) = N.seq.getD u 0 := by
          rw [hmem5 _ (by omega)]; exact hN.2.2.2.2.2.2.2.2.1 u (by omega)
        obtain ⟨-, s1, s2, -⟩ := hN.2.2.2.2.2.2.1 _ ha
        refine ⟨by omega, by rw [e1]; omega, ?_, ?_⟩
        · rw [e1, hmem5 _ (by omega)]; exact s1
        · rw [e1, hmem5 _ (by omega)]; exact s2
      edge_lt := fun u hu => edge_lt' hNF hne hu
      hgt_le := fun u hu => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := id hNF
        have := (hpp _ (NFLoc.seq_lt hNF hu)).1.2.2
        rw [hQn] at this; exact this }
  obtain ⟨c₆, k₆, e₆, hk₆, R₆, M₆, F₆⟩ := posLoop_exec (P := P) hI.wb hPE hW6
  have w₆ := e₆.wb_right
  have g₆ : ∀ r, Bpos r = false → c₆.nreg r = c₅.nreg r := F₆.1
  have hmem6 : ∀ a, a < b0 → c₆.nmem a = c.nmem a := fun a ha => by
    rw [M₆ a (by left; omega), hmem5 a ha]
  obtain ⟨hdesc₆, hwf₆⟩ := desc_agree' hwf hMD hmem6
  have hK1 : 1 ≤ K := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi, -⟩ := mem_F_iff.1 hx
    omega
  have hcb : c.nmem (NFH + 3) + 5 * K ≤ b0 := by have := aCh (K - 1) (by omega); omega
  have al6 : c₆.nreg ALLOC = b0 + d.oEnd := by rw [g₆ _ (by decide), al5]
  -- 2. the chord ends
  have hNE : NdEnv P W MD NFH (c.nmem (NFH + 3)) d M N c₆ :=
    { hG := hG, hWh := hWh, hGM := hGM, hNF := hNF, hne := hne, hK := rfl, hA := rfl,
      bases := hI.bases.frame fun r a1 a2 => g₆ r (by
        simp only [Bpos, Binit, Bpz, NFLoc.Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        omega),
      r00 := by rw [g₆ _ (by decide), hI.r00], r01 := by rw [g₆ _ (by decide), hI.r01],
      r10 := by rw [g₆ _ (by decide), hI.r10], r13 := by rw [g₆ _ (by decide), hI.r13],
      r19 := by rw [g₆ _ (by decide), hI.r19], r21 := by rw [g₆ _ (by decide), hI.r21],
      alloc := al6, wf := hwf₆, desc := hdesc₆,
      nfw := hNW.transport hmem6,
      chords := fun i hi => by
        obtain ⟨a0, a1, a2, -, -⟩ := hN.2.2.2.2.2.1 i hi
        have := aCh i hi
        exact ⟨by rw [hmem6 _ (by omega)]; exact a0, by rw [hmem6 _ (by omega)]; exact a1,
          by rw [hmem6 _ (by omega)]; exact a2⟩,
      cbB := hcb,
      room := by rw [al6, ← al5]; exact hroom,
      cnt0 := fun j hj => (R₆ j hj).1 }
  have hW5 : 5 ≤ W := by omega
  obtain ⟨c₇, k₇, e₇, hk₇, I₇, i₇, a₇⟩ := ndLoop_exec (P := P) w₆ hNE hW5
  have w₇ := I₇.wb
  have g₇ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₇.nreg r = c₆.nreg r := I₇.r9
  have t7 : ∀ r, 90000 ≤ r → r < 90070 → Bpos r = false → c₇.nreg r = c₅.nreg r :=
    fun r a1 a2 a3 => by rw [g₇ r a1 (by omega) (by simp [Binit]; omega), g₆ r a3]
  -- 3. the end
  obtain ⟨c₈, k₈, e₈, hk₈, f50, f51, f52, fr, fm⟩ : ∃ c₈ k₈, Exec P W finStmt c₇ c₈ k₈ ∧ k₈ = 3 ∧
      c₈.nreg 90050 = K ∧ c₈.nreg 90051 = K ∧ c₈.nreg 90052 = 0 ∧
      (∀ r, r ≠ 90050 → r ≠ 90051 → r ≠ 90052 → c₈.nreg r = c₇.nreg r) ∧ c₈.nmem = c₇.nmem := by
    have t10 : c₇.nreg 90010 = K := by rw [t7 _ (by norm_num) (by norm_num) (by decide), hI.r10]
    unfold finStmt
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 => by simp [upd, a1, a2, a3], rfl⟩ <;> config_simp
      · exact t10
      · exact t10
  have u8 : ∀ r, 90000 ≤ r → r < 90050 → Bpos r = false → c₈.nreg r = c₅.nreg r :=
    fun r a1 a2 a3 => by rw [fr r (by omega) (by omega) (by omega), t7 r a1 (by omega) a3]
  have m8 : ∀ a, a < c₆.nreg ALLOC → (a < d.b0 + d.oNd0 ∨ d.b0 + d.oDeg ≤ a) →
      (a < d.b0 + d.oCnt ∨ d.b0 + d.oNxt ≤ a) → c₈.nmem a = c₆.nmem a := fun a h1 h2 h3 => by
    rw [fm, I₇.mem a h1 h2 h3]
  have hA6 := al6
  have hBp : ∀ r, bandOf r ∉ granBands → Bpos r = false := by
    intro r hr
    simp only [Bpos, Binit, Bpz, NFLoc.Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    have h1 : ¬ (10000 ≤ r ∧ r < 20000) := fun h => hr (by
      simp only [bandOf, granBands, kernelBands, bSign, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega)
    have h5 : ¬ (50000 ≤ r ∧ r < 60000) := fun h => hr (by
      simp only [bandOf, granBands, kernelBands, bLocate, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega)
    have h9 : ¬ (90000 ≤ r ∧ r < 100000) := fun h => hr (by
      simp only [bandOf, granBands, kernelBands, bGran, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega)
    omega
  have hGF6 : GF b0 c₅ c₆ k₆ := ⟨fun r hr _ => g₆ r (hBp r hr), fun r hr => F₆.2.1 r (hBp r hr),
    fun a ha => M₆ a (by left; omega), fun a _ => by rw [F₆.2.2.1], F₆.2.2.2,
    by rw [g₆ _ (by decide)], by rw [g₆ _ (by decide)]; omega⟩
  have hGF7 : GF b0 c₆ c₇ k₇ := ⟨fun r hr ha => I₇.fr r (fun h => hr (by
      simp only [granBands, kernelBands, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h ⊢; tauto)) ha,
    fun r hr => I₇.frr r (fun h => hr (by
      simp only [granBands, kernelBands, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h ⊢; tauto)),
    fun a ha => I₇.mem a (by omega) (by left; omega) (by left; omega),
    fun a ha => I₇.frm a (by omega), I₇.fro, I₇.al1, a₇⟩
  have hGF8 : GF b0 c₇ c₈ k₈ := GF.of_nat e₈ (Bw := fun r => decide (90050 ≤ r ∧ r < 90053))
    (by decide) (by decide)
    (fun r hr => by
      have : 90050 ≤ r ∧ r < 90053 := by simpa using hr
      exact band9_gran (by omega) (by omega))
    (fun a _ => by rw [fm])
  refine ⟨c₈, _, .seq e₆ (.seq e₇ e₈), ?_, ⟨by exact e₈.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, f50, f51, f52, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    (hGF6.trans (hGF7.trans hGF8)).mono le_rfl⟩
  · simp only [hKd, hAd] at hk₆ hk₇ ⊢; omega
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r00]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r01]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r02]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r03]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r10]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r13]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r18]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r14]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r19]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r20]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r21]
  · rw [u8 _ (by norm_num) (by norm_num) (by decide), hI.r28]
  · exact hI.bases.frame fun r a1 a2 => u8 r (by omega) (by omega) (by
      simp only [Bpos, Binit, Bpz, NFLoc.Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega)
  · change b0 + d.oEnd ≤ _
    rw [fr _ (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)]
    have := I₇.al1; omega
  · intro u hu
    change u < K at hu
    obtain ⟨l1, l2, l3⟩ := hI.live u hu
    change c₅.nmem (b0 + u) = 1 at l1
    change c₅.nmem (b0 + K + u) = _ at l2
    change c₅.nmem (b0 + 2 * K + u) = _ at l3
    change c₈.nmem (b0 + u) = 1 ∧ c₈.nmem (b0 + K + u) = _ ∧ c₈.nmem (b0 + 2 * K + u) = _
    refine ⟨?_, ?_, ?_⟩
    · rw [m8 _ (by omega) (by left; omega) (by left; omega), M₆ _ (by left; omega)]; exact l1
    · rw [m8 _ (by omega) (by left; omega) (by left; omega), M₆ _ (by left; omega)]; exact l2
    · rw [m8 _ (by omega) (by left; omega) (by left; omega), M₆ _ (by left; omega)]; exact l3
  · intro u hu
    change u < d.cap at hu
    change c₈.nmem (b0 + d.oStk + u) = u
    have := y4
    rw [m8 _ (by omega) (by right; omega) (by right; omega), M₆ _ (by right; omega)]
    exact hI.stk u hu
  · intro x hx
    change x < R at hx
    obtain ⟨l1, l2, l3, l4⟩ := hI.cls x hx
    change c₅.nmem (b0 + d.oDeg + x) = _ at l1
    change c₅.nmem (b0 + d.oWt + x) = _ at l2
    change c₅.nmem (b0 + d.oExb + x) = b0 + d.oEx + D * x at l3
    change ∀ t, t < D → c₅.nmem (b0 + d.oEx + D * x + t) = _ at l4
    have hs := slot_le (R := R) (D := D) (x := x) hx (le_refl _)
    have hRD : d.R * d.D = R * D := rfl
    change c₈.nmem (b0 + d.oDeg + x) = _ ∧ c₈.nmem (b0 + d.oWt + x) = _ ∧
      c₈.nmem (b0 + d.oExb + x) = b0 + d.oEx + D * x ∧
      ∀ t, t < D → c₈.nmem (b0 + d.oEx + D * x + t) = _
    refine ⟨?_, ?_, ?_, fun t ht => ?_⟩
    · rw [m8 _ (by omega) (by right; omega) (by left; omega), M₆ _ (by left; omega)]; exact l1
    · rw [m8 _ (by omega) (by right; omega) (by left; omega), M₆ _ (by left; omega)]; exact l2
    · rw [m8 _ (by omega) (by right; omega) (by left; omega), M₆ _ (by left; omega)]; exact l3
    · have hs' := slot_lt (R := R) (D := D) (x := x) hx ht
      rw [m8 _ (by omega) (by right; omega) (by left; omega), M₆ _ (by left; omega)]
      exact l4 t ht
  · intro j hj
    obtain ⟨-, r1, r2, r3, r4, r5⟩ := R₆ j hj
    change c₈.nmem (b0 + d.oNxt + j) = _ ∧ c₈.nmem (b0 + d.oPrv + j) = _ ∧
      c₈.nmem (b0 + d.oEg + j) = _ ∧ c₈.nmem (b0 + d.oPz + j) ≤ 1 ∧
      (c₈.nmem (b0 + d.oPz + j) = 1 ↔ _)
    rw [m8 (b0 + d.oNxt + j) (by omega) (by right; omega) (by right; omega),
      m8 (b0 + d.oPrv + j) (by omega) (by right; omega) (by right; omega),
      m8 (b0 + d.oEg + j) (by omega) (by right; omega) (by right; omega),
      m8 (b0 + d.oPz + j) (by omega) (by right; omega) (by right; omega)]
    rw [hmem5 MD (by have := hwf.1; omega)] at r3
    exact ⟨r1, r2, r3, r4, r5⟩
  · intro j hj
    have := I₇.cnt j hj
    rw [i₇] at this
    change c₈.nmem (b0 + d.oCnt + j) = cntInit K (rdArr c₈.nmem (b0 + d.oNd0))
      (rdArr c₈.nmem (b0 + d.oNd1)) j
    rw [fm]; exact this
  · intro u hu
    have := I₇.nd0 u (by rw [i₇]; exact hu)
    rw [fm]
    change c₇.nmem (d.b0 + 3 * d.K + u) < A ∧ _ at this
    exact this
  · intro u hu
    have := I₇.nd1 u (by rw [i₇]; exact hu)
    rw [fm]
    change c₇.nmem (d.b0 + 4 * d.K + u) < A ∧ _ at this
    exact this
  · intro a ha
    rw [m8 a (by omega) (by left; omega) (by left; omega), hmem6 a ha]

end

end Gran

end Chazelle.Core
