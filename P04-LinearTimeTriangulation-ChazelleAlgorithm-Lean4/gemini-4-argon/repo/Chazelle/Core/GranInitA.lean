module

public import Chazelle.Core.GranInitEnv

/-!
# WP-F, init part 13: the first half of the initialisation

`initA = header; layout and allocation; chords; worklist; classes` (`initA_exec`), ending in the
intermediate state `InitMid`.  `GF b c c' k`: the frame of the specification (`Frame granBands`)
with the memory kept below the fixed bound `b` (the allocator at entry).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The frame of the procedure, memory kept below `b`. -/
def GF (b : ℕ) (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ granBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ granBands → c'.rreg r = c.rreg r) ∧
    (∀ a, a < b → c'.nmem a = c.nmem a) ∧ (∀ a, a < b → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem GF.trans {b : ℕ} {c₁ c₂ c₃ : Config} {k₁ k₂ : ℕ} (h₁ : GF b c₁ c₂ k₁)
    (h₂ : GF b c₂ c₃ k₂) : GF b c₁ c₃ (k₁ + k₂) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h₂
  exact ⟨fun r hr ha => (b1 r hr ha).trans (a1 r hr ha), fun r hr => (b2 r hr).trans (a2 r hr),
    fun a ha => (b3 a ha).trans (a3 a ha), fun a ha => (b4 a ha).trans (a4 a ha), b5.trans a5,
    a6.trans b6, by omega⟩

theorem GF.mono {b : ℕ} {c c' : Config} {k k' : ℕ} (h : GF b c c' k) (hk : k ≤ k') :
    GF b c c' k' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, by omega⟩

/-- A natural-only statement writing registers of band `9` or `5` (`Bw`) and storing only at or
above `b` gives `GF b`. -/
theorem GF.of_nat {P : Polygon} {W b : ℕ} {s : Stmt} {c c' : Config} {k : ℕ} {Bw : ℕ → Bool}
    (e : Exec P W s c c' k) (hs : natOnly s = true) (hB : wrS Bw s = true)
    (hBw : ∀ r, Bw r = true → bandOf r ∈ granBands ∧ r ≠ ALLOC)
    (hm : ∀ a, a < b → c'.nmem a = c.nmem a) : GF b c c' k := by
  have F := exec_frameS e hB
  have N := exec_natOnly e hs
  have hA : Bw ALLOC = false := by
    by_contra h'
    exact (hBw ALLOC (by simpa using h')).2 rfl
  refine ⟨fun r hr _ => F.1 r ?_, fun r _ => by rw [N.1], hm, fun a _ => by rw [N.2.1], N.2.2,
    by rw [F.1 _ hA], by rw [F.1 _ hA]; omega⟩
  by_contra h'
  exact hr (hBw r (by simpa using h')).1

theorem band9_gran {r : ℕ} (h1 : 90000 ≤ r) (h2 : r < 100000) : bandOf r ∈ granBands ∧ r ≠ ALLOC := by
  unfold bandOf granBands kernelBands bGran ALLOC
  simp; omega

theorem band5_gran {r : ℕ} (h1 : 50000 ≤ r) (h2 : r < 60000) : bandOf r ∈ granBands ∧ r ≠ ALLOC := by
  unfold bandOf granBands kernelBands bLocate ALLOC
  simp; omega

/-! ## The first half -/

/-- Header, layout and allocation, chords, worklist, classes. -/
def initA : Stmt := .seq hdrStmt (.seq baseStmt (.seq chLoop (.seq stkLoop regLoop)))

/-- The state after the first half of the initialisation (layout `dmOf K A R D b0`). -/
structure InitMid (P : Polygon) (W MD NFH D γ : ℕ) (N : NF) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  r00 : c.nreg 90000 = MD
  r01 : c.nreg 90001 = NFH
  r02 : c.nreg 90002 = D
  r03 : c.nreg 90003 = γ
  r10 : c.nreg 90010 = N.nChords
  r11 : c.nreg 90011 = N.arcs.length
  r12 : c.nreg 90012 = N.nRegions
  r13 : c.nreg 90013 = c₀.nmem (NFH + 3)
  r15 : c.nreg 90015 = c₀.nmem (NFH + 4)
  r17 : c.nreg 90017 = c₀.nmem (NFH + 6)
  r23 : c.nreg 90023 = c₀.nmem MD
  r18 : c.nreg 90018 = szOf P (c₀.nmem MD) (c₀.nmem (MD + 3))
  r14 : c.nreg 90014 = γ
  r19 : c.nreg 90019 = 1
  r20 : c.nreg 90020 = 3
  r21 : c.nreg 90021 = 2
  l00 : c.nreg 50000 = MD
  r26 : c.nreg 90026 = D * N.nChords
  r28 : c.nreg 90028 =
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oList
  bases : Bases c (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC))
  alloc : c.nreg ALLOC =
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oEnd
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
  mem : ∀ a, (a < c₀.nreg ALLOC ∨
    c₀.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c₀.nreg ALLOC)).oEnd ≤ a) →
    c.nmem a = c₀.nmem a

/-- The cost of the first half. -/
def costA (K A R D : ℕ) : ℕ :=
  30 + (4 * R + 4 * D + 32 + 3 * (dmOf K A R D 0).oEnd) + (15 * K + 5) +
    (5 * (dmOf K A R D 0).cap + 4) + ((9 * D + 24) * R + 6)

set_option maxHeartbeats 4000000 in
theorem initA_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {MD NFH D γ : ℕ} {M : Model} {N : NF} {reg : ℕ → Set Point}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = NFH) (h2 : c.nreg 90002 = D)
    (h3 : c.nreg 90003 = γ) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD) (hMD : ModelDescAt c.nmem MD (Qof P) M)
    (hNW : NFWithin c.nmem NFH (c.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hRC : RegionCorr M (Qof P) N reg) (hRO : RegionsOK M (Qof P) N reg)
    (hdeg : M.DegLe (N.F M (Qof P)) D)
    (hroom : c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd ≤ W)
    (hK1 : 1 ≤ N.nChords) (hR1 : 1 ≤ N.nRegions) :
    ∃ c' k, Exec P W initA c c' k ∧ k ≤ costA N.nChords N.arcs.length N.nRegions D ∧
      InitMid P W MD NFH D γ N c c' ∧ GF (c.nreg ALLOC) c c' k := by
  set b0 := c.nreg ALLOC with hb0
  set K := N.nChords with hKd
  set A := N.arcs.length with hAd
  set R := N.nRegions with hRd
  set d := dmOf K A R D b0 with hd
  have hdb : d.b0 = b0 := rfl
  have hdK : d.K = K := rfl
  have hdA : d.A = A := rfl
  have hdR : d.R = R := rfl
  have hdD : d.D = D := rfl
  have hEnd : d.oEnd = (dmOf K A R D 0).oEnd := rfl
  have hN : NFAt c.nmem NFH N := hNW.holds
  obtain ⟨aB, aCh, aRg, aLst, aArc, aSeq⟩ := nf_areas hNW
  have hW5 : 5 ≤ W := by unfold hostWords at hWh; have := hwf.1; omega
  have hWn : P.n ≤ W := by unfold hostWords at hWh; omega
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have hdE := dmOf_oEnd K A R D b0
  -- 1. the header
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q11, q12, q13, q15, q16, q17, q22, q23, q24, q18, q14, q19, q20,
    q21, q50, q51, F₁⟩ := hdr_exec (P := P) c hw h0 h1 (by omega) (by have := hwf.1; omega) hWn
    (fun h0' => by have := chain_m_le hwf hMD h0'; unfold hostWords at hWh; omega)
  have w₁ := e₁.wb_right
  rw [hN.1] at q10; rw [hN.2.1] at q11; rw [hN.2.2.1] at q12
  have g₁ : ∀ r, Bhdr r = false → c₁.nreg r = c.nreg r := F₁.1
  have hA₁ : c₁.nreg ALLOC = b0 := g₁ _ (by decide)
  -- 2. the layout
  obtain ⟨c₂, k₂, e₂, hk₂, B₂, a₂, x27, x28, x26, ab₂, r₂, m₂, F₂⟩ := base_exec (P := P) c₁ w₁
    (K := K) (A := A) (R := R) (by rw [q10]; rfl) (by rw [q11]) (by rw [q12]; rfl)
    (by rw [g₁ _ (by decide), h2]) q19 (by rw [hA₁]; exact hroom)
  rw [hA₁] at hk₂ B₂ a₂ x27 x28
  have w₂ := e₂.wb_right
  have g₂ : ∀ r, (r < 90025 ∨ 90045 ≤ r) → r ≠ 90061 → r ≠ ALLOC → c₂.nreg r = c₁.nreg r := r₂
  have mem₂ : c₂.nmem = c.nmem := by rw [m₂, F₁.2.2.1]
  -- the entry records
  have hrec : ∀ i, i < K → c₂.nmem (c.nmem (NFH + 3) + 5 * i + 3) = (N.chord i).up ∧
      c₂.nmem (c.nmem (NFH + 3) + 5 * i + 4) = (N.chord i).dn := fun i hi => by
    rw [mem₂]
    obtain ⟨-, -, -, h3', h4'⟩ := hN.2.2.2.2.2.1 i hi
    exact ⟨h3', h4'⟩
  have hCB : c.nmem (NFH + 3) + 5 * K ≤ b0 := by have := aCh (K - 1) (by omega); omega
  have hRB : c.nmem (NFH + 5) + 5 * R ≤ b0 := by have := aRg (R - 1) (by omega); omega
  have hbW : d.b0 + d.oEnd ≤ W := by rw [hEnd]; exact hroom
  -- 3. the chords
  have c2 : ∀ r, 90000 ≤ r → r < 90025 → r ≠ 90060 → Bhdr r = false → c₂.nreg r = c.nreg r :=
    fun r a1 a2 a3 a4 => by rw [g₂ r (by omega) (by omega) (by unfold ALLOC; omega), g₁ r a4]
  have t10 : c₂.nreg 90010 = K := by
    rw [g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q10]; rfl
  have t13 : c₂.nreg 90013 = c.nmem (NFH + 3) := by
    rw [g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q13]
  have t19 : c₂.nreg 90019 = 1 := by rw [g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q19]
  have t20 : c₂.nreg 90020 = 3 := by rw [g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q20]
  obtain ⟨c₃, k₃, e₃, hk₃, L₃, M₃, F₃⟩ := chLoop_exec (P := P) (d := d) (chords := N.chord) w₂ B₂
    rfl t10 t13 t19 t20 hrec hCB hbW hW5
  have w₃ := e₃.wb_right
  have g₃ : ∀ r, Binit r = false → c₃.nreg r = c₂.nreg r := F₃.1
  have B₃ : Bases c₃ d := B₂.frame fun r a1 a2 => g₃ r (by simp [Binit]; omega)
  -- 4. the worklist
  obtain ⟨c₄, k₄, e₄, hk₄, S₄, M₄, F₄⟩ := stkLoop_exec (P := P) (d := d) w₃ B₃
    (by rw [g₃ _ (by decide), t10, hdK])
    (by rw [g₃ _ (by decide), x26, hdD, hdK])
    (by rw [g₃ _ (by decide), t19]) hbW
  have w₄ := e₄.wb_right
  have g₄ : ∀ r, Binit r = false → c₄.nreg r = c₃.nreg r := F₄.1
  have B₄ : Bases c₄ d := B₃.frame fun r a1 a2 => g₄ r (by simp [Binit]; omega)
  have t4 : ∀ r, Binit r = false → c₄.nreg r = c₂.nreg r := fun r h => by rw [g₄ r h, g₃ r h]
  -- 5. the classes
  have m4 : ∀ a, a < b0 → c₄.nmem a = c.nmem a := fun a ha => by
    rw [M₄ a (by left; omega), M₃ a (by left; omega), mem₂]
  have u2 : ∀ r, Binit r = false → 90000 ≤ r → r < 90025 → r ≠ 90060 → Bhdr r = false →
      c₄.nreg r = c.nreg r := fun r a0 a1 a2 a3 a4 => by rw [t4 r a0, c2 r a1 a2 a3 a4]
  have hrecR : ∀ r, r < R → RegRec c₄.nmem (c.nmem (NFH + 5)) (c.nmem (NFH + 7)) r
      (N.region r).chords.length (N.region r).wt (N.region r).chords := by
    intro r hr
    obtain ⟨-, a2, a4, -, a5⟩ := hN.2.2.2.2.2.2.2.1 r hr
    have hr4 := aRg r hr
    refine ⟨by rw [m4 _ (by omega)]; exact a2, by rw [m4 _ (by omega)]; exact a4, fun t ht => ?_,
      rfl⟩
    have := aLst r hr t ht
    rw [m4 (c.nmem (NFH + 5) + 5 * r + 3) (by omega), m4 _ (by omega)]
    exact a5 t ht
  obtain ⟨c₅, k₅, e₅, hk₅, C₅, M₅, F₅⟩ := regLoop_exec (P := P) (W := W) (R := R) (D := D)
    (RB := c.nmem (NFH + 5)) (LB := c.nmem (NFH + 7)) (d := d) (rg := N.region) w₄ B₄ rfl rfl
    (by rw [t4 _ (by decide), g₂ _ (by omega) (by omega) (by unfold ALLOC; omega),
      g₁ _ (by decide), h2])
    (by rw [t4 _ (by decide), g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q12]; rfl)
    (by rw [t4 _ (by decide), g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q16])
    (by rw [t4 _ (by decide), g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q22])
    (by rw [t4 _ (by decide), x27]; rfl)
    (by rw [t4 _ (by decide), t19]) (by rw [t4 _ (by decide), t20])
    (by rw [t4 _ (by decide), g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q21])
    hrecR (fun r hr => chords_le hNF hRC hRO hdeg hr) hRB
    (fun r hr h1r => by
      have := aLst r hr ((N.region r).chords.length - 1) (by omega)
      rw [m4 _ (by have := aRg r hr; omega)]; omega) hbW hW5
  have u5 : ∀ r, Binit r = false → c₅.nreg r = c₂.nreg r := fun r h => by
    rw [F₅.1 r h, t4 r h]
  have v2 : ∀ r, 90000 ≤ r → r < 90025 → r ≠ 90060 → c₅.nreg r = c₁.nreg r := fun r a1 a2 a3 => by
    rw [u5 r (by simp [Binit]; omega), g₂ r (by omega) (by omega) (by unfold ALLOC; omega)]
  have v1 : ∀ r, 90000 ≤ r → r < 90025 → r ≠ 90060 → Bhdr r = false → c₅.nreg r = c.nreg r :=
    fun r a1 a2 a3 a4 => by rw [v2 r a1 a2 a3, g₁ r a4]
  have hGF1 : GF b0 c c₁ k₁ := GF.of_nat e₁ (Bw := Bhdr) (by decide) (by decide)
    (fun r hr => by
      simp only [Bhdr, Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with ((h | h) | h) | h
      · exact band9_gran (by omega) (by omega)
      · exact band9_gran (by omega) (by omega)
      · exact band5_gran (by omega) (by omega)
      · exact band5_gran (by omega) (by omega))
    (fun a _ => by rw [F₁.2.2.1])
  have hGF2 : GF b0 c₁ c₂ k₂ := by
    have N2 := exec_natOnly e₂ (by decide)
    refine ⟨fun r hr ha => F₂.1 r ?_, fun r _ => by rw [N2.1], fun a _ => by rw [m₂],
      fun a _ => by rw [N2.2.1], N2.2.2, by rw [a₂, hA₁]; omega, ab₂⟩
    simp only [Bbase, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨fun h => hr (band9_gran (by omega) (by omega)).1, fun h => ha h⟩
  have hGF3 : GF b0 c₂ c₃ k₃ := GF.of_nat e₃ (by decide) wrS_chLoop
    (fun r hr => by
      have : 90070 ≤ r ∧ r < 90100 := by simpa [Binit] using hr
      exact band9_gran (by omega) (by omega))
    (fun a ha => M₃ a (by left; omega))
  have hGF4 : GF b0 c₃ c₄ k₄ := GF.of_nat e₄ (by decide) wrS_stkLoop
    (fun r hr => by
      have : 90070 ≤ r ∧ r < 90100 := by simpa [Binit] using hr
      exact band9_gran (by omega) (by omega))
    (fun a ha => M₄ a (by left; omega))
  have hGF5 : GF b0 c₄ c₅ k₅ := GF.of_nat e₅ (by decide) wrS_regLoop
    (fun r hr => by
      have : 90070 ≤ r ∧ r < 90100 := by simpa [Binit] using hr
      exact band9_gran (by omega) (by omega))
    (fun a ha => M₅ a (by left; omega))
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ⟨e₅.wb_right, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    (hGF1.trans (hGF2.trans (hGF3.trans (hGF4.trans hGF5)))).mono le_rfl⟩
  · have c0 : (dmOf K A R D 0).cap = K + D * K := rfl
    have c1 : d.cap = K + D * K := rfl
    rw [hdE] at hk₂
    rw [c1] at hk₄
    unfold costA; rw [dmOf_oEnd, c0]; omega
  · rw [v1 _ (by norm_num) (by norm_num) (by norm_num) (by decide), h0]
  · rw [v1 _ (by norm_num) (by norm_num) (by norm_num) (by decide), h1]
  · rw [v1 _ (by norm_num) (by norm_num) (by norm_num) (by decide), h2]
  · rw [v1 _ (by norm_num) (by norm_num) (by norm_num) (by decide), h3]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q10]; rfl
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q11]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q12]; rfl
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q13]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q15]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q17]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q23]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q18]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q14, h3]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q19]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q20]
  · rw [v2 _ (by norm_num) (by norm_num) (by norm_num), q21]
  · rw [u5 _ (by decide), g₂ _ (by omega) (by omega) (by unfold ALLOC; omega), q50]
  · rw [u5 _ (by decide), x26]
  · rw [u5 _ (by decide), x28]
  · exact B₄.frame fun r a1 a2 => F₅.1 r (by simp [Binit]; omega)
  · rw [u5 _ (by decide), a₂]
  · intro u hu
    obtain ⟨l1, l2, l3⟩ := L₃ u hu
    refine ⟨?_, ?_, ?_⟩
    · rw [M₅ _ (by left; omega), M₄ _ (by left; omega)]; exact l1
    · rw [M₅ _ (by left; omega), M₄ _ (by left; omega)]; exact l2
    · rw [M₅ _ (by left; omega), M₄ _ (by left; omega)]; exact l3
  · intro u hu
    change u < d.cap at hu
    change c₅.nmem (b0 + d.oStk + u) = u
    rw [M₅ _ (by right; omega)]; exact S₄ u hu
  · exact C₅
  · intro a ha
    change a < b0 ∨ b0 + d.oEnd ≤ a at ha
    have yN : d.oNd0 = 3 * d.K := rfl
    rw [M₅ a (by rcases ha with h | h <;> [left; right] <;> omega),
      M₄ a (by rcases ha with h | h <;> [left; right] <;> omega),
      M₃ a (by rcases ha with h | h <;> [left; right] <;> omega), mem₂]

end

end Gran

end Chazelle.Core
