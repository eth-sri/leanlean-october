module

public import Chazelle.Core.SweepEvStopTasks
public import Chazelle.Core.SweepEvInit2
public import Chazelle.Core.SortRam

/-!
# The sweep (WP-D), stage 2: sorting the raw stop records, part 1 (the comparator)

Task `SortTask` (`SweepEvStopTasks.lean`) sorts the indices `0 … S - 1` of the raw stop records
with `SortR.sortStmt` and the comparator `ssCmp` defined here: the order `ssLe` compares the keys
`(offK e h, dc)` of two records (lexicographically, `KLe`) and puts every index `≥ S` after the
records.  The comparator reads the positions of the records, runs the primitive `offCmp` (with the
allocator temporarily set to the entry allocator `srA0`, so that the primitive's room condition holds
whatever the sort has allocated) and decides with the direction codes.

The comparator writes only the bands `bSign`, `bLocate` (the primitive and its inputs) and
`bOQuery` (`120900 … 120906`): `ssBc`.  Main lemma: `ssCmp_ok` (`SortR.CmpOK`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR

@[expose] public section

/-! ## The order -/

/-- The key of the raw record `i`. -/
noncomputable def ssKey (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (RB i : ℕ) : ℝ × ℕ :=
  rKey P J (rawRec m RB i) (rawDc m RB i)

/-- **The order of the sort**: the records by key, then the indices `≥ S`. -/
noncomputable def ssLe (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (RB S : ℕ) (a b : ℕ) :
    Bool := by
  classical
  exact decide (if a < S then (b < S → KLe (ssKey P J m RB a) (ssKey P J m RB b)) else S ≤ b)

theorem ssLe_iff {P : Polygon} {J : Merge.Junction} {m : ℕ → ℕ} {RB S a b : ℕ} :
    ssLe P J m RB S a b = true ↔
      (if a < S then (b < S → KLe (ssKey P J m RB a) (ssKey P J m RB b)) else S ≤ b) := by
  unfold ssLe; simp

theorem ssLe_in {P : Polygon} {J : Merge.Junction} {m : ℕ → ℕ} {RB S a b : ℕ} (ha : a < S)
    (hb : b < S) : ssLe P J m RB S a b = true ↔ KLe (ssKey P J m RB a) (ssKey P J m RB b) := by
  rw [ssLe_iff, ite_eq_left ha]; exact ⟨fun h => h hb, fun h _ => h⟩

theorem ssLe_trans {P : Polygon} {J : Merge.Junction} {m : ℕ → ℕ} {RB S : ℕ} (a b d : ℕ)
    (h1 : ssLe P J m RB S a b) (h2 : ssLe P J m RB S b d) : ssLe P J m RB S a d := by
  rw [ssLe_iff] at h1 h2 ⊢
  by_cases ha : a < S <;> by_cases hb : b < S <;> by_cases hd : d < S <;>
    simp only [ha, hb, hd, ite_true, ite_false, true_implies, false_implies] at h1 h2 ⊢ <;>
    first | trivial | omega | exact h1.trans h2

theorem ssLe_total {P : Polygon} {J : Merge.Junction} {m : ℕ → ℕ} {RB S : ℕ} (a b : ℕ) :
    (ssLe P J m RB S a b || ssLe P J m RB S b a) = true := by
  rw [Bool.or_eq_true, ssLe_iff, ssLe_iff]
  by_cases ha : a < S <;> by_cases hb : b < S <;>
    simp only [ha, hb, ite_true, ite_false, true_implies, false_implies, true_or, or_true] <;>
    first | omega | exact KLe.total _ _

/-! ## Registers -/

/-- The entry allocator of the sort task (a scratch register of stage 2). -/
def srA0 : ℕ := sw 3000

/-- The bands the comparator writes. -/
def ssBc : Finset ℕ := {bSign, bLocate, bOQuery}

theorem bSort_not_ssBc : bSort ∉ ssBc := by decide

theorem ssBc_oracle : insert bSort ssBc ⊆ oracleBands := by decide

/-! ## The comparator -/

/-- Load the position `(e, h)` (into `pe`, `ph`) and the direction code (into `pd`) of the raw
record whose index is in `s`: address `gRB + 11 s`. -/
def ssLdA (s pe ph pd : ℕ) : List Instr :=
  [.addN 120903 s s, .addN 120904 120903 120903, .addN 120905 120904 120904,
    .addN 120906 120905 120903, .addN 120906 120906 s, .addN 120906 120906 gRB,
    .loadN pe 120906, .addN 120906 120906 K1, .loadN ph 120906, .addN 120906 120906 K1,
    .loadN pd 120906]

/-- The inputs of `offCmp` (descriptor of `C`, the two positions, the base `gW`), the direction
codes, and the allocator set to the entry allocator (saved in `120900`). -/
def ssLd : List Instr :=
  [.copyN 50200 (sw 2), .copyN 50205 cGW] ++ ssLdA 30000 50201 50202 120901 ++
    ssLdA 30001 50203 50204 120902 ++ [.copyN 120900 ALLOC, .copyN ALLOC srA0]

/-- The decision from the two offset bits and the direction codes. -/
def ssDec : Stmt :=
  .ifLtN K0 50210 (.instr (.constN 30002 1))
    (.ifLtN K0 50211 (.instr (.constN 30002 0))
      (.ifLtN 120902 120901 (.instr (.constN 30002 0)) (.instr (.constN 30002 1))))

/-- Two records. -/
def ssMain : Stmt := .seq (block ssLd) (.seq offCmp (.seq (.instr (.copyN ALLOC 120900)) ssDec))

/-- **The comparator.** -/
def ssCmp : Stmt :=
  .ifLtN 30000 gRC (.ifLtN 30001 gRC ssMain (.instr (.constN 30002 1)))
    (.ifLtN 30001 gRC (.instr (.constN 30002 0)) (.instr (.constN 30002 1)))

/-! ## The invariant of the comparator -/

/-- **The invariant of the comparator** (fixed data: the descriptor of `C`, the record array, the
entry allocator `A₀` and the memory below it). -/
def SsCtx (J : Merge.Junction) (d2 RB S A₀ : ℕ) (m₀ : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg (sw 2) = d2 ∧ d.nreg cGW = gW J ∧ d.nreg gRB = RB ∧ d.nreg gRC = S ∧
    d.nreg K0 = 0 ∧ d.nreg K1 = 1 ∧ d.nreg srA0 = A₀ ∧ ∀ a, a < A₀ → d.nmem a = m₀ a

theorem ssCtx_stable {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ} {A₁ : ℕ}
    (hA : A₀ ≤ A₁) : JStable (SsCtx J d2 RB S A₀ m₀) A₁ := by
  intro c c' ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hr _ hm _ _
  have k : ∀ i, c'.nreg (sw i) = c.nreg (sw i) := fun i =>
    hr _ (by unfold bandOf sw bSort; omega) (by unfold sw ALLOC; omega)
  exact ⟨(k 2).trans h1, (k 659).trans h2, (k 4000).trans h3, (k 4001).trans h4,
    (k 610).trans h5, (k 611).trans h6, (k 3000).trans h7,
    fun a ha => (hm a (by omega)).trans (h8 a ha)⟩

set_option maxRecDepth 20000 in
theorem ssLd_val (m f : ℕ → ℕ) (h1 : f K1 = 1) :
    regB m ssLd f 50200 = f (sw 2) ∧ regB m ssLd f 50205 = f cGW ∧
    regB m ssLd f 50201 = m (f gRB + 11 * f 30000) ∧
    regB m ssLd f 50202 = m (f gRB + 11 * f 30000 + 1) ∧
    regB m ssLd f 120901 = m (f gRB + 11 * f 30000 + 2) ∧
    regB m ssLd f 50203 = m (f gRB + 11 * f 30001) ∧
    regB m ssLd f 50204 = m (f gRB + 11 * f 30001 + 1) ∧
    regB m ssLd f 120902 = m (f gRB + 11 * f 30001 + 2) ∧
    regB m ssLd f 120900 = f ALLOC ∧ regB m ssLd f ALLOC = f srA0 ∧
    ∀ r, r ≠ 50200 → r ≠ 50205 → r ≠ 50201 → r ≠ 50202 → r ≠ 50203 → r ≠ 50204 →
      r ≠ ALLOC → (r < 120900 ∨ 120906 < r) → regB m ssLd f r = f r := by
  simp only [K1, sw, Nat.reduceAdd] at h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b d e g i j k => ?_⟩
  all_goals simp only [ssLd, ssLdA, List.cons_append, List.nil_append, regB, regI, K1, gRB, cGW,
    srA0, ALLOC, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  all_goals try rw [h1]
  all_goals try (congr 1; ring)
  simp only [ALLOC] at j
  simp only [upd_apply]
  repeat rw [ite_eq_right (by omega)]

set_option maxRecDepth 20000 in
theorem ssLd_ok {W : ℕ} (m f : ℕ → ℕ) (h1 : f K1 = 1) {S A : ℕ} (ha : f 30000 < S)
    (hb : f 30001 < S) (hRB : f gRB + 11 * S ≤ A) (hAW : A ≤ W) : okW W m ssLd f := by
  simp only [K1, gRB, sw, Nat.reduceAdd] at h1 hRB
  simp only [ssLd, ssLdA, List.cons_append, List.nil_append, okW, okWI, regI, K1, gRB, cGW,
    srA0, ALLOC, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff,
    not_false_eq_true, true_and, and_true]
  rw [h1]
  omega

/-- A comparator branch setting the bit. -/
theorem ssBit_exec {P : Polygon} {W : ℕ} {d : Config} (hw : WordsBounded W d) (v : ℕ)
    (hv : v ≤ 1) (h1 : 1 ≤ W) :
    Exec P W (.instr (.constN 30002 v)) d { d with nreg := upd d.nreg 30002 v } 1 :=
  Exec.constN hw _ _ (by omega)

set_option maxRecDepth 20000 in
/-- **The comparator meets the contract of the sort.** -/
theorem ssCmp_ok {P : Polygon} {W : ℕ} {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ}
    {H : Host} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hwf : ChainWF P A₀ m₀ d2)
    (hC : ChainDescAt m₀ d2 (Qof P) H J.whole) (hWm : 2 * J.whole.m + 7 ≤ W)
    (hroom : A₀ + 11000 ≤ W) (hRB : RB + 11 * S ≤ A₀)
    (hrec : ∀ i, i < S → PosW P J (m₀ (RB + 11 * i)) (m₀ (RB + 11 * i + 1)))
    (hgn : gW J < (chainModel J.whole).W.n) :
    CmpOK P W ssCmp ssBc (SsCtx J d2 RB S A₀ m₀) (ssLe P J m₀ RB S) 12000 := by
  intro d hw hJ
  have hJ' := hJ
  obtain ⟨j2, jg, jRB, jS, j0, j1, jA, jm⟩ := hJ'
  have hW1 : 1 ≤ W := by omega
  -- the frame of a one-bit branch
  have bit : ∀ v, v ≤ 1 → (v = 1 ↔ ssLe P J m₀ RB S (d.nreg 30000) (d.nreg 30001) = true) →
      ∃ c' k, Exec P W (.instr (.constN 30002 v)) d c' k ∧ k ≤ 1 ∧
        SsCtx J d2 RB S A₀ m₀ c' ∧
        c'.nreg 30002 = (if ssLe P J m₀ RB S (d.nreg 30000) (d.nreg 30001) then 1 else 0) ∧
        (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → (bandOf r ∉ ssBc ∨ r = ALLOC) →
          c'.nreg r = d.nreg r) ∧
        (∀ r, bandOf r ∉ ssBc → c'.rreg r = d.rreg r) ∧
        c'.nmem = d.nmem ∧ c'.rmem = d.rmem ∧ c'.output = d.output := by
    intro v hv hiff
    refine ⟨_, 1, ssBit_exec hw v hv hW1, le_rfl, ?_, ?_, fun r h1 h2 h3 _ => ?_,
      fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, jm⟩ <;> simp only <;>
        rw [upd_other _ _ _ (by simp [sw, cGW, gRB, gRC, K0, K1, srA0])] <;> assumption
    · simp only [upd_same]
      split_ifs with h
      · exact hiff.2 h
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hv with h' | h'
        · exact h'
        · exact absurd (hiff.1 h') h
    · simp only; rw [upd_other _ _ _ h3]
  unfold ssCmp
  by_cases ha : d.nreg 30000 < d.nreg gRC
  · by_cases hb : d.nreg 30001 < d.nreg gRC
    · -- the main case
      rw [jS] at ha hb
      obtain ⟨a, had⟩ : ∃ a, d.nreg 30000 = a := ⟨_, rfl⟩
      obtain ⟨b, hbd⟩ : ∃ b, d.nreg 30001 = b := ⟨_, rfl⟩
      rw [had] at ha
      rw [hbd] at hb
      have hj1 : d.nreg K1 = 1 := j1
      have e₁ := exec_regB (P := P) ssLd hw (ssLd_ok d.nmem d.nreg hj1 (by rwa [had])
        (by rwa [hbd])
        (A := A₀) (by rwa [jRB]) (by omega))
      set d₁ : Config := { d with nreg := regB d.nmem ssLd d.nreg }
      obtain ⟨v00, v05, v01, v02, vda, v03, v04, vdb, vsv, vA, vo⟩ :=
        ssLd_val d.nmem d.nreg hj1
      rw [jRB, had] at v01 v02 vda
      rw [jRB, hbd] at v03 v04 vdb
      rw [jA] at vA
      have mA : ∀ i, i < S → ∀ t, t < 11 → d.nmem (RB + 11 * i + t) = m₀ (RB + 11 * i + t) :=
        fun i hi t ht => jm _ (by have : 11 * i + 11 ≤ 11 * S := by omega
                                  omega)
      have hw₁ := e₁.wb_right
      have hd1A : d₁.nreg ALLOC = A₀ := vA
      -- the primitive
      have hpre : PrimPre OffIn P W d₁ := by
        refine ⟨hG, hWh, ?_, H, J.whole, ?_, ?_⟩
        · rw [hd1A, show d₁.nreg 50200 = d2 from v00.trans j2]
          exact (chainDesc_keep hwf hC (fun a ha => jm a ha) le_rfl).2
        · rw [show d₁.nreg 50200 = d2 from v00.trans j2]
          exact (chainDesc_keep hwf hC (fun a ha => jm a ha) le_rfl).1
        · obtain ⟨pa1, pa2, pa3⟩ := hrec a ha
          obtain ⟨pb1, pb2, pb3⟩ := hrec b hb
          have ea := mA a ha 0 (by norm_num)
          have ha1 := mA a ha 1 (by norm_num)
          have eb := mA b hb 0 (by norm_num)
          have hb1 := mA b hb 1 (by norm_num)
          simp only [Nat.add_zero] at ea eb
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hWm⟩
          · show regB d.nmem ssLd d.nreg 50201 < _; rwa [v01, ea]
          · show regB d.nmem ssLd d.nreg 50203 < _; rwa [v03, eb]
          · show regB d.nmem ssLd d.nreg 50205 < _; rwa [v05, jg]
          · show ProperPos _ _ _ ⟨regB d.nmem ssLd d.nreg 50201, regB d.nmem ssLd d.nreg 50202⟩
            rwa [v01, v02, ea, ha1]
          · show ProperPos _ _ _ ⟨regB d.nmem ssLd d.nreg 50203, regB d.nmem ssLd d.nreg 50204⟩
            rwa [v03, v04, eb, hb1]
          · show regB d.nmem ssLd d.nreg 50202 = 0 → 6 ≤ regB d.nmem ssLd d.nreg 50201
            rwa [v01, v02, ea, ha1]
          · show regB d.nmem ssLd d.nreg 50204 = 0 → 6 ≤ regB d.nmem ssLd d.nreg 50203
            rwa [v03, v04, eb, hb1]
      obtain ⟨d₂, k₂, e₂, hk₂, hpost, -⟩ := offCmp_meets P W d₁ hw₁ hpre (by rwa [hd1A])
      have fB := SignK.exec_frameB e₂ wr_offCmp
      have hC₁ : ChainDescAt d₁.nmem (d₁.nreg 50200) (Qof P) H J.whole := by
        rw [show d₁.nreg 50200 = d2 from v00.trans j2]
        exact (chainDesc_keep hwf hC (fun a ha => jm a ha) le_rfl).1
      obtain ⟨blt, bgt⟩ := hpost H J.whole hC₁
      -- the keys
      set ka := ssKey P J m₀ RB a
      set kb := ssKey P J m₀ RB b
      have hoa : off ((chainModel J.whole).W.n : ℝ) ((d₁.nreg 50205 : ℕ) : ℝ)
          ((chainModel J.whole).key (Qof P) ⟨d₁.nreg 50201, d₁.nreg 50202⟩) = ka.1 := by
        show off _ ((regB d.nmem ssLd d.nreg 50205 : ℕ) : ℝ) ((chainModel J.whole).key (Qof P)
          ⟨regB d.nmem ssLd d.nreg 50201, regB d.nmem ssLd d.nreg 50202⟩) = _
        have q0 := mA a ha 0 (by norm_num)
        simp only [Nat.add_zero] at q0
        rw [v05, jg, v01, v02, q0, mA a ha 1 (by norm_num)]
        rfl
      have hob : off ((chainModel J.whole).W.n : ℝ) ((d₁.nreg 50205 : ℕ) : ℝ)
          ((chainModel J.whole).key (Qof P) ⟨d₁.nreg 50203, d₁.nreg 50204⟩) = kb.1 := by
        show off _ ((regB d.nmem ssLd d.nreg 50205 : ℕ) : ℝ) ((chainModel J.whole).key (Qof P)
          ⟨regB d.nmem ssLd d.nreg 50203, regB d.nmem ssLd d.nreg 50204⟩) = _
        have q0 := mA b hb 0 (by norm_num)
        simp only [Nat.add_zero] at q0
        rw [v05, jg, v03, v04, q0, mA b hb 1 (by norm_num)]
        rfl
      rw [hoa, hob] at blt bgt
      have hda : d₂.nreg 120901 = ka.2 := by
        rw [fB.1 _ (by decide)]
        show regB d.nmem ssLd d.nreg 120901 = _
        rw [vda, mA a ha 2 (by norm_num)]; rfl
      have hdb : d₂.nreg 120902 = kb.2 := by
        rw [fB.1 _ (by decide)]
        show regB d.nmem ssLd d.nreg 120902 = _
        rw [vdb, mA b hb 2 (by norm_num)]; rfl
      -- restore the allocator
      have hw₂ := e₂.wb_right
      have e₃ := Exec.copyN (P := P) hw₂ ALLOC 120900
      set d₃ : Config := { d₂ with nreg := upd d₂.nreg ALLOC (d₂.nreg 120900) } with hd₃
      have k₃ : ∀ r, r ≠ ALLOC → d₃.nreg r = d₂.nreg r := fun r h => by
        simp only [hd₃]; rw [upd_other _ _ _ h]
      have hK0 : d₃.nreg K0 = 0 := by
        rw [k₃ _ (by decide), fB.1 _ (by decide)]
        show regB d.nmem ssLd d.nreg K0 = 0
        rwa [vo _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by unfold K0 sw; omega)]
      -- the decision
      have hiff : ssLe P J m₀ RB S a b = true ↔ KLe ka kb := ssLe_in ha hb
      have hw₃ := e₃.wb_right
      have bl1 := blt.1
      have bg1 := bgt.1
      have dec : ∃ v k₄, v ≤ 1 ∧ (v = 1 ↔ KLe ka kb) ∧ k₄ ≤ 7 ∧
          Exec P W ssDec d₃ { d₃ with nreg := upd d₃.nreg 30002 v } k₄ := by
        unfold ssDec
        have b10 : d₃.nreg 50210 = d₂.nreg 50210 := k₃ _ (by decide)
        have b11 : d₃.nreg 50211 = d₂.nreg 50211 := k₃ _ (by decide)
        have da : d₃.nreg 120901 = ka.2 := (k₃ _ (by decide)).trans hda
        have db : d₃.nreg 120902 = kb.2 := (k₃ _ (by decide)).trans hdb
        by_cases t1 : d₃.nreg K0 < d₃.nreg 50210
        · have hlt : ka.1 < kb.1 := blt.2.1 (by rw [b10] at t1; omega)
          exact ⟨1, 2, le_rfl, ⟨fun _ => Or.inl hlt, fun _ => rfl⟩, by norm_num,
            .ifLtN_true t1 (ssBit_exec hw₃ 1 le_rfl hW1)⟩
        · have hnlt : ¬ ka.1 < kb.1 := fun h => by
            have := blt.2.2 h; rw [b10] at t1; omega
          by_cases t2 : d₃.nreg K0 < d₃.nreg 50211
          · have hgt : kb.1 < ka.1 := bgt.2.1 (by rw [b11] at t2; omega)
            refine ⟨0, 4, by omega, ⟨fun h => absurd h (by norm_num), fun h => ?_⟩, by norm_num,
              .ifLtN_false t1 (.ifLtN_true t2 (ssBit_exec hw₃ 0 (by omega) hW1))⟩
            rcases h with h | ⟨h, -⟩
            · exact absurd h hnlt
            · rw [h] at hgt; exact absurd hgt (lt_irrefl _)
          · have hngt : ¬ kb.1 < ka.1 := fun h => by
              have := bgt.2.2 h; rw [b11] at t2; omega
            have heq : ka.1 = kb.1 := le_antisymm (not_lt.1 hngt) (not_lt.1 hnlt)
            by_cases t3 : d₃.nreg 120902 < d₃.nreg 120901
            · rw [da, db] at t3
              refine ⟨0, 6, by omega, ⟨fun h => absurd h (by norm_num), fun h => ?_⟩, by norm_num,
                .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true (by rwa [da, db])
                  (ssBit_exec hw₃ 0 (by omega) hW1)))⟩
              rcases h with h | ⟨-, h⟩
              · exact absurd h hnlt
              · omega
            · rw [da, db] at t3
              exact ⟨1, 7, le_rfl, ⟨fun _ => Or.inr ⟨heq, by omega⟩, fun _ => rfl⟩, by norm_num,
                .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false (by rwa [da, db])
                  (ssBit_exec hw₃ 1 le_rfl hW1)))⟩
      obtain ⟨v, k₄, hv, hvi, hk₄, e₄⟩ := dec
      -- the frame
      have hA₂ : d₂.nreg 120900 = d.nreg ALLOC := by
        rwa [fB.1 _ (by decide)]
      have keep : ∀ r, r ≠ 30002 → (bandOf r ∉ ssBc ∨ r = ALLOC) →
          ({ d₃ with nreg := upd d₃.nreg 30002 v } : Config).nreg r = d.nreg r := by
        intro r h2 h3
        simp only
        rw [upd_other _ _ _ h2]
        by_cases hrA : r = ALLOC
        · subst hrA; simp only [hd₃, upd_same]; exact hA₂
        rcases h3 with h3 | h3
        swap
        · exact absurd h3 hrA
        · rw [k₃ _ hrA]
          rw [fB.1 r (by
            simp only [Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]
            simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton,
              bandOf] at h3
            omega)]
          show regB d.nmem ssLd d.nreg r = _
          rw [vo r (by rintro rfl; exact h3 (by decide)) (by rintro rfl; exact h3 (by decide))
            (by rintro rfl; exact h3 (by decide)) (by rintro rfl; exact h3 (by decide))
            (by rintro rfl; exact h3 (by decide)) (by rintro rfl; exact h3 (by decide))
            hrA (by
              by_contra hc
              simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton,
                bandOf] at h3
              omega)]
      refine ⟨_, _, .ifLtN_true (by rwa [jS, had]) (.ifLtN_true (by rwa [jS, hbd])
        (.seq e₁ (.seq e₂ (.seq e₃ e₄)))), by simp only [ssLd, ssLdA] at *; simp; omega,
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r _ _ h2 h3 => keep r h2 h3, fun r hr => ?_,
        ?_, ?_, ?_⟩
      all_goals first
        | (rw [keep _ (by simp [sw, cGW, gRB, gRC, K0, K1, srA0]) (Or.inl (by decide))]; assumption)
        | skip
      · intro a' ha'
        show d₂.nmem a' = _
        rw [fB.2.2.1]; exact jm a' ha'
      · simp only [upd_same]
        rw [had, hbd]
        split_ifs with h
        · exact hvi.2 (hiff.1 h)
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hv with h' | h'
          · exact h'
          · exact absurd (hiff.2 (hvi.1 h')) h
      · show d₂.rreg r = d.rreg r
        rw [fB.2.1 r (by
          simp only [Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]
          simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton,
            bandOf] at hr
          omega)]
      · exact fB.2.2.1
      · exact fB.2.2.2.1
      · exact fB.2.2.2.2
    · obtain ⟨c', k, ex, hk, rest⟩ := bit 1 le_rfl ⟨fun _ => by
          rw [ssLe_iff, ite_eq_left (by rwa [← jS])]; intro h; rw [jS] at hb; omega,
        fun _ => rfl⟩
      exact ⟨c', _, .ifLtN_true ha (.ifLtN_false hb ex), by omega, rest⟩
  · by_cases hb : d.nreg 30001 < d.nreg gRC
    · obtain ⟨c', k, ex, hk, rest⟩ := bit 0 (by omega) ⟨fun h => absurd h (by norm_num), fun h => by
          rw [ssLe_iff, ite_eq_right (by rwa [← jS])] at h; rw [jS] at hb; omega⟩
      exact ⟨c', _, .ifLtN_false ha (.ifLtN_true hb ex), by omega, rest⟩
    · obtain ⟨c', k, ex, hk, rest⟩ := bit 1 le_rfl ⟨fun _ => by
          rw [ssLe_iff, ite_eq_right (by rwa [← jS])]; rw [jS] at hb; omega, fun _ => rfl⟩
      exact ⟨c', _, .ifLtN_false ha (.ifLtN_false hb ex), by omega, rest⟩

end

end SweepEv

end Chazelle.Core
