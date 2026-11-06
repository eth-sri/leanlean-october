module

public import Chazelle.MacT
public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.ShootCutDyDn
public import Chazelle.Core.BruteCorner
public import Chazelle.Core.OracleRamLoad
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.GranInitL3

namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
def clqCopy : Stmt := block [.addN 70119 70115 70105, .loadN 70114 70119,
  .subN 70114 70114 70105, .storeN ALLOC 70114, .addN ALLOC ALLOC 70105,
  .addN 70119 70113 70118, .loadN 70114 70119, .storeN ALLOC 70114, .addN ALLOC ALLOC 70105,
  .addN 70119 70119 70105, .loadN 70114 70119, .storeN ALLOC 70114, .addN ALLOC ALLOC 70105,
  .addN 70110 70110 70105]

/-- One result. -/
def clqBody : Stmt :=
  .seq (block [.loadN 70114 70113])
    (.seq ztejo
      ztgfj)

/-- The collection loop. -/
def clqLoop : Stmt := .whileLtN 70112 70111 clqBody
variable {P : Polygon} {W : ℕ} {L : List (ℕ × ℕ × ℕ)} {R : List (ℕ × ℕ × ℕ × ℕ)} {QB RB LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
set_option maxHeartbeats 4000000 in
theorem clqCopy_exec (c : Config) (hw : WordsBounded W c) {s t a K : ℕ}
    (h13 : c.nreg 70113 = s) (h15 : c.nreg 70115 = t) (hA : c.nreg ALLOC = a)
    (h05 : c.nreg 70105 = 1) (h18 : c.nreg 70118 = 2) (h10 : c.nreg 70110 = K)
    (hs : s + 3 ≤ W) (ht : t + 1 ≤ W) (ha : a + 3 ≤ W) (hK : K + 1 ≤ W) (hsa : s + 3 < a)
    (_hta : t + 1 < a) :
    ∃ c' k, Exec P W clqCopy c c' k ∧ k = 14 ∧ c'.nreg ALLOC = a + 3 ∧
      ztfjr ∧
      c'.nmem a = c.nmem ztbx - 1 ∧ c'.nmem ztdf = c.nmem ztfp ∧
      c'.nmem ztvj = c.nmem ztjv ∧ c'.nreg 70110 = K + 1 ∧
      (∀ r, r ≠ 70110 → r ≠ 70114 → r ≠ 70119 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clqCopy
  zubtg
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h13, h15, hA', h05, h18, h10, ALLOC]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl⟩
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h13, h15, hA', h05, h18, h10, ALLOC])
  · zujwo
    zup

/-- The invariant of the collection loop (`pre`: the triples written before the loop). -/
structure CLQI (W : ℕ) (L : List zte) (R : List ztpl) (QB RB LB : ℕ)
    (pre : List zte) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 70112 ≤ R.length
  cur : c.nreg 70113 = RB + 4 * c.nreg 70112
  qcur : c.nreg 70115 = QB + 3 * c.nreg 70112
  alloc : c.nreg ALLOC = LB + 3 * (pre ++ collectQ ztzca
    ztzcz).length
  cnt : c.nreg 70110 = (pre ++ collectQ ztzca ztzcz).length
  regs : ∀ r, r ≠ 70110 → r ≠ 70112 → r ≠ 70113 → r ≠ 70114 → r ≠ 70115 → r ≠ 70119 →
    r ≠ ALLOC → c.nreg r = c₀.nreg r
  low : ∀ a, a < LB + 3 * pre.length → c.nmem a = c₀.nmem a
  list : ChordListAt c.nmem LB (pre ++ collectQ ztzca ztzcz)
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
set_option maxHeartbeats 8000000 in
theorem clqBody_step
 {c₀ c : Config}
    (hI : CLQI W L R QB RB LB pre c₀ c) (ht : c.nreg 70112 < R.length) (h05 : c₀.nreg 70105 = 1)
    (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70116 = 3) (h17 : c₀.nreg 70117 = 4)
    (h18 : c₀.nreg 70118 = 2) (hLR : L.length = R.length)
    (hR : ResultListAt c₀.nmem RB R) (hQ : ChordListAt c₀.nmem QB L)
    (hRB : RB + 4 * R.length ≤ LB) (hQB : QB + 3 * L.length ≤ LB)
    (hW : LB + 3 * pre.length + 3 * R.length + 4 ≤ W) (hWK : pre.length + R.length + 1 ≤ W) :
    ∃ c' k, Exec P W clqBody c c' k ∧ CLQI W L R QB RB LB pre c₀ c' ∧ k ≤ 22 ∧ 4 ≤ k ∧
      c'.nreg 70112 = c.nreg 70112 + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, c.nreg 70112 = j := by_simp_all
  zukuk
  zukcu
  zumeq
  have r05 : ztplz := by rw [hreg _ by_decide by_decide by_decide by_decide
    by_decide by_decide by_decide, h05]
  have r08 : ztuoa := by rw [hreg _ by_decide by_decide by_decide by_decide
    by_decide by_decide by_decide, h08]
  have r16 : c.nreg 70116 = 3 := by rw [hreg _ by_decide by_decide by_decide by_decide
    by_decide by_decide by_decide, h16]
  have r17 : c.nreg 70117 = 4 := by rw [hreg _ by_decide by_decide by_decide by_decide
    by_decide by_decide by_decide, h17]
  have r18 : c.nreg 70118 = 2 := by rw [hreg _ by_decide by_decide by_decide by_decide
    by_decide by_decide by_decide, h18]
  have hcur : c.nreg 70113 = RB + 4 * j := by rw [hI.cur, hj]
  have hqcur : c.nreg 70115 = QB + 3 * j := by rw [hI.qcur, hj]
  obtain ⟨q0, q1, q2, q3⟩ := hR j ht
  obtain ⟨p0, p1, p2⟩ := hQ j hjL
  set r := R.getD j ztlt with hr
  set q := L.getD j ztt with hq
  set C0 := pre ++ collectQ ztuzl ztvcz with hC0
  have hmem : ∀ k, k < 4 → c.nmem _ = c₀.nmem (RB + 4 * j + k) :=
    fun k hk => hI.low _ by_omega
  have hqmem : c.nmem _ = c₀.nmem (QB + 3 * j + 1) := hI.low _ by_omega
  have hlenj : (collectQ ztuzl ztvcz).length ≤ j :=
    (collectQ_length_le _ _).trans by_simp
  have htake : R.take ztl = R.take j ++ [r] := by
    rw [hr, getD_lt ht]; simp
  have htakeL : L.take ztl = L.take j ++ [q] := by
    rw [hq, getD_lt hjL]; simp
  have hlt : (L.take j).length = (R.take j).length := by_grind
  have hlenC : C0.length ≤ pre.length + j := by_grind
  -- the flag
  have e₁ := Exec.loadN (P := P) hI.wb 70114 70113
  set c₁ : Config := { c with nreg := upd c.nreg 70114 _ } with hc₁
  have v14 : c₁.nreg 70114 = r.1 := by
    zvmxj; zumwv; rw [hcur]
    have := hmem 0 by_omega; grind
  have q₁ : ∀ x, x ≠ 70114 → c₁.nreg x = c.nreg x := fun x hx => by
    zvmxj; simp [upd_other _ _ _ hx]
  zuka
  -- the copy (or not)
  obtain ⟨c₂, k₂, e₂, hk₂, a₂, n₂, m₂, l₂, q₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      ztejo c₁ c₂ k₂ ∧ k₂ ≤ 16 ∧
      c₂.nreg ALLOC = LB + 3 * (pre ++ collectQ ztyhr ztyhy).length ∧
      c₂.nreg 70110 = (pre ++ collectQ ztyhr ztyhy).length ∧
      (∀ a, a < LB + 3 * C0.length → c₂.nmem a = c.nmem a) ∧
      ChordListAt c₂.nmem LB (pre ++ collectQ ztyhr ztyhy) ∧
      (∀ x, x ≠ 70110 → x ≠ 70114 → x ≠ 70119 → x ≠ ALLOC → c₂.nreg x = c.nreg x) ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    have hc0 : pre ++ collectQ ztyhr ztyhy = C0 ++
        ztfsr := by
      rw [htake, htakeL, collectQ_append hlt, hC0, List.append_assoc]
    have hA0 : c.nreg ALLOC = LB + 3 * C0.length := by zuoko
    have h10 : c.nreg 70110 = C0.length := by zuokp
    by_cases hf : r.1 = 1
    · rw [ite_eq_left hf] at hc0
      have hlt1 : c₁.nreg 70108 < c₁.nreg 70114 := by
        grind
      have hlt2 : c₁.nreg 70114 < c₁.nreg 70118 := by
        grind
      set a := LB + 3 * C0.length
      obtain ⟨c₂, k₂, e₂, hk₂, a₂, mo, m0, m1, m2, n10, R₂, rr₂, rm₂, o₂⟩ := clqCopy_exec
        c₁ hw₁ (s := RB + 4 * j) (t := QB + 3 * j) (K := C0.length)
        by_grind by_grind
        by_tauto by_grind
        by_grind by_grind by_omega by_omega
        by_omega by_omega by_omega by_omega
      refine ⟨c₂, _, .ifLtN_true hlt1 (.ifLtN_true hlt2 e₂), by_omega, ?_, ?_, fun x hx => ?_,
        ?_, fun x a1 a2 a3 a4 => ?_, by zunsn, by zuoez, by zuofa⟩
      · rw [a₂, hc0, List.length_append, List.length_singleton]; omega
      · rw [n10, hc0]; simp
      · grind
      · zunso
        zugmp

        have hl : ChordListAt c₂.nmem LB C0 := fun i hi => by
          zufir
          zusk
          · grind
          · grind
          grind
        refine chordListAt_append hl ?_ ?_ ?_
        · grind
        · grind
        grind
      grind
    · rw [ite_eq_right hf, List.append_nil] at hc0
      have hsk : Exec P W ztejo c₁ c₁
          (if c₁.nreg 70108 < c₁.nreg 70114 then 0 + 2 + 1 else 0 + 2) := by
        by_cases hlt1 : c₁.nreg 70108 < c₁.nreg 70114
        · rw [ite_eq_left hlt1]
          have hlt2 : ¬ c₁.nreg 70114 < c₁.nreg 70118 := by
            grind
          exact .ifLtN_true hlt1 (.ifLtN_false hlt2 ztekd)
        · rw [ite_eq_right hlt1]; exact .ifLtN_false hlt1 ztekd
      refine ⟨c₁, _, hsk, by_grind, ?_, ?_, by_grind, ?_,
        by grind, rfl, rfl, rfl⟩
      · rw [q₁ _ by_decide, hA0, hc0]
      · grind
      · zunso; have := hI.list; grind
  zuja
  have c205 := (q₂ _ by_decide by_decide by_decide by_decide).trans r05
  have c216 := (q₂ _ by_decide by_decide by_decide by_decide).trans r16
  have c217 := (q₂ _ by_decide by_decide by_decide by_decide).trans r17
  have r13 : c₂.nreg 70113 = RB + 4 * j := by
    rw [q₂ _ by_decide by_decide by_decide by_decide, hcur]
  have r15 : c₂.nreg 70115 = QB + 3 * j := by
    rw [q₂ _ by_decide by_decide by_decide by_decide, hqcur]
  have r12 : c₂.nreg 70112 = j := by rw [q₂ _ by_decide by_decide by_decide by_decide, hj]
  obtain ⟨c₃, k₃, e₃, hk₃, u13, u15, u12, u₃, um₃, urr₃, urm₃, uo₃⟩ : ∃ c₃ k₃, Exec P W
      ztgfj c₂ c₃ k₃ ∧
      k₃ = 3 ∧ c₃.nreg 70113 = RB + 4 * ztl ∧ c₃.nreg 70115 = QB + 3 * ztl ∧
      c₃.nreg 70112 = j + 1 ∧
      (∀ r, r ≠ 70112 → r ≠ 70113 → r ≠ 70115 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, r13, r15, r12, c205, c216, c217]; omega)
    refine ztbfo
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      r13, r15, r12, c205, c216, c217]
    all_goals ring
  have ex : Exec P W clqBody c c₃ _ :=
    .seq ztzsa ztcr
  refine ⟨c₃, _, ex, ⟨e₃.wb_right, by_omega, by_omega, by_omega,
    by rw [u12, u₃ _ by_decide by_decide by_decide]; exact a₂,
    by grind,
    fun x a1 a2 a3 a4 a5 a6 a7 => ?_, fun a ha => ?_, by_grind,
    by rw [urr₃, rr₂, hI.rr], by rw [urm₃, rm₂, hI.rm], by rw [uo₃, o₂, hI.out]⟩,
    by omega, by_omega, by_omega⟩
  · rw [u₃ x a2 a3 a5, q₂ x a1 a4 a6 a7, hreg x a1 a2 a3 a4 a5 a6 a7]
  · have : pre.length ≤ C0.length := by_grind
    rw [um₃, m₂ a by_omega, hI.low a ha]

/-- **The collection loop.** -/
theorem clqLoop_exec
 {c₀ : Config}
    (h05 : c₀.nreg 70105 = 1) (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70116 = 3)
    (h17 : c₀.nreg 70117 = 4) (h18 : c₀.nreg 70118 = 2) (h11 : c₀.nreg 70111 = R.length)
    (hLR : L.length = R.length)
    (hR : ResultListAt c₀.nmem RB R) (hQ : ChordListAt c₀.nmem QB L)
    (hRB : RB + 4 * R.length ≤ LB) (hQB : QB + 3 * L.length ≤ LB)
    (hW : LB + 3 * pre.length + 3 * R.length + 4 ≤ W) (hWK : pre.length + R.length + 1 ≤ W) :
    ∀ (n : ℕ) (c : Config), CLQI W L R QB RB LB pre c₀ c → c.nreg 70112 + n = R.length →
      ∃ c' k, Exec P W clqLoop c c' k ∧ k ≤ 24 * n + 2 ∧ 3 * n ≤ k ∧
        CLQI W L R QB RB LB pre c₀ c' ∧
        c'.nreg 70112 = R.length
  | 0, c, hI, hn => by
    have h11' : ztuob := by
      rw [hI.regs 70111 by_decide by_decide by_decide by_decide by_decide by_decide
        by_decide, h11]
    exact ztdiz
  | n + 1, c, hI, hn => by
    have ht : c.nreg 70112 < R.length := by_omega
    obtain ⟨c', k, e, hI', hk, hk4, hc'⟩ := clqBody_step (P := P) hI ht h05 h08 h16 h17 h18 hLR hR hQ
      hRB hQB hW hWK
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := clqLoop_exec h05 h08 h16 h17 h18 h11 hLR hR hQ hRB hQB
      hW hWK n c' hI' by_omega
    have h11' : ztuob := by
      rw [hI.regs 70111 by_decide by_decide by_decide by_decide by_decide by_decide
        by_decide, h11]
    exact ⟨c'', k + 2 + k₂, .whileLtN_true by_omega e e₂, by_omega, by_omega,
      hI'', hK⟩
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
@[expose] public section
open Chazelle.Merge (FreeAt shoot)
variable (J : Merge.Junction) (Q : Polygon)

/-- The query set of the fused family. -/
def fuseZ (S₁ S₂ : Set ztf) : Set ztdgb :=
  endQ ztbzc ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J

/-- The geometric queries of the two sweeps cover the query set of the fused family. -/
def Cover (S₁ S₂ : Set ztf) (L₀ L₁ : List zte) : Prop :=
  geoQ J Q 0 L₀ ∪ geoQ J Q 1 L₁ ⊆ fuseZ J S₁ S₂ ∧
    ∀ x ∈ fuseZ J S₁ S₂, FreeAt J.whole x.1 x.2 → x ∈ geoQ J Q 0 L₀ ∪ geoQ J Q 1 L₁

/-- The answers of the two sweeps. -/
structure Answers (L₀ L₁ : List zte) (R₀ R₁ : List ztpl) : Prop where
  len₀ : R₀.length = L₀.length
  len₁ : R₁.length = L₁.length
  sees₀ : ∀ j, j < L₀.length →
    SeesInWhole J Q 0 (L₀.getD j ztt) (R₀.getD j ztlt)
  sees₁ : ∀ j, j < L₁.length →
    SeesInWhole J Q 1 (L₁.getD j ztt) (R₁.getD j ztlt)
  ok₀ : ∀ q ∈ L₀, QueryOK J Q 0 q ∧ HeightOK J Q 0 q
  ok₁ : ∀ q ∈ L₁, QueryOK J Q 1 q ∧ HeightOK J Q 1 q
theorem fuseList_set {S₁ S₂ : Set ztf} {L₀ L₁ : List zte}
    {R₀ R₁ : List ztpl} (hA : Answers J Q L₀ L₁ R₀ R₁) (hC : Cover J Q S₁ S₂ L₀ L₁)
    {D : List zte} (hD : ∀ x, x ∈ D ↔ x ∈ collectQ L₀ R₀ ++ collectQ L₁ R₁) :
    {c | ∃ x ∈ D, c = (recOf x).toSet ztbm Q} =
        J.fusion S₁ S₂ ∪ glueChords J ∧
      ∀ x ∈ D, (recOf x).Attached ztbm Q ∧ x.1 < Q.n := by
  obtain ⟨e₀, a₀⟩ := collectQ_spec J Q 0 L₀ R₀ hA.len₀ hA.sees₀ hA.ok₀
  obtain ⟨e₁, a₁⟩ := collectQ_spec J Q 1 L₁ R₁ hA.len₁ hA.sees₁ hA.ok₁
  refine ⟨?_, fun x hx => ?_⟩
  · rw [fused_eq_shots, show endQ ztbzc ∪ vtxQ J J.m₁ ∪ topQ J ∪ capQ J = fuseZ J S₁ S₂ from rfl,
      ← shots_eq_of J hC.1 hC.2, shots_union, ← e₀, ← e₁]
    zubcj
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    grind
  grind

/-- **The chord list of the fusion is a valid input of `BuildNF`.** -/
theorem fuseList_ok (hP : J.P.Simple) (hQ : DistinctHeights Q) (hgen : SharedGeneric J)
    {S₁ S₂ : Set ztf} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {L₀ L₁ : List zte}
    {R₀ R₁ : List ztpl} (hA : Answers J Q L₀ L₁ R₀ R₁) (hC : Cover J Q S₁ S₂ L₀ L₁)
    {D : List zte} (hD : ∀ x, x ∈ D ↔ x ∈ collectQ L₀ R₀ ++ collectQ L₁ R₁)
    (hnd : D.Nodup) :
    ChordTriplesOK ztbm Q D ∧
      {c | ∃ x ∈ D, c = (recOf x).toSet ztbm Q} =
        J.fusion S₁ S₂ ∪ glueChords J ∧
      D.length ≤ L₀.length + L₁.length := by
  obtain ⟨hset, hatt⟩ := fuseList_set J Q hA hC hD
  have hadm := FuseDeg.fuse_adm J hgen hS₁.2.1 hS₂.2.1
  have hmemF : ∀ x ∈ D, (recOf x).toSet ztbm Q ∈ (chainModel J.whole).Adm :=
    fun x hx => hadm by_grind
  refine ⟨⟨ztcg, ?_, fun x hx => (hatt x hx).1, fun x hx => (hatt x hx).2⟩, hset, ?_⟩
  · have : {c | ∃ x ∈ D, c = (recOf x).toSet ztbm Q} =
        (fun x => (recOf x).toSet ztbm Q) '' {x | x ∈ D} := by
      ext c; grind
    zvmwk; exact (D.finite_toSet).image _
  · grind
  · zueq
    exact ⟨x.1, (hatt x hx).2, _, _, rfl⟩
  · refine hnd.map_on fun x hx y hy he => ?_
    zucvz
    obtain ⟨e1, e2, e3⟩ := rec_eq_of_toSet hM hQ (hatt x hx).1 (hatt y hy).1 (hmemF x hx)
      (hatt x hx).2 (hatt y hy).2 he
    obtain ⟨a, b, d⟩ := x
    obtain ⟨a', b', d'⟩ := y
    simp only [recOf] at e1 e2 e3
    simp_all
  · have hsub : D ⊆ collectQ L₀ R₀ ++ collectQ L₁ R₁ := fun x hx => (hD x).1 hx
    have := (hnd.subperm hsub).length_le
    rw [List.length_append] at this
    have h0 := collectQ_length_le L₀ R₀
    have h1 := collectQ_length_le L₁ R₁
    omega
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
@[expose] public section
open Chazelle.Merge (FreeAt)
variable (J : Merge.Junction) (Q : Polygon)

/-- The answer to a point query `(z, σ)` of side `i`: a list of valid queries at `z` in
direction `σ`, empty only if `σ` is not free for `C` at `z`. -/
def PtAns (i : ℕ) (z : Point) (σ : ℝ) (l : List zte) : Prop :=
  (∀ q ∈ l, QueryOK J Q i q ∧ HeightOK J Q i q ∧
    (chainModel ztgi).pos Q ztpo = z ∧ dirOf q.2.2 = σ) ∧
    (l = [] → ¬ FreeAt J.whole z σ)

/-- The parameter of a position does not depend on the height code, among codes of the height of
its point. -/
theorem param_eq_of_pos (M : Model) {e h' hv : ℕ} {z : Point} (hpos : M.pos Q ztkkv = z)
    (hhv : (Q.vtx hv).2 = z.2) : M.param Q ⟨e, hv + 1⟩ = M.param Q ztkkv := by
  cases h' with
  | zero =>
    have hwa : M.wa e = z := by
      zuora; unfold Model.pos; rw [show M.param Q ztjy = 0 from rfl, Geometry.lerp_zero]
    rw [param_of_vertex M Q e hv by_simp_all]; rfl
  | succ h =>
    by_cases hh : (M.wa e).2 = (M.wb e).2
    · zudcl
    · have hy : (Q.vtx h).2 = (Q.vtx hv).2 := by
        have hpos' := hpos
        unfold Model.pos Model.param at hpos'
        simp only at hpos'
        rw [ite_eq_right hh] at hpos'
        rw [hhv, ← hpos', Geometry.lerp_snd]
        grind
      exact param_congr M Q e hy.symm

/-- **An arrival position gives a point query.** -/
theorem ptAns_some (i : ℕ) {e' h' ρ hv : ℕ} {z : Point}
    (hA : Sweep.Arrival (chainModel ztgi).W z ztdep e'
      ((chainModel ztgi).param Q ztonh))
    (hhv : (Q.vtx hv).2 = z.2) (hvn : hv < Q.n) (hz2 : z.2 ≤ (sideChain J i).top.2) :
    PtAns J Q i z ztern [ztnxr] := by
  zulrj
  have hpos : M.pos Q ztonh = z := by
    rw [SweepPrim.pos_eq_sidePt]; exact hA.2.2.2.1
  have hpar := param_eq_of_pos Q M hpos hhv
  obtain ⟨hq, hp⟩ := queryOK_of_arrival J Q i (h := hv) hA hpar by_omega hz2
  refine ⟨fun q hq' => ?_, fun h => absurd h by_simp⟩
  zvnns at hq'
  subst hq'
  refine ⟨hq, ?_, hp, rfl⟩
  unfold HeightOK; simp_all

/-- **No arrival position: the direction is not free.** -/
theorem ptAns_none (hP : J.P.Simple) (i : ℕ) {ρ : ℕ} {z : Point}
    (hz : z ∈ (sideChain J i).set) (hz2 : z.2 ≤ (sideChain J i).top.2)
    (hnone : ∀ p t, ¬ Sweep.Arrival (chainModel ztgi).W z ztdep p t) :
    PtAns J Q i z ztern [] :=
  ⟨fun q hq => absurd hq by_simp, fun _ =>
    not_free_of_none J hP i (SweepPrim.dirOf_cases' ρ) hz hz2 hnone⟩
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
@[expose] public section
open Chazelle.Merge (FreeAt lend rend)
variable (J : Merge.Junction) (Q : Polygon)
theorem geoQ_append (i : ℕ) (A B : List zte) :
    geoQ J Q i ztldt = geoQ J Q i A ∪ geoQ J Q i B := by
  ext x; simp only [geoQ, List.mem_append, Set.mem_union, Set.mem_ofPred_eq]
  grind
theorem endQ_union (S₁ S₂ : Set ztf) : endQ ztbzc = endQ S₁ ∪ endQ S₂ := by
  ext x; simp only [endQ, Set.mem_union, Set.mem_ofPred_eq]
  grind
variable {i : ℕ} {z : Point} {σ : ℝ} {l : List (ℕ × ℕ × ℕ)}
theorem geo_ptAns (h : PtAns J Q i z σ l) :
    geoQ J Q i l ⊆ {ztues} ∧ (FreeAt J.whole z σ → ztues ∈ geoQ J Q i l) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro x ⟨q, hq, rfl⟩
    obtain ⟨-, -, hp, hd⟩ := h.1 q hq
    simp_all
  · cases l with
    | nil => exact absurd hf (h.2 rfl)
    | cons q l =>
      obtain ⟨-, -, hp, hd⟩ := h.1 q by_simp
      exact ⟨q, by_simp, by_simp_all⟩
theorem ok_ptAns (h : PtAns J Q i z σ l) :
    ∀ q ∈ l, QueryOK J Q i q ∧ HeightOK J Q i q := fun q hq =>
  ⟨(h.1 q hq).1, (h.1 q hq).2.1⟩

/-- The chord-end queries have the heights of their codes. -/
theorem endQL_height (i : ℕ) {N : NF} (hN : IsNF ztxgp Q N) :
    ∀ q ∈ endQL N.chords, HeightOK J Q i q := by
  zuco
  simp only [endQL, List.mem_map, List.mem_range] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  have hk : j / 2 < N.chords.length := by_omega
  have hA := hN.2.2.1 ztwm hk
  unfold NF.chord at hA
  obtain ⟨⟨-, -, -, hml, -⟩, ⟨-, -, -, hmr, -⟩⟩ := hA
  unfold HeightOK
  split_ifs
  · zudli
    exact hml.1
  · zudli
    exact hmr.1

/-- The nearer arm of the cap is `u` (the far arm `[v, w]` is on `C₂`). -/
def NearU : Prop := |(sharedU J).2 - (sharedV J).2| < |(sharedW J).2 - (sharedV J).2|

/-- The cap queries of the two sides. -/
def CapAns (k₀ k₁ : List zte) : Prop :=
  (SharedExtremum J → (¬ NearU J → PtAns J Q 0 ztchm ztchl k₀ ∧ k₁ = []) ∧
    (NearU J → k₀ = [] ∧ PtAns J Q 1 ztchm ztchl k₁)) ∧
  (¬ SharedExtremum J → k₀ = [] ∧ k₁ = [])

/-- The point queries of the two sides. -/
structure PtLists (v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁ : List zte) : Prop where
  v₁ : PtAns J Q 0 zthrd 1 v₁
  v₀ : PtAns J Q 0 zthrd (-1) v₀
  t₁ : PtAns J Q 0 zthrc 1 t₁
  t₀ : PtAns J Q 0 zthrc (-1) t₀
  t'₁ : PtAns J Q 1 ztxmv 1 t'₁
  t'₀ : PtAns J Q 1 ztxmv (-1) t'₀
  cap : CapAns J Q k₀ k₁
theorem cover_of {N₁ N₂ : NF} (hN₁ : IsNF ztbw Q N₁)
    (hN₂ : IsNF ztj Q N₂) {v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁ : List zte}
    (hP : PtLists J Q v₁ v₀ t₁ t₀ k₀ t'₁ t'₀ k₁) :
    Cover J Q ztxvq ztwzm
        ztxgr
        ztxwm ∧
      (∀ q ∈ endQL N₁.chords ++ ztky,
        QueryOK J Q 0 q ∧ HeightOK J Q 0 q) ∧
      (∀ q ∈ endQL N₂.chords ++ ztdij, QueryOK J Q 1 q ∧ HeightOK J Q 1 q) := by
  have hN₁' : IsNF ztbagu Q N₁ := hN₁
  have hN₂' : IsNF ztbagv Q N₂ := hN₂
  obtain ⟨ok₁, ge₁⟩ := endQL_ok J Q 0 hN₁'
  obtain ⟨ok₂, ge₂⟩ := endQL_ok J Q 1 hN₂'
  have ge₁' : geoQ J Q 0 (endQL N₁.chords) = endQ ztxvq := ge₁
  have ge₂' : geoQ J Q 1 (endQL N₂.chords) = endQ ztwzm := ge₂
  have he₁ := endQL_height J Q 0 hN₁'
  have he₂ := endQL_height J Q 1 hN₂'
  obtain ⟨gv₁, fv₁⟩ := geo_ptAns J Q hP.v₁
  obtain ⟨gv₀, fv₀⟩ := geo_ptAns J Q hP.v₀
  obtain ⟨gt₁, ft₁⟩ := geo_ptAns J Q hP.t₁
  obtain ⟨gt₀, ft₀⟩ := geo_ptAns J Q hP.t₀
  obtain ⟨gs₁, fs₁⟩ := geo_ptAns J Q hP.t'₁
  obtain ⟨gs₀, fs₀⟩ := geo_ptAns J Q hP.t'₀
  have hS : sideChain J 0 = J.left := rfl
  have hS' : ztsmf := rfl
  -- the cap pieces
  have gk : geoQ J Q 0 k₀ ∪ geoQ J Q 1 k₁ ⊆ capQ J ∧
      (∀ x ∈ capQ J, FreeAt J.whole x.1 x.2 → x ∈ geoQ J Q 0 k₀ ∪ geoQ J Q 1 k₁) := by
    zueub

    · zueit

      · zuhhj
        obtain ⟨g, f⟩ := geo_ptAns J Q h1
        zumpx
        refine ztiwg
        · rcases hx' with ⟨q, hq, -⟩ | hx'
          · grind
          · have := g hx'; trivial
        · zugos
      · zuhhl
        obtain ⟨g, f⟩ := geo_ptAns J Q h0
        zumpy
        refine ztiwg
        · rcases hx' with hx' | ⟨q, hq, -⟩
          · have := g hx'; trivial
          grind
        · zugos
    · obtain ⟨e0, e1⟩ := hc2 hx
      subst e0 e1
      refine ⟨fun x hx' => ?_, fun x hx' _ => absurd hx'.1 hx⟩
      rcases hx' with ⟨q, hq, -⟩ | ⟨q, hq, -⟩ <;> simp at hq
  have okk : (∀ q ∈ k₀, QueryOK J Q 0 q ∧ HeightOK J Q 0 q) ∧
      ∀ q ∈ k₁, QueryOK J Q 1 q ∧ HeightOK J Q 1 q := by
    zueub

    · zueit

      · zuhhj
        zumpx
        exact ⟨fun q hq => by_grind, ok_ptAns J Q h1⟩
      · zuhhl
        zumpy
        exact ⟨ok_ptAns J Q h0, fun q hq => by_grind⟩
    grind
  set Z := fuseZ J ztxvq ztwzm with hZ
  have zv₁ : (J.whole.vertex J.m₁, (1 : ℝ)) ∈ Z := Or.inl (Or.inl ztwiz)
  have zv₀ : (J.whole.vertex J.m₁, (-1 : ℝ)) ∈ Z := Or.inl (Or.inl ztwrm)
  have zt₁ : (J.whole.vertex J.left.topIdx, (1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr ztxvr)
  have zt₀ : (J.whole.vertex J.left.topIdx, (-1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr (Or.inl ztbt))
  have zs₁ : (J.whole.vertex ztrw, (1 : ℝ)) ∈ Z :=
    Or.inl ztbajm
  have zs₀ : (J.whole.vertex ztrw, (-1 : ℝ)) ∈ Z :=
    Or.inl (Or.inr ztwrm)
  have ze₁ : endQ ztxvq ⊆ Z := fun x h =>
    Or.inl ztihl
  have ze₂ : endQ ztwzm ⊆ Z := fun x h =>
    Or.inl ztihl
  have zk : capQ J ⊆ Z := fun x h => Or.inr h
  have sing : ∀ {i : ℕ} {l : List zte} {y : Point × ℝ}, geoQ J Q i l ⊆ {y} → y ∈ Z →
      geoQ J Q i l ⊆ Z := fun h hy x hx => by
    have := h hx; grind
  have mono : ∀ {i : ℕ} {A B : List zte}, (∀ q ∈ A, q ∈ B) →
      geoQ J Q i A ⊆ geoQ J Q i B := fun h x ⟨q, hq, hx⟩ => ⟨q, h q hq, hx⟩
  refine ztziq
  · rw [geoQ_append, geoQ_append, geoQ_append, geoQ_append, geoQ_append, geoQ_append,
      geoQ_append, geoQ_append, ge₁, ge₂]
    refine Set.union_subset (Set.union_subset ze₁ (Set.union_subset (Set.union_subset
      (Set.union_subset (Set.union_subset (sing gv₁ zv₁) (sing gv₀ zv₀)) (sing gt₁ zt₁))
      (sing gt₀ zt₀)) ?_)) (Set.union_subset ze₂ (Set.union_subset (Set.union_subset
      (sing gs₁ zs₁) (sing gs₀ zs₀)) ?_))
    · exact fun x hx => zk (gk.1 zthrs)
    · exact fun x hx => zk (gk.1 (Or.inr hx))
  · intro x hx hf
    have m₀ : ∀ {l : List zte}, (∀ q ∈ l, q ∈ endQL N₁.chords ++
        ztky) → x ∈ geoQ J Q 0 l →
        x ∈ geoQ J Q 0 ztxgr ∪
          geoQ J Q 1 ztxwm := fun h hx => Or.inl ztttp
    have m₁ : ∀ {l : List zte}, (∀ q ∈ l, q ∈ endQL N₂.chords ++
        ztdij) → x ∈ geoQ J Q 1 l →
        x ∈ geoQ J Q 0 ztxgr ∪
          geoQ J Q 1 ztxwm := fun h hx => Or.inr ztttp
    obtain ((he | hv) | ht) | hk := hx
    · rw [endQ_union] at he
      rcases he with h | h
      · rw [← ge₁'] at h; exact m₀ ztxm h
      · rw [← ge₂'] at h; exact m₁ ztxm h
    · rcases hv with h | h <;> (try rw [Set.mem_singleton_iff] at h) <;> subst h
      · exact m₀ ztxm (fv₁ hf)
      · exact m₀ ztxm (fv₀ hf)
    · rcases ht with (h | h) | (h | h) <;> (try rw [Set.mem_singleton_iff] at h) <;> subst h
      · exact m₀ ztxm (ft₁ hf)
      · exact m₀ ztxm (ft₀ hf)
      · exact m₁ ztxm (fs₁ hf)
      · exact m₁ ztxm (fs₀ hf)
    · rcases gk.2 x hk hf with h' | h'
      · exact m₀ ztxm h'
      · exact m₁ ztxm h'
  · zuco
    zubmm

    · grind
    · exact ok_ptAns J Q hP.v₁ q h
    · exact ok_ptAns J Q hP.v₀ q h
    · exact ok_ptAns J Q hP.t₁ q h
    · exact ok_ptAns J Q hP.t₀ q h
    grind
  · zuco
    zucqv

    · grind
    · exact ok_ptAns J Q hP.t'₁ q h
    · exact ok_ptAns J Q hP.t'₀ q h
    grind
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
@[expose] public section
open WalkEmbed
open Chazelle.Chain (sideE)
variable (C : Chain) (Q : Polygon)
theorem walk_vtx_tpos {k : ℕ} (hk : k ≤ C.m) :
    (chainModel C).W.vtx ztpuv = C.vertex k := by
  zukk
  zufwx
  zueqa
  have := walk_tour C k 0 by_omega
  zuhkd
  zubk
  zuhrg

  zuhay

/-- **A chain vertex as a walk position.** -/
theorem vpos {k : ℕ} (hk : k ≤ C.m) :
    (chainModel C).pos Q ztols = C.vertex k := by
  zueew
  rw [show (chainModel C).param Q ztols = 0 from rfl, Geometry.lerp_zero]
  exact walk_vtx_tpos C hk
theorem vpos_edge (k : ℕ) : 6 + tpos C k < (chainModel C).W.n := by
  have := tpos_lt C k; zvokr; omega
theorem lerp_mem_set (C : Chain) {k : ℕ} (hk : k < C.m) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Geometry.lerp ztib ztwkj t ∈ C.set :=
  ⟨k, hk, by rw [C.chainEdge_eq]; exact Geometry.lerp_mem_segment _ _ h0 h1⟩
theorem lerp_mem_set' (C : Chain) {k : ℕ} (hk : k < C.m) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Geometry.lerp ztwkj ztib t ∈ C.set :=
  ⟨k, hk, by rw [C.chainEdge_eq, Geometry.segment_comm]; exact Geometry.lerp_mem_segment _ _ h0 h1⟩
theorem abs_snd_lt_radius (C : Chain) {p : Point} (hp : p ∈ C.set) : |p.2| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).2 C.coordBound_lt_radius
variable (J : Merge.Junction)
theorem sharedV_left : sharedV J = J.left.vertex J.m₁ := rfl
theorem sharedU_left : sharedU J = J.left.vertex (J.m₁ - 1 + 1 - 1) := by
  rfl
theorem sharedV_right : sharedV J = J.right.vertex 0 := by
  rfl
theorem sharedW_right : sharedW J = J.right.vertex 1 := by
  rfl

/-- The ratio of the nearer arm to the far arm is in `(0, 1)`. -/
theorem ratio_mem {a b : ℝ} (hab : 0 < a * b) (hle : |b| ≤ |a|) (hne : a ≠ b) :
    0 ≤ b / a ∧ b / a < 1 := by
  rcases lt_or_gt_of_ne (show a ≠ 0 by rintro rfl; simp at hab) with ha | ha
  · have hb : b < 0 := by
      zubdi
    rw [abs_of_neg ha, abs_of_neg hb] at hle
    refine ⟨le_of_lt (div_pos_of_neg_of_neg hb ha), ?_⟩
    rw [div_lt_one_of_neg ha]
    grind
  · have hb : ztrzh := by
      simp_all
    rw [abs_of_pos ha, abs_of_pos hb] at hle
    refine ⟨le_of_lt (div_pos hb ha), ?_⟩
    rw [div_lt_one ha]
    grind

/-- **The cap query on `C₁`** (the nearer arm is `w`, the far arm `[v, u]` is on `C₁`). -/
theorem capPos₀ (hgen : SharedGeneric J) (hx : SharedExtremum J) (hu : ¬ NearU J)
    {h : ℕ} (hh : (Q.vtx h).2 = (capNear J).2) :
    (chainModel J.left).pos Q ztdqc = capOrigin J ∧
      0 ≤ (chainModel J.left).param Q ztdqc ∧
      (chainModel J.left).param Q ztdqc < 1 ∧
      capOrigin J ∈ J.left.set := by
  zugoz
  have hnear : capNear J = sharedW J := by unfold capNear; exact ite_eq_right hu
  have hfar : capFar J = sharedU J := by unfold capFar; exact ite_eq_right hu
  have hm := J.one_le_m₁
  set M := chainModel J.left
  have ha : M.W.vtx ztgcv = sharedV J := walk_vtx_tpos J.left by_simp
  have hb : M.W.vtx (ztnho % M.W.n) = sharedU J := by
    have := tpos_lt J.left J.m₁
    have hlm : ztcql := rfl
    rw [hlm] at this
    rw [Nat.mod_eq_of_lt (by rw [cm_n, hlm]; omega)]
    exact left_next J
  have hpos := pos_edge (Q := Q) (h := h) ha hb (Ne.symm g1)
  have hpar : M.param Q ztdqc =
      ztblm / ztbll := by
    zulbe
  have hr := ratio_mem (a := (sharedU J).2 - (sharedV J).2) (b := (sharedW J).2 - (sharedV J).2)
    hx (not_lt.1 hu) ztqns
  have hco : capOrigin J = Geometry.lerp ztiar (sharedU J)
      (ztblm / ztbll) := by
    zumsd
  refine ztomx
  rw [hco, sharedV_left, sharedU_left]
  have := lerp_mem_set' J.left (k := J.m₁ - 1) (by show J.m₁ - 1 < J.m₁; omega) hr.1 hr.2.le
  rw [show J.m₁ - 1 + 1 = J.m₁ by omega] at this ⊢; assumption

/-- **The cap query on `C₂`** (the nearer arm is `u`, the far arm `[v, w]` is on `C₂`). -/
theorem capPos₁ (hgen : SharedGeneric J) (hx : SharedExtremum J) (hu : NearU J)
    {h : ℕ} (hh : (Q.vtx h).2 = (capNear J).2) :
    (chainModel J.right).pos Q ztdqd = capOrigin J ∧
      0 ≤ (chainModel J.right).param Q ztdqd ∧
      (chainModel J.right).param Q ztdqd < 1 ∧
      capOrigin J ∈ J.right.set := by
  zugoz
  have hnear : capNear J = sharedU J := by unfold capNear; exact ite_eq_left hu
  have hfar : capFar J = sharedW J := by unfold capFar; exact ite_eq_left hu
  have hm := J.one_le_m₂
  set M := chainModel J.right
  have ha : M.W.vtx ztbrv = sharedV J := by
    rw [sharedV_right]; exact walk_vtx_tpos J.right ztbg
  have hb : M.W.vtx (ztnhp % M.W.n) = sharedW J := by
    have := tpos_lt J.right 0
    have hrm : ztdjs := rfl
    zvnmc at this
    rw [Nat.mod_eq_of_lt (by rw [cm_n, hrm]; omega)]
    exact right_next J
  have hpos := pos_edge (Q := Q) (h := h) ha hb (Ne.symm g2)
  have hpar : M.param Q ztdqd =
      ztbll / ztblm := by
    zulbe
  have hx' : 0 < ztblm * ztbll := by
    have := hx; unfold SharedExtremum at this; grind
  have hr := ratio_mem (a := (sharedW J).2 - (sharedV J).2) (b := (sharedU J).2 - (sharedV J).2)
    hx' (le_of_lt hu) ztqns
  have hco : capOrigin J = Geometry.lerp ztiar (sharedW J)
      (ztbll / ztblm) := by
    zumsd
  refine ztomx
  rw [hco, sharedV_right, sharedW_right]
  exact lerp_mem_set J.right (k := 0) by_positivity hr.1 hr.2.le

/-- The cap direction from the direction bit of `capPrim`. -/
theorem capDir_eq {ρ : ℕ} (h : ρ ≤ 1 ∧ (ρ = 1 ↔ ¬ (capNear J).1 < (capOrigin J).1)) :
    dirOf ρ = capDir J := by
  unfold dirOf capDir
  grind
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK SweepPrim WalkEmbed
@[expose] public section
theorem primRun {s : Stmt} {Inp : Polygon → ℕ → Chain → Config → Prop}
    {Out : Polygon → Chain → Config → Config → Prop} {K : ℕ}
    (hM : Meets s primBands ztqbn ztqbm ztgis) (hwr : wr Bprim s = true)
    {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hwf : ChainWF P ztm c.nmem ztbok) {H : Host}
    {C : Chain} (hC : ChainDescAt c.nmem ztbok zta H C) (hin : Inp P W C c)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ Out P C c c' ∧ FrameB Bprim c c' := by
  obtain ⟨c', k, e, hk, hout, -⟩ := hM P W c hw ⟨hG, hHW, hwf, H, C, hC, hin⟩ hroom
  exact ⟨c', k, e, hk, hout H C hC, exec_frameB e hwr⟩
variable {c c' : Config} {P : Polygon} {W : ℕ}
theorem frameB_alloc (h : FrameB Bprim c c') : c'.nreg ALLOC = c.nreg ALLOC :=
  h.1 ALLOC by_rfl
theorem frameB_reg (h : FrameB Bprim c c') {r : ℕ}
    (hr : r < 10000 ∨ ztndv ∨ ztqt ∨ 51000 ≤ r) :
    c'.nreg r = c.nreg r :=
  h.1 r (by simp only [Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)

/-! ## The tour offset of a chain vertex -/

/-- `50201 := 6 + tpos C k` (`k` in `50110`, the descriptor address in `50200`). -/
def tposS : Stmt :=
  .seq (block [.copyN 50100 50200]) (.seq readS (.seq (block [.subN 50103 50108 50102])
    (.seq (candR 50110 50102 50103 50111) ztjpf)))

/-- The registers written by `tposS`. -/
def Btp (r : ℕ) : Bool := decide (50100 ≤ r ∧ r ≤ 50112) || r == 50201
theorem wr_tposS : wr Btp tposS = true := by_decide
theorem tposS_exec (c : Config) (hw : WordsBounded W c) {Q : Polygon}
    {H : Host} {C : Chain} (hC : ChainDescAt c.nmem ztbok Q H C) {k : ℕ}
    (hk : c.nreg 50110 = k) (hkm : k ≤ C.m) (hXW : c.nreg 50200 + 5 ≤ W)
    (hmW : 2 * C.m + 7 ≤ W) :
    ∃ c' k', Exec P W tposS c c' k' ∧ k' ≤ 30 ∧ c'.nreg 50201 = 6 + tpos C k ∧
      FrameB Btp c c' := by
  zueqa
  have e₁ := Exec.copyN (P := P) hw 50100 50200
  set c₁ : Config := { c with nreg := upd c.nreg 50100 (c.nreg 50200) } with hc₁
  have w₁ : ztidr := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, r01, r02, r08, rr₂, rm₂⟩ := readS_exec (P := P) c₁ w₁
    (X := c.nreg 50200) by_rfl by_omega hXW by_omega
  zue
  zuec
  have e₃ := Exec.subN (P := P) w₂ 50103 50108 50102
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50103 (c₂.nreg 50108 - c₂.nreg 50102) }
    with hc₃
  have w₃ : ztlaj := e₃.wb_right
  have v10 : c₃.nreg 50110 = k := by
    simp_all
  have v02 : c₃.nreg 50102 = C.sideS C.sideBeta := by
    simp_all
  have v03 : c₃.nreg 50103 = 2 * C.m - C.sideS C.sideBeta := by
    simp_all
  obtain ⟨c₄, k₄, e₄, hk₄, v11, r₄⟩ := candR_exec (P := P) c₃ w₃ (j := 50110) (s := 50102)
    (d := 50103) (dst := 50111) by_omega
  zucc
  have hc : c₄.nreg 50111 = tpos C k := by
    rw [v11, v10, v02, v03, tpos_eq_cand C by_omega]; rfl
  have htp := tpos_lt C k
  obtain ⟨c₅, k₅, e₅, hk₅, q01, q5, qm, qrr, qrm, qo⟩ : ∃ c₅ k₅, Exec P W
      ztjpf c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg 50201 = 6 + tpos C k ∧
      (∀ r, r ≠ 50112 → r ≠ 50201 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; zvnmd; omega)
    refine ⟨rfl, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; omega
    · zup
  have ex : Exec P W tposS c c₅ (ztceh + (k₂ + (ztceh + ztjzr))) :=
    .seq ztzsb (.seq e₂ (.seq (.seq e₃ ztpsb) ztgxe))
  exact ⟨c₅, _, ex, by_omega, q01, exec_frameB ex wr_tposS⟩

/-! ## One point query -/

/-- Append the query `(50211, 70124 + 1, 50203)`. -/
def ptApp : Stmt := block [.storeN ALLOC 50211, .addN ALLOC ALLOC 70105, .addN 70129 70124 70105,
  .storeN ALLOC 70129, .addN ALLOC ALLOC 70105, .storeN ALLOC 50203, .addN ALLOC ALLOC 70105,
  .addN 70128 70128 70105]

/-- **One point query.** -/
def ptQ : Stmt := .seq arrivalPos (.ifLtN 70108 50210 ptApp .skip)

/-- The outcome of a point query. -/
def PtRes (P : Polygon) (C : Chain) (e h ρ hv : ℕ) (l : List zte) : Prop :=
  (l = [] ∧ ∀ p t, ¬ Sweep.Arrival (chainModel C).W ztwqb
    ztdep p t) ∨
  (∃ e' h', l = [ztnxr] ∧ Sweep.Arrival (chainModel C).W
    ztwqb ztdep e' ((chainModel C).param zta ztonh))
set_option maxHeartbeats 4000000 in
theorem ptQ_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hwf : ChainWF P ztm c.nmem ztbok) {H : Host}
    {C : Chain} (hC : ChainDescAt c.nmem ztbok zta H C) (hin : ArrIn P W C c)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0) {LB : ℕ} {pre : List zte}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + 35003 ≤ W)
    (hvW : c.nreg 70124 + 1 ≤ W) (hcW : pre.length + 1 ≤ W) :
    ∃ c' k l, Exec P W ptQ c c' k ∧ k ≤ 35011 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧ c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB zthze ∧ zth ∧
      (∀ r, Bprim r = false → r ≠ 70128 → r ≠ 70129 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, Bprim r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      PtRes P C ztcuv ztjsc ztdzm (c.nreg 70124) l := by
  obtain ⟨c₁, k₁, e₁, hk₁, hout, F₁⟩ := primRun arrivalPos_meets wr_arrivalPos c hw hG hHW hwf hC
    hin by_omega
  zud
  have a₁ := frameB_alloc F₁
  have m₁ : ztwh := F₁.2.2.1
  have g : ∀ r, (r < 10000 ∨ ztndv ∨ ztqt ∨ 51000 ≤ r) →
      c₁.nreg r = c.nreg r := fun r hr => frameB_reg F₁ hr
  obtain ⟨hf1, hyes, hno⟩ := hout
  by_cases hf : c₁.nreg 50210 = 1
  · obtain ⟨-, hpp, harr⟩ := hyes hf
    have hlt : c₁.nreg 70108 < c₁.nreg 50210 := by_simp_all
    set a := LB + 3 * pre.length with ha
    have hA₁ : c₁.nreg 9999 = a := by rw [show (9999 : ℕ) = ALLOC from rfl, a₁, hA]
    have r05 : ztpmw := by_simp_all
    have r24 : c₁.nreg 70124 = c.nreg 70124 := g _ by_omega
    have r28 : c₁.nreg 70128 = pre.length := by_grind
    have r03 : ztsgh := g _ by_omega
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W ptApp c₁ c₂ k₂ ∧ k₂ = 8 ∧
        (c₂.nreg ALLOC = a + 3 ∧ c₂.nreg 70128 = pre.length + 1 ∧
        c₂.nmem a = c₁.nreg 50211 ∧ c₂.nmem ztdf = c.nreg 70124 + 1 ∧
        c₂.nmem ztvj = c.nreg 50203 ∧ (∀ x, (x < a ∨ a + 3 ≤ x) → c₂.nmem x = c₁.nmem x) ∧
        (∀ r, r ≠ 70128 → r ≠ 70129 → r ≠ ALLOC → c₂.nreg r = c₁.nreg r) ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output) := by
      unfold ptApp
      exec_block
      all_goals try (simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA₁, r05, r24, r28, ALLOC]; omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl⟩
      all_goals try (simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA₁, r05, r24, r28, r03, ALLOC])
      · have a3' : zteif := a3
        zup
    obtain ⟨q9, q28, qa, qb, qc, qm, qr, qrr, qrm, qo⟩ := q
    have ex : Exec P W ptQ c c₂ ztyrf := .seq e₁ ztnaj
    refine ⟨c₂, _, [(c₁.nreg 50211, c.nreg 70124 + 1, c.nreg 50203)], ex, by_omega,
      by grind, by_simp,
      by grind,
      by grind, ?_, fun x hx => ?_,
      fun r hr a2 a3 a4 => ?_, fun r hr => ?_, by rw [qrm, F₁.2.2.2.1], by rw [qo, F₁.2.2.2.2],
      Or.inr ⟨_, _, rfl, harr⟩⟩
    · zuknk
      · obtain ⟨b0, b1, b2⟩ := hL i hi
        grind
      · exact qa
      · exact qb
      omega
    · grind
    · rw [qr r a2 a3 a4]; exact F₁.1 r hr
    · zuoey; exact F₁.2.1 r hr
  · have hf0 : ztuqj := by_omega
    have hlt : ¬ c₁.nreg 70108 < c₁.nreg 50210 := by_omega
    have ex : Exec P W ptQ c c₁ (k₁ + ztdeu) := .seq e₁ (.ifLtN_false hlt ztwd)
    refine ⟨c₁, _, [], ex, by_omega, by_simp, by_simp, by_simp_all,
      by simp_all, by_simp_all, fun x _ => by zvmxn,
      fun r hr _ _ _ => F₁.1 r hr, fun r hr => F₁.2.1 r hr, F₁.2.2.2.1, F₁.2.2.2.2,
      Or.inl ⟨rfl, hno hf⟩⟩
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK SweepPrim WalkEmbed MergeAsm
@[expose] public section
theorem ptAns_of_res (J : Merge.Junction) (P : Polygon) (i : ℕ) (hP : J.P.Simple)
    {e h ρ hv : ℕ} {l : List zte} (hres : PtRes P ztgi e h ρ hv l) {z : Point}
    (hz : (chainModel ztgi).pos zta ztcq = z) (hzs : z ∈ (sideChain J i).set)
    (hhv : ((Qof P).vtx hv).2 = z.2) (hvn : hv < (Qof P).n) :
    PtAns J zta i z ztern l := by
  rcases hres with ⟨rfl, hno⟩ | ⟨e', h', rfl, harr⟩
  · zvncr at hno
    exact ptAns_none J _ hP i hzs ztmzr hno
  · zvncr at harr
    exact ptAns_some J _ i harr hhv hvn ztmzr
theorem dirOf_one : dirOf 1 = 1 := by_rfl
theorem dirOf_zero : dirOf 0 = -1 := by_rfl

/-- The registers that the point queries may write outside the primitive bands. -/
def Bpt (r : ℕ) : Bool := Bprim r || decide ztqt ||
  decide (70120 ≤ r ∧ r < 70126) || decide (70127 ≤ r ∧ r < 70140) || r == ALLOC

/-- The real registers that the point queries may write. -/
def BR (r : ℕ) : Bool := Bprim r || Btp r
variable {r : ℕ}
theorem br_prim (h : BR r = false) : Bprim r = false := by
  zuggk
theorem br_tp (h : BR r = false) : Btp r = false := by
  zuggk
theorem bprim_of (h : Bpt r = false) : Bprim r = false := by
  simp only [Bpt, Bool.or_eq_false_iff] at h; simp_all
theorem btp_of (h : Bpt r = false) : Btp r = false := by
  simp only [Bpt, Bprim, Btp, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    at h ⊢
  omega

/-- The vertex queries at the vertex stored at `D + off`. -/
def vtxPts (D off : ℕ) : Stmt :=
  .seq (block [.copyN 50200 D, .constN 70131 off, .addN 70132 D 70131, .loadN 70125 70132,
      .copyN 50201 70125])
    (.seq hvPrim (.seq (block [.copyN 70124 50210, .copyN 50110 70125]) (.seq tposS
      (.seq (block [.constN 50202 0, .constN 50203 1]) (.seq ptQ
        (.seq ztoyh ptQ))))))

/-- The cost bound of `vtxPts`. -/
def vtxCost : ℕ := 74000
set_option maxHeartbeats 16000000 in
theorem vtxPts_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) {D off : ℕ} (hD : 70000 ≤ D ∧ D < 70100) (hoff : off ≤ 4)
    (hwf : ChainWF P ztm c.nmem ztmgt) (J : Merge.Junction) (i : ℕ)
    {H : Host} (hC : ChainDescAt c.nmem ztmgt zta H ztgi)
    (hP : J.P.Simple) {kk : ℕ} (hk : c.nmem (c.nreg D + off) = kk)
    (hkk : kk ≤ (sideChain J i).m) (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List zte}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + vtxCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l₁ l₀, Exec P W ztucz c c' k ∧ k ≤ vtxCost ∧
      3 * (l₁.length + l₀.length) ≤ k ∧ l₁.length ≤ 1 ∧
      l₀.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l₁ ++ l₀).length ∧
      c'.nreg 70128 = (pre ++ l₁ ++ l₀).length ∧
      ChordListAt c'.nmem LB (pre ++ l₁ ++ l₀) ∧ zth ∧
      ztcji ∧ ztrf ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      PtAns J zta i ((sideChain J i).vertex kk) 1 l₁ ∧
      PtAns J (Qof P) i ((sideChain J i).vertex kk) (-1) l₀ := by
  zuckf

  zubp
  zucum

  rw [hX] at hC hk hB5 hwf'
  -- the vertex index
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 D, .constN 70131 off,
      .addN 70132 D 70131, .loadN 70125 70132, .copyN 50201 70125]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 70125 = kk ∧ c₁.nreg 50201 = kk ∧
        (∀ r, r ≠ 50200 → r ≠ 50201 → r ≠ 70125 → r ≠ 70131 → r ≠ 70132 →
          c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hX]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hX]
    all_goals exact hk
  zucsy
  zud
  have a₁ : ztdc := qr₁ _ by_decide by_decide by_decide
    by_decide by_decide
  -- the height of the vertex
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨hv₁, hv₂⟩, F₂⟩ := primRun hvPrim_meets wr_hvPrim c₁ w₁ hG
    by_tauto (by rw [q00, a₁, qm₁]; exact ztfwm)
    ztkue (show c₁.nreg 50201 ≤ C.m by rw [q01]; exact hkk)
    (by rw [a₁]; unfold vtxCost at hroom; omega)
  rw [q01] at hv₂
  zue
  obtain ⟨hv, hhv⟩ : ∃ hv, c₂.nreg 50210 = hv := by_grind
  rw [hhv] at hv₁ hv₂
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 70124 50210,
      .copyN 50110 70125]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      (c₃.nreg 70124 = hv ∧ c₃.nreg 50110 = kk ∧
        (∀ r, r ≠ 70124 → r ≠ 50110 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    have r26 : c₂.nreg 70125 = kk := by rw [frameB_reg F₂ by_omega, q26]
    exec_block
    zuloy
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      hhv, r26]
  obtain ⟨q24, q10, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  zubj
  zuehp
  have r00 : ztusf := by
    rw [qr₃ _ by_decide by_decide, frameB_reg F₂ by_omega, q00]
  -- the walk position
  obtain ⟨c₄, k₄, e₄, hk₄, q41, F₄⟩ := tposS_exec (P := P) c₃ w₃ (by rw [r00, m₃]; exact hC)
    q10 hkk by_omega hmW
  zucc
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50202 0, .constN 50203 1])
      c₄ c₅ k₅ ∧ k₅ = 2 ∧
      (c₅.nreg 50202 = 0 ∧ c₅.nreg 50203 = 1 ∧
        (∀ r, r ≠ 50202 → r ≠ 50203 → c₅.nreg r = c₄.nreg r) ∧
        c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    exec_block
    all_goals try omega
    zuloy
    zuit
  obtain ⟨q52, q53, qr₅, qm₅, qrr₅, qrm₅, qo₅⟩ := q
  zuef
  have m₅ : ztlaq := by rw [qm₅, F₄.2.2.1, m₃]
  -- registers kept from `c` to `c₅`
  have k₅r : ∀ r, Bpt r = false → c₅.nreg r = c.nreg r := fun r hr => by
    zudpc
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    rw [qr₅ r by_omega by_omega, F₄.1 r ztvfw, qr₃ r by_omega by_omega,
      F₂.1 r ztmcs, qr₁ r by_omega by_omega by_omega by_omega by_omega]
  have k₅rr : ∀ r, BR r = false → c₅.rreg r = c.rreg r := fun r hr => by
    rw [qrr₅, F₄.2.1 r ztvfs, qrr₃, F₂.2.1 r ztjpp, qrr₁]
  have a₅ : ztizp := by
    rw [qr₅ _ by_decide by_decide, F₄.1 _ by_decide, qr₃ _ by_decide by_decide,
      frameB_alloc F₂, a₁]
  have r500 : c₅.nreg 50200 = X := by
    rw [qr₅ _ by_decide by_decide, F₄.1 _ by_decide, r00]
  have r501 : c₅.nreg 50201 = 6 + tpos C kk := by_grind
  have r524 : c₅.nreg 70124 = hv := by
    rw [qr₅ _ by_decide by_decide, F₄.1 _ by_decide, q24]
  have r528 : c₅.nreg 70128 = pre.length := by
    rw [qr₅ _ by_decide by_decide, F₄.1 _ by_decide, qr₃ _ by_decide by_decide,
      frameB_reg F₂ by_omega, qr₁ _ by_decide by_decide by_decide by_decide by_decide,
      h28]
  -- the geometry of the query
  have hvpos : (chainModel C).pos zta ⟨6 + tpos C kk, 0⟩ = C.vertex kk := vpos C _ hkk
  have hzs := C.vertex_mem_set hkk
  zudyn
  have hin : ∀ c' : Config, c'.nreg 50201 = 6 + tpos C kk → c'.nreg 50202 = 0 →
      ArrIn P W C c' := fun c' h1 h2 => ⟨⟨by zvmwp; exact vpos_edge C kk,
      ⟨by zvmza; rfl, by zvmza; positivity,
        by grind⟩,
      by rw [h1, h2, hvpos]; exact abs_snd_lt_radius C hzs⟩, hPC, hmW⟩
  -- direction `1`
  obtain ⟨c₆, k₆, l₁, e₆, hk₆, hk₆', hl₁, a₆, n₆, L₆, m₆, r₆, rr₆, rm₆, o₆, res₁⟩ :=
    ptQ_exec (P := P) c₅ w₅ hG ztdmm
      (by rw [r500, a₅, m₅]; exact ztfwm) (by rw [r500, m₅]; exact hC)
      (hin c₅ r501 q52) (by rw [k₅r _ by_decide, h05]) (by rw [k₅r _ by_decide, h08])
      (by rw [a₅, hA]) r528 by_grind
      (by zuoxy; unfold vtxCost at hroom; omega) by_omega
      by_omega
  rw [r501, q52, q53, r524] at res₁
  zujb
  obtain ⟨c₇, k₇, e₇, hk₇, q73, qr₇, qm₇, qrr₇, qrm₇, qo₇⟩ : ∃ c₇ k₇, Exec P W
      ztoyh c₆ c₇ k₇ ∧ k₇ = 1 ∧ c₇.nreg 50203 = 0 ∧
      (∀ r, r ≠ 50203 → c₇.nreg r = c₆.nreg r) ∧
      c₇.nmem = c₆.nmem ∧ c₇.rreg = c₆.rreg ∧ c₇.rmem = c₆.rmem ∧ c₇.output = c₆.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zuit
  zubgp
  have k67 : ∀ r, Bprim r = false → r ≠ 70128 → r ≠ 70129 → r ≠ ALLOC → r ≠ 50203 →
      c₇.nreg r = c₅.nreg r := fun r h1 h2 h3 h4 h5 => by rw [qr₇ r h5, r₆ r h1 h2 h3 h4]
  have a₇ : c₇.nreg ALLOC = LB + 3 * (pre ++ l₁).length := by rw [qr₇ _ by_decide, a₆]
  -- direction `0`
  obtain ⟨c₈, k₈, l₀, e₈, hk₈, hk₈', hl₀, a₈, n₈, L₈, m₈, r₈, rr₈, rm₈, o₈, res₀⟩ :=
    ptQ_exec (P := P) c₇ w₇ hG ztdmm
      (by
        zuemk
        exact chainWF_copy ztfwm hC ztiji
          ztijp
          ztlgt ztlgt)
      (by
        zuemk
        zueaf
        exact chainDescAt_copy hC hEb ztiji
          ztijp)
      (hin c₇ (by rw [k67 50201 by_decide by_decide by_decide by_decide by_decide, r501])
        (by rw [k67 50202 by_decide by_decide by_decide by_decide by_decide, q52]))
      (by rw [k67 70105 by_decide by_decide by_decide by_decide by_decide,
        k₅r _ by_decide, h05])
      (by rw [k67 70108 by_decide by_decide by_decide by_decide by_decide,
        k₅r _ by_decide, h08])
      a₇ (by rw [qr₇ _ by_decide, n₆]) by_grind
      (by rw [a₇]; unfold vtxCost at hroom; rw [List.length_append]; omega)
      (by rw [k67 70124 by_decide by_decide by_decide by_decide by_decide, r524]; omega)
      (by rw [List.length_append]; omega)
  rw [k67 50201 by_decide by_decide by_decide by_decide by_decide,
    k67 50202 by_decide by_decide by_decide by_decide by_decide,
    k67 70124 by_decide by_decide by_decide by_decide by_decide, r501, q52, r524, q73]
    at res₀
  have ex : Exec P W ztucz c c₈
      _ :=
    .seq e₁ ztey
  have hvn : hv < (Qof P).n := by_omega
  refine ⟨c₈, _, l₁, l₀, ex, by unfold vtxCost; omega, by_omega, hl₁, hl₀, a₈, n₈, L₈,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₈ a (by rw [a₇, List.length_append]; grind), qm₇,
      m₆ a by_grind, m₅]
  · zudpc
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    rw [r₈ r ztmcs by_omega by_omega by_omega, qr₇ r by_omega,
      r₆ r ztmcs by_omega by_omega by_omega, k₅r r hr]
  · rw [rr₈ r ztjpp, qrr₇, rr₆ r ztjpp, k₅rr r hr]
  · rw [rm₈, qrm₇, rm₆, qrm₅, F₄.2.2.2.1, qrm₃, F₂.2.2.2.1, qrm₁]
  · rw [o₈, qo₇, o₆, qo₅, F₄.2.2.2.2, qo₃, F₂.2.2.2.2, qo₁]
  · rw [← dirOf_one]
    exact ptAns_of_res J P i hP res₁ hvpos hzs ztqfd hvn
  · rw [← dirOf_zero]
    exact ptAns_of_res J P i hP res₀ hvpos hzs ztqfd hvn
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK SweepPrim WalkEmbed MergeAsm
@[expose] public section
theorem capOrigin_snd (J : Merge.Junction) (hgen : SharedGeneric J) :
    (capOrigin J).2 = (capNear J).2 := by
  obtain ⟨g1, g2, -⟩ := hgen
  have hf : (capFar J).2 - (sharedV J).2 ≠ 0 := by
    unfold capFar; grind
  unfold capOrigin
  simp_all

/-- The point query at a walk position of the chain of the descriptor in `D`. -/
def capB (D K : ℕ) : Stmt :=
  .seq (block [.copyN 50200 D, .copyN 50110 K]) (.seq tposS
    (.seq (block [.copyN 50202 70142, .copyN 50203 70143, .subN 70124 70142 70105]) ptQ))

/-- The cost bound of `capB`. -/
def capBCost : ℕ := 35100
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
theorem capB_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) {D K : ℕ} (_hD : 70000 ≤ D ∧ D < 70100)
    (hK : 70000 ≤ K ∧ K < 70200)
    (hwf : ChainWF P ztm c.nmem ztmgt) (J : Merge.Junction) (i : ℕ)
    {H : Host} (hC : ChainDescAt c.nmem ztmgt zta H ztgi)
    (hP : J.P.Simple) {kk code ρ : ℕ} (hk : c.nreg K = kk) (hkk : kk ≤ (sideChain J i).m)
    (h42 : c.nreg 70142 = code) (h1c : 1 ≤ code) (hcn : code ≤ P.n) (h43 : c.nreg 70143 = ρ)
    {z : Point}
    (hgeo : (chainModel ztgi).pos zta ztxlx = z ∧
      0 ≤ (chainModel ztgi).param zta ztxlx ∧
      (chainModel ztgi).param zta ztxlx < 1 ∧
      z ∈ (sideChain J i).set)
    (hhv : ((Qof P).vtx (code - 1)).2 = z.2)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List zte}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W ztthv c c' k ∧ k ≤ capBCost ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧
      c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB zthze ∧ zth ∧
      ztcji ∧ ztrf ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      PtAns J (Qof P) i z (dirOf ρ) l := by
  zuckf

  zubp
  zucum

  rw [hX] at hC hB5 hwf'
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 D, .copyN 50110 K])
      c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 50110 = kk ∧
        (∀ r, r ≠ 50200 → r ≠ 50110 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    exec_block
    zuloy
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      hX, hk]
  obtain ⟨q00, q10, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, q21, F₂⟩ := tposS_exec (P := P) c₁ w₁ ztkue
    q10 hkk by_omega hmW
  zue
  have r42 : c₂.nreg 70142 = code := by
    rw [F₂.1 _ by_decide, qr₁ _ by_decide by_decide, h42]
  have r43 : c₂.nreg 70143 = ρ := by
    rw [F₂.1 _ by_decide, qr₁ _ by_decide by_decide, h43]
  have r05 : c₂.nreg 70105 = 1 := by
    rw [F₂.1 _ by_decide, qr₁ _ by_decide by_decide, h05]
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50202 70142,
      .copyN 50203 70143, .subN 70124 70142 70105]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      (c₃.nreg 50202 = code ∧ c₃.nreg 50203 = ρ ∧ c₃.nreg 70124 = code - 1 ∧
        (∀ r, r ≠ 50202 → r ≠ 50203 → r ≠ 70124 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    exec_block
    refine ztbfo
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      r42, r43, r05]
  obtain ⟨q32, q33, q24, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  zubj
  zuehp
  have k₃r : ∀ r, Bpt r = false → c₃.nreg r = c.nreg r := fun r hr => by
    zudpc
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    rw [qr₃ r by_omega by_omega by_omega, F₂.1 r ztvfw,
      qr₁ r by_omega by_omega]
  have k₃rr : ∀ r, BR r = false → c₃.rreg r = c.rreg r := fun r hr => by
    rw [qrr₃, F₂.2.1 r ztvfs, qrr₁]
  have a₃ : ztcke := by
    rw [qr₃ _ by_decide by_decide by_decide, F₂.1 _ by_decide,
      qr₁ _ by_decide by_decide]
  have r300 : ztusf := by
    rw [qr₃ _ by_decide by_decide by_decide, F₂.1 _ by_decide, q00]
  have r301 : c₃.nreg 50201 = 6 + tpos C kk := by
    grind
  have r328 : c₃.nreg 70128 = pre.length := by
    rw [qr₃ _ by_decide by_decide by_decide, F₂.1 _ by_decide,
      qr₁ _ by_decide by_decide, h28]
  obtain ⟨hpos, hp0, hp1, hzs⟩ := hgeo
  zudyn
  obtain ⟨c₄, k₄, l, e₄, hk₄, hk₄', hl, a₄, n₄, L₄, m₄, r₄, rr₄, rm₄, o₄, res⟩ :=
    ptQ_exec (P := P) c₃ w₃ hG ztdmm
      (by rw [r300, a₃, m₃]; exact ztfwm) (by rw [r300, m₃]; exact hC)
      ⟨⟨by rw [r301]; exact vpos_edge C kk, ⟨by_grind,
        by grind, by_grind⟩,
        by rw [r301, q32, hpos]; exact abs_snd_lt_radius C hzs⟩, hPC, hmW⟩
      by_grind (by rw [k₃r _ by_decide, h08])
      (by rw [a₃, hA]) r328 by_grind
      (by rw [a₃]; unfold capBCost at hroom; omega) by_omega by_omega
  rw [r301, q32, q33, q24] at res
  have ex : Exec P W ztthv c c₄ _ :=
    .seq e₁ ztcb
  have hvn : code - 1 < (Qof P).n := by_omega
  have hcode : code = code - 1 + 1 := by_omega
  refine ⟨c₄, _, l, ex, by unfold capBCost; omega, by_omega, hl, a₄, n₄, L₄,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · grind
  · zudpc
    simp only [Bpt, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      at hr'
    rw [r₄ r ztmcs by_omega by_omega by_omega, k₃r r hr]
  · rw [rr₄ r ztjpp, k₃rr r hr]
  · rw [rm₄, qrm₃, F₂.2.2.2.1, qrm₁]
  · rw [o₄, qo₃, F₂.2.2.2.2, qo₁]
  · exact ptAns_of_res J P i hP res hpos hzs hhv hvn

/-! ## The cap data -/

/-- `capPrim` on the whole chain at the shared vertex, answers saved in `70140 … 70143`. -/
def capS : Stmt :=
  .seq (block [.copyN 50200 70002, .constN 70131 2, .addN 70132 70000 70131, .loadN 70126 70132,
      .copyN 50201 70126])
    (.seq capPrim (block [.copyN 70140 50210, .copyN 70141 50211, .copyN 70142 50212,
      .copyN 70143 50213]))

/-- The registers written by `capS`. -/
def Bcs (r : ℕ) : Bool := Bprim r || r == 50200 || r == 50201 || r == 70126 || r == 70131 ||
  r == 70132 || decide ztgzj
theorem bprim_of_bcs {r : ℕ} (h : Bcs r = false) : Bprim r = false := by
  simp only [Bcs, Bool.or_eq_false_iff] at h; simp_all

/-- The cap data in the registers. -/
structure CapRegs (P : Polygon) (J : Merge.Junction) (c : Config) : Prop where
  m1 : c.nreg 70126 = J.m₁
  ext : BitIs c 70140 (SharedExtremum J)
  near : SharedExtremum J → BitIs c 70141 (NearU J)
  code1 : 1 ≤ c.nreg 70142
  coden : c.nreg 70142 ≤ P.n
  ht : SharedExtremum J → ((Qof P).vtx (c.nreg 70142 - 1)).2 = (capNear J).2
  dir : SharedExtremum J → BitIs c 70143 (¬ (capNear J).1 < (capOrigin J).1)
theorem CapRegs.keep {J : Merge.Junction} {c c' : Config} (h : CapRegs P J c)
    (hr : ∀ r, (r = 70126 ∨ ztgzj) → c'.nreg r = c.nreg r) :
    CapRegs P J c' :=
  ⟨by zungg; exact h.m1,
    h.ext.of_eq by_simp_all,
    fun hx => (h.near hx).of_eq by_simp_all,
    by zungg; exact h.code1,
    by zungg; exact h.coden,
    fun hx => by zungg; exact h.ht hx,
    fun hx => (h.dir hx).of_eq by_simp_all⟩
set_option maxHeartbeats 8000000 in
theorem capS_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hgen : SharedGeneric J) {H H' : Host}
    (hwf : ChainWF P ztm c.nmem ztfgr)
    (hCw : ChainDescAt c.nmem ztfgr zta H J.whole)
    (hC0 : ChainDescAt c.nmem ztghg zta H' J.left)
    (hX0 : c.nreg 70000 + 5 ≤ W) (hroom : c.nreg ALLOC + 10200 ≤ W) :
    ∃ c' k, Exec P W capS c c' k ∧ k ≤ 10200 ∧ CapRegs P J c' ∧ c'.nmem = c.nmem ∧
      (∀ r, Bcs r = false → c'.nreg r = c.nreg r) ∧ ztrf ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨X, hX⟩ : ∃ X, c.nreg 70002 = X := by_simp_all
  obtain ⟨X0, hX0'⟩ : ∃ X, c.nreg 70000 = X := by_simp_all
  rw [hX] at hwf hCw
  rw [hX0'] at hC0 hX0
  have hm2 : c.nmem _ = J.m₁ := hC0.2.2.2.1
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50200 70002, .constN 70131 2,
      .addN 70132 70000 70131, .loadN 70126 70132, .copyN 50201 70126]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50200 = X ∧ c₁.nreg 70126 = J.m₁ ∧ c₁.nreg 50201 = J.m₁ ∧
        (∀ r, r ≠ 50200 → r ≠ 50201 → r ≠ 70126 → r ≠ 70131 → r ≠ 70132 →
          c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hX0']; omega)
    simp_all
  zucsy
  zud
  have a₁ : ztdc := qr₁ _ by_decide by_decide by_decide
    by_decide by_decide
  zumeb
  have hm2' := J.one_le_m₂
  obtain ⟨c₂, k₂, e₂, hk₂, hout, F₂⟩ := primRun capPrim_meets wr_capPrim c₁ w₁ hG hHW
    by_simp_all (by rw [q00, qm₁]; omega)
    (show 1 ≤ c₁.nreg 50201 ∧ c₁.nreg 50201 + 1 ≤ J.whole.m by
      rw [q01]; exact ⟨hm1, by_simp_all⟩)
    by_omega
  simp only [CapOut] at hout
  rw [q01] at hout
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hout
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 70140 50210,
      .copyN 70141 50211, .copyN 70142 50212, .copyN 70143 50213]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 70140 = c₂.nreg 50210 ∧ c₃.nreg 70141 = c₂.nreg 50211 ∧
        c₃.nreg 70142 = c₂.nreg 50212 ∧ c₃.nreg 70143 = c₂.nreg 50213 ∧
        (∀ r, r ≠ 70140 → r ≠ 70141 → r ≠ 70142 → r ≠ 70143 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
    zuit
  obtain ⟨t40, t41, t42, t43, qr₃, qm₃, qrr₃, qrm₃, qo₃⟩ := q
  have ex : Exec P W capS c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, ⟨?_, o1.of_eq t40, fun hx => (o2 hx).of_eq t41,
    by omega, by_omega, fun hx => by rw [t42]; exact o5 hx,
    fun hx => (o6 hx hgen.2.2).of_eq t43⟩, by rw [qm₃, F₂.2.2.1, qm₁], fun r hr => ?_,
    fun r hr => ?_, by rw [qrm₃, F₂.2.2.2.1, qrm₁], by rw [qo₃, F₂.2.2.2.2, qo₁]⟩
  · rw [qr₃ _ by_decide by_decide by_decide by_decide, frameB_reg F₂ by_omega, q26]
  · zudpc
    simp only [Bcs, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr'
    rw [qr₃ r by_omega by_omega by_omega by_omega, F₂.1 r (bprim_of_bcs hr),
      qr₁ r by_omega by_omega by_omega by_omega by_omega]
  · rw [qrr₃, F₂.2.1 r ztjpp, qrr₁]

/-- The cap query of side `0`. -/
def capQ₀ : Stmt := .ifLtN 70108 70140 (.ifLtN 70141 70105 (capB 70000 70126) .skip) .skip

/-- The cap query of side `1`. -/
def capQ₁ : Stmt := .ifLtN 70108 70140 (.ifLtN 70108 70141 (capB 70001 70108) .skip) .skip
set_option maxHeartbeats 8000000 in
theorem capQ₀_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hP : J.P.Simple) (hgen : SharedGeneric J)
    {H : Host} (hwf : ChainWF P ztm c.nmem ztghg)
    (hC : ChainDescAt c.nmem ztghg zta H J.left) (hR : CapRegs P J c)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List zte}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W capQ₀ c c' k ∧ k ≤ capBCost + 4 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧
      c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB zthze ∧ zth ∧
      ztcji ∧ ztrf ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (SharedExtremum J → ¬ NearU J → PtAns J zta 0 ztchm ztchl l) ∧ (¬ ztffx → l = []) := by
  zufsz

  · zuccy

    · zuljh
      have hlt2 : ¬ c.nreg 70141 < c.nreg 70105 := by_omega
      refine ⟨c, _, [], .ifLtN_true hlt1 ztzrs,
        by omega, by_simp, by_simp, by_simp_all, by_simp_all,
        by simp_all, by_omega, by_omega, by_simp_all, rfl, rfl,
        by simp_all, by_simp_all⟩
    · zucwb

      have hlt2 : c.nreg 70141 < c.nreg 70105 := by_omega
      zubxm

      have hgeo := capPos₀ _ J hgen hX hU hh
      zudkn
      obtain ⟨c', k, l, e, hk, hk', hl, a', n', L', m', r', rr', rm', o', hans⟩ :=
        capB_exec c hw hG hHW by_norm_num by_norm_num
          hwf J 0 hC hP hR.m1 by_rfl rfl h1c hcn rfl hgeo
          ztkss h05 h08 hA h28 hL hroom hcW
      zuihb
      exact ⟨c', _, l, .ifLtN_true hlt1 ztspl, by_omega, by_omega, hl, a', n', L', m',
        r', rr',
        rm', o', by_simp_all, by_simp_all⟩
  · zucwe

    refine ⟨c, _, [], .ifLtN_false hlt1 ztjd, by_omega, by_simp, by_simp,
      by simp_all, by_simp_all, by_simp_all, by_omega, by_omega,
      by simp_all, rfl, rfl, by_simp_all, by_simp_all⟩
set_option maxHeartbeats 8000000 in
theorem capQ₁_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (J : Merge.Junction) (hP : J.P.Simple) (hgen : SharedGeneric J)
    {H : Host} (hwf : ChainWF P ztm c.nmem zthuw)
    (hC : ChainDescAt c.nmem zthuw zta H J.right) (hR : CapRegs P J c)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    {LB : ℕ} {pre : List zte}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + capBCost ≤ W)
    (hcW : pre.length + 2 ≤ W) :
    ∃ c' k l, Exec P W capQ₁ c c' k ∧ k ≤ capBCost + 4 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧
      c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB zthze ∧ zth ∧
      ztcji ∧ ztrf ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (SharedExtremum J → NearU J → PtAns J zta 1 ztchm ztchl l) ∧ (¬ ztget → l = []) := by
  zufsz

  · zuccy

    · zuljh
      have hlt2 : c.nreg 70108 < c.nreg 70141 := by_omega
      zubxm

      have hgeo := capPos₁ _ J hgen hX hU hh
      zudkn
      obtain ⟨c', k, l, e, hk, hk', hl, a', n', L', m', r', rr', rm', o', hans⟩ :=
        capB_exec c hw hG hHW by_norm_num by_norm_num
          hwf J 1 hC hP h08 ztbg rfl h1c hcn rfl hgeo
          ztkss h05 h08 hA h28 hL hroom hcW
      zuihb
      exact ⟨c', _, l, .ifLtN_true hlt1 ztspl, by_omega, by_omega, hl, a', n', L', m',
        r', rr',
        rm', o', by_simp_all, by_simp_all⟩
    · zucwb

      have hlt2 : ¬ c.nreg 70108 < c.nreg 70141 := by_omega
      refine ⟨c, _, [], .ifLtN_true hlt1 ztzrs,
        by omega, by_simp, by_simp, by_simp_all, by_simp_all,
        by simp_all, by_omega, by_omega, by_simp_all, rfl, rfl,
        by simp_all, by_simp_all⟩
  · zucwe

    refine ⟨c, _, [], .ifLtN_false hlt1 ztjd, by_omega, by_simp, by_simp,
      by simp_all, by_simp_all, by_simp_all, by_omega, by_omega,
      by simp_all, rfl, rfl, by_simp_all, by_simp_all⟩
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm
@[expose] public section
structure FCtx (P : Polygon) (W : ℕ) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (A : ℕ)
    (c : Config) : Prop where
  good : GoodEnv P
  hw : hostWords P.n ≤ W
  jat : JunctionAt c.nmem ztghg zthuw ztfgr zta H J
  jwf : JunctionWF P A c.nmem ztghg zthuw ztfgr
  simple : J.P.Simple
  gen : SharedGeneric J
  nf₁ : NFWithin c.nmem (c.nreg 70003) A N₁
  nf₂ : NFWithin c.nmem (c.nreg 70004) A N₂
  is₁ : IsNF ztbw zta N₁
  is₂ : IsNF ztj zta N₂
  le : A ≤ c.nreg ALLOC
variable {P : Polygon} {W : ℕ} {J : Merge.Junction}
theorem chainDesc_keep {A : ℕ} {m m' : ℕ → ℕ} {B : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P A m B) (hC : ChainDescAt m B zta H C) (he : ∀ a, a < A → m' a = m a) :
    ChainDescAt m' B zta H C ∧ ChainWF P A m' B := by
  zuta
  zuivl
  exact ⟨chainDescAt_copy hC hEb he ztnze,
    chainWF_copy hwf hC he ztnze h5 le_rfl⟩
theorem FCtx.keep {H : Host} {N₁ N₂ : NF} {A : ℕ}
    {c c' : Config} (h : FCtx P W J H N₁ N₂ A c)
    (hr : ∀ r, 70000 ≤ r → r < 70005 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < A → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    FCtx P W J H N₁ N₂ A c' := by
  obtain ⟨hG, hW, ⟨hl, hr', hw⟩, ⟨wl, wr', ww, hreg⟩, hP, hgen, n₁, n₂, i₁, i₂, hle⟩ := h
  have e0 := hr 70000 by_norm_num by_norm_num
  have e1 := hr 70001 by_norm_num by_norm_num
  have e2 := hr 70002 by_norm_num by_norm_num
  rw [← e0] at hl wl
  rw [← e1] at hr' wr'
  rw [← e2] at hw ww hreg
  rw [← hr 70003 by_norm_num by_norm_num] at n₁
  rw [← hr 70004 by_norm_num by_norm_num] at n₂
  obtain ⟨kl, kwl⟩ := chainDesc_keep wl hl hm
  obtain ⟨kr, kwr⟩ := chainDesc_keep wr' hr' hm
  obtain ⟨kw, kww⟩ := chainDesc_keep ww hw hm
  refine ⟨hG, hW, ⟨kl, kr, kw⟩, ⟨kwl, kwr, kww, fun H' hH' => ?_⟩, hP, hgen,
    n₁.transport hm, n₂.transport hm, i₁, i₂, le_trans hle ha⟩
  obtain ⟨-, -, hEb, -⟩ := ww.2 H J.whole hw
  have h5 := ww.1
  have e0 : c'.nmem ztqhc = c.nmem ztqhc := hm _ by_omega
  have hH : HostAt c'.nmem (c'.nmem ztqhc) H := by
    zvokq; exact hostAt_agree hw.1 hEb hm
  have := NFLoc.hostAt_unique hH' hH
  zumo
  exact hreg H' hw.1

/-- The side chains in the input registers. -/
theorem FCtx.side {H : Host} {N₁ N₂ : NF} {A : ℕ}
    {c : Config} (h : FCtx P W J H N₁ N₂ A c) :
    ChainDescAt c.nmem ztghg zta H ztohu ∧
      ChainWF P ztm c.nmem ztghg ∧
      ChainDescAt c.nmem zthuw zta H ztohv ∧
      ChainWF P ztm c.nmem zthuw ∧
      ChainDescAt c.nmem ztfgr zta H J.whole ∧
      ChainWF P ztm c.nmem ztfgr :=
  ⟨h.jat.1, h.jwf.1.mono h.le, h.jat.2.1, h.jwf.2.1.mono h.le, h.jat.2.2, h.jwf.2.2.1.mono h.le⟩
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm
@[expose] public section
def sqInit (S G : ℕ) : Stmt := block [.constN 70105 1, .constN 70106 5, .constN 70108 0,
  .copyN S ALLOC, .loadN 70100 G, .constN 70131 3, .addN 70132 G 70131, .loadN 70101 70132,
  .constN 70102 0]

/-- The query count after the chord-end queries. -/
def sqMid : Stmt := block [.addN 70128 70100 70100]

/-- The chord-end queries. -/
def endPart (S G : ℕ) : Stmt := .seq (sqInit S G) (.seq qlLoop sqMid)

/-- The registers written by `endPart S G`. -/
def Bend (S r : ℕ) : Bool := decide (70100 ≤ r ∧ r ≤ 70108) || r == 70128 || r == 70131 ||
  r == 70132 || r == S || r == ALLOC
set_option maxHeartbeats 16000000 in
theorem endPart_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {S G : ℕ}
    (hS : S = 70150 ∨ S = 70151) (hGr : G = 70003 ∨ G = 70004) {A : ℕ} {N : NF}
    {M : Model} (hN : NFWithin c.nmem (c.nreg G) A N) (hA : A ≤ c.nreg ALLOC)
    (hIs : IsNF M zta N) (hnW : P.n ≤ W)
    (hroom : c.nreg ALLOC + 22 * N.nChords + 20 ≤ W) :
    ∃ c' k, Exec P W zttjv c c' k ∧ k ≤ 22 * N.nChords + 13 ∧
      6 * N.nChords ≤ k ∧
      c'.nreg S = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (endQL N.chords).length ∧
      c'.nreg 70128 = (endQL N.chords).length ∧
      c'.nreg 70105 = 1 ∧ c'.nreg 70108 = 0 ∧
      ChordListAt c'.nmem ztm ztvpw ∧
      zth ∧
      (∀ r, Bend S r = false → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  obtain ⟨A₀, hA₀⟩ : ztcgh := zths
  zujyw
  obtain ⟨Hd, hHd⟩ : ∃ x, c.nreg G = x := zths
  rw [hHd] at hN
  have hat := hN.nfAt
  obtain ⟨hK, -, -, -, -, hch, -⟩ := hat
  obtain ⟨hB7, hch', -⟩ := Gran.nf_areas hN
  zukzl
  have hKc : c.nmem Hd = K := hK
  obtain ⟨CB, hCB⟩ : ∃ x, c.nmem (Hd + 3) = x := zths
  rw [hCB] at hch hch'
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (sqInit S G) c c₁ k₁ ∧ k₁ = 9 ∧
      (c₁.nreg 70105 = 1 ∧ c₁.nreg 70106 = 5 ∧ c₁.nreg 70108 = 0 ∧ c₁.nreg S = A₀ ∧
        c₁.nreg 70100 = K ∧ c₁.nreg 70101 = CB ∧ c₁.nreg 70102 = 0 ∧ c₁.nreg ALLOC = A₀ ∧
        (∀ r, (r < 70100 ∨ 70108 < r) → r ≠ S → r ≠ 70131 → r ≠ 70132 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold sqInit
    rcases hS with rfl | rfl <;> rcases hGr with rfl | rfl <;>
    · exec_block
      all_goals try omega
      all_goals try (simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hHd]; omega)
      zubee
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hHd, hA', ALLOC]
      and_intros
      all_goals first | trivial | exact hKc | exact hCB |
        (intro r h1 h2 h3 h4; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨q05, q06, q08, qS, q00, q01, q02, qA, qr, qm, qrr, qrm, qo⟩ := q
  zud
  -- the loop
  have hIs' := hIs
  obtain ⟨-, -, -, -, -, -, -, -, -, hhQ, -⟩ := hIs'
  zubp
  have I0 : QLI W K CB A₀ c₁ c₁ := ⟨w₁, by_omega, by_omega, by_omega,
    fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, fun i hi => by_omega, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', I₂, h₂⟩ := qlLoop_exec (P := P) q05 q06 q08 q00
    ztbmx
    (fun i hi => by
      grind)
    by_omega by_omega K c₁ I0 by_omega
  zumfx
  have g₂ : ∀ r, r ≠ 70101 → r ≠ 70102 → r ≠ 70103 → r ≠ 70104 → r ≠ 70107 → r ≠ ALLOC →
      c₂.nreg r = c₁.nreg r := I₂.regs
  have r00 : c₂.nreg 70100 = K := by
    rw [g₂ _ by_decide by_decide by_decide by_decide by_decide by_decide, q00]
  obtain ⟨c₃, k₃, e₃, hk₃, t28, tr, tm, trr, trm, tou⟩ : ∃ c₃ k₃, Exec P W sqMid c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 70128 = 2 * K ∧ (∀ r, r ≠ 70128 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    unfold sqMid
    exec_block
    all_goals try (simp only [r00]; omega)
    refine ztgpj
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      r00]
    ring
  have ex : Exec P W zttjv c c₃ ztxee := .seq e₁ ztcr
  have hlen : (endQL N.chords).length = 2 * K := endQL_length _
  have hS' : S ≠ ALLOC := by rcases hS with rfl | rfl <;> decide
  refine ⟨c₃, _, ex, by_omega, by_omega, ?_, ?_, by_omega, ?_, ?_, ?_, fun a ha => ?_,
    fun r hr => ?_, by rw [trr, I₂.rr, qrr], by rw [trm, I₂.rm, qrm], by rw [tou, I₂.out, qo]⟩
  · rw [tr _ by_omega, g₂ _ by_omega
      by_omega by_omega
      by_omega by_omega hS', qS,
      hA₀]
  · rw [tr _ by_decide, I₂.alloc, h₂, hlen, hA₀]; ring
  · grind
  · grind
  · rw [tm, hA₀]
    have hdone := I₂.done
    rw [h₂] at hdone
    refine chordList_endQL (m₀ := c₁.nmem) (CB := CB) ztdp (fun i hi => hdone i hi)
    zujlh
    obtain ⟨d0, d1, d2, -, -⟩ := hch i hi
    exact ⟨d0, d1, d2⟩
  · rw [tm, I₂.low a by_omega, qm]
  · zudpc
    simp only [Bend, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr'
    rw [tr r by_omega, g₂ r by_omega by_omega by_omega by_omega by_omega by_omega,
      qr r by_omega by_omega by_omega by_omega]
def sideQ₀ : Stmt :=
  .seq (endPart 70150 70003) (.seq (vtxPts 70000 2) (.seq (vtxPts 70000 3) (.seq capS capQ₀)))

/-- The query list of side `1`. -/
def sideQ₁ : Stmt := .seq (endPart 70151 70004) (.seq (vtxPts 70001 3) capQ₁)

/-- The registers written by the side stages. -/
def Bside (S r : ℕ) : Bool := Bend S r || Bpt r || Bcs r

/-- The cost bound of `sideQ₀`. -/
def sq0Cost (K : ℕ) : ℕ := 22 * K + 200000

/-- The cost bound of `sideQ₁`. -/
def sq1Cost (K : ℕ) : ℕ := 22 * K + 120000
variable {S r : ℕ} {P : Polygon} {W : ℕ} (c : Config)
theorem bend_of (h : Bside S r = false) : Bend S r = false := by
  zucqt
theorem bcs_of (h : Bside S r = false) : Bcs r = false := by
  zucqt
theorem bpt_of_side (h : Bside S r = false) : Bpt r = false := by
  zucqt
theorem bpt_lo {r : ℕ} (h1 : 70000 ≤ r) (h2 : r < 70120) : Bpt r = false := by
  zudvz
theorem bcs_lo {r : ℕ} (h1 : 70000 ≤ r) (h2 : r < 70120) : Bcs r = false := by
  simp only [Bcs, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega
theorem bend_lo (h1 : 70000 ≤ r) (h2 : r < 70100) (hS : r ≠ S) : Bend S r = false := by
  zufaq
  omega
theorem bpt_cap {r : ℕ} (h : r = 70126 ∨ ztgzj) : Bpt r = false := by
  zudvz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sideQ₀_exec (hw : WordsBounded W c)
    {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {A : ℕ} (hF : FCtx P W J H N₁ N₂ A c)
    (hroom : c.nreg ALLOC + sq0Cost N₁.nChords ≤ W) :
    ∃ c' k v₁ v₀ t₁ t₀ k₀, Exec P W sideQ₀ c c' k ∧ k ≤ sq0Cost N₁.nChords ∧
      3 * (endQL N₁.chords ++ ztky).length ≤ k ∧
      v₁.length ≤ 1 ∧ v₀.length ≤ 1 ∧ t₁.length ≤ 1 ∧ t₀.length ≤ 1 ∧ k₀.length ≤ 1 ∧
      c'.nreg 70150 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (endQL N₁.chords ++ ztky).length ∧
      c'.nreg 70128 = (endQL N₁.chords ++ ztky).length ∧
      ChordListAt c'.nmem ztm ztxgr ∧
      zth ∧
      (∀ r, Bside 70150 r = false → c'.nreg r = c.nreg r) ∧
      ztrf ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 70105 = 1 ∧ c'.nreg 70108 = 0 ∧ CapRegs P J c' ∧
      PtAns J zta 0 zthrd 1 v₁ ∧
      PtAns J zta 0 zthrd (-1) v₀ ∧
      PtAns J zta 0 zthrc 1 t₁ ∧
      PtAns J zta 0 zthrc (-1) t₀ ∧
      (SharedExtremum J → ¬ NearU J → PtAns J zta 0 ztchm ztchl k₀) ∧
      (¬ ztffx → k₀ = []) := by
  zudyh

  unfold sq0Cost at hroom
  zubmh

  -- the chord-end queries
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', s₁, a₁, n₁, o05, o08, L₁, m₁, r₁, rr₁, rm₁, ou₁⟩ :=
    endPart_exec (P := P) c hw (S := 70150) (G := 70003) ztp ztp hF.nf₁ hF.le
      hF.is₁ hnW by_omega
  zud
  have hF₁ := hF.keep (fun r h1 h2 => r₁ r (bend_lo h1 by_omega
      by_omega)) (fun a ha => m₁ a (by have := hF.le; omega)) by_omega
  obtain ⟨sd0, sw0, -, -, sdw, sww⟩ := hF₁.side
  obtain ⟨pre, hpre⟩ : ∃ l, l = endQL N₁.chords := by_simp_all
  have hlenpre : pre.length = 2 * N₁.nChords := by zuoya; exact endQL_length _
  zugxv
  -- the shared vertex
  obtain ⟨c₂, k₂, v₁, v₀, e₂, hk₂, hk₂', hv₁, hv₀, a₂, n₂, L₂, m₂, r₂, rr₂, rm₂, ou₂, pv₁, pv₀⟩ :=
    vtxPts_exec (P := P) c₁ w₁ hG hHW (D := 70000) (off := 2) by_norm_num by_norm_num sw0 J 0
      sd0 hF.simple (kk := J.m₁) sd0.2.2.2.1 by_rfl o05 o08
      (LB := A₀) (pre := pre) by_omega n₁ by_simp_all
      zthtp
      by_omega
  zue
  have hF₂ := hF₁.keep ztist (fun a ha => m₂ a (by have := hF₁.le; omega))
      by_simp_all
  obtain ⟨sd0', sw0', -, -, -, -⟩ := hF₂.side
  -- the top of `C₁`
  obtain ⟨c₃, k₃, t₁, t₀, e₃, hk₃, hk₃', ht₁, ht₀, a₃, n₃, L₃, m₃, r₃, rr₃, rm₃, ou₃, pt₁, pt₀⟩ :=
    vtxPts_exec (P := P) c₂ w₂ hG hHW (D := 70000) (off := 3) by_norm_num by_norm_num sw0' J 0
      sd0' hF.simple (kk := J.left.topIdx) sd0'.2.2.2.2.1 J.left.topIdx_le
      ztlis ztlit
      (LB := A₀) (pre := pre ++ v₁ ++ v₀) a₂ n₂ L₂
      (by rw [a₂, show vtxCost = 74000 from rfl]; grind)
      by_grind
  zubj
  have hF₃ := hF₂.keep (fun r h1 h2 => r₃ r (bpt_lo h1 by_omega)) (fun a ha => m₃ a (by have := hF₂.le; omega))
      by_grind
  obtain ⟨sd0'', sw0'', -, -, sdw'', sww''⟩ := hF₃.side
  -- the cap data
  obtain ⟨c₄, k₄, e₄, hk₄, R₄, m₄, r₄, rr₄, rm₄, ou₄⟩ := capS_exec (P := P) c₃ w₃ hG hHW J hF.gen
    sww'' sdw'' sd0''
    (by have h5 := sw0''.1; grind)
    by_grind
  zucc
  have a₄ : ztmvk := r₄ _ by_decide
  have hF₄ := hF₃.keep (fun r h1 h2 => r₄ r (bcs_lo h1 by_omega)) by_grind (by rw [a₄])
  obtain ⟨sd0₄, sw0₄, -, -, -, -⟩ := hF₄.side
  -- the cap query
  obtain ⟨c₅, k₅, k₀, e₅, hk₅, hk₅', hk₀, a₅, n₅, L₅, m₅, r₅, rr₅, rm₅, ou₅, pk₀, nk₀⟩ :=
    capQ₀_exec (P := P) c₄ w₄ hG hHW J hF.simple hF.gen sw0₄ sd0₄ R₄
      (by rw [r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, o05])
      (by rw [r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, o08])
      (LB := A₀) (pre := pre ++ v₁ ++ v₀ ++ t₁ ++ t₀) by_omega
      (by rw [r₄ _ by_decide, n₃]) by_grind
      (by rw [a₄, a₃, show capBCost = 35100 from rfl]; grind)
      by_grind
  have hL : pre ++ v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀ = pre ++ ztky := by
    simp
  have ex : Exec P W sideQ₀ c c₅ _ :=
    .seq e₁ ztbq
  have hlen : (pre ++ ztky).length =
      2 * N₁.nChords + v₁.length + v₀.length + t₁.length + t₀.length + k₀.length := by
    grind
  refine ⟨c₅, _, v₁, v₀, t₁, t₀, k₀, ex, ?_, ?_, hv₁, hv₀, ht₁, ht₀, hk₀, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, pv₁, pv₀, pt₁, pt₀,
    pk₀, nk₀⟩
  · unfold sq0Cost; unfold vtxCost at hk₂ hk₃; unfold capBCost at hk₅; omega
  · omega
  · rw [r₅ _ by_decide, r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, s₁]
  · grind
  · grind
  · grind
  · rw [m₅ a by_omega, m₄,
      m₃ a by_omega,
      m₂ a by_omega, m₁ a ha]
  · rw [r₅ r ztjpo, r₄ r (bcs_of hr), r₃ r ztjpo, r₂ r ztjpo,
      r₁ r ztvev]
  · grind
  · grind
  · grind
  · rw [r₅ _ by_decide, r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, o05]
  · rw [r₅ _ by_decide, r₄ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, o08]
  · exact R₄.keep fun r h1 => r₅ r (bpt_cap h1)
set_option maxHeartbeats 16000000 in
theorem sideQ₁_exec (hw : WordsBounded W c)
    {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {A : ℕ} (hF : FCtx P W J H N₁ N₂ A c)
    (hR : CapRegs P J c) (hroom : c.nreg ALLOC + sq1Cost N₂.nChords ≤ W) :
    ∃ c' k t₁ t₀ k₁, Exec P W sideQ₁ c c' k ∧ k ≤ sq1Cost N₂.nChords ∧
      3 * (endQL N₂.chords ++ ztdil).length ≤ k ∧
      t₁.length ≤ 1 ∧ t₀.length ≤ 1 ∧ k₁.length ≤ 1 ∧
      c'.nreg 70151 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (endQL N₂.chords ++ ztdil).length ∧
      c'.nreg 70128 = (endQL N₂.chords ++ ztdil).length ∧
      ChordListAt c'.nmem ztm (endQL N₂.chords ++ ztdil) ∧
      zth ∧
      (∀ r, Bside 70151 r = false → c'.nreg r = c.nreg r) ∧
      ztrf ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 70105 = 1 ∧ c'.nreg 70108 = 0 ∧
      PtAns J zta 1 ztxmv 1 t₁ ∧
      PtAns J zta 1 ztxmv (-1) t₀ ∧
      (SharedExtremum J → NearU J → PtAns J zta 1 ztchm ztchl k₁) ∧
      (¬ ztget → k₁ = []) := by
  zudyh

  unfold sq1Cost at hroom
  zubmh

  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', s₁, a₁, n₁, o05, o08, L₁, m₁, r₁, rr₁, rm₁, ou₁⟩ :=
    endPart_exec (P := P) c hw (S := 70151) (G := 70004) ztbt ztbt hF.nf₂ hF.le
      hF.is₂ hnW by_omega
  zud
  have hF₁ := hF.keep (fun r h1 h2 => r₁ r (bend_lo h1 by_omega
      by_omega)) (fun a ha => m₁ a (by have := hF.le; omega)) by_omega
  have hR₁ := hR.keep fun r h => r₁ r (by
    zufaq
    omega)
  obtain ⟨-, -, sd1, sw1, -, -⟩ := hF₁.side
  obtain ⟨pre, hpre⟩ : ∃ l, l = endQL N₂.chords := by_simp_all
  have hlenpre : pre.length = 2 * N₂.nChords := by zuoya; exact endQL_length _
  zugxv
  -- the top of `C₂`
  obtain ⟨c₂, k₂, t₁, t₀, e₂, hk₂, hk₂', ht₁, ht₀, a₂, n₂, L₂, m₂, r₂, rr₂, rm₂, ou₂, pt₁, pt₀⟩ :=
    vtxPts_exec (P := P) c₁ w₁ hG hHW (D := 70001) (off := 3) by_norm_num by_norm_num sw1 J 1
      sd1 hF.simple (kk := J.right.topIdx) sd1.2.2.2.2.1 J.right.topIdx_le o05 o08
      (LB := A₀) (pre := pre) by_omega n₁ by_simp_all
      zthtp
      by_omega
  zue
  have hF₂ := hF₁.keep ztist
      (fun a ha => m₂ a (by have := hF₁.le; omega))
      by_simp_all
  have hR₂ := hR₁.keep fun r h => r₂ r (bpt_cap h)
  obtain ⟨-, -, sd1', sw1', -, -⟩ := hF₂.side
  -- the cap query
  obtain ⟨c₃, k₃, k₁', e₃, hk₃, hk₃', hk₀, a₃, n₃, L₃, m₃, r₃, rr₃, rm₃, ou₃, pk₁, nk₁⟩ :=
    capQ₁_exec (P := P) c₂ w₂ hG hHW J hF.simple hF.gen sw1' sd1' hR₂
      ztlis ztlit
      (LB := A₀) (pre := pre ++ t₁ ++ t₀) a₂ n₂ L₂
      (by rw [a₂, show capBCost = 35100 from rfl]; grind)
      by_grind
  have hL : pre ++ t₁ ++ t₀ ++ k₁' = pre ++ ztoiw := by
    simp
  have ex : Exec P W sideQ₁ c c₃ _ := .seq e₁ ztcr
  have hlen : (pre ++ ztoiw).length =
      2 * N₂.nChords + t₁.length + t₀.length + k₁'.length := by
    grind
  have hv : J.whole.vertex _ = (sideChain J 1).vertex J.right.topIdx :=
    Merge.Junction.whole_vertex_add J _
  refine ⟨c₃, _, t₁, t₀, k₁', ex, ?_, ?_, ht₁, ht₀, hk₀, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, by_grind,
    by grind, pk₁, nk₁⟩
  · unfold sq1Cost; unfold vtxCost at hk₂; unfold capBCost at hk₃; omega
  · omega
  · rw [r₃ _ by_decide, r₂ _ by_decide, s₁]
  · grind
  · grind
  · grind
  · grind
  · rw [r₃ r ztjpo, r₂ r ztjpo, r₁ r ztvev]
  · grind
  · grind
  · grind
  · rw [r₃ _ by_decide, r₂ _ by_decide, o05]
  · rw [r₃ _ by_decide, r₂ _ by_decide, o08]
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm
@[expose] public section
def SwPre (X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem ztefy ztm ∧
    rd c bSweep 5 ≤ X.cap P c.nmem ztefy ∧ rd c bSweep 7 ≤ 1 ∧
    JunctionWF P ztm c.nmem ztcds ztcdt ztcdu ∧
    ∃ H J N₁ N₂ L, JunctionAt c.nmem ztcds ztcdt ztcdu
        zta H J ∧
      J.P.Simple ∧
      Ok P ztbw ∧ Ok P ztj ∧
      NFWithin c.nmem ztwb ztm N₁ ∧
      NFWithin c.nmem ztrl ztm N₂ ∧
      IsNF ztbw zta N₁ ∧ IsNF ztj zta N₂ ∧
      (chainModel J.left).DegLe ztwjx ztbwd ∧
      (chainModel J.right).DegLe ztwis ztbwd ∧
      (chainModel J.left).Semigranular ztwjx ztbro ∧
      (chainModel J.right).Semigranular ztwis ztbro ∧
      rd c bSweep 9 = L.length ∧ rd c bSweep 8 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztiae L ∧
      ztybp ∧
      (rd c bSweep 7 = 1 → ∃ L₁ : List zte, L = sweepEndQ N₂.chords ++ L₁ ∧
        L₁.length ≤ 3) ∧
      ∀ q ∈ L, ((chainModel ztzxx).pos zta ztpo).2 =
        ((Qof P).vtx zteut).2

/-- The postcondition of the sweep. -/
def SwPost (P : Polygon) (c c' : Config) : Prop :=
  ∀ H J (L : List zte),
    JunctionAt c.nmem ztcds ztcdt ztcdu zta H J →
    rd c bSweep 9 = L.length → ChordListAt c.nmem ztiae L →
    ∃ R : List ztpl, c.nreg ALLOC ≤ rd c' bSweep 11 ∧
      rd c' bSweep 11 + 4 * L.length ≤ c'.nreg ALLOC ∧ R.length = L.length ∧
      ResultListAt c'.nmem ztrvs R ∧
      ∀ j, j < L.length →
        SeesInWhole J zta ztdae ztwzi ztxkj

/-- The cost of the sweep. -/
def SwCost (κ : ℕ → ℕ) (F : ℕ → ℕ) (_ : Polygon) (c : Config) : ℕ :=
  κ ztbwd * ztwqz *
    (F ztbro +
      Nat.clog 2 ztwqz + 1)
theorem sweep_meets (hS : SweepSpecH) : ∃ (mk : Stmt → Stmt) (κ : ℕ → ℕ),
    ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
      X.CapLocal → Bs ⊆ oracleBands → ShooterOK sh Bs F X Ok →
      Meets ztkbc ztdwg ztnpn SwPost (SwCost κ F) := hS
theorem holds_frameF {X : MemCtx} {P : Polygon} {g : ℕ} {B : Finset ℕ} {c c' : Config} {k : ℕ}
    (hX : X.holds P c.nmem g ztm) (hf : Frame B c c' k) :
    X.holds P c'.nmem g ztdo :=
  X.mono _ _ _ _ _ hf.2.2.2.2.2.1 ztfow
theorem cap_frameF {X : MemCtx} (hloc : X.CapLocal) {P : Polygon} {g : ℕ} {B : Finset ℕ}
    {c c' : Config} {k : ℕ} (hX : X.holds P c.nmem g ztm) (hf : Frame B c c' k) :
    X.cap P c'.nmem g = X.cap P c.nmem g :=
  hloc P c.nmem c'.nmem g _ ztnym hX

/-- The facts of the fusion's precondition beyond `FCtx`. -/
structure FPre (P : Polygon) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
    (N₁ N₂ : NF) (c : Config) : Prop where
  okL : Ok P ztbw
  okR : Ok P ztj
  okW : Ok P ztbm
  degL : (chainModel J.left).DegLe ztwjx ztghh
  degR : (chainModel J.right).DegLe ztwis ztghh
  sgL : (chainModel J.left).Semigranular ztwjx ztmgf
  sgR : (chainModel J.right).Semigranular ztwis ztmgf
  holds : X.holds P c.nmem ztvim ztm
  cap : c.nreg 70005 ≤ X.cap P c.nmem ztvim
variable {P : Polygon}
theorem FPre.keep {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
    {N₁ N₂ : NF} {c c' : Config} (h : FPre P X Ok J N₁ N₂ c) (hloc : X.CapLocal)
    (hr : ∀ r, 70005 ≤ r → r < 70009 → c'.nreg r = c.nreg r) {B : Finset ℕ} {k : ℕ}
    (hf : Frame B c c' k) : FPre P X Ok J N₁ N₂ c' := by
  obtain ⟨o1, o2, o3, d1, d2, s1, s2, hh, hc⟩ := h
  have e5 := hr 70005 by_norm_num by_norm_num
  have e6 := hr 70006 by_norm_num by_norm_num
  have e8 := hr 70008 by_norm_num by_norm_num
  refine ⟨o1, o2, o3, by_simp_all, by_simp_all, by_simp_all,
    by simp_all, by rw [e8]; exact holds_frameF hh hf, ?_⟩
  rw [e5, e8, cap_frameF hloc hh hf]; exact hc
theorem junctionWF_mono {E E' : ℕ} {m : ℕ → ℕ} {bl br bw : ℕ}
    (h : JunctionWF P E m bl br bw) (hE : E ≤ E') : JunctionWF P E' m bl br bw :=
  ⟨h.1.mono hE, h.2.1.mono hE, h.2.2.1.mono hE, h.2.2.2⟩

/-- The sweep arguments. -/
def swSet (i S Lr : ℕ) : Stmt := block [.copyN 240000 70000, .copyN 240001 70001,
  .copyN 240002 70002, .copyN 240003 70003, .copyN 240004 70004, .copyN 240005 70005,
  .copyN 240006 70006, .constN 240007 i, .copyN 240008 S, .copyN 240009 Lr,
  .copyN 240010 70008, .copyN ztena Lr]

/-- **One sweep stage.** -/
def swStage (mk : Stmt) (i S Lr RB : ℕ) : Stmt :=
  .seq ztrxh (.seq mk ztoza)
theorem swSet_exec {W : ℕ} (c : Config) (hw : WordsBounded W c) {i S Lr : ℕ}
    (hi : i ≤ 1) (hW1 : 1 ≤ W) (hS : 70000 ≤ S ∧ S < 80000) (hLr : 70100 ≤ Lr ∧ Lr < 70200) :
    ∃ c' k, Exec P W ztrxh c c' k ∧ k = 12 ∧
      (∀ j, j < 7 → c'.nreg ztjfo = c.nreg (70000 + j)) ∧ c'.nreg 240007 = i ∧
      c'.nreg 240008 = c.nreg S ∧ c'.nreg 240009 = c.nreg Lr ∧ c'.nreg 240010 = c.nreg 70008 ∧
      c'.nreg ztena = c.nreg Lr ∧
      (∀ r, bandOf r ≠ bSweep → r ≠ Lr + 24 + 2 * i → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swSet
  exec_block
  all_goals try omega
  refine ⟨rfl, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · interval_cases j <;> simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, Nat.add_zero]
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other])
  · have : r < 240000 ∨ 250000 ≤ r := by
      unfold bandOf bSweep at h1; omega
    zup

/-- The bands of the fusion. -/
def FB : Finset ℕ := fuseBands ∪ oracleBands
theorem ftrF {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : Frame FB c c₁ k₁) (h₂ : Frame FB c₁ c₂ k₂) :
    Frame FB c c₂ ztbct :=
  (h₁.trans h₂).mono by_simp le_rfl
theorem sweep_sub : sweepBands ∪ oracleBands ⊆ FB := by_decide
theorem band7 : bFuse ∈ FB := by_decide
theorem band24 : bSweep ∈ FB := by_decide
set_option maxHeartbeats 8000000 in
/-- **One sweep stage.** -/
theorem swStage_exec {mk : Stmt} {κs F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hM : Meets mk ztdwg ztnpn SwPost zttde)
    {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {A : ℕ} (hF : FCtx P W J H N₁ N₂ A c) (hP : FPre P X Ok J N₁ N₂ c)
    {i S Lr RB : ℕ} (hi : i ≤ 1) (hS : 70000 ≤ S ∧ S < 80000) (hLr : 70100 ≤ Lr ∧ Lr < 70200)
    (hRB : 70000 ≤ RB ∧ RB < 80000) (hRB' : RB ≠ Lr + 24 + 2 * i)
    {L : List zte} (hLl : c.nreg Lr = L.length) (hL : ChordListAt c.nmem (c.nreg S) L)
    (hQB : c.nreg S + 3 * L.length ≤ c.nreg ALLOC) (hOK : ∀ q ∈ L, QueryOK J zta i q)
    (hend : i = 1 → ∃ L₁ : List zte, L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3)
    (hHt : ∀ q ∈ L, ((chainModel ztgi).pos zta ztpo).2 =
      ((Qof P).vtx zteut).2)
    (hroom : c.nreg ALLOC + 13 + κs ztghh * zthbu *
      ztclj ≤ W) :
    ∃ c' k R, Exec P W ztpei c c' k ∧
      k ≤ 13 + κs ztghh * zthbu *
        ztclj ∧
      R.length = L.length ∧ c.nreg ALLOC ≤ c'.nreg RB ∧
      c'.nreg RB + 4 * L.length ≤ c'.nreg ALLOC ∧ ResultListAt c'.nmem (c'.nreg RB) R ∧
      (∀ j, j < L.length →
        SeesInWhole J zta i ztwzi ztxkj) ∧
      Frame FB c c' k ∧
      (∀ r, bandOf r = bFuse → r ≠ RB → r ≠ Lr + 24 + 2 * i → c'.nreg r = c.nreg r) ∧
      c'.nreg ztena = L.length := by
  zudk
  obtain ⟨c₁, k₁, e₁, hk₁, q0, q7, q8, q9, q10, q24, qr, qm, qrr, qrm, qo⟩ :=
    swSet_exec (P := P) c hw hi hW1 hS hLr
  zud
  have a₁ : ztdc := qr _ by_decide ztu
  have F₁ : ztsbj := ⟨fun r hr ha => qr r (fun h => hr (h ▸ band24)) (fun h => hr (by
      zvmwc; unfold bandOf; rw [show ztena / 10000 = 7 by omega]; decide)),
    by grind, by_grind, by_grind, qo, by rw [a₁],
    by omega⟩
  have r0 : rd c₁ bSweep 0 = c.nreg 70000 := q0 0 by_norm_num
  have r1 : rd c₁ bSweep 1 = c.nreg 70001 := q0 1 by_norm_num
  have r2 : rd c₁ bSweep 2 = c.nreg 70002 := q0 2 by_norm_num
  have r3 : rd c₁ bSweep 3 = c.nreg 70003 := q0 3 by_norm_num
  have r4 : rd c₁ bSweep 4 = c.nreg 70004 := q0 4 by_norm_num
  have r5 : rd c₁ bSweep 5 = c.nreg 70005 := q0 5 by_norm_num
  have r6 : rd c₁ bSweep 6 = c.nreg 70006 := q0 6 by_norm_num
  have r7 : rd c₁ bSweep 7 = i := q7
  have r8 : rd c₁ bSweep 8 = c.nreg S := q8
  have r9 : rd c₁ bSweep 9 = L.length := by rw [← hLl]; exact q9
  have r10 : rd c₁ bSweep 10 = c.nreg 70008 := q10
  have hK1 : ztplu := (Robust.holds hF.nf₁).1
  have hK2 : ztplv := (Robust.holds hF.nf₂).1
  have hpre : SwPre X Ok P W c₁ := by
    unfold SwPre
    rw [qm, a₁, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
    exact ⟨hF.good, hF.hw, hP.holds, hP.cap, hi, junctionWF_mono hF.jwf hF.le, H, J, N₁, N₂, L,
      hF.jat, hF.simple, hP.okL, hP.okR, hF.nf₁.mono hF.le, hF.nf₂.mono hF.le,
      hF.is₁, hF.is₂, hP.degL, hP.degR, hP.sgL, hP.sgR, rfl, hQB, hL, hOK, hend, hHt⟩
  have hcost : SwCost κs F P c₁ = κs ztghh * zthbu *
      ztclj := by
    unfold SwCost; grind
  obtain ⟨c₂, k₂, e₂, hk₂, post, F₂⟩ := hM P W c₁ w₁ hpre by_omega
  rw [hcost] at hk₂
  obtain ⟨R, hR1, hR2, hRl, hRL, hsees⟩ := post H J L (by rw [qm, r0, r1, r2]; exact hF.jat)
    r9 by_grind
  rw [r7] at hsees
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, t0, tr, tm, trr, trm, tou⟩ : ∃ c₃ k₃, Exec P W
      ztoza c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg RB = c₂.nreg 240011 ∧
      (∀ r, r ≠ RB → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    refine ztgpj
    zuit
  have hRBA : RB ≠ ALLOC := by unfold ALLOC; omega
  have F₃ : Frame FB c₂ c₃ k₃ := ⟨fun r hr ha => tr r (fun h => hr (by
      zvmwc; unfold bandOf; rw [show RB / 10000 = 7 by omega]; decide)),
    by grind, by_grind, by_grind, tou,
    by grind, by_grind⟩
  have ex : Exec P W ztpei c c₃ _ := .seq e₁ ztcr
  have Ft : Frame FB c c₃ _ :=
    ftrF F₁ (ftrF (F₂.mono sweep_sub le_rfl) F₃)
  have hband : ∀ r, bandOf r = bFuse → bandOf r ∉ sweepBands ∪ oracleBands := fun r h => by
    zvmwc; decide
  refine ⟨c₃, _, R, ex, by_omega, hRl, ?_, ?_, ?_, ?_, Ft, fun r h1 h2 h3 => ?_, ?_⟩
  · rw [t0]; rw [a₁] at hR1; exact hR1
  · rw [t0, tr _ hRBA.symm]; exact hR2
  · rw [tm, t0]; exact hRL
  · omega
  · have hA : ztjag := by intro h; zvmwc at h1; exact absurd h1 by_decide
    rw [tr r h2, F₂.1 r by_grind hA, qr r (by rw [h1]; decide) h3]
  · rw [tr _ (Ne.symm hRB'), F₂.1 _ (hband _ ztiiv) ztu,
      q24, hLl]
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
variable {m m' : ℕ → ℕ} {B E : ℕ}
theorem chordList_agree {L : List zte}
    (h : ChordListAt m B L) (hE : B + 3 * L.length ≤ E) (he : ∀ a, a < E → m' a = m a) :
    ChordListAt m' B L := fun i hi => by
  zuety
theorem resultList_agree {R : List ztpl}
    (h : ResultListAt m B R) (hE : B + 4 * R.length ≤ E) (he : ∀ a, a < E → m' a = m a) :
    ResultListAt m' B R := fun i hi => by
  obtain ⟨h0, h1, h2, h3⟩ := h i hi
  grind

/-- The arguments of the first collection loop. -/
def clSet : Stmt := block [.constN 70110 0, .constN 70116 3, .constN 70117 4, .constN 70118 2,
  .copyN 70156 ALLOC, .copyN 70111 70152, .constN 70112 0, .copyN 70113 70153,
  .copyN 70115 70150]

/-- The arguments of the second collection loop. -/
def clSet2 : Stmt := block [.copyN 70111 70154, .constN 70112 0, .copyN 70113 70155,
  .copyN 70115 70151]

/-- **The collection.** -/
def collectS : Stmt := .seq clSet (.seq clqLoop (.seq clSet2 clqLoop))
set_option maxHeartbeats 16000000 in
theorem collectS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {L₀ L₁ : List zte} {R₀ R₁ : List ztpl}
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    (hL₀ : ChordListAt c.nmem ztvin L₀) (hn₀ : c.nreg 70152 = L₀.length)
    (hR₀ : ResultListAt c.nmem ztvip R₀) (hl₀ : R₀.length = L₀.length)
    (hb₀ : c.nreg 70150 + 3 * L₀.length ≤ c.nreg ALLOC)
    (hb₀' : c.nreg 70153 + 4 * R₀.length ≤ c.nreg ALLOC)
    (hL₁ : ChordListAt c.nmem ztvio L₁) (hn₁ : c.nreg 70154 = L₁.length)
    (hR₁ : ResultListAt c.nmem ztviq R₁) (hl₁ : R₁.length = L₁.length)
    (hb₁ : c.nreg 70151 + 3 * L₁.length ≤ c.nreg ALLOC)
    (hb₁' : c.nreg 70155 + 4 * R₁.length ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 30 * ztszq + 40 ≤ W) :
    ∃ c' k, Exec P W collectS c c' k ∧ k ≤ 24 * ztszq + 20 ∧
      c'.nreg 70156 = c.nreg ALLOC ∧
      c'.nreg 70110 = (collectQ L₀ R₀ ++ collectQ L₁ R₁).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (collectQ L₀ R₀ ++ collectQ L₁ R₁).length ∧
      ChordListAt c'.nmem ztm (collectQ L₀ R₀ ++ collectQ L₁ R₁) ∧
      Frame FB c c' k ∧
      (∀ r, zthjx → r ≠ 70156 → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  zugot
  zufth
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W clSet c c₁ k₁ ∧ k₁ = 9 ∧
      (c₁.nreg 70110 = 0 ∧ c₁.nreg 70116 = 3 ∧ c₁.nreg 70117 = 4 ∧ c₁.nreg 70118 = 2 ∧
        c₁.nreg 70156 = A ∧ c₁.nreg 70111 = L₀.length ∧ c₁.nreg 70112 = 0 ∧
        c₁.nreg 70113 = c.nreg 70153 ∧ c₁.nreg 70115 = c.nreg 70150 ∧
        (∀ r, zthjx → r ≠ 70156 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold clSet
    exec_block
    all_goals try omega
    zubee
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA', hn₀, ALLOC]
    and_intros
    all_goals first | trivial | rfl |
      (intro r h1 h2; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨t10, t16, t17, t18, t56, t11, t12, t13, t15, tr, tm, trr, trm, tou⟩ := q
  zud
  have a₁ : ztizl := by rw [tr _ by_decide by_decide, hA]
  have c05 : ztpmw := by_simp_all
  have c08 : c₁.nreg 70108 = 0 := by_simp_all
  -- the first loop
  have I0 : CLQI W L₀ R₀ ztvin ztvip A [] c₁ c₁ :=
    ⟨w₁, by_omega, by_omega, by_omega,
      by rw [a₁, t12]; rfl, by rw [t10, t12]; rfl,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, by rw [t12]; zuofb; intro i hi; simp_all,
      rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', I₂, h₂⟩ := clqLoop_exec (P := P) (L := L₀) (R := R₀)
    (pre := []) c05 c08 t16 t17 t18 by_omega hl₀.symm
    by_simp_all by_simp_all by_omega by_omega
    by_grind by_grind
    R₀.length c₁ I0 by_omega
  have tk0 : L₀.take ztvmy = L₀ := by_simp_all
  have tk0' : R₀.take ztvmy = R₀ := by_simp_all
  have i2a := I₂.alloc
  have i2c := I₂.cnt
  have i2l := I₂.list
  rw [tk0, tk0'] at i2a i2c i2l
  zumfx
  set C₀ := collectQ L₀ R₀ with hC₀
  have hC₀l : C₀.length ≤ L₀.length := collectQ_length_le _ _
  have g₂ : ∀ r, r ≠ 70110 → r ≠ 70112 → r ≠ 70113 → r ≠ 70114 → r ≠ 70115 → r ≠ 70119 →
      r ≠ ALLOC → c₂.nreg r = c₁.nreg r := I₂.regs
  -- the second loop
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W clSet2 c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 70111 = L₁.length ∧ c₃.nreg 70112 = 0 ∧
        c₃.nreg 70113 = c.nreg 70155 ∧ c₃.nreg 70115 = c.nreg 70151 ∧
        (∀ r, r ≠ 70111 → r ≠ 70112 → r ≠ 70113 → r ≠ 70115 → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    have r54 : c₂.nreg 70154 = L₁.length := by
      grind
    have r55 : c₂.nreg 70155 = c.nreg 70155 := by
      rw [g₂ _ by_decide by_decide by_decide by_decide by_decide by_decide
        by_decide, tr _ by_decide by_decide]
    have r51 : c₂.nreg 70151 = c.nreg 70151 := by
      rw [g₂ _ by_decide by_decide by_decide by_decide by_decide by_decide
        by_decide, tr _ by_decide by_decide]
    unfold clSet2
    exec_block
    all_goals try omega
    zubee
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, r54, r55, r51]
    and_intros
    all_goals first | trivial | rfl |
      (intro r h1 h2 h3 h4; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨u11, u12, u13, u15, ur, um, urr, urm, uou⟩ := q
  zubj
  have c305 : ztusj := by
    grind
  have c308 : c₃.nreg 70108 = 0 := by
    grind
  have c3k : ∀ r, r = 70116 ∨ r = 70117 ∨ r = 70118 → c₃.nreg r = c₁.nreg r := by
    rintro r (rfl | rfl | rfl) <;>
    rw [ur _ by_decide by_decide by_decide by_decide, g₂ _ by_decide by_decide
      by_decide by_decide by_decide by_decide by_decide]
  have mA : ∀ a, a < A → c₃.nmem a = c.nmem a := fun a ha => by
    rw [um, I₂.low a by_omega, tm]
  have a₂ : c₂.nreg ALLOC = A + 3 * C₀.length := by_grind
  have a₃ : c₃.nreg ALLOC = A + 3 * C₀.length := by
    rw [ur _ by_decide by_decide by_decide by_decide, a₂]
  have n₃ : c₃.nreg 70110 = C₀.length := by
    grind
  have J0 : CLQI W L₁ R₁ ztvio ztviq A C₀ c₃ c₃ :=
    ⟨w₃, by_omega, by_omega, by_omega,
      by rw [a₃, u12]; zuofb, by rw [n₃, u12]; zuofb,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl,
      by rw [u12, um]; simp only [List.take_zero, collectQ, List.zip_nil_left, List.filter_nil,
        List.map_nil, List.append_nil]; grind, rfl, rfl, rfl⟩
  obtain ⟨c₄, k₄, e₄, hk₄, hk₄', I₄, h₄⟩ := clqLoop_exec (P := P) (L := L₁) (R := R₁)
    (pre := C₀) c305 c308 by_grind by_grind
    by_grind by_omega hl₁.symm
    (resultList_agree hR₁ by_omega mA) (chordList_agree hL₁ by_omega mA) by_omega
    by_omega by_omega by_omega R₁.length c₃ J0 by_omega
  have tk1 : L₁.take ztvns = L₁ := by_grind
  have tk1' : R₁.take ztvns = R₁ := by_grind
  have i4a := I₄.alloc
  have i4c := I₄.cnt
  have i4l := I₄.list
  rw [tk1, tk1'] at i4a i4c i4l
  set C₁ := collectQ L₁ R₁ with hC₁
  have hC₁l : C₁.length ≤ L₁.length := collectQ_length_le _ _
  have ex : Exec P W collectS c c₄ ztwwh := .seq e₁ ztcb
  have g₄ : ∀ r, r ≠ 70110 → r ≠ 70112 → r ≠ 70113 → r ≠ 70114 → r ≠ 70115 → r ≠ 70119 →
      r ≠ ALLOC → c₄.nreg r = c₃.nreg r := I₄.regs
  have regs : ∀ r, zthjx → r ≠ 70156 → r ≠ ALLOC → c₄.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [g₄ r by_omega by_omega by_omega by_omega by_omega by_omega h3,
        ur r by_omega by_omega by_omega by_omega,
        g₂ r by_omega by_omega by_omega by_omega by_omega by_omega h3, tr r h1 h2]
  have a₄ : c₄.nreg ALLOC = A + 3 * (C₀ ++ C₁).length := i4a
  have hlen : (C₀ ++ C₁).length ≤ L₀.length + L₁.length := by
    zukpn
  refine ⟨c₄, _, ex, by_omega, ?_, i4c, by_grind, by_grind,
    ⟨fun r hr ha => ?_, fun r _ => by rw [I₄.rr, urr, I₂.rr, trr], fun a ha => ?_,
      fun a _ => by rw [I₄.rm, urm, I₂.rm, trm], by rw [I₄.out, uou, I₂.out, tou],
      by omega, by_omega⟩, regs⟩
  · rw [g₄ _ by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, ur _ by_decide by_decide by_decide by_decide,
      g₂ _ by_decide by_decide by_decide by_decide by_decide by_decide by_decide,
      t56, hA]
  · have h7 : ztumz := fun h => hr zttlh
    have : r < 70000 ∨ 80000 ≤ r := by unfold bandOf bFuse at h7; omega
    exact regs r by_omega by_omega ha
  · rw [I₄.low a by_grind, um, I₂.low a by_grind,
      tm]
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK MergeAsm
@[expose] public section
def BPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    ModelDescWF P ztm c.nmem ztue ∧
    ∃ M L, ModelDescAt c.nmem ztue zta M ∧
    GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
    ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L

/-- The postcondition of `BuildNF`. -/
def BPost (P : Polygon) (c c' : Config) : Prop :=
  ∀ M L, ModelDescAt c.nmem ztue zta M →
    rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
      ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem ztdph ztdo N ∧
        IsNF M zta N ∧ N.chords.map ztwma = L ∧ N.dec = []

/-- The cost of `BuildNF`. -/
def BCost (κ : ℕ) (_ : Polygon) (c : Config) : ℕ :=
  κ * (rd c bBuild 2 * (Nat.clog 2 (rd c bBuild 2) + 1) + 1)
theorem build_meets (hB : BuildNFSpec) :
    ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign} BPre BPost (BCost κ) := hB

/-- A model descriptor of the whole chain at the allocator. -/
def descF : Stmt := block [.constN 70165 1, .constN 70166 5, .copyN 70160 ALLOC,
  .constN 70161 0, .storeN 70160 70161, .copyN 70162 70002, .addN 70163 70160 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164,
  .constN 70167 6, .addN ALLOC ALLOC 70167]
theorem descF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {A bw : ℕ}
    (hA : c.nreg ALLOC = A) (hbw : c.nreg 70002 = bw) (hbA : bw + 5 ≤ A) (hAW : A + 6 ≤ W) :
    ∃ c' k, Exec P W descF c c' k ∧ k = 27 ∧ c'.nreg 70160 = A ∧ c'.nreg ALLOC = A + 6 ∧
      c'.nmem A = 0 ∧ ztxsm ∧
      ztfjc ∧
      (∀ r, ztofx → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descF
  zufth
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', hbw, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun j hj => ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl⟩
  · tauto
  · zudvw
  · simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hA', hbw, ALLOC]
  · interval_cases j <;>
      simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hA', hbw, ALLOC, add_zero]
  · zudvv
  · zujym
    zup

/-- The arguments of `BuildNF`. -/
def bldSet : Stmt := block [.copyN 40000 70160, .copyN 40001 70242, .copyN 40002 70219]

/-- The output handle. -/
def bldOut : Stmt := block [.copyN 70007 40003]

/-- **The normal form of the fused chord list.** -/
def bldStage (sB : Stmt) : Stmt := .seq descF (.seq bldSet (.seq sB bldOut))
set_option maxHeartbeats 8000000 in
theorem bldStage_exec {sB : Stmt} {κB : ℕ}
    (hB : Meets sB {bBuild, bSort, bSign} BPre BPost ztuwn) {P : Polygon} {W : ℕ}
    (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W)
    {J : Merge.Junction} {H : Host} (hwf : ChainWF P ztm c.nmem ztfgr)
    (hC : ChainDescAt c.nmem ztfgr zta H J.whole) (hP : J.P.Simple)
    {D : List zte} (h42 : ChordListAt c.nmem ztvir D)
    (h19 : c.nreg 70219 = D.length) (hD : c.nreg 70242 + 3 * D.length ≤ c.nreg ALLOC)
    (hok : ChordTriplesOK ztbm zta D)
    (hroom : c.nreg ALLOC + 40 + κB * ztemg ≤ W) :
    ∃ c' k N, Exec P W ztqdy c c' k ∧
      k ≤ 40 + κB * ztemg ∧
      c.nreg ALLOC ≤ c'.nreg 70007 ∧ NFWithin c'.nmem ztvgp ztdo N ∧
      IsNF ztbm zta N ∧ N.chords.map ztwma = D ∧
      Frame FB c c' k ∧
      (∀ r, bandOf r = bFuse → r ≠ 70007 → ztofx → c'.nreg r = c.nreg r) := by
  zugot
  obtain ⟨bw, hbw⟩ : ∃ x, c.nreg 70002 = x := zths
  rw [hbw] at hwf hC
  zuivl
  obtain ⟨c₁, k₁, e₁, hk₁, v60, a₁, m0, mc, mo, r₁, rr₁, rm₁, o₁⟩ :=
    descF_exec (P := P) c hw hA hbw by_omega by_omega
  zud
  have he : ztknx := fun a ha => mo a ztbbu
  obtain ⟨hMD, hMWF⟩ := modelDesc_copy (E := A) (E' := c₁.nreg ALLOC) (A := A)
    by_simp_all hC le_rfl he m0 mc (by rw [a₁])
  have r42 : c₁.nreg 70242 = c.nreg 70242 := r₁ _ ztvcg by_decide
  have r19 : c₁.nreg 70219 = D.length := by_grind
  obtain ⟨c₂, k₂, e₂, hk₂, q0, q1, q2, qr, qm, qrr, qrm, qo⟩ : ∃ c₂ k₂, Exec P W bldSet c₁ c₂ k₂ ∧
      k₂ = 3 ∧ c₂.nreg 40000 = A ∧ c₂.nreg 40001 = c.nreg 70242 ∧ c₂.nreg 40002 = D.length ∧
      (∀ r, ztoft → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    unfold bldSet
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      v60, r42, r19]
  zue
  have a₂ : c₂.nreg ALLOC = A + 6 := by rw [qr _ ztbuo, a₁]
  have hL₂ : ChordListAt c₂.nmem ztvir D :=
    chordList_agree (E := A) h42 by_omega ztese
  have hpre : BPre P W c₂ := by
    unfold BPre
    refine ⟨hG, hHW, ?_, chainModel J.whole, D, ?_, Or.inl ztexm, q2, ?_, ?_, hok⟩
    · show ModelDescWF P zthwb c₂.nmem ztqkj
      simp_all
    · show ModelDescAt c₂.nmem ztqkj zta ztbm
      simp_all
    · show c₂.nreg 40001 + 3 * D.length ≤ c₂.nreg ALLOC
      omega
    · show ChordListAt c₂.nmem (c₂.nreg 40001) D
      simp_all
  have hcost : BCost κB P c₂ = κB * ztemg := by
    show κB * (c₂.nreg 40002 * (Nat.clog 2 (c₂.nreg 40002) + 1) + 1) = _; rw [q2]
  obtain ⟨c₃, k₃, e₃, hk₃, post, F₃⟩ := hB P W c₂ w₂ hpre by_omega
  rw [hcost] at hk₃
  obtain ⟨N, hN1, hN2, hN3, hN4, -⟩ := post ztbm D
    (by show ModelDescAt c₂.nmem ztqkj zta ztbm
        simp_all) q2 (by show ChordListAt c₂.nmem (c₂.nreg 40001) D; simp_all)
  zubj
  obtain ⟨c₄, k₄, e₄, hk₄, t7, tr, tm, trr, trm, tou⟩ : ∃ c₄ k₄, Exec P W bldOut c₃ c₄ k₄ ∧
      k₄ = 1 ∧ c₄.nreg 70007 = c₃.nreg 40003 ∧ (∀ r, r ≠ 70007 → c₄.nreg r = c₃.nreg r) ∧
      c₄.nmem = c₃.nmem ∧ c₄.rreg = c₃.rreg ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    unfold bldOut
    exec_block
    simp_all
  have ex : Exec P W ztqdy c c₄ ztwwh := .seq e₁ ztcb
  have F₁ : ztsbj := ⟨fun r hr ha => r₁ r (by
      have : ztumz := fun h => hr zttlh
      unfold bandOf bFuse at this; omega) ha, fun r _ => by zunkd, fun a ha => mo a (Or.inl
      by_omega), fun a _ => by zunkf, o₁, by_omega,
      by omega⟩
  have F₂ : Frame FB c₁ c₂ k₂ := ⟨fun r hr ha => qr r (by
      have : bandOf r ≠ bBuild := fun h => hr ztik
      unfold bandOf bBuild at this; omega), fun r _ => by zuoey, fun a _ => by zunsl,
      fun a _ => by zuoer, qo, by_omega, by_omega⟩
  have F₄ : Frame FB c₃ c₄ k₄ := ⟨fun r hr ha => tr r ztwmm,
    fun r _ => by rw [trr], fun a _ => by rw [tm], fun a _ => by rw [trm], tou,
    by zuokn, by zuokn; omega⟩
  have Ft : Frame FB c c₄ ztwwh :=
    ftrF F₁ (ftrF F₂ (ftrF (F₃.mono by_decide le_rfl) F₄))
  refine ⟨c₄, _, N, ex, by_omega, ?_, ?_, hN3, hN4, Ft, fun r h1 h2 h3 => ?_⟩
  · have e3 : rd c₃ bBuild 3 = c₃.nreg 40003 := rfl
    omega
  · rw [t7, tr _ by_decide, tm]; exact hN2
  · have hb3 : ztbow := by zvmwp; decide
    have hA' : ztjag := by intro h; zvmwc at h1; exact absurd h1 by_decide
    rw [tr r h2, F₃.1 r hb3 hA', qr r (by unfold bandOf bFuse at h1; omega), r₁ r h3 hA']
open SweepPrim
variable {S r : ℕ} {m : ℕ → ℕ} (J : Merge.Junction) (Q : Polygon) {N : NF}
theorem bside_of_band (hS : S = 70150 ∨ S = 70151) (hr : bandOf r ∉ FB)
    (ha : r ≠ ALLOC) : Bside S r = false := by
  zucrp

  have h7 : bandOf r ≠ 7 := fun h => hr ztik
  unfold bandOf at h1 h5 h7
  unfold ALLOC at ha
  simp only [Bside, Bend, Bpt, Bcs, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega
theorem bside_lo (hS : S = 70150 ∨ S = 70151) (h1 : 70000 ≤ r) (h2 : r < 70100) :
    Bside S r = false := by
  simp only [Bside, Bend, Bpt, Bcs, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega
theorem br_of_band {r : ℕ} (hr : bandOf r ∉ FB) : BR r = false := by
  zucrp

  unfold bandOf at h1 h5
  simp only [BR, Btp, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

/-- **The frame of a side stage.** -/
theorem frame_side {S : ℕ} (hS : S = 70150 ∨ S = 70151) {c c' : Config} {k x : ℕ}
    (hr : ∀ r, Bside S r = false → c'.nreg r = c.nreg r)
    (hrr : ∀ r, BR r = false → c'.rreg r = c.rreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) (ha : c'.nreg ALLOC = c.nreg ALLOC + x) (hk : x ≤ k) :
    Frame FB c c' k :=
  ⟨fun r h1 h2 => hr r (bside_of_band hS h1 h2), fun r h1 => hrr r (br_of_band h1), hm,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩
theorem junction_eq {bl br bw : ℕ} {Q : Polygon} {H H' : Host}
    {J J' : Merge.Junction} (h : JunctionAt m bl br bw Q H J) (h' : JunctionAt m bl br bw Q H' J') :
    J = J' := by
  have e1 := NFLoc.chain_eq_of_desc h.1 h'.1
  have e2 := NFLoc.chain_eq_of_desc h.2.1 h'.2.1
  obtain ⟨P, s, m₁, m₂, a1, a2, a3⟩ := J
  obtain ⟨P', s', m₁', m₂', b1, b2, b3⟩ := J'
  simp only [Merge.Junction.left, Merge.Junction.right, Chain.mk.injEq] at e1 e2
  simp_all
theorem chords_eq_of_nfAt {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N.chords = N'.chords := by
  obtain ⟨hl, -, -, -, -, hc, -⟩ := h
  obtain ⟨hl', -, -, -, -, hc', -⟩ := h'
  have hext : ∀ r r' : CRec, r.h = r'.h → r.lp = r'.lp → r.rp = r'.rp → r.up = r'.up →
      r.dn = r'.dn → r = r' := by
    rintro ⟨⟩ ⟨⟩ h1 h2 h3 h4 h5; simp_all
  apply List.ext_getElem by_omega
  zugoh
  obtain ⟨a0, a1, a2, a3, a4⟩ := hc i hi
  obtain ⟨b0, b1, b2, b3, b4⟩ := hc' i hi'
  have e := hext _ _ (a0.symm.trans b0) (a1.symm.trans b1) (a2.symm.trans b2)
    (a3.symm.trans b3) (a4.symm.trans b4)
  unfold NF.chord at e
  grind
theorem tlist_eq {T : ℕ} {C : List zte} (h : ChordListAt m T C) :
    tlist m T C.length = C := by
  apply List.ext_getElem (by simp [tlist])
  zumgy
  simp only [tlist, List.getElem_map, List.getElem_range, trip]
  obtain ⟨a, b, c⟩ := h j h2
  simp_all
theorem side₀_ok
    (hN : IsNF ztbw Q N) {v₁ v₀ t₁ t₀ k₀ : List zte}
    (pv₁ : PtAns J Q 0 zthrd 1 v₁)
    (pv₀ : PtAns J Q 0 zthrd (-1) v₀)
    (pt₁ : PtAns J Q 0 zthrc 1 t₁)
    (pt₀ : PtAns J Q 0 zthrc (-1) t₀)
    (pk : SharedExtremum J → ¬ NearU J → PtAns J Q 0 ztchm ztchl k₀)
    (nk : ¬ ztffx → k₀ = []) :
    ∀ q ∈ endQL N.chords ++ ztky, QueryOK J Q 0 q ∧ HeightOK J Q 0 q := by
  have hN' : IsNF ztbagu Q N := hN
  zuco
  zubmm

  · exact ⟨(endQL_ok J Q 0 hN').1 q h, endQL_height J Q 0 hN' q h⟩
  · exact ok_ptAns J Q pv₁ q h
  · exact ok_ptAns J Q pv₀ q h
  · zuitt
  · zuits
  · by_cases hx : SharedExtremum J ∧ ¬ NearU J
    · zuitu
    simp_all
theorem side₁_ok
    (hN : IsNF ztj Q N) {t₁ t₀ k₁ : List zte}
    (pt₁ : PtAns J Q 1 ztxmv 1 t₁)
    (pt₀ : PtAns J Q 1 ztxmv (-1) t₀)
    (pk : SharedExtremum J → NearU J → PtAns J Q 1 ztchm ztchl k₁)
    (nk : ¬ ztget → k₁ = []) :
    ∀ q ∈ endQL N.chords ++ ztdil, QueryOK J Q 1 q ∧ HeightOK J Q 1 q := by
  have hN' : IsNF ztbagv Q N := hN
  zuco
  zucqv

  · exact ⟨(endQL_ok J Q 1 hN').1 q h, endQL_height J Q 1 hN' q h⟩
  · zuitt
  · zuits
  · by_cases hx : SharedExtremum J ∧ NearU J
    · zuitu
    simp_all
theorem capAns_of {k₀ k₁ : List zte}
    (pk₀ : SharedExtremum J → ¬ NearU J → PtAns J Q 0 ztchm ztchl k₀)
    (nk₀ : ¬ ztffx → k₀ = [])
    (pk₁ : SharedExtremum J → NearU J → PtAns J Q 1 ztchm ztchl k₁)
    (nk₁ : ¬ ztget → k₁ = []) (h₀ : k₀.length ≤ 1)
    (h₁ : k₁.length ≤ 1) :
    CapAns J Q k₀ k₁ ∧ k₀.length + k₁.length ≤ 1 := by
  refine ⟨⟨fun hx => ⟨fun hu => ⟨pk₀ hx hu, nk₁ fun h => hu h.2⟩,
    fun hu => ⟨nk₀ fun h => h.2 hu, pk₁ hx hu⟩⟩, fun hx => ⟨nk₀ fun h => hx h.1,
    nk₁ fun h => hx h.1⟩⟩, ?_⟩
  by_cases hu : NearU J
  · simp_all
  simp_all
