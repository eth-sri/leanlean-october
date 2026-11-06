module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleRamXp

/-!
# Lemma 3.6 (WP-H), RAM part 9: binary search with a stored table of powers

The binary search of `SearchR` builds its table of powers `2 ^ j` in fresh memory.  The query of
Lemma 3.6 writes no memory (its precondition does not place its structure below the allocator),
so it searches with the table stored by the preprocessing: `tsearch rT rL cmp` takes the table
base and length from the registers `rT`, `rL` and runs the lifting loop `SearchR.liftLoop`.

Main result: `tsearch_exec` (the partition point in `lr 105`, no memory written, the allocator
unchanged).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey

@[expose] public section

/-- Initialise the lifting from the stored table (`rT` base, `rL` length). -/
def tsInit (rT rL : ℕ) : Stmt :=
  block [.constN 50106 1, .copyN 50109 rT, .constN 50105 0, .constN 50115 0, .copyN 50112 rL]

/-- **The search with a stored table.** -/
def tsearch (rT rL : ℕ) (cmp : Stmt) : Stmt := .seq (tsInit rT rL) (liftLoop cmp)

/-- **The search with a stored table.**  From a configuration satisfying `J` with the items
`lr 104 = n` at `lr 103` (below the table), the table of the powers `2 ^ j`, `j < L`, at `T`
(`n < 2 ^ L`), the search leaves the partition point `t ≤ n` in `lr 105`. -/
theorem tsearch_exec {P : Polygon} {W : ℕ} {cmp : Stmt} {Bc : Finset ℕ} {J : Config → Prop}
    {pr : ℕ → Bool} {κ : ℕ} (hcmp : PredOK P W cmp Bc J pr κ) (hB : bLocate ∉ Bc)
    {rT rL T L : ℕ} (hrT5 : bandOf rT ≠ bLocate) (hrL5 : bandOf rL ≠ bLocate)
    {c : Config} (hw : WordsBounded W c) (hJ : J c) (hJs : JStableL J T)
    (hrT : c.nreg rT = T) (hrL : c.nreg rL = L) (htab : ∀ j, j < L → c.nmem (T + j) = 2 ^ j)
    (hbig : c.nreg 50104 < 2 ^ L) (hA : c.nreg 50103 + c.nreg 50104 ≤ T) (hTW : T + L ≤ W)
    (hmono : ∀ i j, i ≤ j → j < c.nreg 50104 → pr (c.nmem (c.nreg 50103 + j)) = true →
      pr (c.nmem (c.nreg 50103 + i)) = true) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W (tsearch rT rL cmp) c c' k ∧ k ≤ (κ + 15) * L + 7 ∧ J c' ∧
      LocL Bc T c c' ∧ c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
      c'.nreg 50105 ≤ c.nreg 50104 ∧
      (∀ j, j < c'.nreg 50105 → pr (c.nmem (c.nreg 50103 + j)) = true) ∧
      (c'.nreg 50105 < c.nreg 50104 → pr (c.nmem (c.nreg 50103 + c'.nreg 50105)) = false) := by
  set A := c.nreg 50103 with hAdef
  set n := c.nreg 50104 with hndef
  have hr5 := bandOf_loc hrT5
  have hl5 := bandOf_loc hrL5
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (tsInit rT rL) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50106 = 1 ∧ c₁.nreg 50109 = T ∧ c₁.nreg 50105 = 0 ∧ c₁.nreg 50115 = 0 ∧
        c₁.nreg 50112 = L ∧
        (∀ r, r ≠ 50106 → r ≠ 50109 → r ≠ 50105 → r ≠ 50115 → r ≠ 50112 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold tsInit
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, by config_simp, ?_, by config_simp, by config_simp, ?_, fun r h1 h2 h3 h4 h5 => ?_,
        rfl, rfl, rfl, rfl⟩
      · ram_simp
      · config_simp; ((try simp only [Machine.upd_apply]); grind)
      · ram_simp
  obtain ⟨o₁, t₁, s₁, z₁, i₁, r₁, m₁, rr₁, rm₁, out₁⟩ := q
  have sl₁ : SLL T c c₁ := ⟨fun r hb _ => by
      have := bandOf_loc hb
      ram_simp,
    rr₁, fun x _ => by rw [m₁], rm₁, out₁⟩
  have I₁ : LiftInv W J Bc T c c₁ pr A n L c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (LocL.refl Bc T c).sl sl₁,
      rA := r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      rn := r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      one := o₁, rT := t₁, zero := z₁, mem := rfl, alloc := rfl, iL := by rw [i₁],
      posn := by omega, tab := fun j hj => by grind,
      bA := hA, bT := hTW, pre := fun j hj => by omega,
      post := fun h' => by grind }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hfin⟩ := liftLoop_inv (P := P) hcmp hJs hB hmono I₁
  rw [i₁] at hk₂
  refine ⟨c₂, _, .seq e₁ e₂, by omega, I₂.hJ, I₂.loc, by rw [I₂.mem, m₁], ?_, I₂.posn, I₂.pre,
    hfin⟩
  rw [I₂.alloc, r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]

/-! ## The search predicate on the chords -/

section Chord
variable (m : ℕ → ℕ) (V : QV)

section
variable (i : ℕ)
include i
/-- The height vertex of chord record `i`. -/
def chH : ℕ := m (V.CB + 5 * i)
/-- The walk edge of the left end of chord record `i`. -/
def chL : ℕ := m (V.CB + 5 * i + 1)
/-- The walk edge of the right end of chord record `i`. -/
def chR : ℕ := m (V.CB + 5 * i + 2)

end

/-- The chord at position `q` of the sorted chord table. -/
def chAt (q : ℕ) : ℕ := m (V.CH + q)

end Chord

open Classical in
/-- **The search predicate** on the chord record `i`: below the height of the ray, or at it and
before the origin (the right end not ahead, rightwards; the left end behind, leftwards). -/
noncomputable def chPr (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (i : ℕ) : Bool :=
  decide (i < V.K ∧ (chH m V i < V.hz ∨ (chH m V i = V.hz ∧
    (if V.σb = 1 then ¬ EndGtZ P C V (chR m V i) V.hz else EndLtZ P C V (chL m V i) V.hz))))

/-- **The search predicate procedure** (item in `lr 100`, bit in `lr 102`). -/
def chordPr : Stmt :=
  .ifLtN 50100 120039
    (.seq (t5 120130 50100 120043)
      (.seq (block [.loadN 120131 120130, .addN 120130 120130 120011, .loadN 120132 120130,
          .addN 120130 120130 120011, .loadN 120133 120130])
        (.ifLtN 120131 120023 (.instr (.constN 50102 1))
          (.ifLtN 120023 120131 (.instr (.constN 50102 0))
            (.ifLtN 120024 120011
              (.seq (block [.copyN 120120 120132, .copyN 120121 120023])
                (.seq ltZS (.instr (.copyN 50102 120128))))
              (.seq (block [.copyN 120120 120133, .copyN 120121 120023])
                (.seq gtZS (.instr (.subN 50102 120011 120128)))))))))
    (.instr (.constN 50102 0))

/-- The registers written by `chordPr`. -/
def BP (r : ℕ) : Bool := BX2 r || decide (120120 ≤ r ∧ r ≤ 120133) || decide (r = 50102)

theorem wr_chordPr : wr BP chordPr = true := by decide

section
variable (P : Polygon) (V : QV) (T : ℕ) (m₀ : ℕ → ℕ)
include P V T m₀
/-- The invariant of the chord search: the constants, and the memory below the table. -/
def ChJ (c : Config) : Prop :=
  QConst P V c ∧ ∀ a, a < T → c.nmem a = m₀ a

theorem chJ_stable : JStableL (ChJ P V T m₀) T := by
  intro c c' h hr _ hm _ _
  refine ⟨h.1.congr fun r h1 h2 => hr r ?_ (by omega_nf), fun a ha => (hm a ha).trans (h.2 a ha)⟩
  omega_nf


end


open Classical in
/-- **The search predicate procedure meets the contract of the binary search.** -/
theorem chordPr_ok {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) {T : ℕ} {m₀ : ℕ → ℕ}
    (hKT : ∀ i, i < V.K → V.CB + 5 * i + 2 < T) (hTW : T ≤ W) :
    PredOK P W chordPr {bSign, bOQuery} (ChJ P V T m₀) (chPr P C V m₀) 700 := by
  intro c hw ⟨hq, hm⟩
  suffices H : ∃ c' k, Exec P W chordPr c c' k ∧ k ≤ 700 ∧
      c'.nreg 50102 = (if chPr P C V m₀ (c.nreg 50100) then 1 else 0) by
    obtain ⟨c', k, ex, hk, hv'⟩ := H
    have fb := exec_frameB ex wr_chordPr
    have hBP : ∀ r, BP r = true → bandOf r ∈ ({bSign, bOQuery} : Finset ℕ) ∨ r = 50102 := by
      core_grind
    refine ⟨c', k, ex, hk, ⟨hq.frame fb fun r h1 h2 => ?_, fun a ha => by ram_grind⟩,
      hv', fun r h1 h2 h3 h4 => fb.1 r ?_, fun r h1 => exec_rframe ex (B := Bk) (by decide) r ?_,
      fb.2.2.1, fb.2.2.2.1, fb.2.2.2.2⟩
    · core_grind
    · by_contra hc
      simp only [Bool.not_eq_false] at hc
      grind [BP, BX2, Bk, ALLOC]
    · by_contra hc
      simp only [Bool.not_eq_false] at hc
      apply h1
      have : bandOf r = bSign := by
        simp only [Bk, decide_eq_true_eq] at hc; omega_nf
      simp_all
  obtain ⟨i, hi⟩ : ∃ i, c.nreg 50100 = i := ⟨_, rfl⟩
  rw [hi]
  by_cases hiK : i < V.K
  swap
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec (P := P) hw 50102 0 (by omega)
    refine ⟨c₁, _, .ifLtN_false (by ram_grind) e₁, by omega, ?_⟩
    simp_all [chPr] 
  have haddr := hKT i hiK
  -- read the record
  obtain ⟨c₁, e₁, v₁, r₁, m₁, -, -, -⟩ := t5_exec (P := P) (rd := 120130) (rs := 50100) (rb := 120043)
    (by decide) (by decide) c hw (by ram_grind)
  rw [hi, hq.CB] at v₁
  obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W (block [.loadN 120131 120130,
      .addN 120130 120130 120011, .loadN 120132 120130, .addN 120130 120130 120011,
      .loadN 120133 120130]) c₁ c₂ k₂ ∧ k₂ = 5 ∧
      (c₂.nreg 120131 = chH m₀ V i ∧ c₂.nreg 120132 = chL m₀ V i ∧ c₂.nreg 120133 = chR m₀ V i ∧
        (∀ r, r < 120130 ∨ 120133 < r → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem) := by
    have w₁ := e₁.wb_right
    have one₁ : c₁.nreg 120011 = 1 := by ram_grind
    exec_block
    · omega_nf
    · omega_nf
    · refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
      · config_simp; rw [v₁, m₁, hm _ (by omega)]; rfl
      · config_simp; rw [v₁, one₁, m₁, hm _ (by omega)]; rfl
      · config_simp; rw [v₁, one₁, m₁, hm _ (by omega)]; rfl
      · config_simp; upd_solve
  obtain ⟨x131, x132, x133, r₂, m₂⟩ := v₂
  have hq₂ : QConst P V c₂ := hq.congr fun r h1 h2 => by grind
  
  have hpr : chPr P C V m₀ i = decide (chH m₀ V i < V.hz ∨ (chH m₀ V i = V.hz ∧
      (if V.σb = 1 then ¬ EndGtZ P C V (chR m₀ V i) V.hz else EndLtZ P C V (chL m₀ V i) V.hz))) := by
    grind [chPr]
  rw [hpr]
  have w₂ := e₂.wb_right
  by_cases hlt : chH m₀ V i < V.hz
  · obtain ⟨c₃, e₃, v₃, -⟩ := const_exec (P := P) w₂ 50102 1 (by omega)
    refine ⟨c₃, _, .ifLtN_true (by rw [hi, hq.K]; exact hiK) (.seq e₁ (.seq e₂
      (.ifLtN_true (by rw [x131, hq₂.hz]; exact hlt) e₃))), by omega, ?_⟩
    simp_all
  by_cases hgt : V.hz < chH m₀ V i
  · obtain ⟨c₃, e₃, v₃, -⟩ := const_exec (P := P) w₂ 50102 0 (by omega)
    refine ⟨c₃, _, .ifLtN_true (by rw [hi, hq.K]; exact hiK) (.seq e₁ (.seq e₂
      (.ifLtN_false (by rw [x131, hq₂.hz]; exact hlt) (.ifLtN_true (by rw [x131, hq₂.hz]; exact hgt)
        e₃)))), by omega, ?_⟩
    grind
  
  by_cases hσ : V.σb < 1
  · -- leftwards: the left end is behind
    obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 120120 120132,
        .copyN 120121 120023]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 120120 = chL m₀ V i ∧
          c₃.nreg 120121 = V.hz ∧ ∀ r, r ≠ 120120 → r ≠ 120121 → c₃.nreg r = c₂.nreg r) := by
      exec_block
      exact ⟨rfl, by ram_simp, by config_simp; exact hq₂.hz,
        fun r h1 h2 => by simp_all⟩
    obtain ⟨x120, x121, r₃⟩ := v₃
    have hq₃ : QConst P V c₃ := hq₂.congr fun r h1 h2 => r₃ r (by omega) (by omega)
    obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := ltZS_exec (P := P) hG (by omega) hv htv c₃ e₃.wb_right hq₃
      (by rw [x121]; exact hv.hz_lt)
    obtain ⟨c₅, e₅, v₅, -⟩ := copy_exec (P := P) e₄.wb_right 50102 120128
    refine ⟨c₅, _, .ifLtN_true (by rw [hi, hq.K]; exact hiK) (.seq e₁ (.seq e₂
      (.ifLtN_false (by rw [x131, hq₂.hz]; exact hlt) (.ifLtN_false (by rw [x131, hq₂.hz]; exact hgt)
        (.ifLtN_true (by rw [hq₂.σb, hq₂.one]; exact hσ) (.seq e₃ (.seq e₄ e₅))))))), by omega, ?_⟩
    grind
  · -- rightwards: the right end is not ahead
    obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 120120 120133,
        .copyN 120121 120023]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 120120 = chR m₀ V i ∧
          c₃.nreg 120121 = V.hz ∧ ∀ r, r ≠ 120120 → r ≠ 120121 → c₃.nreg r = c₂.nreg r) := by
      exec_block
      exact ⟨rfl, by ram_simp, by config_simp; exact hq₂.hz,
        fun r h1 h2 => by simp_all⟩
    obtain ⟨x120, x121, r₃⟩ := v₃
    have hq₃ : QConst P V c₃ := hq₂.congr fun r h1 h2 => r₃ r (by omega) (by omega)
    obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, g₄⟩ := gtZS_exec (P := P) hG (by omega) hv htv c₃ e₃.wb_right hq₃
      (by rw [x121]; exact hv.hz_lt)
    have one₄ : c₄.nreg 120011 = 1 := by
      rw [f₄.1 _ (by decide), r₃ _ (by decide) (by decide), hq₂.one]
    have w₄ := e₄.wb_right
    obtain ⟨c₅, e₅, v₅, -⟩ : ∃ c₅, Exec P W (.instr (.subN 50102 120011 120128)) c₄ c₅ 1 ∧
        c₅.nreg 50102 = c₄.nreg 120011 - c₄.nreg 120128 ∧ True :=
      ⟨_, Exec.subN w₄ _ _ _, by config_simp, trivial⟩
    refine ⟨c₅, _, .ifLtN_true (by rw [hi, hq.K]; exact hiK) (.seq e₁ (.seq e₂
      (.ifLtN_false (by rw [x131, hq₂.hz]; exact hlt) (.ifLtN_false (by rw [x131, hq₂.hz]; exact hgt)
        (.ifLtN_false (by rw [hq₂.σb, hq₂.one]; exact hσ) (.seq e₃ (.seq e₄ e₅))))))), by omega, ?_⟩
    rw [v₅, one₄, x120, x121] at *
    have hσ' : V.σb = 1 := by have := hv.σb_le; omega
    grind

end

end OracleR

end Chazelle.Core
