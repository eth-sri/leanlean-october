module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvHProg

/-!
# Down-phase driver, host RAM (D3a), part 4: emitting points and runs

* `Kst n li d`: the constant registers (`1`, `n`, `0`, `3`, `2`, the bit `li`);
* `Buf n T xs d`: the items `xs` written at `T`, the write pointer, the item and point counts;
* `emitS_exec`: `emitS` appends `ptE li n e h`;
* `runS_exec`: `runS` appends `runItems li n s e` and computes the edge of the end point of the
  arc (`ptI … true`).
-/

namespace Chazelle.Core

namespace DrvH

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- The constant registers. -/
structure Kst (n : ℕ) (li : Bool) (d : Config) : Prop where
  one : d.nreg 215020 = 1
  nn : d.nreg 215021 = n
  zero : d.nreg 215022 = 0
  three : d.nreg 215023 = 3
  two : d.nreg 215024 = 2
  li : d.nreg 215002 = if li then 1 else 0


section exec

variable {P : Polygon} {W : ℕ}

theorem qES_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n e : ℕ} (hK : Kst n li d)
    (h64 : d.nreg 215064 = e) (hW : e + 1 ≤ W) :
    ∃ d' k, Exec P W qES d d' k ∧ k ≤ 6 ∧ d'.nreg 215066 = qE li n e ∧ d'.nmem = d.nmem ∧
      FrameM (fun q => decide (q = 215066) || decide (q = 215069)) d d' := by
  obtain ⟨d', k, ex, hk, h66, hm⟩ : ∃ d' k, Exec P W qES d d' k ∧ k ≤ 6 ∧
      d'.nreg 215066 = qE li n e ∧ d'.nmem = d.nmem := by
    unfold qES
    cases li with
    | true =>
      refine spec_ifLtN_true (by ram_grind) ?_
      exec_block
      aesop
    | false =>
      refine spec_ifLtN_false (by ram_grind) ?_
      refine spec_seq ?_
      exec_block
      · ram_grind
      by_cases hlt : e + 1 < n
      · refine spec_ifLtN_true (by config_simp; rw [h64, hK.one, hK.nn]; exact hlt) ?_
        exec_block
        refine ⟨by omega, ?_, rfl⟩
        config_simp
        rw [hK.nn, h64, hK.two]
        simp only [qE, hlt, ↓reduceIte, Bool.false_eq_true, ↓reduceIte]
        omega
      · refine spec_ifLtN_false (by config_simp; rw [h64, hK.one, hK.nn]; exact hlt) ?_
        exec_block
        refine ⟨by omega, ?_, rfl⟩
        config_simp
        rw [hK.nn, hK.one]
        simp only [qE, hlt, ↓reduceIte, Bool.false_eq_true]
  exact ⟨d', k, ex, hk, h66, hm, exec_frameM ex (by decide)⟩


/-- The buffer: items `xs` at `T`, the write pointer after them, the item and point counts. -/
def Buf (n T : ℕ) (xs : List HostItem) (d : Config) : Prop :=
  ItemsAt d.nmem T xs ∧ d.nreg 215040 = T + 3 * xs.length ∧ d.nreg 215011 = xs.length ∧
    d.nreg 215012 = ptsLen n xs

theorem emitS_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n e h T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (h64 : d.nreg 215064 = e) (h65 : d.nreg 215065 = h)
    (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W) (hW2 : ptsLen n xs + 1 ≤ W)
    (hW3 : e + 1 ≤ W) :
    ∃ d' k, Exec P W emitS d d' k ∧ k ≤ 15 ∧ Buf n T (xs ++ [ptE li n e h]) d' ∧
      (∀ a, a < T + 3 * xs.length → d'.nmem a = d.nmem a) ∧ FrameM Bem d d' := by
  obtain ⟨hI, h40, h11, h12⟩ := hB
  obtain ⟨d₁, k₁, e₁, hk₁, q66, qm, qf⟩ := qES_exec (P := P) d hw hK h64 hW3
  have g : ∀ q, (decide (q = 215066) || decide (q = 215069)) = false → d₁.nreg q = d.nreg q :=
    qf.1
  have r20 : d₁.nreg 215020 = 1 := by ram_grind
  have r24 : d₁.nreg 215024 = 2 := by ram_grind
  have r23 : d₁.nreg 215023 = 3 := by ram_grind
  have r65 : d₁.nreg 215065 = h := by ram_simp
  have r40 : d₁.nreg 215040 = T + 3 * xs.length := by ram_simp
  have r11 : d₁.nreg 215011 = xs.length := by ram_simp
  have r12 : d₁.nreg 215012 = ptsLen n xs := by ram_simp
  have hw₁ := e₁.wb_right
  obtain ⟨d', k₂, e₂, hk₂, hm', p40, p11, p12⟩ : ∃ d' k₂, Exec P W wrPt d₁ d' k₂ ∧ k₂ = 9 ∧
      d'.nmem = wr3 d₁.nmem (T + 3 * xs.length) 2 (qE li n e) (h - 1) ∧
      d'.nreg 215040 = T + 3 * xs.length + 3 ∧ d'.nreg 215011 = xs.length + 1 ∧
      d'.nreg 215012 = ptsLen n xs + 1 := by
    unfold wrPt
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp only [r20, r23, r24, r65, r40, q66, r11, r12]
    rw [show T + 3 * xs.length + 1 + 1 = T + 3 * xs.length + 2 by omega]; rfl
  refine ⟨d', k₁ + k₂, .seq e₁ e₂, by omega, ⟨?_, ?_, ?_, ?_⟩, fun a ha => ?_, ?_⟩
  · rw [hm', qm]
    exact hI.snoc (ptE li n e h)
  · omega_nf
  · ram_simp
  · grind [ptsLen_append, ptE, ptsLen_pt]
  · rw [hm', wr3_lt ha, qm]
  · exact (qf.mono (fun q hq => by simp only [Bem, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega)).trans
      (exec_frameM e₂ (by decide))

theorem mod_prev {e n : ℕ} (he : e < n) : (e + n - 1) % n = if e < 1 then n - 1 else e - 1 := by
  split_ifs with h
  · simp_all
  · rw [show e + n - 1 = (e - 1) + n by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)

theorem mod_once {v n : ℕ} (hv : v < 2 * n) : v % n = if v < n then v else v - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)

section
variable (d : Config) (hw : WordsBounded W d) {li : Bool}
include hw
theorem ivS_exec {n ee : ℕ} (hK : Kst n li d)
    (h50 : d.nreg 215050 = ee) :
    ∃ d' k, Exec P W ivS d d' k ∧ k ≤ 4 ∧ d'.nreg 215070 = ivB li n ee ∧ d'.nmem = d.nmem ∧
      FrameM (fun q => decide (q = 215070)) d d' := by
  obtain ⟨d', k, ex, hk, h1, hm⟩ : ∃ d' k, Exec P W ivS d d' k ∧ k ≤ 4 ∧
      d'.nreg 215070 = ivB li n ee ∧ d'.nmem = d.nmem := by
    unfold ivS
    cases li with
    | true =>
      refine spec_ifLtN_true (by ram_grind) ?_
      exec_block
      aesop
    | false =>
      refine spec_ifLtN_false (by ram_grind) ?_
      exec_block
      refine ⟨by omega, ?_, rfl⟩
      config_simp; rw [hK.nn, hK.one, h50]; rfl
  exact ⟨d', k, ex, hk, h1, hm, exec_frameM ex (by decide)⟩

theorem atS_exec {n ee eh iv : ℕ}
    (hK : Kst n li d) (h50 : d.nreg 215050 = ee) (h51 : d.nreg 215051 = eh)
    (h70 : d.nreg 215070 = iv) :
    ∃ d' k, Exec P W atS d d' k ∧ k ≤ 10 ∧
      d'.nreg 215071 = (if eh - 1 = iv then 0 else 1) ∧
      d'.nreg 215072 = (if eh - 1 = iv then (if ee < 1 then n - 1 else ee - 1) else ee) ∧
      d'.nmem = d.nmem ∧
      FrameM (fun q => decide (q = 215063) || decide (q = 215071) || decide (q = 215072) ||
        decide (q = 215076)) d d' := by
  have b51 := hw.1 215051
  have b70 := hw.1 215070
  obtain ⟨d', k, ex, hk, h1, h2, hm⟩ : ∃ d' k, Exec P W atS d d' k ∧ k ≤ 10 ∧
      d'.nreg 215071 = (if eh - 1 = iv then 0 else 1) ∧
      d'.nreg 215072 = (if eh - 1 = iv then (if ee < 1 then n - 1 else ee - 1) else ee) ∧
      d'.nmem = d.nmem := by
    unfold atS
    refine spec_seq ?_
    exec_block
    · omega_nf
    by_cases hv : eh - 1 = iv
    · refine spec_ifLtN_true (by config_simp; rw [h51, hK.one, h70]; omega) ?_
      refine spec_seq ?_
      exec_block
      · omega
      by_cases h0 : ee < 1
      · refine spec_ifLtN_true (by config_simp; rw [h50, hK.one]; omega) ?_
        exec_block
        refine ⟨by omega, ?_, ?_, rfl⟩ <;> config_simp <;> ram_grind
      · refine spec_ifLtN_false (by config_simp; rw [h50, hK.one]; omega) ?_
        exec_block
        refine ⟨by omega, ?_, ?_, rfl⟩ <;> config_simp <;>
          ram_grind
    · refine spec_ifLtN_false (by config_simp; rw [h51, hK.one, h70]; omega) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, ?_, rfl⟩ <;> config_simp <;> grind
  exact ⟨d', k, ex, hk, h1, h2, hm, exec_frameM ex (by decide)⟩


theorem rcS_exec {n ee se δ : ℕ}
    (hK : Kst n li d) (h50 : d.nreg 215050 = ee) (h71 : d.nreg 215071 = δ)
    (h48 : d.nreg 215048 = se) (hee : ee < n) (hse : se < n) (hδ : δ ≤ 1) (hW : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W rcS d d' k ∧ k ≤ 7 ∧ d'.nreg 215073 = (ee + δ + n - 1 - se) % n ∧
      d'.nmem = d.nmem ∧ FrameM (fun q => decide (q = 215073)) d d' := by
  obtain ⟨d', k, ex, hk, h1, hm⟩ : ∃ d' k, Exec P W rcS d d' k ∧ k ≤ 7 ∧
      d'.nreg 215073 = (ee + δ + n - 1 - se) % n ∧ d'.nmem = d.nmem := by
    have hm := mod_once (v := ee + δ + n - 1 - se) (n := n) (by omega)
    unfold rcS
    refine spec_seq ?_
    exec_block
    · omega
    · config_simp; rw [h50, h71, hK.nn]; omega
    by_cases hv : ee + δ + n - 1 - se < n
    · refine spec_ifLtN_true (by config_simp; rw [h50, h71, hK.nn, hK.one, h48]; exact hv) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, rfl⟩
      config_simp; simp only [h50, h71, hK.nn, hK.one, h48, hm, hv, ↓reduceIte]
    · refine spec_ifLtN_false (by config_simp; rw [h50, h71, hK.nn, hK.one, h48]; exact hv) ?_
      exec_block
      refine ⟨by omega, ?_, rfl⟩
      config_simp; simp only [h50, h71, hK.nn, hK.one, h48, hm, hv, ↓reduceIte]
  exact ⟨d', k, ex, hk, h1, hm, exec_frameM ex (by decide)⟩

theorem rsS_exec {n se rc : ℕ}
    (hK : Kst n li d) (h48 : d.nreg 215048 = se) (h73 : d.nreg 215073 = rc) (hse : se < n)
    (hrc : rc < n) (hW : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W rsS d d' k ∧ k ≤ 9 ∧
      d'.nreg 215074 = (if li then (se + 1) % n else n - 1 - (se + rc) % n) ∧
      d'.nmem = d.nmem ∧ FrameM (fun q => decide (q = 215074) || decide (q = 215076)) d d' := by
  obtain ⟨d', k, ex, hk, h1, hm⟩ : ∃ d' k, Exec P W rsS d d' k ∧ k ≤ 9 ∧
      d'.nreg 215074 = (if li then (se + 1) % n else n - 1 - (se + rc) % n) ∧ d'.nmem = d.nmem := by
    unfold rsS
    cases li with
    | true =>
      refine spec_ifLtN_true (by ram_grind) ?_
      refine spec_seq ?_
      exec_block
      · ram_grind
      by_cases hv : se + 1 < n
      · refine spec_ifLtN_true (by config_simp; rw [h48, hK.one, hK.nn]; exact hv) ?_
        refine spec_skip ‹_› ⟨by omega, ?_, rfl⟩
        config_simp; simp only [h48, hK.one, ↓reduceIte, Nat.mod_eq_of_lt hv]
      · refine spec_ifLtN_false (by config_simp; rw [h48, hK.one, hK.nn]; exact hv) ?_
        exec_block
        · omega
        refine ⟨by omega, ?_, rfl⟩
        config_simp; simp only [↓reduceIte, show se + 1 = n by omega, Nat.mod_self]
    | false =>
      have hm := mod_once (v := se + rc) (n := n) (by omega)
      refine spec_ifLtN_false (by ram_grind) ?_
      refine spec_seq ?_
      exec_block
      · omega
      refine spec_seq ?_
      by_cases hv : se + rc < n
      · refine spec_ifLtN_true (by config_simp; rw [h48, h73, hK.nn]; exact hv) ?_
        refine spec_skip ‹_› ?_
        exec_block
        refine ⟨by omega, ?_, rfl⟩
        config_simp; simp only [h48, h73, hK.nn, hK.one, Bool.false_eq_true, ↓reduceIte, hm, hv]
      · refine spec_ifLtN_false (by config_simp; rw [h48, h73, hK.nn]; exact hv) ?_
        exec_block
        refine ⟨by omega, ?_, rfl⟩
        config_simp; simp only [h48, h73, hK.nn, hK.one, Bool.false_eq_true, ↓reduceIte, hm, hv]
  exact ⟨d', k, ex, hk, h1, hm, exec_frameM ex (by decide)⟩



end

theorem Kst.frame {n : ℕ} {li : Bool} {d d' : Config} (h : Kst n li d) {B : ℕ → Bool}
    (hf : FrameM B d d')
    (hB : B 215002 = false ∧ B 215020 = false ∧ B 215021 = false ∧ B 215022 = false ∧
      B 215023 = false ∧ B 215024 = false) : Kst n li d' :=
  by ram_grind

theorem Buf.frame {n T : ℕ} {xs : List HostItem} {d d' : Config} (h : Buf n T xs d)
    {B : ℕ → Bool} (hf : FrameM B d d')
    (hB : B 215040 = false ∧ B 215011 = false ∧ B 215012 = false) (hm : d'.nmem = d.nmem) :
    Buf n T xs d' :=
  ⟨hm ▸ h.1, (hf.1 _ hB.1).trans h.2.1, (hf.1 _ hB.2.1).trans h.2.2.1,
    (hf.1 _ hB.2.2).trans h.2.2.2⟩

theorem wrRun_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n a rc T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (h73 : d.nreg 215073 = rc) (h74 : d.nreg 215074 = a)
    (hrc : 1 ≤ rc) (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W)
    (hW2 : ptsLen n xs + rc ≤ W) :
    ∃ d' k, Exec P W wrRun d d' k ∧ k = 9 ∧ Buf n T (xs ++ [.run a (rc - 1)]) d' ∧
      (∀ x, x < T + 3 * xs.length → d'.nmem x = d.nmem x) ∧
      FrameM (fun q => decide (q = 215011) || decide (q = 215012) || decide (q = 215040) ||
        decide (q = 215069) || decide (q = 215075)) d d' := by
  obtain ⟨hI, h40, h11, h12⟩ := hB
  obtain ⟨d', k, ex, hk, hm', p40, p11, p12⟩ : ∃ d' k, Exec P W wrRun d d' k ∧ k = 9 ∧
      d'.nmem = wr3 d.nmem (T + 3 * xs.length) 0 a (rc - 1) ∧
      d'.nreg 215040 = T + 3 * xs.length + 3 ∧ d'.nreg 215011 = xs.length + 1 ∧
      d'.nreg 215012 = ptsLen n xs + rc := by
    unfold wrRun
    exec_block
    all_goals
      try (config_simp; (try simp only [hK.one, hK.three, hK.zero, h40, h11, h12, h73, h74]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp only [hK.one, hK.three, hK.zero, h40, h11, h12, h73, h74]
    rw [show T + 3 * xs.length + 1 + 1 = T + 3 * xs.length + 2 by omega]; rfl
  refine ⟨d', k, ex, hk, ⟨?_, ?_, ?_, ?_⟩, fun x hx => ?_, exec_frameM ex (by decide)⟩
  · rw [hm']; exact hI.snoc (.run a (rc - 1))
  · rw [p40, List.length_append, List.length_singleton]; ring
  · rw [p11, List.length_append, List.length_singleton]
  · rw [p12, ptsLen_append, ptsLen_run]; omega
  · rw [hm', wr3_lt hx]

theorem runItems_of_ne {li : Bool} {n : ℕ} {s e : WPos} (h : runCnt li n s e ≠ 0) :
    runItems li n s e = [.run (if li then (s.edge + 1) % n
      else n - 1 - (s.edge + runCnt li n s e) % n) (runCnt li n s e - 1)] := by
  grind [runItems]

theorem runCnt_eq (li : Bool) (n : ℕ) (s e : WPos) :
    runCnt li n s e = (e.edge + (if e.hgt - 1 = ivB li n e.edge then 0 else 1) + n - 1 - s.edge) % n := by
  unfold runCnt atVtx; simp_all

theorem runS_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n T : ℕ} {s e : WPos}
    {xs : List HostItem} (hK : Kst n li d) (h48 : d.nreg 215048 = s.edge)
    (h50 : d.nreg 215050 = e.edge) (h51 : d.nreg 215051 = e.hgt) (hs : s.edge < n)
    (he : e.edge < n) (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W)
    (hW2 : ptsLen n xs + n ≤ W) (hW3 : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W runS d d' k ∧ k ≤ 45 ∧ Buf n T (xs ++ runItems li n s e) d' ∧
      d'.nreg 215072 = (if atVtx li n e then (e.edge + n - 1) % n else e.edge) ∧
      (∀ a, a < T + 3 * xs.length → d'.nmem a = d.nmem a) ∧ FrameM Brun d d' := by
  have hn : 0 < n := by omega
  obtain ⟨d₁, k₁, e₁, hk₁, v70, m₁, f₁⟩ := ivS_exec (P := P) d hw hK h50
  have K₁ := hK.frame f₁ (by decide)
  have B₁ := hB.frame f₁ (by decide) m₁
  obtain ⟨d₂, k₂, e₂, hk₂, v71, v72, m₂, f₂⟩ := atS_exec (P := P) d₁ e₁.wb_right K₁
    (by rw [f₁.1 _ (by decide), h50]) (by rw [f₁.1 _ (by decide), h51]) v70
  have K₂ := K₁.frame f₂ (by decide)
  have B₂ := B₁.frame f₂ (by decide) m₂
  obtain ⟨d₃, k₃, e₃, hk₃, v73, m₃, f₃⟩ := rcS_exec (P := P) d₂ e₂.wb_right K₂
    (by ram_grind) v71
    (by ram_grind) he hs (by grind) hW3
  have K₃ := K₂.frame f₃ (by decide)
  have B₃ := B₂.frame f₃ (by decide) m₃
  rw [← runCnt_eq] at v73
  have hrc := runCnt_lt li hn s e
  have v72' : d₃.nreg 215072 = (if atVtx li n e then (e.edge + n - 1) % n else e.edge) := by
    rw [f₃.1 _ (by decide), v72, mod_prev he]
    unfold atVtx; grind
  have f₁₃ : FrameM Brun d d₃ := ((f₁.mono (fun q hq => by
    simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega)).trans (f₂.mono
    (fun q hq => by simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega))).trans
    (f₃.mono (fun q hq => by simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega))
  have hm₁₃ : d₃.nmem = d.nmem := by grind
  by_cases h0 : runCnt li n s e = 0
  · have hr : runItems li n s e = [] := by grind [runItems]
    refine ⟨d₃, k₁ + (k₂ + (k₃ + (0 + 1))), .seq e₁ (.seq e₂ (.seq e₃
      (.ifLtN_true (by rw [v73, K₃.one, h0]; omega) (.skip e₃.wb_right)))), by omega,
      by grind, v72', fun a _ => by rw [hm₁₃], f₁₃⟩
  · obtain ⟨d₄, k₄, e₄, hk₄, v74, m₄, f₄⟩ := rsS_exec (P := P) d₃ e₃.wb_right K₃
      (by rw [f₃.1 _ (by decide), f₂.1 _ (by decide), f₁.1 _ (by decide), h48]) v73 hs hrc hW3
    have K₄ := K₃.frame f₄ (by decide)
    have B₄ := B₃.frame f₄ (by decide) m₄
    obtain ⟨d₅, k₅, e₅, hk₅, B₅, m₅, f₅⟩ := wrRun_exec (P := P) d₄ e₄.wb_right K₄
      (by rw [f₄.1 _ (by decide), v73]) v74 (by omega) B₄ hW1 (by omega)
    refine ⟨d₅, k₁ + (k₂ + (k₃ + ((k₄ + k₅) + 2))), .seq e₁ (.seq e₂ (.seq e₃
      (.ifLtN_false (by rw [v73, K₃.one]; omega) (.seq e₄ e₅)))), by omega, ?_, ?_,
      fun a ha => ?_, ?_⟩
    · rw [runItems_of_ne h0]; exact B₅
    · rw [f₅.1 _ (by decide), f₄.1 _ (by decide), v72']
    · grind
    · exact (f₁₃.trans (f₄.mono (fun q hq => by
        simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega))).trans
        (f₅.mono (fun q hq => by simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega))

end exec

end

end DrvH

end Chazelle.Core
