module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFBuildPassRam

/-!
# WP-C (BuildNF), RAM part 15: counting the arcs and exit chords of the regions

Three arrays of `R` words at `CA` (arc counts), `CA + R` (chord counts), `CA + 2R` (largest arc
weight) — `regMem` — are filled by:

* `zeroLoop`: all zero;
* `arcCntLoop`: for each arc `j < A` (region `key j = AT[5 j]`, weight `WT[j]`), count it and take
  the maximum of the weights (`cntF`, `wmaxF`);
* `chCntLoop`: for each chord `i < K` (regions `u i = CT[5 i + 3]`, `v i = CT[5 i + 4]`), count it
  once in each of its regions (`cnt2F`).

Registers: `r43200 = R`, `r43201` the counter, `r43202 … r43209` scratch, `r44008 = CA`,
`r44002 = AT`, `r44007 = WT`, `r44001 = CT`, `r43102 = A`, `r43002 = K`, `r43010 = 0`,
`r43011 = 1`, `r43013 = 3`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## The counts -/

/-- The items below `n` with key `r`. -/
def lstF (key : ℕ → ℕ) (n r : ℕ) : List ℕ := (List.range n).filter fun j => key j = r

/-- Their number. -/
def cntF (key : ℕ → ℕ) (n r : ℕ) : ℕ := (lstF key n r).length

/-- The largest weight among them. -/
def wmaxF (key w : ℕ → ℕ) (n r : ℕ) : ℕ := ((lstF key n r).map w).foldr max 0

section
variable (u v : ℕ → ℕ) (n r : ℕ)
include u v n r
/-- The chords below `n` with a side `r`. -/
def lst2F : List ℕ := (List.range n).filter fun i => u i = r ∨ v i = r

/-- Their number. -/
def cnt2F : ℕ := (lst2F u v n r).length


end

theorem lstF_succ (key : ℕ → ℕ) (n r : ℕ) :
    lstF key (n + 1) r = lstF key n r ++ (if key n = r then [n] else []) := by
  unfold lstF
  rw [List.range_succ, List.filter_append]
  by_cases h : key n = r <;> simp [h]

theorem lst2F_succ (u v : ℕ → ℕ) (n r : ℕ) :
    lst2F u v (n + 1) r = lst2F u v n r ++ (if u n = r ∨ v n = r then [n] else []) := by
  aesop (add simp [lst2F, List.range_succ, List.filter_append]) (add safe (by omega))

theorem cntF_succ (key : ℕ → ℕ) (n r : ℕ) :
    cntF key (n + 1) r = cntF key n r + (if key n = r then 1 else 0) := by
  core_grind [lstF_succ]

theorem cnt2F_succ (u v : ℕ → ℕ) (n r : ℕ) :
    cnt2F u v (n + 1) r = cnt2F u v n r + (if u n = r ∨ v n = r then 1 else 0) := by
  core_grind [lst2F_succ]

theorem foldr_max_append (l : List ℕ) (x : ℕ) :
    (l ++ [x]).foldr max 0 = max (l.foldr max 0) x := by
  induction l with
  | nil => simp
  | cons y l ih => simp_all

theorem wmaxF_succ (key w : ℕ → ℕ) (n r : ℕ) :
    wmaxF key w (n + 1) r = if key n = r then max (wmaxF key w n r) (w n) else wmaxF key w n r := by
  core_grind [lstF_succ, List.map_append, List.map_singleton, foldr_max_append]

/-! ## The three arrays -/

/-- The memory with the three arrays at `CA`. -/
def regMem (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) (a : ℕ) : ℕ :=
  if CA ≤ a ∧ a < CA + R then fA (a - CA)
  else if CA + R ≤ a ∧ a < CA + 2 * R then fC (a - (CA + R))
  else if CA + 2 * R ≤ a ∧ a < CA + 3 * R then fW (a - (CA + 2 * R)) else m₀ a

section
variable (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r v : ℕ} (hr : r < R)
include hr
theorem regMem_A :
    upd (regMem m₀ CA R fA fC fW) (CA + r) v = regMem m₀ CA R (Function.update fA r v) fC fW := by
  grind [upd_apply, regMem, Function.update_apply]

theorem regMem_C :
    upd (regMem m₀ CA R fA fC fW) (CA + R + r) v =
      regMem m₀ CA R fA (Function.update fC r v) fW := by
  grind [upd_apply, regMem, Function.update_apply]

theorem regMem_W :
    upd (regMem m₀ CA R fA fC fW) (CA + 2 * R + r) v =
      regMem m₀ CA R fA fC (Function.update fW r v) := by
  grind [upd_apply, regMem, Function.update_apply]


end

section
variable (m₀ : ℕ → ℕ) (CA R : ℕ) (fA fC fW : ℕ → ℕ) {r : ℕ} (hr : r < R)
include hr
theorem regMem_rdA :
    regMem m₀ CA R fA fC fW (CA + r) = fA r := by
  unfold regMem
  split_ifs <;> first | (congr 1; omega)

theorem regMem_rdC :
    regMem m₀ CA R fA fC fW (CA + R + r) = fC r := by
  grind [regMem]

theorem regMem_rdW :
    regMem m₀ CA R fA fC fW (CA + 2 * R + r) = fW r := by
  grind [regMem]


end

section
variable (m₀ : ℕ → ℕ) (CA R : ℕ)
theorem regMem_out (fA fC fW : ℕ → ℕ) {a : ℕ}
    (ha : a < CA ∨ CA + 3 * R ≤ a) : regMem m₀ CA R fA fC fW a = m₀ a := by
  grind [regMem]

theorem regMem_congr {fA fC fW gA gC gW : ℕ → ℕ}
    (hA : ∀ r, r < R → fA r = gA r) (hC : ∀ r, r < R → fC r = gC r)
    (hW : ∀ r, r < R → fW r = gW r) : regMem m₀ CA R fA fC fW = regMem m₀ CA R gA gC gW := by
  grind [regMem]

theorem regMem_self :
    regMem m₀ CA R (fun r => m₀ (CA + r)) (fun r => m₀ (CA + R + r)) (fun r => m₀ (CA + 2 * R + r))
      = m₀ := by
  aesop (add simp [regMem]) (add safe (by omega))

/-! ## The programs -/


end

/-- Zero the three arrays. -/
def zeroLoop : Stmt :=
  .whileLtN 43201 43200 (block [.addN 43202 44008 43201, .storeN 43202 43010,
    .addN 43202 43202 43200, .storeN 43202 43010, .addN 43202 43202 43200, .storeN 43202 43010,
    .addN 43201 43201 43011])

/-- Count the arcs by region and take the largest weight. -/
def arcCntLoop : Stmt :=
  .whileLtN 43201 43102
    (.seq (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
        .addN 43202 43202 44002, .loadN 43203 43202,
        .addN 43204 44008 43203, .loadN 43205 43204, .addN 43205 43205 43011,
        .storeN 43204 43205,
        .addN 43206 44007 43201, .loadN 43207 43206,
        .addN 43208 44008 43200, .addN 43208 43208 43200, .addN 43208 43208 43203,
        .loadN 43209 43208])
      (.seq (.ifLtN 43209 43207 (.instr (.storeN 43208 43207)) .skip)
        (.instr (.addN 43201 43201 43011))))

/-- One increment of a chord count. -/
def incV : Stmt :=
  block [.addN 43207 44008 43200, .addN 43207 43207 43204, .loadN 43208 43207,
    .addN 43208 43208 43011, .storeN 43207 43208]

/-- Count the chords by side region. -/
def chCntLoop : Stmt :=
  .whileLtN 43201 43002
    (.seq (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
        .addN 43202 43202 44001, .addN 43202 43202 43013, .loadN 43203 43202,
        .addN 43202 43202 43011, .loadN 43204 43202,
        .addN 43205 44008 43200, .addN 43205 43205 43203, .loadN 43206 43205,
        .addN 43206 43206 43011, .storeN 43205 43206])
      (.seq (.ifLtN 43203 43204 incV (.ifLtN 43204 43203 incV .skip))
        (.instr (.addN 43201 43201 43011))))


section
variable (i : ℕ) (f : ℕ → ℕ)
include i f
/-- `f` with its first `i` values zeroed. -/
def zU (r : ℕ) : ℕ := if r < i then 0 else f r

theorem zU_succ : Function.update (zU i f) i 0 = zU (i + 1) f := by
  core_grind


end

section exec

variable {P : Polygon} {W : ℕ}

/-- **Zeroing the arrays.** -/
theorem zeroLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R : ℕ}
    {fA fC fW : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h0 : d.nreg 43010 = 0)
    (h1 : d.nreg 43011 = 1) (hi : d.nreg 43201 = 0) (hRW : CA + 3 * R ≤ W)
    (hm : d.nmem = regMem m₀ CA R fA fC fW) :
    ∃ d' k, Exec P W zeroLoop d d' k ∧ k ≤ 9 * R + 2 ∧ WordsBounded W d' ∧
      FrameM (fun r => decide (43201 ≤ r ∧ r < 43210)) d d' ∧
      d'.nmem = regMem m₀ CA R (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  obtain ⟨d', k, e, ⟨hw', i, hi', hiR, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P)
    (W := W) (a := 43201) (b := 43200) (body := block [.addN 43202 44008 43201, .storeN 43202 43010,
      .addN 43202 43202 43200, .storeN 43202 43010, .addN 43202 43202 43200, .storeN 43202 43010,
      .addN 43201 43201 43011])
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ R ∧
      FrameM (fun r => decide (43201 ≤ r ∧ r < 43210)) d e ∧
      e.nmem = regMem m₀ CA R (zU i fA) (zU i fC) (zU i fW))
    (fun e => 9 * (R - e.nreg 43201)) (fun e he => he.1)
    (fun e ⟨hwe, i, hie, hiR, hfe, hme⟩ htest => by
      have r1 : e.nreg 44008 = CA := by rw [hfe.1 _ (by decide), hCA]
      have r2 : e.nreg 43200 = R := by rw [hfe.1 _ (by decide), hR]
      have r3 : e.nreg 43010 = 0 := by rw [hfe.1 _ (by decide), h0]
      have r4 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      rw [hie, r2] at htest
      have X : ∃ e' k, Exec P W (block [.addN 43202 44008 43201, .storeN 43202 43010,
          .addN 43202 43202 43200, .storeN 43202 43010, .addN 43202 43202 43200,
          .storeN 43202 43010, .addN 43201 43201 43011]) e e' k ∧ k = 7 ∧
          e'.nreg 43201 = i + 1 ∧
          e'.nmem = upd (upd (upd e.nmem (CA + i) 0) (CA + R + i) 0) (CA + 2 * R + i) 0 := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r3, r4, hie];
             omega)
          | skip
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp
        · rw [hie, r4]
        · rw [r1, r2, r3, hie, show CA + i + R = CA + R + i by omega,
            show CA + R + i + R = CA + 2 * R + i by omega]
      obtain ⟨e', k, x, hk, hi', hm'⟩ := X
      refine ⟨e', k, x, ⟨x.wb_right, i + 1, hi', by omega,
        hfe.trans (exec_frameM x (by decide)), ?_⟩, ?_⟩
      · rw [hm', hme, regMem_A _ _ _ _ _ _ (by omega), regMem_C _ _ _ _ _ _ (by omega),
          regMem_W _ _ _ _ _ _ (by omega), zU_succ, zU_succ, zU_succ]
      omega)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      aesop⟩
  have hiR' : i = R := by
    rw [hi', hf.1 _ (by decide), hR] at htest; omega
  subst hiR'
  refine ⟨d', k, e, by omega, hw', hf, ?_⟩
  rw [hm']
  exact regMem_congr _ _ _ (fun r hr => by grind [zU]) (fun r hr => by grind [zU])
    (fun r hr => by grind [zU])

end exec

theorem cntF_update (key : ℕ → ℕ) (j : ℕ) :
    Function.update (cntF key j) (key j) (cntF key j (key j) + 1) = cntF key (j + 1) := by
  funext r
  by_cases h : r = key j
  all_goals (aesop (add simp [Function.update_self, cntF_succ, Nat.add_zero]) (add safe (by omega)))

section
variable (key w : ℕ → ℕ) (j : ℕ)
theorem wmaxF_update (hlt : wmaxF key w j (key j) < w j) :
    Function.update (wmaxF key w j) (key j) (w j) = wmaxF key w (j + 1) := by
  grind [Function.update_self, wmaxF_succ]

theorem wmaxF_same (hge : ¬ wmaxF key w j (key j) < w j) :
    wmaxF key w j = wmaxF key w (j + 1) := by
  funext r
  rw [wmaxF_succ]
  split_ifs with h1
  · subst h1; omega
  · rfl


end

section exec

variable {P : Polygon} {W : ℕ}

/-- **Counting the arcs by region**, with the largest weight. -/
theorem arcCntLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R A AT WT : ℕ}
    {fC : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1)
    (hi : d.nreg 43201 = 0) (hA : d.nreg 43102 = A) (hAT : d.nreg 44002 = AT)
    (hWT : d.nreg 44007 = WT) (hRW : CA + 3 * R ≤ W) (hATC : AT + 5 * A ≤ CA) (hWTC : WT + A ≤ CA)
    (hkey : ∀ j, j < A → m₀ (AT + 5 * j) < R)
    (hm : d.nmem = regMem m₀ CA R (fun _ => 0) fC (fun _ => 0)) :
    ∃ d' k, Exec P W arcCntLoop d d' k ∧ k ≤ 21 * A + 2 ∧ WordsBounded W d' ∧
      FrameM (fun r => decide (43201 ≤ r ∧ r < 43210)) d d' ∧
      d'.nmem = regMem m₀ CA R (cntF (fun j => m₀ (AT + 5 * j)) A) fC
        (wmaxF (fun j => m₀ (AT + 5 * j)) (fun j => m₀ (WT + j)) A) := by
  obtain ⟨key, hkeydef⟩ : ∃ f : ℕ → ℕ, f = fun j => m₀ (AT + 5 * j) := ⟨_, rfl⟩
  obtain ⟨wt, hwdef⟩ : ∃ f : ℕ → ℕ, f = fun j => m₀ (WT + j) := ⟨_, rfl⟩
  rw [← hkeydef, ← hwdef]
  have hkey' : ∀ j, j < A → key j < R := fun j hj => by simp_all
  obtain ⟨d', k, e, ⟨hw', i, hi', hiA, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P)
    (W := W) (a := 43201) (b := 43102) (body := _)
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ A ∧
      FrameM (fun r => decide (43201 ≤ r ∧ r < 43210)) d e ∧
      e.nmem = regMem m₀ CA R (cntF key i) fC (wmaxF key wt i))
    (fun e => 21 * (A - e.nreg 43201)) (fun e he => he.1)
    (fun e ⟨hwe, j, hje, hjA, hfe, hme⟩ htest => by
      have r1 : e.nreg 44008 = CA := by rw [hfe.1 _ (by decide), hCA]
      have r2 : e.nreg 43200 = R := by rw [hfe.1 _ (by decide), hR]
      have r4 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      have r5 : e.nreg 44002 = AT := by rw [hfe.1 _ (by decide), hAT]
      have r6 : e.nreg 44007 = WT := by rw [hfe.1 _ (by decide), hWT]
      have r7 : e.nreg 43102 = A := by rw [hfe.1 _ (by decide), hA]
      rw [hje, r7] at htest
      have hkj := hkey' j htest
      have mk : e.nmem (AT + 5 * j) = key j := by
        rw [hme, regMem_out _ _ _ _ _ _ (by omega), hkeydef]
      have mw : e.nmem (WT + j) = wt j := by
        rw [hme, regMem_out _ _ _ _ _ _ (by omega), hwdef]
      have mc : e.nmem (CA + key j) = cntF key j (key j) := by
        rw [hme, regMem_rdA _ _ _ _ _ _ hkj]
      have hcW : cntF key j (key j) + 1 ≤ W := by
        grind [cntF, lstF]
      obtain ⟨e₁, k₁, x₁, hk₁, v7, v8, v9, v1, m₁, g₁⟩ : ∃ e₁ k₁, Exec P W
          (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
            .addN 43202 43202 44002, .loadN 43203 43202,
            .addN 43204 44008 43203, .loadN 43205 43204, .addN 43205 43205 43011,
            .storeN 43204 43205,
            .addN 43206 44007 43201, .loadN 43207 43206,
            .addN 43208 44008 43200, .addN 43208 43208 43200, .addN 43208 43208 43203,
            .loadN 43209 43208]) e e₁ k₁ ∧ k₁ = 15 ∧
          e₁.nreg 43207 = wt j ∧ e₁.nreg 43208 = CA + 2 * R + key j ∧
          e₁.nreg 43209 = wmaxF key wt j (key j) ∧ e₁.nreg 43201 = j ∧
          e₁.nmem = regMem m₀ CA R (cntF key (j + 1)) fC (wmaxF key wt j) ∧
          (∀ r, (r < 43202 ∨ 43209 < r) → e₁.nreg r = e.nreg r) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r4, r5,
              r6, hje, show j + j + (j + j) + j + AT = AT + 5 * j by omega, mk, mc]; omega)
          | skip
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> config_simp
        · rw [r1, r5, r6, r4, hje, show j + j + (j + j) + j + AT = AT + 5 * j by omega, mk,
            upd_other _ _ _ (by omega), mw]
        · grind
        · rw [r1, r2, hje, r5, r4, show j + j + (j + j) + j + AT = AT + 5 * j by omega, mk, mc,
            hme, regMem_A _ _ _ _ _ _ hkj, show CA + R + R + key j = CA + 2 * R + key j by omega,
            regMem_rdW _ _ _ _ _ _ hkj]
        · rw [hje]
        · rw [r1, r5, r4, hje, show j + j + (j + j) + j + AT = AT + 5 * j by omega, mk, mc,
            hme, regMem_A _ _ _ _ _ _ hkj, cntF_update]
        grind [upd_other]
      have w₁ := x₁.wb_right
      -- the maximum
      obtain ⟨e₂, k₂, x₂, hk₂, v1', m₂⟩ : ∃ e₂ k₂, Exec P W
          (.ifLtN 43209 43207 (.instr (.storeN 43208 43207)) .skip) e₁ e₂ k₂ ∧ k₂ ≤ 2 ∧
          e₂.nreg = e₁.nreg ∧
          e₂.nmem = regMem m₀ CA R (cntF key (j + 1)) fC (wmaxF key wt (j + 1)) := by
        by_cases hlt : wmaxF key wt j (key j) < wt j
        · refine spec_ifLtN_true (by omega)
            (spec_instr (Exec.storeN w₁ _ _) fun _ => ⟨by omega, rfl, ?_⟩)
          simp only
          rw [v8, v7, m₁, regMem_W _ _ _ _ _ _ hkj, wmaxF_update _ _ _ hlt]
        · refine spec_ifLtN_false (by omega) (spec_skip w₁ ⟨by omega, rfl, ?_⟩)
          rw [m₁, wmaxF_same _ _ _ hlt]
      have w₂ := x₂.wb_right
      have e1011 : e₂.nreg 43011 = 1 := by simp_all
      have e1201 : e₂.nreg 43201 = j := by rw [v1', v1]
      have x₃ := Exec.addN (P := P) w₂ 43201 43201 43011 (by omega)
      have X := Exec.seq x₁ (Exec.seq x₂ x₃)
      refine ⟨_, _, X, ⟨X.wb_right, j + 1, by simp [e1011, e1201], by omega,
        hfe.trans (exec_frameM X (by decide)), by omega⟩, ?_⟩
      grind [upd_same])
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      rw [hm]; exact regMem_congr _ _ _ (fun r _ => by simp [cntF, lstF]) (fun _ _ => rfl)
        (fun r _ => by simp [wmaxF, lstF])⟩
  have hiA' : i = A := by
    rw [hi', hf.1 _ (by decide), hA] at htest; omega
  subst hiA'
  exact ⟨d', k, e, by omega, hw', hf, hm'⟩

end exec

section
variable (u v : ℕ → ℕ) (i : ℕ)
theorem cnt2_update_eq (h : u i = v i) :
    Function.update (cnt2F u v i) (u i) (cnt2F u v i (u i) + 1) = cnt2F u v (i + 1) := by
  funext r
  by_cases hr : r = u i
  all_goals (aesop (add simp [Function.update_self, cnt2F_succ, Nat.add_zero]) (add safe (by omega)))

theorem cnt2_update_ne (_h : u i ≠ v i) :
    Function.update (Function.update (cnt2F u v i) (u i) (cnt2F u v i (u i) + 1)) (v i)
      (cnt2F u v i (v i) + 1) = cnt2F u v (i + 1) := by
  funext r
  by_cases hr : r = v i
  · grind [Function.update_self, cnt2F_succ]
  · rw [Function.update_of_ne hr]
    by_cases hr' : r = u i
    all_goals (aesop (add simp [Function.update_self, cnt2F_succ, Nat.add_zero]) (add safe (by omega)))


end

section exec

variable {P : Polygon} {W : ℕ}

theorem incV_exec (e : Config) (hw : WordsBounded W e) {CA R v : ℕ} (hCA : e.nreg 44008 = CA)
    (hR : e.nreg 43200 = R) (hv : e.nreg 43204 = v) (h1 : e.nreg 43011 = 1)
    (hW : CA + R + v ≤ W) (hc : e.nmem (CA + R + v) + 1 ≤ W) :
    ∃ e' k, Exec P W incV e e' k ∧ k = 5 ∧
      e'.nmem = upd e.nmem (CA + R + v) (e.nmem (CA + R + v) + 1) ∧
      (∀ r, (r < 43207 ∨ 43208 < r) → e'.nreg r = e.nreg r) := by
  unfold incV
  exec_block
  · omega
  · simp_all
  · simp_all
  grind [upd_other]

/-- **Counting the chords by side region.** -/
theorem chCntLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R K CT : ℕ}
    {fA fW : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1)
    (h3 : d.nreg 43013 = 3) (hi : d.nreg 43201 = 0) (hK : d.nreg 43002 = K)
    (hCT : d.nreg 44001 = CT) (hRW : CA + 3 * R ≤ W) (hCTC : CT + 5 * K ≤ CA)
    (hu : ∀ i, i < K → m₀ (CT + 5 * i + 3) < R) (hv : ∀ i, i < K → m₀ (CT + 5 * i + 4) < R)
    (hm : d.nmem = regMem m₀ CA R fA (fun _ => 0) fW) :
    ∃ d' k, Exec P W chCntLoop d d' k ∧ k ≤ 26 * K + 2 ∧ WordsBounded W d' ∧
      FrameM (fun r => decide (43201 ≤ r ∧ r < 43210)) d d' ∧
      d'.nmem = regMem m₀ CA R fA
        (cnt2F (fun i => m₀ (CT + 5 * i + 3)) (fun i => m₀ (CT + 5 * i + 4)) K) fW := by
  obtain ⟨u, hudef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₀ (CT + 5 * i + 3) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₀ (CT + 5 * i + 4) := ⟨_, rfl⟩
  rw [← hudef, ← hvdef]
  have hu' : ∀ i, i < K → u i < R := fun i hi => by simp_all
  have hv' : ∀ i, i < K → v i < R := fun i hi => by simp_all
  obtain ⟨d', k, e, ⟨hw', i, hi', hiK, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P)
    (W := W) (a := 43201) (b := 43002) (body := _)
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ K ∧
      FrameM (fun r => decide (43201 ≤ r ∧ r < 43210)) d e ∧
      e.nmem = regMem m₀ CA R fA (cnt2F u v i) fW)
    (fun e => 26 * (K - e.nreg 43201)) (fun e he => he.1)
    (fun e ⟨hwe, j, hje, hjK, hfe, hme⟩ htest => by
      have r1 : e.nreg 44008 = CA := by rw [hfe.1 _ (by decide), hCA]
      have r2 : e.nreg 43200 = R := by rw [hfe.1 _ (by decide), hR]
      have r4 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      have r3 : e.nreg 43013 = 3 := by rw [hfe.1 _ (by decide), h3]
      have r5 : e.nreg 44001 = CT := by rw [hfe.1 _ (by decide), hCT]
      have r7 : e.nreg 43002 = K := by rw [hfe.1 _ (by decide), hK]
      rw [hje, r7] at htest
      have huj := hu' j htest
      have hvj := hv' j htest
      have mu : e.nmem (CT + 5 * j + 3) = u j := by
        rw [hme, regMem_out _ _ _ _ _ _ (by omega), hudef]
      have mv : e.nmem (CT + 5 * j + 4) = v j := by
        rw [hme, regMem_out _ _ _ _ _ _ (by omega), hvdef]
      have mc : e.nmem (CA + R + u j) = cnt2F u v j (u j) := by
        rw [hme, regMem_rdC _ _ _ _ _ _ huj]
      have hcle : ∀ r, cnt2F u v j r ≤ j := fun r => by
        grind [cnt2F, lst2F]
      have hcW : cnt2F u v j (u j) + 1 ≤ W := by grind
      obtain ⟨e₁, k₁, x₁, hk₁, v3, v4, v1, m₁, g₁⟩ : ∃ e₁ k₁, Exec P W
          (block [.addN 43202 43201 43201, .addN 43202 43202 43202, .addN 43202 43202 43201,
            .addN 43202 43202 44001, .addN 43202 43202 43013, .loadN 43203 43202,
            .addN 43202 43202 43011, .loadN 43204 43202,
            .addN 43205 44008 43200, .addN 43205 43205 43203, .loadN 43206 43205,
            .addN 43206 43206 43011, .storeN 43205 43206]) e e₁ k₁ ∧ k₁ = 13 ∧
          e₁.nreg 43203 = u j ∧ e₁.nreg 43204 = v j ∧ e₁.nreg 43201 = j ∧
          e₁.nmem = regMem m₀ CA R fA
            (Function.update (cnt2F u v j) (u j) (cnt2F u v j (u j) + 1)) fW ∧
          (∀ r, (r < 43202 ∨ 43209 < r) → e₁.nreg r = e.nreg r) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r3, r4, r5,
              hje, show j + j + (j + j) + j + CT + 3 = CT + 5 * j + 3 by omega,
              show CT + 5 * j + 3 + 1 = CT + 5 * j + 4 by omega, mu, mv, mc]; omega)
          | skip
        refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> config_simp
        · grind
        · grind
        · rw [hje]
        · rw [r1, r2, r3, r4, r5, hje, show j + j + (j + j) + j + CT + 3 = CT + 5 * j + 3 by omega,
            mu, mc, hme, regMem_C _ _ _ _ _ _ huj]
        grind [upd_other]
      have w₁ := x₁.wb_right
      -- the other side
      obtain ⟨e₂, k₂, x₂, hk₂, g₂, m₂⟩ : ∃ e₂ k₂, Exec P W
          (.ifLtN 43203 43204 incV (.ifLtN 43204 43203 incV .skip)) e₁ e₂ k₂ ∧ k₂ ≤ 9 ∧
          (∀ r, (r < 43207 ∨ 43208 < r) → e₂.nreg r = e₁.nreg r) ∧
          e₂.nmem = regMem m₀ CA R fA (cnt2F u v (j + 1)) fW := by
        have inc : u j ≠ v j → ∃ e₂ k₂, Exec P W incV e₁ e₂ k₂ ∧ k₂ = 5 ∧
            (∀ r, (r < 43207 ∨ 43208 < r) → e₂.nreg r = e₁.nreg r) ∧
            e₂.nmem = regMem m₀ CA R fA (cnt2F u v (j + 1)) fW := fun hne => by
          have hrd : e₁.nmem (CA + R + v j) = cnt2F u v j (v j) := by
            rw [m₁, regMem_rdC _ _ _ _ _ _ hvj, Function.update_of_ne (Ne.symm hne)]
          obtain ⟨e₂, k₂, x₂, hk₂, m₂, g₂⟩ := incV_exec (P := P) e₁ w₁ (CA := CA) (R := R)
            (v := v j) (by grind) (by grind) v4
            (by grind) (by omega) (by grind)
          refine ⟨e₂, k₂, x₂, hk₂, g₂, ?_⟩
          rw [m₂, hrd, m₁, regMem_C _ _ _ _ _ _ hvj, cnt2_update_ne u v j hne]
        by_cases a1 : u j < v j
        · obtain ⟨e₂, k₂, x₂, hk₂, g₂, m₂⟩ := inc (by omega)
          exact ⟨e₂, _, .ifLtN_true (by omega) x₂, by omega, g₂, m₂⟩
        by_cases a2 : v j < u j
        · obtain ⟨e₂, k₂, x₂, hk₂, g₂, m₂⟩ := inc (by omega)
          exact ⟨e₂, _, .ifLtN_false (by omega)
            (.ifLtN_true (by omega) x₂), by omega, g₂, m₂⟩
        · refine ⟨e₁, _, .ifLtN_false (by omega)
            (.ifLtN_false (by omega) (.skip w₁)), by omega, fun _ _ => rfl, ?_⟩
          rw [m₁, cnt2_update_eq u v j (by omega)]
      have w₂ := x₂.wb_right
      have e1011 : e₂.nreg 43011 = 1 := by grind
      have e1201 : e₂.nreg 43201 = j := by grind
      have x₃ := Exec.addN (P := P) w₂ 43201 43201 43011 (by omega)
      have X := Exec.seq x₁ (Exec.seq x₂ x₃)
      refine ⟨_, _, X, ⟨X.wb_right, j + 1, by simp [e1011, e1201], by omega,
        hfe.trans (exec_frameM X (by decide)), by omega⟩, ?_⟩
      grind [upd_same])
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      rw [hm]; exact regMem_congr _ _ _ (fun _ _ => rfl) (fun r _ => by simp [cnt2F, lst2F])
        (fun _ _ => rfl)⟩
  have hiK' : i = K := by
    rw [hi', hf.1 _ (by decide), hK] at htest; omega
  subst hiK'
  exact ⟨d', k, e, by omega, hw', hf, hm'⟩

end exec

end

end BuildRam

end Chazelle.Core
