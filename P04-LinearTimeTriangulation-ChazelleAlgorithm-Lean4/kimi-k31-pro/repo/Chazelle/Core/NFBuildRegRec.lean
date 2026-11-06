module

public import Chazelle.Core.NFBuildRegCnt
public import Chazelle.Core.SortRam
public import Chazelle.RewriteTactics

/-!
# WP-C (BuildNF), RAM part 16: the region records and the fill pointers

With the counts `cA` (arcs), `cC` (chords) and weights `wR` of the regions at `CA`, `CA + R`,
`CA + 2R`, `regRecLoop` writes for each region `r < R` its record at `RT + 5 r`
(`cA r`, `off r`, `cC r`, `off r + cA r`, `wR r`, where `off r = Σ_{r' < r} (cA r' + cC r')`) and
the fill pointers `FA[r] = off r`, `FC[r] = off r + cA r` (`FC = FA + R`).

Registers: `r43201` the region, `r43210` the running offset, `r43211 … r43217` scratch,
`r44003 = RT`, `r44011 = FA`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The offset of region `r` in the list table. -/
def offF (cA cC : ℕ → ℕ) (r : ℕ) : ℕ := ((List.range r).map fun r' => cA r' + cC r').sum

theorem offF_succ (cA cC : ℕ → ℕ) (r : ℕ) : offF cA cC (r + 1) = offF cA cC r + cA r + cC r := by
  unfold offF
  rw [List.range_succ, List.map_append, List.sum_append]
  simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  try omega

theorem offF_mono (cA cC : ℕ → ℕ) {r r' : ℕ} (h : r ≤ r') : offF cA cC r ≤ offF cA cC r' := by
  induction r' with
  | zero => rw [Nat.le_zero.1 h]
  | succ n ih =>
    rcases Nat.lt_or_ge r (n + 1) with h' | h'
    · rw [offF_succ]; have := ih (by omega); omega
    · rw [show r = n + 1 by omega]

/-- The word `q` of the region table. -/
def rtv (cA cC wR : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q % 5 = 0 then cA (q / 5) else if q % 5 = 1 then offF cA cC (q / 5)
  else if q % 5 = 2 then cC (q / 5) else if q % 5 = 3 then offF cA cC (q / 5) + cA (q / 5)
  else wR (q / 5)

/-- The memory after the records of the first `n` regions. -/
def recRMem (m₁ : ℕ → ℕ) (RT FA R : ℕ) (cA cC wR : ℕ → ℕ) (n a : ℕ) : ℕ :=
  if RT ≤ a ∧ a < RT + 5 * n then rtv cA cC wR (a - RT)
  else if FA ≤ a ∧ a < FA + n then offF cA cC (a - FA)
  else if FA + R ≤ a ∧ a < FA + R + n then offF cA cC (a - (FA + R)) + cA (a - (FA + R))
  else m₁ a

theorem rtv_eq (cA cC wR : ℕ → ℕ) (r f : ℕ) (hf : f < 5) :
    rtv cA cC wR (5 * r + f) = if f = 0 then cA r else if f = 1 then offF cA cC r
      else if f = 2 then cC r else if f = 3 then offF cA cC r + cA r else wR r := by
  unfold rtv
  rw [show (5 * r + f) % 5 = f by omega, show (5 * r + f) / 5 = r by omega]

/-- The memory step of the region records. -/
theorem recR_step (m₁ : ℕ → ℕ) {RT FA R : ℕ} (cA cC wR : ℕ → ℕ) {n : ℕ} (hn : n < R)
    (hlay : RT + 5 * R ≤ FA ∨ FA + 2 * R ≤ RT) (a : ℕ) :
    upd (upd (upd (upd (upd (upd (upd (recRMem m₁ RT FA R cA cC wR n) (RT + 5 * n) (cA n))
      (RT + 5 * n + 1) (offF cA cC n)) (RT + 5 * n + 2) (cC n))
      (RT + 5 * n + 3) (offF cA cC n + cA n)) (RT + 5 * n + 4) (wR n))
      (FA + n) (offF cA cC n)) (FA + R + n) (offF cA cC n + cA n) a =
      recRMem m₁ RT FA R cA cC wR (n + 1) a := by
  simp [upd_apply]
  unfold recRMem
  have hr : a < RT ∨ (RT ≤ a ∧ a < RT + 5 * n) ∨ (∃ f, f < 5 ∧ a = RT + 5 * n + f) ∨
      (RT + 5 * n + 5 ≤ a ∧ a < RT + 5 * R) ∨ RT + 5 * R ≤ a := by
    by_cases h : RT + 5 * n ≤ a ∧ a < RT + 5 * n + 5
    · exact Or.inr (Or.inr (Or.inl ⟨a - (RT + 5 * n), by omega, by omega⟩))
    · omega
  have hq : a < FA ∨ (FA ≤ a ∧ a < FA + n) ∨ a = FA + n ∨ (FA + n + 1 ≤ a ∧ a < FA + R) ∨
      (FA + R ≤ a ∧ a < FA + R + n) ∨ a = FA + R + n ∨ FA + R + n + 1 ≤ a := by omega
  rcases hr with h | h | ⟨f, hf, rfl⟩ | h | h
  · rcases hq with h' | h' | rfl | h' | h' | rfl | h' <;> ifs_omega <;>
      first | rfl | omega | (congr 1; omega) | (congr 1 <;> congr 1 <;> omega)
  · ifs_omega
  · interval_cases f <;> ifs_omega <;>
      first
        | rfl
        | (rwr [show RT + 5 * n + 0 - RT = 5 * n + 0 by omega, rtv_eq _ _ _ _ _ (by norm_num)])
        | (rwr [show RT + 5 * n + 1 - RT = 5 * n + 1 by omega, rtv_eq _ _ _ _ _ (by norm_num)])
        | (rwr [show RT + 5 * n + 2 - RT = 5 * n + 2 by omega, rtv_eq _ _ _ _ _ (by norm_num)])
        | (rwr [show RT + 5 * n + 3 - RT = 5 * n + 3 by omega, rtv_eq _ _ _ _ _ (by norm_num)])
        | (rwr [show RT + 5 * n + 4 - RT = 5 * n + 4 by omega, rtv_eq _ _ _ _ _ (by norm_num)])
  · rcases hq with h' | h' | rfl | h' | h' | rfl | h' <;> ifs_omega <;>
      first | rfl | omega
  · rcases hq with h' | h' | rfl | h' | h' | rfl | h' <;> ifs_omega <;>
      first | rfl | omega | (congr 1; omega) | (congr 1 <;> congr 1 <;> omega)

/-- `recR_step` with the addresses and values given by equations. -/
theorem recR_step' (m₁ : ℕ → ℕ) {RT FA R : ℕ} (cA cC wR : ℕ → ℕ) {n : ℕ} (hn : n < R)
    (hlay : RT + 5 * R ≤ FA ∨ FA + 2 * R ≤ RT) {M : ℕ → ℕ}
    (hM : M = recRMem m₁ RT FA R cA cC wR n)
    {a0 a1 a2 a3 a4 a5 a6 v0 v1 v2 v3 v4 v5 v6 : ℕ}
    (e0 : a0 = RT + 5 * n) (e1 : a1 = RT + 5 * n + 1) (e2 : a2 = RT + 5 * n + 2)
    (e3 : a3 = RT + 5 * n + 3) (e4 : a4 = RT + 5 * n + 4) (e5 : a5 = FA + n)
    (e6 : a6 = FA + R + n) (w0 : v0 = cA n) (w1 : v1 = offF cA cC n) (w2 : v2 = cC n)
    (w3 : v3 = offF cA cC n + cA n) (w4 : v4 = wR n) (w5 : v5 = offF cA cC n)
    (w6 : v6 = offF cA cC n + cA n) :
    upd (upd (upd (upd (upd (upd (upd M a0 v0) a1 v1) a2 v2) a3 v3) a4 v4) a5 v5) a6 v6 =
      recRMem m₁ RT FA R cA cC wR (n + 1) := by
  subst a0 a1 a2 a3 a4 a5 a6 v0 v1 v2 v3 v4 v5 v6 M
  funext a
  exact recR_step m₁ cA cC wR hn hlay a

/-- The region records and the fill pointers. -/
def regRecLoop : Stmt :=
  .whileLtN 43201 43200 (block [
    .addN 43211 43201 43201, .addN 43211 43211 43211, .addN 43211 43211 43201,
    .addN 43211 43211 44003,
    .addN 43212 44008 43201, .loadN 43213 43212,
    .addN 43212 43212 43200, .loadN 43214 43212,
    .addN 43212 43212 43200, .loadN 43215 43212,
    .storeN 43211 43213, .addN 43211 43211 43011, .storeN 43211 43210,
    .addN 43211 43211 43011, .storeN 43211 43214, .addN 43211 43211 43011,
    .addN 43216 43210 43213, .storeN 43211 43216, .addN 43211 43211 43011,
    .storeN 43211 43215,
    .addN 43217 44011 43201, .storeN 43217 43210,
    .addN 43217 43217 43200, .storeN 43217 43216,
    .addN 43210 43216 43214,
    .addN 43201 43201 43011])

/-- The registers `regRecLoop` writes. -/
def BregRec (r : ℕ) : Bool := decide (r = 43201) || decide (43210 ≤ r ∧ r < 43218)

theorem wr_regRecLoop : wrM BregRec regRecLoop = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

/-- **The region records and the fill pointers.** -/
theorem regRecLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R RT FA : ℕ}
    {cA cC wR : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1)
    (hi : d.nreg 43201 = 0) (hP : d.nreg 43210 = 0) (hRT : d.nreg 44003 = RT)
    (hFA : d.nreg 44011 = FA) (hRTW : RT + 5 * R ≤ W) (hFAW : FA + 2 * R ≤ W)
    (hlay : RT + 5 * R ≤ FA ∨ FA + 2 * R ≤ RT)
    (hdis : (RT + 5 * R ≤ CA ∨ CA + 3 * R ≤ RT) ∧ (FA + 2 * R ≤ CA ∨ CA + 3 * R ≤ FA))
    (hoff : offF cA cC R ≤ W) (hCAW : CA + 3 * R ≤ W)
    (hm : d.nmem = regMem m₀ CA R cA cC wR) :
    ∃ d' k, Exec P W regRecLoop d d' k ∧ k ≤ 28 * R + 2 ∧ 26 * R ≤ k ∧ WordsBounded W d' ∧
      FrameM BregRec d d' ∧
      d'.nmem = recRMem (regMem m₀ CA R cA cC wR) RT FA R cA cC wR R := by
  obtain ⟨d', k, e, ⟨hw', n, hn', hnR, hPn, hf, hm'⟩, htest, hk, hψ⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 43201) (b := 43200) (body := _)
    (fun e => WordsBounded W e ∧ ∃ n, e.nreg 43201 = n ∧ n ≤ R ∧ e.nreg 43210 = offF cA cC n ∧
      FrameM BregRec d e ∧ e.nmem = recRMem (regMem m₀ CA R cA cC wR) RT FA R cA cC wR n)
    (fun e => 28 * (R - e.nreg 43201)) (fun e => 26 * e.nreg 43201) (fun e he => he.1)
    (fun e ⟨hwe, n, hne, hnR, hPe, hfe, hme⟩ htest => by
      have r1 : e.nreg 44008 = CA := by rw [hfe.1 _ (by decide), hCA]
      have r2 : e.nreg 43200 = R := by rw [hfe.1 _ (by decide), hR]
      have r4 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      have r5 : e.nreg 44003 = RT := by rw [hfe.1 _ (by decide), hRT]
      have r6 : e.nreg 44011 = FA := by rw [hfe.1 _ (by decide), hFA]
      rw [hne, r2] at htest
      have ma : e.nmem (CA + n) = cA n := by
        rw [hme]; unfold recRMem
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), regMem_rdA _ _ _ _ _ _ htest]
      have mc : e.nmem (CA + n + R) = cC n := by
        rw [hme]; unfold recRMem
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          show CA + n + R = CA + R + n by omega, regMem_rdC _ _ _ _ _ _ htest]
      have mw : e.nmem (CA + n + R + R) = wR n := by
        rw [hme]; unfold recRMem
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          show CA + n + R + R = CA + 2 * R + n by omega, regMem_rdW _ _ _ _ _ _ htest]
      have ho1 := offF_succ cA cC n
      have ho2 := offF_mono cA cC (show n + 1 ≤ R by omega)
      have X : ∃ e' k, Exec P W (block [
          .addN 43211 43201 43201, .addN 43211 43211 43211, .addN 43211 43211 43201,
          .addN 43211 43211 44003,
          .addN 43212 44008 43201, .loadN 43213 43212,
          .addN 43212 43212 43200, .loadN 43214 43212,
          .addN 43212 43212 43200, .loadN 43215 43212,
          .storeN 43211 43213, .addN 43211 43211 43011, .storeN 43211 43210,
          .addN 43211 43211 43011, .storeN 43211 43214, .addN 43211 43211 43011,
          .addN 43216 43210 43213, .storeN 43211 43216, .addN 43211 43211 43011,
          .storeN 43211 43215,
          .addN 43217 44011 43201, .storeN 43217 43210,
          .addN 43217 43217 43200, .storeN 43217 43216,
          .addN 43210 43216 43214,
          .addN 43201 43201 43011]) e e' k ∧ k = 26 ∧ e'.nreg 43201 = n + 1 ∧
          e'.nreg 43210 = offF cA cC (n + 1) ∧
          e'.nmem = recRMem (regMem m₀ CA R cA cC wR) RT FA R cA cC wR (n + 1) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r4, r5, r6,
              hne, hPe, ma, mc, mw]; omega)
          | skip
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> config_simp
        · rw [hne, r4]
        · rwo [r1, r2, hne, hPe, ma, mc]
        · rw [r1, r2, r4, r5, r6, hne, hPe, ma, mc, mw]
          exact recR_step' _ cA cC wR htest hlay hme (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨e', k, x, hk, hn', hP', hm'⟩ := X
      exact ⟨e', k, x, ⟨x.wb_right, n + 1, hn', by omega, hP',
        hfe.trans (exec_frameM x (by decide)), hm'⟩, by rwo [hn', hne],
        by rwo [hn', hne]⟩)
    ⟨hw, 0, hi, Nat.zero_le _, by rwr [hP], FrameM.refl _ _, by
      rw [hm]; funext a; unfold recRMem; rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]⟩
  have hnR' : n = R := by
    rwo [hn', hf.1 _ (by decide), hR] at htest
  subst hnR'
  exact ⟨d', k, e, by rwo [hi] at hk, by rwo [hi, hn'] at hψ, hw', hf, hm'⟩

end exec

end

end BuildRam

end Chazelle.Core
