module

public import Chazelle.Core.DownPhaseDrvRLib
public import Chazelle.Core.DownPhaseDrvRBktM
public import Chazelle.Core.NFBuildMain
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 2000000

/-!
# Down-phase driver (RAM side): the bucket distribution (a counting sort)

`bktS` distributes the `n` new event codes `base + q` (`q < n`) by their buckets
`bk q = m (BB + q) ≤ A` (a counting sort, `O(n + A)` steps).  Registers (band `bDownDrv`):
inputs `210022` (`BB`), `210031` (`n`), `210032` (`A`), `210033` (`base`); constants `210034`
(`1`), `210035` (`0`), `210039` (`A + 1`); the fresh arrays `C = 210036` (`A + 1` counters, at
the entry allocator `A₀`), `S = 210037` (`A + 1` bucket starts), `R = 210048` (`n` codes); the
counter `210038`, the running sum `210044`, scratch `210040 … 210047`.

**`bktS_exec`**: `seg R n = bktList bk n A base` (`DownPhaseDrvRBktM`), `S[b] = bstart b`,
`C[b] = bstart (b + 1)`, memory below `A₀` unchanged, cost `≤ 21 (A + 1) + 21 n + 30`.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam

@[expose] public section

/-! ## The program -/

/-- Constants and the allocation of the three arrays. -/
def bkInit : Stmt :=
  block [.constN 210034 1, .constN 210035 0, .copyN 210036 9999, .addN 210039 210032 210034,
    .addN 210037 210036 210039, .addN 210048 210037 210039, .addN 9999 210048 210031,
    .constN 210038 0]

/-- Clear the counters. -/
def bkL1 : Stmt :=
  .whileLtN 210038 210039
    (block [.addN 210040 210036 210038, .storeN 210040 210035, .addN 210038 210038 210034])

/-- Count. -/
def bkL2 : Stmt :=
  .whileLtN 210038 210031
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034])

/-- Prefix sums: `C[b] := S[b] := s`, `s := s + count`. -/
def bkL3 : Stmt :=
  .whileLtN 210038 210039
    (block [.addN 210040 210036 210038, .loadN 210041 210040, .storeN 210040 210044,
      .addN 210042 210037 210038, .storeN 210042 210044, .addN 210044 210044 210041,
      .addN 210038 210038 210034])

/-- Place: `R[C[bk q]] := base + q`, `C[bk q] += 1`. -/
def bkL4 : Stmt :=
  .whileLtN 210038 210031
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210046 210048 210043, .addN 210047 210033 210038,
      .storeN 210046 210047, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034])

/-- **The bucket distribution.** -/
def bktS : Stmt :=
  .seq bkInit (.seq bkL1 (.seq (.instr (.constN 210038 0)) (.seq bkL2
    (.seq (block [.constN 210038 0, .constN 210044 0]) (.seq bkL3
      (.seq (.instr (.constN 210038 0)) bkL4))))))

/-- The registers the loop bodies write. -/
def Bbody (r : ℕ) : Bool := decide (r = 210038) || decide (210040 ≤ r ∧ r ≤ 210047)

/-- The registers `bktS` writes. -/
def Bbkt (r : ℕ) : Bool := decide (210034 ≤ r ∧ r ≤ 210048) || decide (r = 9999)

/-! ## The invariants -/

/-- The registers during the loops (relative to the entry configuration `c₀`). -/
structure BkR (c₀ : Config) (BB n A base A₀ : ℕ) (d : Config) : Prop where
  r22 : d.nreg 210022 = BB
  r31 : d.nreg 210031 = n
  r32 : d.nreg 210032 = A
  r33 : d.nreg 210033 = base
  r34 : d.nreg 210034 = 1
  r35 : d.nreg 210035 = 0
  r36 : d.nreg 210036 = A₀
  r37 : d.nreg 210037 = A₀ + (A + 1)
  r39 : d.nreg 210039 = A + 1
  r48 : d.nreg 210048 = A₀ + (A + 1) + (A + 1)
  fr : ∀ r, Bbkt r = false → d.nreg r = c₀.nreg r
  alloc : d.nreg ALLOC = A₀ + (A + 1) + (A + 1) + n
  rr : ∀ r, Bbkt r = false → d.rreg r = c₀.rreg r
  rm : d.rmem = c₀.rmem
  out : d.output = c₀.output

theorem Bbody_imp {r : ℕ} (h : Bbody r = true) : Bbkt r = true := by
  sio only [Bbody, Bbkt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢

/-- The register facts survive a body (its writes are in `Bbody`). -/
theorem BkR.body {c₀ d d' : Config} {BB n A base A₀ : ℕ} (h : BkR c₀ BB n A base A₀ d)
    (hf : FrameM Bbody d d') : BkR c₀ BB n A base A₀ d' := by
  have e  := hf.1
  refine ⟨(e _ (by decide)).trans h.r22, (e _ (by decide)).trans h.r31,
    (e _ (by decide)).trans h.r32, (e _ (by decide)).trans h.r33, (e _ (by decide)).trans h.r34,
    (e _ (by decide)).trans h.r35, (e _ (by decide)).trans h.r36, (e _ (by decide)).trans h.r37,
    (e _ (by decide)).trans h.r39, (e _ (by decide)).trans h.r48, fun r hr => ?_,
    (e _ (by decide)).trans h.alloc, fun r hr => ?_, hf.2.2.1.trans h.rm, hf.2.2.2.trans h.out⟩
  · have hb : Bbody r = false := by
      cases hh : Bbody r
      · rfl
      · rw [Bbody_imp hh] at hr; exact absurd hr (by decide)
    exact (e r hb).trans (h.fr r hr)
  · have hb : Bbody r = false := by
      cases hh : Bbody r
      · rfl
      · rw [Bbody_imp hh] at hr; exact absurd hr (by decide)
    exact (hf.2.1 r hb).trans (h.rr r hr)

theorem wrM_L1 : wrM Bbody
    (block [.addN 210040 210036 210038, .storeN 210040 210035, .addN 210038 210038 210034]) =
      true := by decide

theorem wrM_L2 : wrM Bbody
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034]) = true := by decide

theorem wrM_L3 : wrM Bbody
    (block [.addN 210040 210036 210038, .loadN 210041 210040, .storeN 210040 210044,
      .addN 210042 210037 210038, .storeN 210042 210044, .addN 210044 210044 210041,
      .addN 210038 210038 210034]) = true := by decide

theorem wrM_L4 : wrM Bbody
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210046 210048 210043, .addN 210047 210033 210038,
      .storeN 210046 210047, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034]) = true := by decide

/-! ## The bodies -/

section exec

variable {P : Polygon} {W : ℕ}

theorem body1_exec (d : Config) (hw : WordsBounded W d) {j Cb : ℕ} (h36 : d.nreg 210036 = Cb)
    (h38 : d.nreg 210038 = j) (h34 : d.nreg 210034 = 1) (h35 : d.nreg 210035 = 0)
    (hW : Cb + j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210036 210038, .storeN 210040 210035,
      .addN 210038 210038 210034]) d d' k ∧ k = 3 ∧ d'.nreg 210038 = j + 1 ∧
      d'.nmem = upd d.nmem (Cb + j) 0 ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210040 210036 210038,
      .storeN 210040 210035, .addN 210038 210038 210034]) d d' k ∧ k = 3 ∧
      d'.nreg 210038 = j + 1 ∧ d'.nmem = upd d.nmem (Cb + j) 0 := by
    exec_block
    · omega
    · cso
    · refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp [h34, h35, h36, h38]
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_L1⟩

theorem body2_exec (d : Config) (hw : WordsBounded W d) {j Cb BB x v : ℕ}
    (h36 : d.nreg 210036 = Cb) (h22 : d.nreg 210022 = BB) (h38 : d.nreg 210038 = j)
    (h34 : d.nreg 210034 = 1) (hx : d.nmem (BB + j) = x) (hv : d.nmem (Cb + x) = v)
    (hW1 : BB + j ≤ W) (hW2 : Cb + x ≤ W) (hW3 : v + 1 ≤ W) (hW4 : j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210022 210038, .loadN 210041 210040,
      .addN 210042 210036 210041, .loadN 210043 210042, .addN 210043 210043 210034,
      .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧ k = 7 ∧
      d'.nreg 210038 = j + 1 ∧ d'.nmem = upd d.nmem (Cb + x) (v + 1) ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210040 210022 210038,
      .loadN 210041 210040, .addN 210042 210036 210041, .loadN 210043 210042,
      .addN 210043 210043 210034, .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧
      k = 7 ∧ d'.nreg 210038 = j + 1 ∧ d'.nmem = upd d.nmem (Cb + x) (v + 1) := by
    exec_block
    all_goals try (config_simp; sio only [h22, h38, h36, h34, hx, hv])
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp [h22, h38, h36, h34, hx, hv]
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_L2⟩

theorem body3_exec (d : Config) (hw : WordsBounded W d) {j Cb Sb sv t : ℕ}
    (h36 : d.nreg 210036 = Cb) (h37 : d.nreg 210037 = Sb) (h38 : d.nreg 210038 = j)
    (h34 : d.nreg 210034 = 1) (h44 : d.nreg 210044 = sv) (ht : d.nmem (Cb + j) = t)
    (_hne : Cb + j ≠ Sb + j)
    (hW1 : Cb + j ≤ W) (hW2 : Sb + j ≤ W) (hW3 : sv + t ≤ W) (hW4 : j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210036 210038, .loadN 210041 210040,
      .storeN 210040 210044, .addN 210042 210037 210038, .storeN 210042 210044,
      .addN 210044 210044 210041, .addN 210038 210038 210034]) d d' k ∧ k = 7 ∧
      d'.nreg 210038 = j + 1 ∧ d'.nreg 210044 = sv + t ∧
      d'.nmem = upd (upd d.nmem (Cb + j) sv) (Sb + j) sv ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3⟩ : ∃ d' k, Exec P W (block [.addN 210040 210036 210038,
      .loadN 210041 210040, .storeN 210040 210044, .addN 210042 210037 210038,
      .storeN 210042 210044, .addN 210044 210044 210041, .addN 210038 210038 210034]) d d' k ∧
      k = 7 ∧ d'.nreg 210038 = j + 1 ∧ d'.nreg 210044 = sv + t ∧
      d'.nmem = upd (upd d.nmem (Cb + j) sv) (Sb + j) sv := by
    exec_block
    all_goals try (config_simp; sio only [h36, h37, h38, h34, h44, ht])
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> config_simp <;> simp [h36, h37, h38, h34, h44, ht]
  exact ⟨d', k, ex, hk, h1, h2, h3, exec_frameM ex wrM_L3⟩

theorem body4_exec (d : Config) (hw : WordsBounded W d) {j Cb BB Rb base x v : ℕ}
    (h36 : d.nreg 210036 = Cb) (h22 : d.nreg 210022 = BB) (h38 : d.nreg 210038 = j)
    (h48 : d.nreg 210048 = Rb) (h33 : d.nreg 210033 = base)
    (h34 : d.nreg 210034 = 1) (hx : d.nmem (BB + j) = x) (hv : d.nmem (Cb + x) = v)
    (_hne : Rb + v ≠ Cb + x)
    (hW1 : BB + j ≤ W) (hW2 : Cb + x ≤ W) (hW3 : Rb + v + 1 ≤ W) (hW4 : base + j ≤ W)
    (hW5 : j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210022 210038, .loadN 210041 210040,
      .addN 210042 210036 210041, .loadN 210043 210042, .addN 210046 210048 210043,
      .addN 210047 210033 210038, .storeN 210046 210047, .addN 210043 210043 210034,
      .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧ k = 10 ∧
      d'.nreg 210038 = j + 1 ∧
      d'.nmem = upd (upd d.nmem (Rb + v) (base + j)) (Cb + x) (v + 1) ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210040 210022 210038,
      .loadN 210041 210040, .addN 210042 210036 210041, .loadN 210043 210042,
      .addN 210046 210048 210043, .addN 210047 210033 210038, .storeN 210046 210047,
      .addN 210043 210043 210034, .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧
      k = 10 ∧ d'.nreg 210038 = j + 1 ∧
      d'.nmem = upd (upd d.nmem (Rb + v) (base + j)) (Cb + x) (v + 1) := by
    exec_block
    all_goals try (config_simp; sio only [h22, h38, h36, h34, h48, h33, hx, hv])
    refine ⟨rfl, ?_⟩
    config_simp
    simp only [h22, h38, h36, h34, h48, h33, hx, hv, true_and]
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_L4⟩

/-! ## The memory during the loops -/

/-- After the first `j` iterations of the first loop. -/
def mem1 (m₀ : ℕ → ℕ) (A₀ j a : ℕ) : ℕ := if A₀ ≤ a ∧ a < A₀ + j then 0 else m₀ a

/-- During the second loop. -/
def mem2 (m₀ bk : ℕ → ℕ) (A₀ A j a : ℕ) : ℕ :=
  if A₀ ≤ a ∧ a < A₀ + (A + 1) then bcnt bk j (a - A₀) else m₀ a

/-- During the third loop. -/
def mem3 (m₀ bk : ℕ → ℕ) (n A₀ A j a : ℕ) : ℕ :=
  if A₀ ≤ a ∧ a < A₀ + (A + 1) then
    (if a - A₀ < j then bstart bk n (a - A₀) else bcnt bk n (a - A₀))
  else if A₀ + (A + 1) ≤ a ∧ a < A₀ + (A + 1) + j then bstart bk n (a - (A₀ + (A + 1)))
  else m₀ a

/-- The two arrays during the fourth loop. -/
def memCS (m₀ bk : ℕ → ℕ) (n A₀ A j a : ℕ) : ℕ :=
  if A₀ ≤ a ∧ a < A₀ + (A + 1) then bstart bk n (a - A₀) + bcnt bk j (a - A₀)
  else if A₀ + (A + 1) ≤ a ∧ a < A₀ + (A + 1) + (A + 1) then bstart bk n (a - (A₀ + (A + 1)))
  else m₀ a

theorem bcnt_le (bk : ℕ → ℕ) (q b : ℕ) : bcnt bk q b ≤ q := by
  unfold bcnt bfilt
  exact (List.length_filter_le _ _).trans (by simp)

theorem bstart_le {bk : ℕ → ℕ} {n A b : ℕ} (hA : ∀ q, q < n → bk q ≤ A) (hb : b ≤ A + 1) :
    bstart bk n b ≤ n := by
  have := bstart_mono (bk := bk) n hb
  rw [bstart_all hA] at this; exact this

/-! ## The loops -/

/-- The loop invariant of the first loop. -/
def I1 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) (d : Config) : Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧ ∀ a, d.nmem a = mem1 m₀ A₀ j a

theorem loop1_exec {c₀ d : Config} {BB n A base A₀ : ℕ} {m₀ : ℕ → ℕ}
    (hroom : A₀ + (A + 1) + 1 ≤ W) (h : I1 W c₀ BB n A base A₀ m₀ 0 d) :
    ∃ d' k, Exec P W bkL1 d d' k ∧ I1 W c₀ BB n A base A₀ m₀ (A + 1) d' ∧
      k ≤ 5 * (A + 1) + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210039)
    (I1 W c₀ BB n A base A₀ m₀) 3 (A + 1)
    (fun j d ⟨hw, hR, h38, _⟩ => ⟨hw, h38, hR.r39⟩)
    (fun j d hj ⟨hw, hR, h38, hm⟩ => by
      obtain ⟨d', k, ex, hk, h38', hm', hf⟩ := body1_exec (P := P) d hw hR.r36 h38 hR.r34 hR.r35
        (by omega)
      refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', fun a => ?_⟩, by omega⟩
      rw [hm', Machine.upd_apply, hm]
      unfold mem1
      by_cases ha : a = A₀ + j
      · rw [ite_eq_left ha, ite_eq_left (by omega)]
      · rw [ite_eq_right ha]; splao) h (Nat.zero_le _)
  exact ⟨d', k, ex, hI, by omega⟩

/-- The loop invariant of the second loop. -/
def I2 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ bk : ℕ → ℕ) (j : ℕ) (d : Config) :
    Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧
    ∀ a, d.nmem a = mem2 m₀ bk A₀ A j a

theorem loop2_exec {c₀ d : Config} {BB n A base A₀ : ℕ} {m₀ bk : ℕ → ℕ} (hBB : BB + n ≤ A₀)
    (hbkd : ∀ q, q < n → m₀ (BB + q) = bk q)
    (hbk : ∀ q, q < n → bk q ≤ A) (hroom : A₀ + (A + 1) + n + 1 ≤ W)
    (h : I2 W c₀ BB n A base A₀ m₀ bk 0 d) :
    ∃ d' k, Exec P W bkL2 d d' k ∧ I2 W c₀ BB n A base A₀ m₀ bk n d' ∧ k ≤ 9 * n + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210031)
    (I2 W c₀ BB n A base A₀ m₀ bk) 7 n
    (fun j d ⟨hw, hR, h38, _⟩ => ⟨hw, h38, hR.r31⟩)
    (fun j d hj ⟨hw, hR, h38, hm⟩ => by
      have hx : d.nmem (BB + j) = bk j := by
        rw [hm]; unfold mem2; rw [ite_eq_right (by omega), hbkd j hj]
      have hxA := hbk j hj
      have hv : d.nmem (A₀ + bk j) = bcnt bk j (bk j) := by
        rw [hm]; unfold mem2; rw [ite_eq_left (by omega)]; congr 1; omega
      have hvb := bcnt_le bk j (bk j)
      obtain ⟨d', k, ex, hk, h38', hm', hf⟩ := body2_exec (P := P) d hw hR.r36 hR.r22 h38 hR.r34
        hx hv (by omega) (by omega) (by omega) (by omega)
      refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', fun a => ?_⟩, by omega⟩
      rw [hm', Machine.upd_apply, hm]
      unfold mem2
      by_cases ha : a = A₀ + bk j
      · rw [ite_eq_left ha, ite_eq_left (by omega), show a - A₀ = bk j by omega, bcnt_succ, ite_eq_left rfl]
      · rw [ite_eq_right ha]
        split_ifs with h1
        · rw [bcnt_succ, ite_eq_right (by omega), Nat.add_zero]
        · rfl) h (Nat.zero_le _)
  exact ⟨d', k, ex, hI, by omega⟩

/-- The loop invariant of the third loop. -/
def I3 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ bk : ℕ → ℕ) (j : ℕ) (d : Config) :
    Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧
    d.nreg 210044 = bstart bk n j ∧ ∀ a, d.nmem a = mem3 m₀ bk n A₀ A j a

theorem loop3_exec {c₀ d : Config} {BB n A base A₀ : ℕ} {m₀ bk : ℕ → ℕ}
    (hbk : ∀ q, q < n → bk q ≤ A) (hroom : A₀ + (A + 1) + (A + 1) + n + 1 ≤ W)
    (h : I3 W c₀ BB n A base A₀ m₀ bk 0 d) :
    ∃ d' k, Exec P W bkL3 d d' k ∧ I3 W c₀ BB n A base A₀ m₀ bk (A + 1) d' ∧
      k ≤ 9 * (A + 1) + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210039)
    (I3 W c₀ BB n A base A₀ m₀ bk) 7 (A + 1)
    (fun j d ⟨hw, hR, h38, _⟩ => ⟨hw, h38, hR.r39⟩)
    (fun j d hj ⟨hw, hR, h38, h44, hm⟩ => by
      have ht : d.nmem (A₀ + j) = bcnt bk n j := by
        rw [hm]; unfold mem3; rw [ite_eq_left (by omega), ite_eq_right (by omega)]; congr 1; omega
      have hs := bstart_le (bk := bk) hbk (show j ≤ A + 1 by omega)
      have hs1 := bstart_le (bk := bk) hbk (show j + 1 ≤ A + 1 by omega)
      rw [bstart_succ] at hs1
      obtain ⟨d', k, ex, hk, h38', h44', hm', hf⟩ := body3_exec (P := P) d hw hR.r36 hR.r37 h38
        hR.r34 h44 ht (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', by rw [h44', bstart_succ], fun a => ?_⟩,
        by omega⟩
      rw [hm', Machine.upd_apply, Machine.upd_apply, hm]
      unfold mem3
      by_cases ha : a = A₀ + (A + 1) + j
      · rw [ite_eq_left ha, ite_eq_right (by omega), ite_eq_left (by omega), show a - (A₀ + (A + 1)) = j by omega]
      · rw [ite_eq_right ha]
        by_cases hb : a = A₀ + j
        · rw [ite_eq_left hb, ite_eq_left (by omega), ite_eq_left (by omega), show a - A₀ = j by omega]
        · rw [ite_eq_right hb]
          split_ifs <;> first | rfl | omega) h (Nat.zero_le _)
  exact ⟨d', k, ex, hI, by omega⟩

/-- The loop invariant of the fourth loop. -/
def I4 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ bk : ℕ → ℕ) (j : ℕ) (d : Config) :
    Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧
    (∀ a, a < A₀ + (A + 1) + (A + 1) → d.nmem a = memCS m₀ bk n A₀ A j a) ∧
    ∀ q, q < j → d.nmem (A₀ + (A + 1) + (A + 1) + slot bk n q) = base + q

theorem loop4_exec {c₀ d : Config} {BB n A base A₀ : ℕ} {m₀ bk : ℕ → ℕ} (hBB : BB + n ≤ A₀)
    (hbkd : ∀ q, q < n → m₀ (BB + q) = bk q)
    (hbk : ∀ q, q < n → bk q ≤ A) (hroom : A₀ + (A + 1) + (A + 1) + n + 1 ≤ W)
    (hbase : base + n ≤ W) (h : I4 W c₀ BB n A base A₀ m₀ bk 0 d) :
    ∃ d' k, Exec P W bkL4 d d' k ∧ I4 W c₀ BB n A base A₀ m₀ bk n d' ∧ k ≤ 12 * n + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210031)
    (I4 W c₀ BB n A base A₀ m₀ bk) 10 n
    (fun j d ⟨hw, hR, h38, _⟩ => ⟨hw, h38, hR.r31⟩)
    (fun j d hj ⟨hw, hR, h38, hm, hq⟩ => by
      have hx : d.nmem (BB + j) = bk j := by
        rw [hm _ (by omega)]; unfold memCS; rw [ite_eq_right (by omega), ite_eq_right (by omega), hbkd j hj]
      have hxA := hbk j hj
      have hv : d.nmem (A₀ + bk j) = slot bk n j := by
        rw [hm _ (by omega)]; unfold memCS; rw [ite_eq_left (by omega)]
        unfold slot; congr 2 <;> omega
      have hsl := slot_lt (bk := bk) hj hbk
      obtain ⟨d', k, ex, hk, h38', hm', hf⟩ := body4_exec (P := P) d hw hR.r36 hR.r22 h38 hR.r48
        hR.r33 hR.r34 hx hv (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', fun a ha => ?_, fun q hq' => ?_⟩, by omega⟩
      · rw [hm', Machine.upd_apply, Machine.upd_apply]
        by_cases hb : a = A₀ + bk j
        · rw [ite_eq_left hb]
          unfold memCS
          rw [ite_eq_left (by omega), show a - A₀ = bk j by omega, bcnt_succ, ite_eq_left rfl]
          ufo slot
        · rw [ite_eq_right hb, ite_eq_right (by omega), hm _ ha]
          unfold memCS
          split_ifs with h1
          all_goals first | rfl | rw [bcnt_succ, ite_eq_right (by omega), Nat.add_zero]
      · have hqn : q < n := by omega
        have hsq := slot_lt (bk := bk) hqn hbk
        rw [hm', Machine.upd_apply, Machine.upd_apply]
        rw [ite_eq_right (by omega)]
        by_cases hqj : q = j
        · subst hqj; rw [ite_eq_left rfl]
        · have hne : slot bk n q ≠ slot bk n j := fun h' => hqj (slot_inj hqn hj h')
          have hqj' : q < j := by omega
          rw [ite_eq_right (by omega), hq q hqj']) h (Nat.zero_le _)
  exact ⟨d', k, ex, hI, by omega⟩

theorem wrM_init : wrM Bbkt bkInit = true := by decide

theorem wrM_reset1 : wrM Bbody (.instr (.constN 210038 0)) = true := by decide

theorem wrM_reset2 : wrM Bbody (block [.constN 210038 0, .constN 210044 0]) = true := by decide

/-- **The bucket distribution.** -/
theorem bktS_exec (c : Config) (hw : WordsBounded W c) {BB n A base : ℕ} {bk : ℕ → ℕ}
    (h22 : c.nreg 210022 = BB) (h31 : c.nreg 210031 = n) (h32 : c.nreg 210032 = A)
    (h33 : c.nreg 210033 = base) (hBB : BB + n ≤ c.nreg ALLOC)
    (hbkd : ∀ q, q < n → c.nmem (BB + q) = bk q) (hbk : ∀ q, q < n → bk q ≤ A)
    (hroom : c.nreg ALLOC + (A + 1) + (A + 1) + n + 1 ≤ W) (hbase : base + n ≤ W) :
    ∃ c' k, Exec P W bktS c c' k ∧ k ≤ 21 * (A + 1) + 21 * n + 30 ∧
      c'.nreg 210036 = c.nreg ALLOC ∧ c'.nreg 210037 = c.nreg ALLOC + (A + 1) ∧
      c'.nreg 210048 = c.nreg ALLOC + (A + 1) + (A + 1) ∧
      c'.nreg ALLOC = c.nreg ALLOC + (A + 1) + (A + 1) + n ∧
      c'.nreg 210034 = 1 ∧ c'.nreg 210039 = A + 1 ∧
      seg c'.nmem (c.nreg ALLOC + (A + 1) + (A + 1)) n = bktList bk n A base ∧
      (∀ b, b ≤ A → c'.nmem (c.nreg ALLOC + (A + 1) + b) = bstart bk n b) ∧
      (∀ b, b ≤ A → c'.nmem (c.nreg ALLOC + b) = bstart bk n (b + 1)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bbkt r = false → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A₀ := c.nreg ALLOC with hA₀
  -- the initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v35, v36, v39, v37, v48, vA, v38, hm₁⟩ : ∃ c₁ k₁,
      Exec P W bkInit c c₁ k₁ ∧ k₁ = 8 ∧ c₁.nreg 210034 = 1 ∧ c₁.nreg 210035 = 0 ∧
      c₁.nreg 210036 = A₀ ∧ c₁.nreg 210039 = A + 1 ∧ c₁.nreg 210037 = A₀ + (A + 1) ∧
      c₁.nreg 210048 = A₀ + (A + 1) + (A + 1) ∧ c₁.nreg ALLOC = A₀ + (A + 1) + (A + 1) + n ∧
      c₁.nreg 210038 = 0 ∧ c₁.nmem = c.nmem := by
    unfold bkInit
    exec_block
    all_goals try (config_simp; (try simp only [h32, h31, show c.nreg 9999 = A₀ from rfl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h32, h31, show c.nreg 9999 = A₀ from rfl])
  have f₁ := exec_frameM e₁ wrM_init
  have hR₁ : BkR c BB n A base A₀ c₁ :=
    { r22 := (f₁.1 _ (by decide)).trans h22, r31 := (f₁.1 _ (by decide)).trans h31,
      r32 := (f₁.1 _ (by decide)).trans h32, r33 := (f₁.1 _ (by decide)).trans h33,
      r34 := v34, r35 := v35, r36 := v36, r37 := v37, r39 := v39, r48 := v48, fr := f₁.1,
      alloc := vA, rr := f₁.2.1, rm := f₁.2.2.1, out := f₁.2.2.2 }
  have w₁ := e₁.wb_right
  -- the first loop
  obtain ⟨c₂, k₂, e₂, ⟨w₂, hR₂, h38₂, hm₂⟩, hk₂⟩ := loop1_exec (P := P) (m₀ := c.nmem)
    (by omega) ⟨w₁, hR₁, v38, fun a => by rw [hm₁]; unfold mem1; rw [ite_eq_right (by omega)]⟩
  -- reset
  have e₃ := Exec.constN (P := P) w₂ 210038 0 (Nat.zero_le _)
  have f₃ := exec_frameM e₃ wrM_reset1
  have hR₃ := hR₂.body f₃
  -- the second loop
  obtain ⟨c₄, k₄, e₄, ⟨w₄, hR₄, h38₄, hm₄⟩, hk₄⟩ := loop2_exec (P := P) (m₀ := c.nmem)
    (bk := bk) (by omega) hbkd hbk (by omega)
    ⟨e₃.wb_right, hR₃, by simp, fun a => by
      rw [hm₂]; unfold mem1 mem2; split_ifs <;> first | rfl⟩
  -- reset
  obtain ⟨c₅, k₅, e₅, hk₅, v38₅, v44₅, hm₅⟩ : ∃ c₅ k₅,
      Exec P W (block [.constN 210038 0, .constN 210044 0]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg 210038 = 0 ∧ c₅.nreg 210044 = 0 ∧ c₅.nmem = c₄.nmem := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, rfl⟩
  have f₅ := exec_frameM e₅ wrM_reset2
  have hR₅ := hR₄.body f₅
  -- the third loop
  obtain ⟨c₆, k₆, e₆, ⟨w₆, hR₆, h38₆, h44₆, hm₆⟩, hk₆⟩ := loop3_exec (P := P) (m₀ := c.nmem)
    (bk := bk) hbk (by omega)
    ⟨e₅.wb_right, hR₅, v38₅, by rwr [v44₅], fun a => by
      rw [hm₅, hm₄]; unfold mem2 mem3; split_ifs <;> first | rfl | omega⟩
  -- reset
  have e₇ := Exec.constN (P := P) w₆ 210038 0 (Nat.zero_le _)
  have f₇ := exec_frameM e₇ wrM_reset1
  have hR₇ := hR₆.body f₇
  -- the fourth loop
  obtain ⟨c₈, k₈, e₈, ⟨w₈, hR₈, h38₈, hm₈, hq₈⟩, hk₈⟩ := loop4_exec (P := P) (m₀ := c.nmem)
    (bk := bk) (by omega) hbkd hbk (by omega) hbase
    ⟨e₇.wb_right, hR₇, by simp, fun a ha => by
      rw [hm₆]; unfold mem3 memCS
      split_ifs <;> first | rfl | omega, fun q hq => absurd hq (by omega)⟩
  refine ⟨c₈, k₁ + (k₂ + (1 + (k₄ + (k₅ + (k₆ + (1 + k₈)))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))), by omega,
    hR₈.r36, hR₈.r37, hR₈.r48, hR₈.alloc, hR₈.r34, hR₈.r39, ?_, fun b hb => ?_, fun b hb => ?_,
    fun a ha => ?_,
    hR₈.fr, ?_, hR₈.rm, hR₈.out⟩
  · exact seg_eq_bktList hbk hq₈
  · rw [hm₈ _ (by omega)]; unfold memCS
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]; congr 1; omega
  · rw [hm₈ _ (by omega)]; unfold memCS
    rw [ite_eq_left (by omega), show c.nreg ALLOC + b - A₀ = b by omega, bstart_succ]
  · rw [hm₈ _ (by omega)]; unfold memCS; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · funext r
    exact exec_frameM2 (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))))
      (BN := Bbkt) (BR := fun _ => false) (by decide) r rfl

end exec

end

end DrvR

end Chazelle.Core
