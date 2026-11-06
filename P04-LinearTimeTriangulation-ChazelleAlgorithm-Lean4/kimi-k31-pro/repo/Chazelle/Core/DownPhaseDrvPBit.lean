module

public import Chazelle.Core.DownPhaseDrvPScan
public import Chazelle.Core.DownPhaseOracleChR2
public import Chazelle.Core.DownPhaseMathJunc
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 2000000

/-!
# Down-phase pieces (D4), part 4: the top and the orientation bit of a host chain

Mathematics: for a chain `C = ⟨H.poly Q, s, m⟩` of a host,

* `hchain_vertex`: its vertices are the evaluated host points `(s + k) mod N`;
* `hchain_topIdx`: the least offset of a highest point (`scanS`) is the top index;
* `hchain_topIdx_leaf`: on a leaf (the points are vertices of `Q`, distinct heights) every
  offset of a highest point (`gTop`) is the top index;
* `sideCcw_up'`, `sideBeta_iff'`: the orientation bit from six sign tests at the top, for any
  chain whose top is not its first vertex — the neighbour after the top may be at the same height
  (host chains have horizontal chord edges), which `Brute.sideCcw_up` excludes;
* `hchain_beta`: the same on the host points.

RAM: `betaS` (`betaS_exec`): `218014 := 0` if `T = 0`, else three host lookups (the points
before, at and after the top, the last one modulo `N`), the six sign tests of `IOrc.testsI`
into `170082 … 170088` and the decision tree `IOrc.logI`.
-/


namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Chain (sideCcw sideCross sideDot)

@[expose] public section

/-! ## The orientation bit of a chain -/

/-- **The orientation bit from sign tests** at a top vertex `v` above its predecessor `a`, for
any successor `b` (also at the height of `v`). -/
theorem sideCcw_up' {a v b : Point} {h : ℝ} (hh : 0 < h) (ha : a.2 < v.2) :
    sideCcw (b - v) ((0 : ℝ), h) (a - v) ↔
      (0 < det a v b ∧ v.1 < b.1 ∧ a.1 < v.1) ∨ (det a v b < 0 ∧ (v.1 < b.1 ∨ a.1 < v.1)) ∨
      (det a v b = 0 ∧ v.2 < b.2 ∧ v.1 < b.1) ∨ (det a v b = 0 ∧ b.2 < v.2) := by
  by_cases hb : b.2 = v.2
  swap
  · exact Brute.sideCcw_up hh ha hb
  have e1  := Chain.sideCross_corner a v b
  have hdet : det a v b = (b.1 - v.1) * (a.2 - v.2) := by
    rw [← e1]; unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; rwring [hb]
  have e2 : sideCross (b - v) ((0 : ℝ), h) = h * (b.1 - v.1) := by
    unfold sideCross; sir only [Prod.fst_sub, Prod.snd_sub]
  have e3 : sideCross ((0 : ℝ), h) (a - v) = h * (v.1 - a.1) := by
    unfold sideCross; sir only [Prod.fst_sub, Prod.snd_sub]
  have e4 : sideDot (b - v) ((0 : ℝ), h) = 0 := by
    unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; rwring [hb]
  have e5 : sideDot (b - v) (a - v) = (b.1 - v.1) * (a.1 - v.1) := by
    unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; rwring [hb]
  unfold sideCcw
  rw [e1, e2, e3, e4, e5, hdet, hb]
  rcases lt_trichotomy b.1 v.1 with h1 | h1 | h1
  · have p1 : 0 < (b.1 - v.1) * (a.2 - v.2) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have p2 : h * (b.1 - v.1) < 0 := mul_neg_of_pos_of_neg hh (by linarith)
    constructor
    · rintro (⟨-, h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩) <;> linarith
    · rintro (⟨-, h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩) <;> linarith
  · rws [h1]
  · have p1 : (b.1 - v.1) * (a.2 - v.2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have p2 : 0 < h * (b.1 - v.1) := mul_pos hh (by linarith)
    exact iff_of_true (Or.inr (Or.inl ⟨p1, Or.inl p2⟩)) (Or.inr (Or.inl ⟨p1, Or.inl h1⟩))

/-- **The orientation bit of a chain** whose top is not its first vertex (no distinct heights
needed). -/
theorem sideBeta_iff' (C : Chain) (h0 : 0 < C.topIdx) :
    C.sideBeta = true ↔ IOrc.BetaF (C.vertex (C.topIdx - 1)) C.top (C.vertex (C.topIdx + 1)) := by
  rw [C.sideBeta_eq_true_iff]
  have hsl : C.slitTop - C.top = ((0 : ℝ), C.radius - C.top.2) := by
    unfold Chain.slitTop; ext <;> simp
  rw [hsl]
  have hT := C.topIdx_le
  have ha : (C.vertex (C.topIdx - 1)).2 < C.top.2 := by
    refine lt_of_le_of_ne (C.vertex_snd_le_top (by omega)) (fun e => ?_)
    have := C.topIdx_min (j := C.topIdx - 1) (by omega) (fun i hi => by
      rw [e]; exact C.vertex_snd_le_top hi)
    omega
  rw [sideCcw_up' (by linarith [C.top_snd_lt_radius]) ha]
  unfold IOrc.BetaF
  constructor
  · rintro (h | ⟨h1, h3⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨not_lt.2 h1.le, h1.ne, h3⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | ⟨h1, h2, h3⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨lt_of_le_of_ne (not_lt.1 h1) h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-! ## Host chains -/

section hostchain

variable {P : Polygon} {H : Host} {C : Chain}

theorem qof_n (P : Polygon) : (Qof P).n = P.n := shear_n _ _

theorem hchain_n (hC : C.P = H.poly (Qof P)) : C.P.n = (H.pts P.n).length := by
  rw [hC, DownMath.host_poly_n, qof_n]

/-- The vertices of a host chain are evaluated host points. -/
theorem hchain_vertex (hC : C.P = H.poly (Qof P)) (k : ℕ) :
    C.vertex k = (pt H P.n ((C.s + k) % (H.pts P.n).length)).eval (Qof P) := by
  have hn := hchain_n hC
  have hpos := C.n_pos
  show C.P.vtx ((C.s + k) % C.P.n) = _
  have hlt : (C.s + k) % (H.pts P.n).length < (H.pts (Qof P).n).length := by
    rw [qof_n]; exact Nat.mod_lt _ (by omega)
  rw [hn, hC, DownMath.host_poly_vtx _ _ hlt, qof_n]
  rfl

theorem hchain_vertex_lt (hC : C.P = H.poly (Qof P)) {k : ℕ}
    (hk : C.s + k < (H.pts P.n).length) : C.vertex k = (pt H P.n (C.s + k)).eval (Qof P) := by
  rw [hchain_vertex hC, Nat.mod_eq_of_lt hk]

/-- **The top index of a host chain** is the least offset of a highest point. -/
theorem hchain_topIdx (hC : C.P = H.poly (Qof P)) (hsm : C.s + C.m < (H.pts P.n).length)
    {T : ℕ} (hT : T ≤ C.m) (hle : ∀ j, j ≤ C.m → Yh P H (C.s + j) ≤ Yh P H (C.s + T))
    (hlt : ∀ j, j < T → Yh P H (C.s + j) < Yh P H (C.s + T)) : C.topIdx = T := by
  have ev : ∀ j, j ≤ C.m → (C.vertex j).2 = Yh P H (C.s + j) := fun j hj => by
    rwr [hchain_vertex_lt hC (by omega)]
  have h1 : C.topIdx ≤ T := C.topIdx_min hT (fun i hi => by rw [ev i hi, ev T hT]; exact hle i hi)
  by_contra hne
  have h2 := C.vertex_snd_le_top hT
  unfold Chain.top at h2
  rw [ev T hT, ev _ C.topIdx_le] at h2
  have := hlt C.topIdx (by omega)
  linarith

/-- **The top index of a leaf** (its points are the vertices `a, …, a + m` of `Q`, of distinct
heights) is every offset of a highest point. -/
theorem hchain_topIdx_leaf (hC : C.P = H.poly (Qof P)) (hsm : C.s + C.m < (H.pts P.n).length)
    (hD : DistinctHeights (Qof P)) {a : ℕ} (han : a + C.m < P.n)
    (hpt : ∀ k, k ≤ C.m → pt H P.n (C.s + k) = .vtx (a + k)) {T : ℕ} (hT : T ≤ C.m)
    (hle : ∀ j, j ≤ C.m → IOrc.Y P (a + j) ≤ IOrc.Y P (a + T)) : C.topIdx = T := by
  have ev : ∀ j, j ≤ C.m → (C.vertex j).2 = IOrc.Y P (a + j) := fun j hj => by
    rwr [hchain_vertex_lt hC (by omega), hpt j hj]
  have h1 : C.topIdx ≤ T := C.topIdx_min hT (fun i hi => by rw [ev i hi, ev T hT]; exact hle i hi)
  by_contra hne
  have h2 := C.vertex_snd_le_top hT
  unfold Chain.top at h2
  rw [ev T hT, ev _ C.topIdx_le] at h2
  have h3 := hle _ C.topIdx_le
  have hn : (Qof P).n = P.n := shear_n _ _
  exact hD (a + C.topIdx) (a + T) (by rw [hn]; have := C.topIdx_le; omega) (by rwo [hn])
    (by omega) (le_antisymm h3 h2)

/-- **The orientation bit of a host chain** from the host points before, at and after the top. -/
theorem hchain_beta (hC : C.P = H.poly (Qof P)) (hT0 : 0 < C.topIdx)
    (hsT : C.s + C.topIdx < (H.pts P.n).length) :
    C.sideBeta = true ↔ IOrc.BetaF ((pt H P.n (C.s + C.topIdx - 1)).eval (Qof P))
      ((pt H P.n (C.s + C.topIdx)).eval (Qof P))
      ((pt H P.n ((C.s + C.topIdx + 1) % (H.pts P.n).length)).eval (Qof P)) := by
  rw [sideBeta_iff' C hT0, hchain_vertex_lt hC (by omega),
    show C.s + (C.topIdx - 1) = C.s + C.topIdx - 1 by omega]
  unfold Chain.top
  rw [hchain_vertex_lt hC hsT, hchain_vertex hC, ← Nat.add_assoc]

end hostchain

/-! ## The program -/

/-- The host point of index `src` into the slot `d`. -/
def lkTo (src d : ℕ) : Stmt := .seq (block [.copyN 50071 src])
  (.seq lookStmt (block [.copyN d 50046, .copyN (d + 1) 50047, .copyN (d + 2) 50048]))

/-- The indices of the points before, at and after the top. -/
def nbrS : Stmt :=
  .seq (block [.addN 218050 218001 218013, .subN 218051 218050 218021,
    .addN 218052 218050 218021])
    (.ifLtN 218052 218012 .skip (block [.constN 218052 0]))

/-- The six sign tests (the bits of `IOrc.logI`). -/
def testsS : Stmt :=
  .seq (kbit 218053 218056 218059 2 170082) (.seq (kbit 218053 218056 218059 3 170083)
  (.seq (kbit 218056 218059 218056 0 170085) (.seq (kbit 218053 218056 218053 0 170086)
  (.seq (kbit 218056 218059 218056 1 170087) (kbit 218059 218056 218059 1 170088)))))

/-- The orientation bit for a top that is not the first vertex. -/
def bitI : Stmt :=
  .seq nbrS (.seq (lkTo 218051 218053) (.seq (lkTo 218050 218056) (.seq (lkTo 218052 218059)
    (.seq testsS (.seq (block [.constN 170012 0]) (.seq IOrc.logI
      (block [.copyN 218014 170075])))))))

/-- **The orientation bit** into `218014`. -/
def betaS : Stmt := .ifLtN 218020 218013 bitI (block [.constN 218014 0])

/-- The registers `betaS` writes. -/
def Bbit (r : ℕ) : Bool :=
  decide (50046 ≤ r ∧ r < 50080) || Bk r || decide (170000 ≤ r ∧ r < 170100) ||
    decide (r = 218014) || decide (218050 ≤ r ∧ r < 218062)

theorem wr_betaS : wr Bbit betaS = true := by
  have h : wr Bbit lookStmt = true := SweepPrim.wr_mono wr_lookStmt (fun r hr => by
    simp only [Bhost, Bool.or_eq_true, decide_eq_true_eq] at hr
    sio only [Bbit, Bool.or_eq_true, decide_eq_true_eq])
  have hk : ∀ a b d op dst, 170000 ≤ dst → dst < 170100 → wr Bbit (kbit a b d op dst) = true :=
    fun a b d op dst h1 h2 => SweepPrim.wr_mono (SweepPrim.wr_kbit _ _ _ _ _) (fun r hr => by
      simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      simp only [Bbit, Bool.or_eq_true, decide_eq_true_eq]
      rcases hr with hr | hr
      · exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
      · subst hr; left; left; right; omega)
  have hl : wr Bbit IOrc.logI = true := by
    sid only [IOrc.logI, IOrc.setB, wr, block, wrOK]
  simp only [betaS, bitI, nbrS, lkTo, testsS, wr, block, wrOK, h, hl,
    hk _ _ _ _ 170082 (by norm_num) (by norm_num), hk _ _ _ _ 170083 (by norm_num) (by norm_num),
    hk _ _ _ _ 170085 (by norm_num) (by norm_num), hk _ _ _ _ 170086 (by norm_num) (by norm_num),
    hk _ _ _ _ 170087 (by norm_num) (by norm_num), hk _ _ _ _ 170088 (by norm_num) (by norm_num),
    Bool.and_true, Bool.true_and]
  decide

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **A host point into a slot.** -/
theorem lkTo_exec {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) {src d p : ℕ} (hsrc : c.nreg src = p)
    (hp : p < (H.pts P.n).length) (hd : 50080 ≤ d) :
    ∃ c' k, Exec P W (lkTo src d) c c' k ∧ k ≤ 1737 ∧ HostEnv W HB H.length m₀ c' ∧
      SymPtIn c' d (pt H P.n p) ∧
      (∀ r, Bhost r = false → r ≠ d → r ≠ d + 1 → r ≠ d + 2 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  have hw := hE.wb
  obtain ⟨c₁, k₁, e₁, hk₁, v71, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50071 src])
      c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 50071 = p ∧ (∀ r, r ≠ 50071 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, by config_simp; exact hsrc, fun r hr => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right hr]
  have E₁ : HostEnv W HB H.length m₀ c₁ := ⟨e₁.wb_right, by rw [r₁ _ (by decide)]; exact hE.h60,
    by rw [r₁ _ (by decide)]; exact hE.h61, by rw [r₁ _ (by decide)]; exact hE.h67,
    by rw [r₁ _ (by decide)]; exact hE.h68, by rw [r₁ _ (by decide)]; exact hE.h69,
    by rw [m₁]; exact hE.mem⟩
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, s₂⟩ := look_pt E c₁ E₁ v71 hp
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN d 50046, .copyN (d + 1) 50047, .copyN (d + 2) 50048]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      SymPtIn c₃ d (pt H P.n p) ∧
      (∀ r, r ≠ d → r ≠ d + 1 → r ≠ d + 2 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem := by
    exec_block
    refine ⟨rfl, symPtIn_copy s₂ ?_ ?_ ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  have ex : Exec P W (lkTo src d) c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ⟨e₃.wb_right, ?_, ?_, ?_, ?_, ?_, by rw [m₃]; exact E₂.mem⟩, s₃,
    fun r h0 h1 h2 h3 => ?_, by rw [m₃, F₂.2.2.1, m₁]⟩
  all_goals try (rw [r₃ _ (by omega) (by omega) (by omega)])
  · exact E₂.h60
  · exact E₂.h61
  · exact E₂.h67
  · exact E₂.h68
  · exact E₂.h69
  · rw [F₂.1 r h0, r₁ r (by rintro rfl; simp [Bhost] at h0)]

/-- The indices of the neighbours of the top. -/
theorem nbrS_exec (c : Config) (hw : WordsBounded W c) {s T N : ℕ} (h01 : c.nreg 218001 = s)
    (h13 : c.nreg 218013 = T) (h21 : c.nreg 218021 = 1) (h12 : c.nreg 218012 = N)
    (_hT : 1 ≤ T) (hsT : s + T < N) (hNW : N ≤ W) :
    ∃ c' k, Exec P W nbrS c c' k ∧ k ≤ 6 ∧ c'.nreg 218050 = s + T ∧
      c'.nreg 218051 = s + T - 1 ∧ c'.nreg 218052 = (s + T + 1) % N ∧
      (∀ r, r ≠ 218050 → r ≠ 218051 → r ≠ 218052 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, v50, v51, v52, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 218050 218001 218013, .subN 218051 218050 218021, .addN 218052 218050 218021])
      c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 218050 = s + T ∧ c₁.nreg 218051 = s + T - 1 ∧
      c₁.nreg 218052 = s + T + 1 ∧
      (∀ r, r ≠ 218050 → r ≠ 218051 → r ≠ 218052 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    · config_simp; rwo [h01, h13]
    · config_simp; rwo [h01, h13, h21]
    refine ⟨rfl, by config_simp; rw [h01, h13], by config_simp; rw [h01, h13, h21],
      by config_simp; rw [h01, h13, h21], fun r a b d => ?_, rfl⟩
    simp only [Config.nreg_mk, upd, ite_eq_right a, ite_eq_right b, ite_eq_right d]
  have w₁ := e₁.wb_right
  have n₁ : c₁.nreg 218012 = N := by rw [r₁ _ (by norm_num) (by norm_num) (by norm_num), h12]
  by_cases hc : c₁.nreg 218052 < c₁.nreg 218012
  · refine spec_seq ⟨c₁, k₁, e₁, spec_ifLtN_true hc (spec_skip w₁ ⟨by omega, v50, v51, ?_, r₁, m₁⟩)⟩
    rw [v52, Nat.mod_eq_of_lt (by rw [v52, n₁] at hc; exact hc)]
  · refine spec_seq ⟨c₁, k₁, e₁, spec_ifLtN_false hc ?_⟩
    exec_block
    · omega
    refine ⟨by omega, by config_simp; exact v50, by config_simp; exact v51, ?_, fun r a b d => ?_,
      m₁⟩
    · config_simp
      rw [v52, n₁] at hc
      rw [show s + T + 1 = N by omega, Nat.mod_self]
    · simp only [Config.nreg_mk, upd, ite_eq_right d]; exact r₁ r a b d

theorem bkb_ne {r d : ℕ} (h : r < 10000 ∨ 10500 ≤ r) (hd : r ≠ d) : SweepPrim.Bkb d r = false := by
  simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]; exact ⟨by omega, hd⟩

/-- One kernel bit into a register of band `17`, with its frame. -/
theorem kbit17 (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b d op dst : ℕ} (ha : 218000 ≤ a) (hb : 218000 ≤ b) (hd : 218000 ≤ d)
    (hdst1 : 170000 ≤ dst) (hdst2 : dst < 170100) (hop : op ≤ 3) {sa sb sd : SymPt}
    (hla : sa.Lt P.n) (hlb : sb.Lt P.n) (hld : sd.Lt P.n) (hsa : SymPtIn c a sa)
    (hsb : SymPtIn c b sb) (hsd : SymPtIn c d sd) :
    ∃ c' k, Exec P W (kbit a b d op dst) c c' k ∧ k ≤ 241 ∧
      BitIs c' dst (SignTest op (sa.eval (Qof P)) (sb.eval (Qof P)) (sd.eval (Qof P))) ∧
      (∀ r, (r < 10000 ∨ 10500 ≤ r) → r ≠ dst → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec hG hW c hw (a := a) (b := b) (d := d) (op := op)
    (dst := dst) (by omega) (by omega) (by omega) (by omega) hop hla hlb hld hsa hsb hsd
  exact ⟨c', k, e, hk, ⟨b1, b2⟩, fun r h1 h2 => F.1 r (bkb_ne h1 h2), F.2.2.1⟩

/-- **The six sign tests** on the slots `218053` (`A`), `218056` (`V`), `218059` (`B`). -/
theorem testsS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {A V B : SymPt} (hA : A.Lt P.n) (hV : V.Lt P.n) (hB : B.Lt P.n) (sA : SymPtIn c 218053 A)
    (sV : SymPtIn c 218056 V) (sB : SymPtIn c 218059 B) :
    ∃ c' k, Exec P W testsS c c' k ∧ k ≤ 1446 ∧
      BitIs c' 170082 (0 < det (A.eval (Qof P)) (V.eval (Qof P)) (B.eval (Qof P))) ∧
      BitIs c' 170083 (det (A.eval (Qof P)) (V.eval (Qof P)) (B.eval (Qof P)) = 0) ∧
      BitIs c' 170085 ((V.eval (Qof P)).1 < (B.eval (Qof P)).1) ∧
      BitIs c' 170086 ((A.eval (Qof P)).1 < (V.eval (Qof P)).1) ∧
      BitIs c' 170087 ((V.eval (Qof P)).2 < (B.eval (Qof P)).2) ∧
      BitIs c' 170088 ((B.eval (Qof P)).2 < (V.eval (Qof P)).2) ∧
      (∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  -- slots survive every kernel bit
  have keep : ∀ {d d' : Config} {x : ℕ} {sp : SymPt}, SymPtIn d x sp → 218000 ≤ x →
      (∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → d'.nreg r = d.nreg r) →
      SymPtIn d' x sp := fun h hx hr => symPtIn_copy h (hr _ (by omega) (by omega))
        (hr _ (by omega) (by omega)) (hr _ (by omega) (by omega))
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁, m₁⟩ := kbit17 (op := 2) (dst := 170082) hG hW c hw
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hV hB
    sA sV sB
  have f₁ : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 => r₁ r h1 (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, r₂, m₂⟩ := kbit17 (op := 3) (dst := 170083) hG hW c₁ e₁.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hV hB
    (keep sA (by norm_num) f₁) (keep sV (by norm_num) f₁) (keep sB (by norm_num) f₁)
  have f₂ : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => (r₂ r h1 (by omega)).trans (f₁ r h1 h2)
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, r₃, m₃⟩ := kbit17 (op := 0) (dst := 170085) hG hW c₂ e₂.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hV hB hV
    (keep sV (by norm_num) f₂) (keep sB (by norm_num) f₂) (keep sV (by norm_num) f₂)
  have f₃ : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → c₃.nreg r = c.nreg r :=
    fun r h1 h2 => (r₃ r h1 (by omega)).trans (f₂ r h1 h2)
  obtain ⟨c₄, k₄, e₄, hk₄, b₄, r₄, m₄⟩ := kbit17 (op := 0) (dst := 170086) hG hW c₃ e₃.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hV hA
    (keep sA (by norm_num) f₃) (keep sV (by norm_num) f₃) (keep sA (by norm_num) f₃)
  have f₄ : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => (r₄ r h1 (by omega)).trans (f₃ r h1 h2)
  obtain ⟨c₅, k₅, e₅, hk₅, b₅, r₅, m₅⟩ := kbit17 (op := 1) (dst := 170087) hG hW c₄ e₄.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hV hB hV
    (keep sV (by norm_num) f₄) (keep sB (by norm_num) f₄) (keep sV (by norm_num) f₄)
  have f₅ : ∀ r, (r < 10000 ∨ 10500 ≤ r) → (r < 170082 ∨ 170089 ≤ r) → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => (r₅ r h1 (by omega)).trans (f₄ r h1 h2)
  obtain ⟨c₆, k₆, e₆, hk₆, b₆, r₆, m₆⟩ := kbit17 (op := 1) (dst := 170088) hG hW c₅ e₅.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hV hB
    (keep sB (by norm_num) f₅) (keep sV (by norm_num) f₅) (keep sB (by norm_num) f₅)
  have ex : Exec P W testsS c c₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  refine ⟨c₆, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, b₆, fun r h1 h2 => (r₆ r h1 (by omega)).trans
    (f₅ r h1 h2), by rw [m₆, m₅, m₄, m₃, m₂, m₁]⟩
  · refine b₁.of_eq ?_
    rw [r₆ _ (by norm_num) (by norm_num), r₅ _ (by norm_num) (by norm_num),
      r₄ _ (by norm_num) (by norm_num), r₃ _ (by norm_num) (by norm_num),
      r₂ _ (by norm_num) (by norm_num)]
  · refine b₂.of_eq ?_
    rw [r₆ _ (by norm_num) (by norm_num), r₅ _ (by norm_num) (by norm_num),
      r₄ _ (by norm_num) (by norm_num), r₃ _ (by norm_num) (by norm_num)]
  · refine b₃.of_eq ?_
    rw [r₆ _ (by norm_num) (by norm_num), r₅ _ (by norm_num) (by norm_num),
      r₄ _ (by norm_num) (by norm_num)]
  · refine b₄.of_eq ?_
    rw [r₆ _ (by norm_num) (by norm_num), r₅ _ (by norm_num) (by norm_num)]
  · refine b₅.of_eq ?_
    rw [r₆ _ (by norm_num) (by norm_num)]

/-- **The orientation bit**: `218014 := 1` iff the top offset `T` (`218013`) is positive and the
six sign tests at the host points `s + T - 1`, `s + T`, `(s + T + 1) mod N` give `BetaF`. -/
theorem betaS_exec {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) (h12 : c.nreg 218012 = (H.pts P.n).length)
    (h20 : c.nreg 218020 = 0) (h21 : c.nreg 218021 = 1)
    (hsT : c.nreg 218001 + c.nreg 218013 < (H.pts P.n).length) :
    ∃ c' k, Exec P W betaS c c' k ∧ k ≤ 7000 ∧ FrameB Bbit c c' ∧ c'.nreg 218014 ≤ 1 ∧
      (c'.nreg 218014 = 1 ↔ 0 < c.nreg 218013 ∧
        IOrc.BetaF ((pt H P.n (c.nreg 218001 + c.nreg 218013 - 1)).eval (Qof P))
          ((pt H P.n (c.nreg 218001 + c.nreg 218013)).eval (Qof P))
          ((pt H P.n ((c.nreg 218001 + c.nreg 218013 + 1) % (H.pts P.n).length)).eval
            (Qof P))) := by
  have hw := hE.wb
  have hWn := E.nW
  have hNW := E.hN
  obtain ⟨s, hs⟩ : ∃ s, c.nreg 218001 = s := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, c.nreg 218013 = T := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, (H.pts P.n).length = N := ⟨_, rfl⟩
  rw [hs, hT, hN] at hsT ⊢
  rw [hN] at h12 hNW
  unfold betaS
  by_cases hc : c.nreg 218020 < c.nreg 218013
  swap
  · have hT0 : T = 0 := by rwo [h20, hT] at hc
    refine spec_ifLtN_false hc ?_
    obtain ⟨c', k, e, hk, v⟩ : ∃ c' k, Exec P W (block [.constN 218014 0]) c c' k ∧ k = 1 ∧
        c'.nreg 218014 = 0 := by
      exec_block
      · omega
      exact ⟨rfl, by config_simp⟩
    exact ⟨c', k, e, by omega, exec_frameB (Exec.ifLtN_false hc e) wr_betaS, by omega,
      by rw [v]; simp [hT0]⟩
  have hT1 : 1 ≤ T := by rwo [h20, hT] at hc
  refine spec_ifLtN_true hc ?_
  -- the indices
  obtain ⟨c₁, k₁, e₁, hk₁, v50, v51, v52, r₁, m₁⟩ := nbrS_exec (P := P) c hw hs hT h21 h12 hT1
    hsT hNW
  have E₁ : HostEnv W HB H.length m₀ c₁ := ⟨e₁.wb_right,
    by rw [r₁ _ (by decide) (by decide) (by decide)]; exact hE.h60,
    by rw [r₁ _ (by decide) (by decide) (by decide)]; exact hE.h61,
    by rw [r₁ _ (by decide) (by decide) (by decide)]; exact hE.h67,
    by rw [r₁ _ (by decide) (by decide) (by decide)]; exact hE.h68,
    by rw [r₁ _ (by decide) (by decide) (by decide)]; exact hE.h69, by rw [m₁]; exact hE.mem⟩
  have hNpos : 0 < N := by omega
  -- the three points
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, sA₂, r₂, m₂⟩ := lkTo_exec E c₁ E₁ v51 (by omega)
    (d := 218053) (by norm_num)
  obtain ⟨c₃, k₃, e₃, hk₃, E₃, sV₃, r₃, m₃⟩ := lkTo_exec E c₂ E₂ (src := 218050) (p := s + T)
    (by rwx [r₂ _ (by decide) (by decide) (by decide) (by decide)])
    (by omega) (d := 218056) (by norm_num)
  obtain ⟨c₄, k₄, e₄, hk₄, E₄, sB₄, r₄, m₄⟩ := lkTo_exec E c₃ E₃ (src := 218052)
    (p := (s + T + 1) % N)
    (by rw [r₃ _ (by decide) (by decide) (by decide) (by decide),
      r₂ _ (by decide) (by decide) (by decide) (by decide)]; exact v52)
    (by rw [hN]; exact Nat.mod_lt _ hNpos) (d := 218059) (by norm_num)
  have sA₃ : SymPtIn c₃ 218053 (pt H P.n (s + T - 1)) := by
    refine symPtIn_copy sA₂ ?_ ?_ ?_
    all_goals exact r₃ _ (by decide) (by decide) (by decide) (by decide)
  have sA₄ : SymPtIn c₄ 218053 (pt H P.n (s + T - 1)) := by
    refine symPtIn_copy sA₃ ?_ ?_ ?_
    all_goals exact r₄ _ (by decide) (by decide) (by decide) (by decide)
  have sV₄ : SymPtIn c₄ 218056 (pt H P.n (s + T)) := by
    refine symPtIn_copy sV₃ ?_ ?_ ?_
    all_goals exact r₄ _ (by decide) (by decide) (by decide) (by decide)
  have hA := pt_lt (n := P.n) (i := s + T - 1) E.hwf E.npos (by rwo [hN])
  have hV := pt_lt (n := P.n) (i := s + T) E.hwf E.npos (by rwo [hN])
  have hB := pt_lt (n := P.n) (i := (s + T + 1) % N) E.hwf E.npos
    (by rw [hN]; exact Nat.mod_lt _ hNpos)
  -- the tests
  obtain ⟨c₅, k₅, e₅, hk₅, bpp, bp0, bbx, bax, bby, bby', r₅, m₅⟩ := testsS_exec E.good hWn c₄
    e₄.wb_right hA hV hB sA₄ sV₄ sB₄
  have w₅ := e₅.wb_right
  obtain ⟨c₆, k₆, e₆, hk₆, v12, r₆⟩ : ∃ c₆ k₆, Exec P W (block [.constN 170012 0]) c₅ c₆ k₆ ∧
      k₆ = 1 ∧ c₆.nreg 170012 = 0 ∧ c₆ = { c₅ with nreg := upd c₅.nreg 170012 0 } := by
    exec_block
    · omega
    exact ⟨rfl, by config_simp, rfl⟩
  have w₆ := e₆.wb_right
  have bit6 : ∀ {r : ℕ} {p : Prop}, BitIs c₅ r p → r ≠ 170012 → BitIs c₆ r p :=
    fun h hr => h.of_eq (by rw [r₆]; simp only [upd, ite_eq_right hr])
  obtain ⟨c₇, k₇, e₇, hk₇, b, hb, rfl, hbit⟩ := IOrc.logI_exec (P := P) c₆ w₆ v12 (by omega)
    (bit6 bpp (by decide)) (bit6 bp0 (by decide)) (bit6 bbx (by decide)) (bit6 bax (by decide))
    (bit6 bby (by decide)) (bit6 bby' (by decide)) (fun h0 hp => by rw [h0] at hp; exact lt_irrefl _ hp)
  have w₇ := e₇.wb_right
  obtain ⟨c₈, k₈, e₈, hk₈, v14⟩ : ∃ c₈ k₈, Exec P W (block [.copyN 218014 170075])
      { c₆ with nreg := upd c₆.nreg 170075 b } c₈ k₈ ∧ k₈ = 1 ∧ c₈.nreg 218014 = b := by
    exec_block
    exact ⟨rfl, by config_simp⟩
  have ex : Exec P W bitI c c₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  refine ⟨c₈, _, ex, by omega, exec_frameB (Exec.ifLtN_true hc ex) wr_betaS, by omega, ?_⟩
  rw [v14, hbit]
  unfold IOrc.BetaF
  exact ⟨fun h => ⟨hT1, h⟩, fun h => h.2⟩

end exec

end

end DrvP

end Chazelle.Core
