module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutStepR

/-!
# WP-G, part 19: the outcomes of one step of the main loop

* `SEnv`: the static facts of the core (the host and its layout, the grade table, the word
  bound); `swEnv_of`: the tables the sweeps read;
* `StepPost`: what a step from the walk vertex `c` achieves: pieces from `c` to `c + L`,
  `1 ≤ L ≤ lim`, and the step stops at the limit or at a breakpoint (or it is a single edge from
  a breakpoint);
* `single_post`, `up_post`, `dn_post`: a single edge, a climbing and a descending stretch.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

/-- **The static facts of the core.** -/
structure SEnv (O : OracleIface) (P : Polygon) (C : Chain) (H : Host) (Hh h γ : ℕ)
    (m₀ : ℕ → ℕ) (A₀ W : ℕ) : Prop where
  hP : C.P = H.poly (Qof P)
  hH : HostAt m₀ Hh H
  hHA : Hh + 3 * H.length + 4 ≤ A₀
  hwf : HostWF P.n H
  hlen : H.length ≤ 64
  hs : C.s < C.P.n
  hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀
  hcap : γ ≤ 2 ^ (m₀ h - 1)
  hAW : A₀ ≤ W
  hW : hostWords P.n ≤ W
  hn : 2 ≤ P.n
  hG : GoodEnv P

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

theorem SEnv.hQn (_S : SEnv O P C H Hh h γ m₀ A₀ W) : (Qof P).n = P.n := shear_n _ _

theorem SEnv.hN (S : SEnv O P C H Hh h γ m₀ A₀ W) : C.P.n = (H.pts P.n).length := by
  rw [S.hP, ← S.hQn]; simp [Host.poly, Polygon.n]

theorem SEnv.hNn (S : SEnv O P C H Hh h γ m₀ A₀ W) : (H.pts P.n).length ≤ 64 * P.n := by
  have := Host.pts_length_le S.hwf
  have := S.hlen
  nlinarith

theorem SEnv.hm2' (S : SEnv O P C H Hh h γ m₀ A₀ W) : 2 * C.m + 9 ≤ 128 * P.n + 8 := by
  have := C.m_lt
  have := S.hNn
  rw [S.hN] at *
  omega

theorem SEnv.hm2 (S : SEnv O P C H Hh h γ m₀ A₀ W) : 2 * C.m + 9 ≤ hostWords P.n := by
  have := S.hm2'
  unfold hostWords; omega

/-- **The tables of the sweeps.** -/
theorem swEnv_of (S : SEnv O P C H Hh h γ m₀ A₀ W) :
    SwEnv P.n W A₀ (m₀ (h + 2)) (m₀ (h + 3)) (m₀ (h + 1) + 2) (topGrade P.n) m₀ := by
  have hG := S.hR.holds
  obtain ⟨-, hpow, hhalf⟩ := grade_low S.hR
  refine ⟨fun x hx => ⟨hG.2.2.1 x hx, hhalf x hx⟩, fun j hj => ⟨?_, hpow j hj⟩, S.hAW⟩
  have := (hG.2.1.2.2.1 j hj).1
  Ξ show m₀ (h + 1) + 2 + j = m₀ (h + 1) + 2 + j from rfl
  exact this

theorem tg_ok (_hn : 2 ≤ P.n) : P.n - 1 ≤ 2 ^ topGrade P.n := Nat.le_pow_clog (⊛) _

/-- **The outcome of a step** from the walk vertex `c` (pieces `ps'`, length `L`). -/
structure StepPost (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps : List Pc) (A₀ W : ℕ)
    (m₀ : ℕ → ℕ) (B : ℕ → Prop) (c lim : ℕ) (d d' : Config) (ps' : List Pc) (L : ℕ) : Prop where
  hI : I (ps ++ ps') d'
  ch : Chained ⟨c, 0⟩ ps' ⟨c + L, 0⟩
  pv : ∀ pc ∈ ps', Pv pc
  len : ps'.length ≤ 2 * (Nat.log 2 L + 1)
  L1 : 1 ≤ L
  Llim : L ≤ lim
  brk : L = lim ∨ B (c - 6 + L) ∨ (L = 1 ∧ B (c - 6))
  r40 : d'.nreg 150040 = c + L
  keep : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → d'.nreg r = d.nreg r
  k90 : d'.nreg 150090 = 0
  k91 : d'.nreg 150091 = 1
  k92 : d'.nreg 150092 = 2
  k93 : d'.nreg 150093 = 3
  k96 : d'.nreg 150096 = 6
  wb : WordsBounded W d'
  mem : ∀ a, a < A₀ → d'.nmem a = m₀ a

/-- **A single edge from a breakpoint.** -/
theorem single_post (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (VPc P C m₀ h γ) I K)
    {B : ℕ → Prop} {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1) (h92 : e.nreg 150092 = 2)
    (h93 : e.nreg 150093 = 3) (h96 : e.nreg 150096 = 6)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc : c < 2 * C.m + 6) (hlim : 1 ≤ lim) (hb : B (c - 6)) (hI : I ps e) :
    ∃ d' k, Exec P W (single emit) e d' k ∧ k ≤ K + 7 ∧
      StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ B c lim d d' [sgPc c] 1 := by
  have hWc : c + 1 ≤ W := by have := S.hm2; have := S.hW; omega
  have hpv : VPc P C m₀ h γ (sgPc c) :=
    ⟨single_ok (P := P) (C := C) (m := m₀) (h := h) (γ := γ) 0 0 0 0 (c := c) (⋄),
      rfl, rfl, ⊚ sgPc⟩
  obtain ⟨d', k, ex, hk', hI', o40, kp, mem'⟩ := single_exec hE e hw h40 h91 hWc hI hpv
  have kk : ∀ r, 150089 ≤ r → r < 150100 → d'.nreg r = e.nreg r := fun r h1 h2 =>
    kp r (Or.inr ⟨⋄, h2⟩) (by omega)
  refine ⟨d', k, ex, hk', ⟨hI', ⟨rfl, rfl⟩, fun p hp => by
      simp only [List.mem_singleton] at hp; rw [hp]; exact hpv, ✓, le_rfl, hlim,
    Or.inr (Or.inr ⟨rfl, hb⟩), o40, fun r h1 h2 h3 => (kp r (Or.inl ⟨h1, h2⟩) h3).trans
      (hk r h1 h2 h3), by rw [kk _ (⋄) (by omega)]; exact h90,
    by rw [kk _ (⋄) (by omega)]; exact h91, by rw [kk _ (by omega) (by omega)]; exact h92,
    by rw [kk _ (⋄) (by omega)]; exact h93, by rw [kk _ (by omega) (by omega)]; exact h96,
    ex.wb_right, fun a ha => by rw [mem' a ha]; exact hm a ha⟩⟩

/-- `(a + t + L) mod n` from `q = (a + t) mod n` without wrap. -/
theorem mod_add_of {n a t q L : ℕ} (hq : (a + t) % n = q) (hqL : q + L < n) :
    (a + (t + L)) % n = q + L := by
  rw [← Nat.add_assoc, Nat.add_mod, hq, Nat.mod_eq_of_lt (show L < n by omega),
    Nat.mod_eq_of_lt hqL]

/-- `(a + t - L) mod n` from `q = (a + t) mod n`, `L ≤ q`, `L ≤ t`. -/
theorem mod_sub_of {n a t q L : ℕ} (hn : 0 < n) (hq : (a + t) % n = q) (hLq : L ≤ q)
    (hLt : L ≤ t) : (a + (t - L)) % n = q - L := by
  have e := Nat.div_add_mod (a + t) n
  rw [hq] at e
  have e2 : a + (t - L) = n * ((a + t) / n) + (q - L) := ⋄
  Ξ e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt (a + t) hn; omega)

/-- **A climbing stretch** from the walk vertex `c` (tour position `i = c - 6`, host point in the
run `H[r] = run a ℓ` at offset `t < ℓ`, `q = (a + t) mod n`). -/
theorem up_post (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (VPc P C m₀ h γ) I K)
    {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim J r a ℓ t q : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1)
    (h34 : e.nreg 150034 = m₀ (h + 2)) (h35 : e.nreg 150035 = m₀ (h + 3))
    (h36 : e.nreg 150036 = m₀ (h + 1) + 2)
    (h23 : e.nreg 150023 = C.m) (h61 : e.nreg 150061 = J) (h69 : e.nreg 150069 = ℓ)
    (h66 : e.nreg 150066 = t) (h27 : e.nreg 150027 = P.n) (h70 : e.nreg 150070 = q)
    (h72 : e.nreg 150072 = lim)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc6 : 6 ≤ c) (hlim1 : 1 ≤ lim) (hlim : c + lim ≤ 2 * C.m + 6) (hlimγ : lim ≤ γ)
    (hJ : tJ C (c - 6) = J) (hJm : J < C.m) (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C (c - 6) = NFLoc.preLen (Qof P).n H r + t) (ht : t < ℓ)
    (hq : (a + t) % (Qof P).n = q) (hq1 : q + 1 < P.n) (hI : I ps e) :
    ∃ d' k L ps', Exec P W (upStretch emit) e d' k ∧
      k ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 40 ∧
      StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c lim d d' ps' L := by
  have hQn := S.hQn
  set L := min (min (min (C.m - J) (ℓ - t)) (P.n - q - 1)) lim with hL
  have hL1 : 1 ≤ L := by omega
  have hLl : L ≤ lim := by omega
  have hi : c - 6 + L ≤ 2 * C.m := by omega
  have hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx (c + d) = (Qof P).vtx (q + d) := by
    intro d hd
    have := run_up C S.hP (i := c - 6) (d := d) (by omega) (by omega) hr hrun hu (by omega)
      (by rw [hq, hQn]; omega)
    rw [show c - 6 + d + 6 = c + d by omega, hq] at this
    exact this
  have hblk := upBlocks_of (O := O) S.hR S.hAW (W := W) hwalk hc6 (by omega) (by omega)
    (by omega) S.hcap
  have hW' : 5 * P.n + 6 ≤ W := by have := S.hW; unfold hostWords at this; omega
  have hcW : c + lim + 2 ≤ W := by have := S.hm2; have := S.hW; omega
  obtain ⟨d', k, ps', ex, hk', hI', hch, hv, hlen, o40, kp, a90, a91, a92, a93, a96, w', m'⟩ :=
    upStretch_exec (hE.mono fun pc hp => hp) (swEnv_of S) e hw hm h90 h91 h34 h35 h36 h23 h61
      h69 h66 h27 h70 h72 h40 hI hq1 hJm ht (tg_ok S.hn) hcW hW' hblk
  have hLγ : Nat.log 2 L ≤ Nat.log 2 γ := Nat.log_mono_right (by omega)
  have hk'' : k ≤ (2 * K + 90) * (Nat.log 2 L + 1) + 40 := hk'
  refine ⟨d', k, L, ps', ex, le_trans hk'' (by
      have := Nat.mul_le_mul_left (2 * K + 90) (Nat.add_le_add_right hLγ 1); omega),
    ⟨hI', hch, hv, hlen, hL1, hLl, ?_, o40, fun r h1 h2 h3 => (kp r h1 h2 h3).trans (hk r h1 h2 h3),
      a90, a91, a92, a93, a96, w', m'⟩⟩
  -- the breakpoint
  by_cases h1 : L = lim
  · exact Or.inl h1
  right; left
  have hlt : min (min (C.m - J) (ℓ - t)) (P.n - q - 1) < lim := by omega
  have hLe : L = min (min (C.m - J) (ℓ - t)) (P.n - q - 1) := by omega
  rcases (show L = C.m - J ∨ L = ℓ - t ∨ L = P.n - q - 1 by omega) with h2 | h2 | h2
  · right; left
    rw [tJ_add C (by rw [hJ]; omega), hJ]; omega
  · have hu' := uOf_up C S.hP (i := c - 6) (d := L) (by omega) hr hrun hu (by omega)
    exact brk_run C hr hrun (t := t + L) hu' (by omega) (Or.inr (Or.inl (by omega)))
  · have hu' := uOf_up C S.hP (i := c - 6) (d := L) (by omega) hr hrun hu (by omega)
    refine brk_run C hr hrun (t := t + L) hu' (by omega) (Or.inr (Or.inr (Or.inr ?_)))
    rw [mod_add_of hq (by rw [hQn]; omega), hQn]; omega

/-- **A descending stretch** from the walk vertex `c` (host point in the run `H[r] = run a ℓ` at
offset `0 < t`, `0 < q = (a + t) mod n`). -/
theorem dn_post (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (VPc P C m₀ h γ) I K)
    {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim J r a ℓ t q : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1)
    (h34 : e.nreg 150034 = m₀ (h + 2)) (h35 : e.nreg 150035 = m₀ (h + 3))
    (h36 : e.nreg 150036 = m₀ (h + 1) + 2)
    (h29 : e.nreg 150029 = 2 * C.m) (h61 : e.nreg 150061 = J)
    (h66 : e.nreg 150066 = t) (h70 : e.nreg 150070 = q)
    (h72 : e.nreg 150072 = lim)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc6 : 6 ≤ c) (hlim1 : 1 ≤ lim) (hlim : c + lim ≤ 2 * C.m + 6) (hlimγ : lim ≤ γ)
    (hJ : tJ C (c - 6) = J) (hJm : C.m ≤ J) (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C (c - 6) = NFLoc.preLen (Qof P).n H r + t) (ht : t ≤ ℓ) (ht0 : 0 < t)
    (hq : (a + t) % (Qof P).n = q) (hq0 : 0 < q) (hI : I ps e) :
    ∃ d' k L ps', Exec P W (dnStretch emit) e d' k ∧
      k ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 40 ∧
      StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c lim d d' ps' L := by
  have hQn := S.hQn
  have hn : 0 < (Qof P).n := by rw [hQn]; have := S.hn; omega
  have hqn : q < P.n := by rw [← hQn, ← hq]; exact Nat.mod_lt _ hn
  have hJlt : J < 2 * C.m := by rw [← hJ]; exact tJ_lt C _
  set L := min (min (min (2 * C.m - J) t) q) lim with hL
  have hL1 : 1 ≤ L := by omega
  have hLl : L ≤ lim := by omega
  have hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx (c + d) = (Qof P).vtx (q - d) := by
    intro d hd
    have := run_down C S.hP (i := c - 6) (d := d) (by omega) (by omega) (by omega) hr hrun hu
      ht (by omega) (by rw [hq]; omega) hn
    rw [show c - 6 + d + 6 = c + d by omega, hq] at this
    exact this
  have hblk := dnBlocks_of (O := O) S.hR S.hAW (W := W) hwalk hc6 (by omega) hqn (by omega)
    (by omega) S.hcap
  have hW' : 5 * P.n + 6 ≤ W := by have := S.hW; unfold hostWords at this; omega
  have hcW : c + lim + 2 ≤ W := by have := S.hm2; have := S.hW; omega
  obtain ⟨d', k, ps', ex, hk', hI', hch, hv, hlen, o40, kp, a90, a91, a92, a93, a96, w', m'⟩ :=
    dnStretch_exec (hE.mono fun pc hp => hp) (swEnv_of S) e hw hm h90 h91 h34 h35 h36 h29 h61
      h66 h70 h72 h40 hI hqn (tg_ok S.hn) hcW hW' hblk
  have hLγ : Nat.log 2 L ≤ Nat.log 2 γ := Nat.log_mono_right (by omega)
  have hk'' : k ≤ (2 * K + 90) * (Nat.log 2 L + 1) + 40 := hk'
  refine ⟨d', k, L, ps', ex, le_trans hk'' (by
      have := Nat.mul_le_mul_left (2 * K + 90) (Nat.add_le_add_right hLγ 1); omega),
    ⟨hI', hch, hv, hlen, hL1, hLl, ?_, o40, fun r h1 h2 h3 => (kp r h1 h2 h3).trans (hk r h1 h2 h3),
      a90, a91, a92, a93, a96, w', m'⟩⟩
  by_cases h1 : L = lim
  · exact Or.inl h1
  right; left
  rcases (show L = 2 * C.m - J ∨ L = t ∨ L = q by omega) with h2 | h2 | h2
  · left
    have e1 : tJ C (c - 6 + L) = (tJ C (c - 6) + L) % (2 * C.m) := by
      unfold tJ; rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [e1, hJ, show J + L = 2 * C.m by omega, Nat.mod_self]
  · have hu' := uOf_down C S.hP (i := c - 6) (d := L) (by omega) (by omega) hr hrun hu ht
      (by omega)
    exact brk_run C hr hrun (t := t - L) hu' (by omega) (Or.inl (by omega))
  · have hu' := uOf_down C S.hP (i := c - 6) (d := L) (by omega) (by omega) hr hrun hu ht
      (by omega)
    refine brk_run C hr hrun (t := t - L) hu' (by omega) (Or.inr (Or.inr (Or.inl ?_)))
    rw [mod_sub_of hn hq (by omega) (by omega)]; omega

end

end ShootCut

end Chazelle.Core
