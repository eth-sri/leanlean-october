module

public import Chazelle.Core.ShootCutKey
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-G, part 25: the symbolic point of a walk vertex

`vtxPt_exec`: for a walk vertex `v` of the double boundary (`6 ≤ v ≤ 2m + 6`), `vtxPt` leaves in
`150045 …` the symbolic point of its host point, whose point is the walk vertex.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

/-- The registers written by `vtxPt`. -/
def Bvp : ℕ → Bool := Bl [150045, 150046, 150047, 150060, 150061, 150062, 150063, 150064,
  150065, 150066, 150067, 150068, 150069, 150073, 150074, 150075, 150077, 150078, 150079]

theorem wr_vtxPt : wr Bvp vtxPt = true := by decide

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- A chain descriptor depends only on the memory below its end. -/
theorem chainDesc_agree' {m m' : ℕ → ℕ} {B E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (h : ChainDescAt m B Q H C) (hB : B + 5 ≤ E) (hH : m B + 3 * H.length + 4 ≤ E)
    (hm : ∀ a, a < E → m' a = m a) : ChainDescAt m' B Q H C := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, h2, by rwx [hm _ (by omega)], by rwx [hm _ (by omega)],
    by rwx [hm _ (by omega)], by rwx [hm _ (by omega)]⟩
  rw [hm _ (by omega)]
  exact hostAt_agree' h1 hH hm

/-- **The symbolic point of a walk vertex** of the double boundary. -/
theorem vtxPt_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) (d : Config) (hw : WordsBounded W d)
    (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (R : ChainRegs C (H.pts P.n).length Hh d)
    (h27 : d.nreg 150027 = P.n) (h92 : d.nreg 150092 = 2) {v : ℕ} (h44 : d.nreg 150044 = v)
    (hv6 : 6 ≤ v) (hv : v ≤ 2 * C.m + 6) :
    ∃ d' k sp, Exec P W vtxPt d d' k ∧ k ≤ 22 * H.length + 40 ∧ FrameB Bvp d d' ∧
      SymPtIn d' 150045 sp ∧ sp.Lt P.n ∧ sp.eval (Qof P) = (chainModel C).W.vtx v := by
  have hQn := S.hQn
  have hN := S.hN
  have hNn := S.hNn
  have hWn := S.hW
  unfold hostWords at hWn
  have hmN := C.m_lt
  have hsN := S.hs
  rw [hN] at hmN hsN
  have hHA := S.hHA
  have hAW := S.hAW
  have hH' : HostAt d.nmem Hh H := hostAt_agree' S.hH hHA fun a ha => hm a (by omega)
  obtain ⟨d₁, k₁, ex₁, hk₁, fr₁, o60, o61, o62, o63, o63', o64, found⟩ :=
    locV_exec (P := P) (W := W) (v := v) d hw rfl hH' R h44 hv6 hv hsN hmN (by omega) (by omega)
  obtain ⟨hr, hp1, hp2, h66, h67, h68, h69⟩ := found
  set r := d₁.nreg 150065 with hrdef
  set u := d₁.nreg 150064 with hudef
  have g₁ : ∀ x, (x < 150060 ∨ 150080 ≤ x) → d₁.nreg x = d.nreg x := fun x hx =>
    fr₁.1 x (bloc_false hx)
  have hlo : Hh + 3 + 3 * r < A₀ := by omega
  have e67 : d₁.nreg 150067 = m₀ (Hh + 1 + 3 * r) := by rw [h67, hm _ (by omega)]
  have e68 : d₁.nreg 150068 = m₀ (Hh + 2 + 3 * r) := by rw [h68, hm _ (by omega)]
  have e69 : d₁.nreg 150069 = m₀ (Hh + 3 + 3 * r) := by rw [h69, hm _ (by omega)]
  obtain ⟨hit, hc2⟩ := NFLoc.hostAt_item S.hH hr
  have hsucc := NFLoc.preLen_succ P.n H hr
  have hwf := S.hwf _ (List.getElem_mem hr)
  -- the walk vertex is the host point
  have hwalk : ∀ sp, (H.pts P.n)[u]? = some sp → sp.eval (Qof P) = (chainModel C).W.vtx v := by
    intro sp hsp
    have := walk_vtx C (v - 6) (by omega)
    rw [show v - 6 + 6 = v by omega] at this
    rw [this]
    refine (NFLoc.chain_vertex_host C S.hP _ ?_).symm
    rw [hQn, hN, show C.s + sideE C.m (tJ C (v - 6)) = C.s + sideE C.m
      ((C.sideS C.sideBeta + (v - 6)) % (2 * C.m)) from rfl, ← o64]
    exact hsp
  have hpts : (H.pts P.n)[u]? = (H[r].pts P.n)[u - NFLoc.preLen P.n H r]? :=
    NFLoc.pts_getElem? P.n H hr hp1 (by omega)
  have w₁ := ex₁.wb_right
  have b91 : d₁.nreg 150091 = 1 := by rw [g₁ _ (by omega), R.h91]
  have b92 : d₁.nreg 150092 = 2 := by rw [g₁ _ (by omega), h92]
  have b27 : d₁.nreg 150027 = P.n := by rw [g₁ _ (by omega), h27]
  have fin : ∀ (d₂ : Config) (k₂ : ℕ) (sp : SymPt), Exec P W (.ifLtN 150067 150091
      (.seq (.instr (.addN 150075 150068 150066))
        (.seq (.ifLtN 150075 150027 (.instr (.copyN 150046 150075))
            (.instr (.subN 150046 150075 150027)))
          (.instr (.constN 150045 0))))
      (.ifLtN 150067 150092 (block [.constN 150045 0, .copyN 150046 150068])
        (block [.constN 150045 1, .copyN 150046 150068, .copyN 150047 150069]))) d₁ d₂ k₂ →
      k₂ ≤ 8 → SymPtIn d₂ 150045 sp → sp.Lt P.n → (H.pts P.n)[u]? = some sp →
      ∃ d' k sp, Exec P W vtxPt d d' k ∧ k ≤ 22 * H.length + 40 ∧ FrameB Bvp d d' ∧
        SymPtIn d' 150045 sp ∧ sp.Lt P.n ∧ sp.eval (Qof P) = (chainModel C).W.vtx v := by
    intro d₂ k₂ sp ex₂ hk₂ hin hlt hsp
    have ex : Exec P W vtxPt d d₂ (k₁ + k₂) := by unfold vtxPt; exact .seq ex₁ ex₂
    exact ⟨d₂, _, sp, ex, by omega, exec_frameB ex wr_vtxPt, hin, hlt, hwalk sp hsp⟩
  by_cases hc0 : d₁.nreg 150067 < d₁.nreg 150091
  · -- a run
    have hk0 : m₀ (Hh + 1 + 3 * r) = 0 := by rwo [← e67]
    set a := m₀ (Hh + 2 + 3 * r)
    set ℓ := m₀ (Hh + 3 + 3 * r)
    have hrun : H[r] = .run a ℓ := by rwr [hit, hk0]
    rw [hrun] at hwf hsucc hpts
    simp [NFLoc.itemCnt] at hsucc
    obtain ⟨ha, hℓ⟩ := hwf
    set t := u - NFLoc.preLen P.n H r
    have ht : t ≤ ℓ := by omega
    obtain ⟨d₂, k₂, ex₂, hk₂, o45, o46⟩ : ∃ d₂ k₂, Exec P W
        (.seq (.instr (.addN 150075 150068 150066))
          (.seq (.ifLtN 150075 150027 (.instr (.copyN 150046 150075))
              (.instr (.subN 150046 150075 150027)))
            (.instr (.constN 150045 0)))) d₁ d₂ k₂ ∧ k₂ ≤ 5 ∧
        d₂.nreg 150045 = 0 ∧ d₂.nreg 150046 = (a + t) % P.n := by
      refine spec_seq (spec_instr (Exec.addN w₁ _ _ _ (by rwo [e68, h66])) fun w' => ?_)
      by_cases hlt : a + t < P.n
      · refine spec_seq (spec_ifLtN_true (by config_simp; rwx [e68, h66, b27])
          (spec_instr (Exec.copyN w' _ _) fun w'' => ?_))
        refine spec_instr (Exec.constN w'' _ _ (by omega)) fun _ => ⟨by omega, by config_simp, ?_⟩
        config_simp; rw [e68, h66, Nat.mod_eq_of_lt hlt]
      · refine spec_seq (spec_ifLtN_false (by config_simp; rwx [e68, h66, b27])
          (spec_instr (Exec.subN w' _ _ _) fun w'' => ?_))
        refine spec_instr (Exec.constN w'' _ _ (by omega)) fun _ => ⟨by omega, by config_simp, ?_⟩
        config_simp
        rw [e68, h66, b27, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    exact fin d₂ (k₂ + 1) (.vtx ((a + t) % P.n)) (.ifLtN_true hc0 ex₂) (by omega) ⟨o45, o46⟩
      (Nat.mod_lt _ (by have := S.hn; omega)) (by rw [hpts, NFLoc.run_pts_getElem? _ _ _ ht])
  · have hk1 : 1 ≤ m₀ (Hh + 1 + 3 * r) := by rwo [← e67]
    rcases hH : H[r] with ⟨a, ℓ⟩ | x
    · exfalso; rw [hit] at hH; unfold NFLoc.itemOf at hH; rw [ite_eq_right (by omega)] at hH
      split_ifs at hH
    rw [hH] at hwf hsucc hpts
    simp [NFLoc.itemCnt] at hsucc
    have ht0 : u - NFLoc.preLen P.n H r = 0 := by omega
    rw [ht0] at hpts
    have hsp : (H.pts P.n)[u]? = some x := by rwr [hpts]
    by_cases hc1 : d₁.nreg 150067 < d₁.nreg 150092
    · have hx : x = .vtx (m₀ (Hh + 2 + 3 * r)) := by
        rw [hit] at hH; unfold NFLoc.itemOf at hH
        rw [ite_eq_right (by omega), ite_eq_left (by omega)] at hH
        exact (HostItem.pt.inj hH).symm
      obtain ⟨d₂, k₂, ex₂, hk₂, o45, o46⟩ : ∃ d₂ k₂, Exec P W
          (block [.constN 150045 0, .copyN 150046 150068]) d₁ d₂ k₂ ∧ k₂ = 2 ∧
          d₂.nreg 150045 = 0 ∧ d₂.nreg 150046 = m₀ (Hh + 2 + 3 * r) := by
        exec_block
        all_goals first | omega | skip
        exact ⟨rfl, by config_simp, by config_simp; exact e68⟩
      rw [hx] at hsp hwf
      exact fin d₂ _ (.vtx (m₀ (Hh + 2 + 3 * r))) (.ifLtN_false hc0 (.ifLtN_true hc1 ex₂))
        (by omega) ⟨o45, o46⟩ hwf hsp
    · have hx : x = .onEdge (m₀ (Hh + 2 + 3 * r)) (m₀ (Hh + 3 + 3 * r)) := by
        rw [hit] at hH; unfold NFLoc.itemOf at hH
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hH
        exact (HostItem.pt.inj hH).symm
      obtain ⟨d₂, k₂, ex₂, hk₂, o45, o46, o47⟩ : ∃ d₂ k₂, Exec P W
          (block [.constN 150045 1, .copyN 150046 150068, .copyN 150047 150069]) d₁ d₂ k₂ ∧
          k₂ = 3 ∧ d₂.nreg 150045 = 1 ∧ d₂.nreg 150046 = m₀ (Hh + 2 + 3 * r) ∧
          d₂.nreg 150047 = m₀ (Hh + 3 + 3 * r) := by
        exec_block
        all_goals first | omega | skip
        exact ⟨rfl, by config_simp, by config_simp; exact e68, by config_simp; exact e69⟩
      rw [hx] at hsp hwf
      exact fin d₂ _ (.onEdge (m₀ (Hh + 2 + 3 * r)) (m₀ (Hh + 3 + 3 * r)))
        (.ifLtN_false hc0 (.ifLtN_false hc1 ex₂)) (by omega) ⟨o45, o46, o47⟩ hwf hsp

theorem wr_posP : wr Scr posP = true := by decide

theorem wr_keyLess : wr Scr keyLess = true := by decide

/-- **The direction code of a walk edge** into `150059`. -/
theorem dirP_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ} (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C)
    (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh) (d : Config) (hw : WordsBounded W d)
    (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h00 : d.nreg 150000 = MD) {p : ℕ}
    (h49 : d.nreg 150049 = p) (hp : p < 2 * C.m + 7) :
    ∃ d' k, Exec P W dirP d d' k ∧ k ≤ 70 * H.length + 610 ∧
      d'.nreg 150059 = NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 ∧
      (∀ r, (r < 150059 ∨ 150060 ≤ r) → Bdir r = false → r ≠ 50000 → r ≠ 50002 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  have hWn := S.hW
  unfold hostWords at hWn
  have hN := S.hN
  have hNn := S.hNn
  obtain ⟨d₁, k₁, e₁, hk₁, o0, o2, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.copyN 50000 150000, .copyN 50002 150049]) d d₁ k₁ ∧ k₁ = 2 ∧
      d₁.nreg 50000 = MD ∧ d₁.nreg 50002 = p ∧
      (∀ r, r ≠ 50000 → r ≠ 50002 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    refine ⟨rfl, by config_simp; exact h00, by config_simp; exact h49, fun r h1 h2 => ?_, rfl⟩
    simp [upd]; split_ifs <;> first | rfl | omega
  have hC : ChainDescAt d₁.nmem (d₁.nreg 50000 + 1) (Qof P) H C := by
    rw [o0, m₁]
    exact chainDesc_agree' hD (by omega) (by rw [hHh]; exact le_trans S.hHA le_rfl)
      (fun a ha => hm a (by have := S.hHA; rwo [hHh] at *))
  obtain ⟨d₂, k₂, e₂, hk₂, fr₂, o₂⟩ := NFLoc.chainDir_exec (P := P) S.hG (by omega) d₁ e₁.wb_right
    hC (by rw [o0]; have := S.hAW; omega)
    (by rw [o0, m₁, hm _ (by omega), hHh]; have := S.hHA; have := S.hAW; omega) S.hwf S.hs
    (by rwo [hN]) (by rwx [o2])
  have e₃ := Exec.copyN (P := P) e₂.wb_right 150059 10502
  refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by have := S.hlen; omega, ?_,
    fun r h1 h2 h3 h4 => ?_, ?_⟩
  · config_simp; rwr [o₂, o2]
  · config_simp
    rw [upd_other _ _ _ (by omega), fr₂.1 r h2, r₁ r h3 h4]
  · config_simp; rw [fr₂.2.2.1, m₁]

theorem dirOf_eq_zero {a b : ℝ} : NFLoc.dirOf a b = 0 ↔ a = b := by
  unfold NFLoc.dirOf
  constructor
  · intro h; split_ifs at h with h1 h2 <;> first | omega | (exact le_antisymm (not_lt.1 h2) (not_lt.1 h1))
  · rintro rfl; simp

/-- **Is the parameter of the position `⟨p, j + 1⟩` positive?** (`6 ≤ p ≤ 2m + 6`): `150089`
is `1` iff the walk edge is not horizontal and the height of `Q.vtx j` differs from the height of
the start of the edge. -/
theorem posP_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : ChainRegs C (H.pts P.n).length Hh d) (h00 : d.nreg 150000 = MD)
    (h27 : d.nreg 150027 = P.n) (h90 : d.nreg 150090 = 0) (h92 : d.nreg 150092 = 2) {p j : ℕ}
    (h49 : d.nreg 150049 = p) (h76 : d.nreg 150076 = j) (hp6 : 6 ≤ p) (hp : p ≤ 2 * C.m + 6)
    (hj : j < P.n) :
    ∃ d' k, Exec P W posP d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        ((chainModel C).W.vtx p).2 ≠ ((Qof P).vtx j).2)) ∧ d'.nreg 150089 ≤ 1 := by
  have hWn := S.hW
  unfold hostWords at hWn
  obtain ⟨d₁, k₁, ex₁, hk₁, o59, r₁, m₁⟩ := dirP_exec S hD hMD hHh d hw hm h00 h49 (by omega)
  have g₁ : ∀ r, 150000 ≤ r → r < 150100 → r ≠ 150059 → d₁.nreg r = d.nreg r :=
    fun r h1 h2 h3 => r₁ r (by omega) (by ufs Bdir; omega) (by omega) (by omega)
  have w₁ := ex₁.wb_right
  have hfin : ∀ (d' : Config) (k : ℕ), Exec P W posP d d' k → k ≤ 100 * H.length + 2000 →
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        ((chainModel C).W.vtx p).2 ≠ ((Qof P).vtx j).2)) → d'.nreg 150089 ≤ 1 →
      ∃ d' k, Exec P W posP d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
        (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
          ((chainModel C).W.vtx p).2 ≠ ((Qof P).vtx j).2)) ∧ d'.nreg 150089 ≤ 1 :=
    fun d' k ex hk h1 h2 => ⟨d', k, ex, hk, exec_frameB ex wr_posP, h1, h2⟩
  by_cases h59 : d₁.nreg 150059 < d₁.nreg 150091
  · have hz : NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 = 0 := by
      rwo [g₁ 150091 (by omega) (by omega) (by omega), R.h91, o59] at h59
    have e₂ := Exec.constN (P := P) w₁ 150089 0 (by omega)
    refine hfin _ _ (by unfold posP; exact .seq ex₁ (.ifLtN_true h59 e₂)) (by omega) ?_
      (by config_simp <;> omega)
    config_simp
    rw [dirOf_eq_zero] at hz
    simp [zero_ne_one, false_iff, not_and, not_not]
    intro h; exact absurd hz h
  · have hnz : NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 ≠ 0 := by
      rwo [g₁ 150091 (by omega) (by omega) (by omega), R.h91, o59] at h59
    rw [Ne, dirOf_eq_zero] at hnz
    have e₂ := Exec.copyN (P := P) w₁ 150044 150049
    set d₂ := ({ d₁ with nreg := upd d₁.nreg 150044 (d₁.nreg 150049) } : Config) with hd₂
    have g₂ : ∀ r, 150000 ≤ r → r < 150100 → r ≠ 150059 → r ≠ 150044 → d₂.nreg r = d.nreg r :=
      fun r h1 h2 h3 h4 => by simp [hd₂, upd]; rw [ite_eq_right h4]; exact g₁ r h1 h2 h3
    have R₂ : ChainRegs C (H.pts P.n).length Hh d₂ := R.of_frame fun r hr => g₂ r (by
      sio only [List.mem_cons, List.not_mem_nil, or_false] at hr) (by
      sio only [List.mem_cons, List.not_mem_nil, or_false] at hr) (by
      sio only [List.mem_cons, List.not_mem_nil, or_false] at hr) (by
      sio only [List.mem_cons, List.not_mem_nil, or_false] at hr)
    obtain ⟨d₃, k₃, sp, ex₃, hk₃, fr₃, in₃, lt₃, ev₃⟩ := vtxPt_exec S d₂ e₂.wb_right
      (fun a ha => by rw [show d₂.nmem = d₁.nmem from rfl, m₁]; exact hm a ha) R₂
      (by rw [g₂ _ (by omega) (by omega) (by omega) (by omega), h27])
      (by rw [g₂ _ (by omega) (by omega) (by omega) (by omega), h92])
      (by simp [hd₂, upd]; rw [g₁ _ (by omega) (by omega) (by omega), h49]) hp6 hp
    have g₃ : ∀ r, Bvp r = false → d₃.nreg r = d₂.nreg r := fr₃.1
    have b76 : d₃.nreg 150076 = j := by
      rw [g₃ _ (by decide), g₂ _ (by omega) (by omega) (by omega) (by omega), h76]
    have b90 : d₃.nreg 150090 = 0 := by
      rw [g₃ _ (by decide), g₂ _ (by omega) (by omega) (by omega) (by omega), h90]
    obtain ⟨d₄, k₄, ex₄, hk₄, a₄, b₄, r₄⟩ : ∃ d₄ k₄, Exec P W
        (block [.copyN 50040 150045, .copyN 50041 150046, .copyN 50042 150047, .constN 50043 0,
          .copyN 50044 150076]) d₃ d₄ k₄ ∧ k₄ = 5 ∧ SymPtIn d₄ 50040 sp ∧
        SymPtIn d₄ 50043 (.vtx j) ∧ d₄.nreg 150090 = 0 := by
      have w₃ := ex₃.wb_right
      exec_block
      all_goals first | omega | skip
      exact ⟨rfl, NFLoc.symPtIn_copy in₃ (by config_simp) (by config_simp) (by config_simp),
        ⟨by config_simp, by config_simp; exact b76⟩, by config_simp; exact b90⟩
    obtain ⟨d₅, k₅, ex₅, hk₅, fr₅, o₅⟩ := NFLoc.dirTail_exec (P := P) S.hG (by omega) d₄
      ex₄.wb_right lt₃ (show (SymPt.vtx j).Lt P.n from hj) a₄ b₄
    have e₆ := Exec.copyN (P := P) ex₅.wb_right 150089 10502
    set d₆ := ({ d₅ with nreg := upd d₅.nreg 150089 (d₅.nreg 10502) } : Config) with hd₆
    have o89 : d₆.nreg 150089 = NFLoc.dirOf ((chainModel C).W.vtx p).2 ((Qof P).vtx j).2 := by
      simp [hd₆, upd, ↓reduceIte]; rwr [o₅, ev₃]
    have c90 : d₆.nreg 150090 = 0 := by
      simp only [hd₆, upd]; rw [ite_eq_right (by omega), fr₅.1 _ (by decide), r₄]
    have w₆ := e₆.wb_right
    have ex_pre : ∀ (d₇ : Config) (k₇ : ℕ), Exec P W
        (.ifLtN 150090 150089 (.instr (.constN 150089 1)) .skip) d₆ d₇ k₇ →
        Exec P W posP d d₇ (k₁ + (1 + (k₃ + ((k₄ + (k₅ + 1)) + k₇)) + 2)) := by
      intro d₇ k₇ e₇
      unfold posP hcmp
      exact .seq ex₁ (.ifLtN_false h59 (.seq e₂ (.seq ex₃ (.seq (.seq ex₄ (.seq ex₅ e₆)) e₇))))
    by_cases hy : ((chainModel C).W.vtx p).2 = ((Qof P).vtx j).2
    · have hz : d₆.nreg 150089 = 0 := by rwx [o89, dirOf_eq_zero]
      have ht : ¬ d₆.nreg 150090 < d₆.nreg 150089 := by omega
      refine hfin d₆ _ (ex_pre d₆ 2 (.ifLtN_false ht (.skip w₆))) (by have := S.hlen; omega)
        ?_ (by omega)
      rw [hz]; simp [zero_ne_one, false_iff, not_and, not_not]; intro _; exact hy
    · have hz : d₆.nreg 150089 ≠ 0 := by rwx [o89, Ne, dirOf_eq_zero]
      have ht : d₆.nreg 150090 < d₆.nreg 150089 := by omega
      have e₇ := Exec.constN (P := P) w₆ 150089 1 (by omega)
      refine hfin _ _ (ex_pre _ 2 (.ifLtN_true ht e₇)) (by have := S.hlen; omega) ?_
        (by config_simp <;> omega)
      config_simp
      exact ⟨fun _ => ⟨hnz, hy⟩, fun _ => trivial⟩

/-- **Is the start before the end** (both on the walk edge `p`, height codes `h₁, h₂ ≥ 1`)?
`150089` is `1` iff the edge is not horizontal and the heights of `Q.vtx (h₁ - 1)` and
`Q.vtx (h₂ - 1)` are in the order of the edge. -/
theorem keyLess_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (h00 : d.nreg 150000 = MD) (h91 : d.nreg 150091 = 1) {p h₁ h₂ : ℕ}
    (h49 : d.nreg 150049 = p) (h02 : d.nreg 150002 = h₁) (h04 : d.nreg 150004 = h₂)
    (hp : p < 2 * C.m + 7) (hh₁ : 1 ≤ h₁) (hh₁' : h₁ ≤ P.n) (hh₂ : 1 ≤ h₂) (hh₂' : h₂ ≤ P.n) :
    ∃ d' k, Exec P W keyLess d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        NFLoc.dirOf ((Qof P).vtx (h₁ - 1)).2 ((Qof P).vtx (h₂ - 1)).2 =
          NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2)) ∧
      d'.nreg 150089 ≤ 1 := by
  have hWn := S.hW
  unfold hostWords at hWn
  obtain ⟨d₁, k₁, ex₁, hk₁, o59, r₁, m₁⟩ := dirP_exec S hD hMD hHh d hw hm h00 h49 hp
  have g₁ : ∀ r, 150000 ≤ r → r < 150100 → r ≠ 150059 → d₁.nreg r = d.nreg r :=
    fun r h1 h2 h3 => r₁ r (by omega) (by ufs Bdir; omega) (by omega) (by omega)
  have w₁ := ex₁.wb_right
  set D := NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 with hDdef
  have hfin : ∀ (d' : Config) (k : ℕ), Exec P W keyLess d d' k → k ≤ 100 * H.length + 2000 →
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        NFLoc.dirOf ((Qof P).vtx (h₁ - 1)).2 ((Qof P).vtx (h₂ - 1)).2 = D)) →
      d'.nreg 150089 ≤ 1 →
      ∃ d' k, Exec P W keyLess d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
        (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
          NFLoc.dirOf ((Qof P).vtx (h₁ - 1)).2 ((Qof P).vtx (h₂ - 1)).2 = D)) ∧
        d'.nreg 150089 ≤ 1 :=
    fun d' k ex hk h1 h2 => ⟨d', k, ex, hk, exec_frameB ex wr_keyLess, h1, h2⟩
  have b91 : d₁.nreg 150091 = 1 := by rw [g₁ 150091 (by omega) (by omega) (by omega), h91]
  by_cases h59 : d₁.nreg 150059 < d₁.nreg 150091
  · have hz : D = 0 := by rwo [b91, o59] at h59
    have e₂ := Exec.constN (P := P) w₁ 150089 0 (by omega)
    refine hfin _ _ (by unfold keyLess; exact .seq ex₁ (.ifLtN_true h59 e₂)) (by omega) ?_
      (by config_simp <;> omega)
    config_simp
    rw [hDdef, dirOf_eq_zero] at hz
    simp [zero_ne_one, false_iff, not_and]
    intro h; exact absurd hz h
  · have hnz : D ≠ 0 := by rwo [b91, o59] at h59
    have hnz' := hnz
    rw [hDdef, Ne, dirOf_eq_zero] at hnz'
    obtain ⟨d₂, k₂, ex₂, hk₂, a₂, b₂, c₂⟩ : ∃ d₂ k₂, Exec P W (block [.constN 50040 0,
        .subN 50041 150002 150091, .constN 50043 0, .subN 50044 150004 150091]) d₁ d₂ k₂ ∧
        k₂ = 4 ∧ SymPtIn d₂ 50040 (.vtx (h₁ - 1)) ∧ SymPtIn d₂ 50043 (.vtx (h₂ - 1)) ∧
        d₂.nreg 150059 = D := by
      exec_block
      all_goals first | omega | skip
      refine ⟨rfl, ⟨by config_simp, ?_⟩, ⟨by config_simp, ?_⟩, by config_simp; exact o59⟩
      · config_simp; rw [g₁ 150002 (by omega) (by omega) (by omega), h02, b91]
      · config_simp; rw [g₁ 150004 (by omega) (by omega) (by omega), h04, b91]
    obtain ⟨d₃, k₃, ex₃, hk₃, fr₃, o₃⟩ := NFLoc.dirTail_exec (P := P) S.hG (by omega) d₂
      ex₂.wb_right (show (SymPt.vtx (h₁ - 1)).Lt P.n from by show h₁ - 1 < P.n; omega)
      (show (SymPt.vtx (h₂ - 1)).Lt P.n from by show h₂ - 1 < P.n; omega) a₂ b₂
    have c59 : d₃.nreg 150059 = D := by rw [fr₃.1 _ (by decide), c₂]
    have w₃ := ex₃.wb_right
    set E := NFLoc.dirOf ((Qof P).vtx (h₁ - 1)).2 ((Qof P).vtx (h₂ - 1)).2 with hE
    have o10 : d₃.nreg 10502 = E := o₃
    have pre : ∀ (d₄ : Config) (k₄ : ℕ), Exec P W (.ifLtN 10502 150059
        (.instr (.constN 150089 0)) (.ifLtN 150059 10502 (.instr (.constN 150089 0))
          (.instr (.constN 150089 1)))) d₃ d₄ k₄ →
        Exec P W keyLess d d₄ (k₁ + ((k₂ + (k₃ + k₄)) + 2)) := by
      intro d₄ k₄ e₄
      unfold keyLess
      exact .seq ex₁ (.ifLtN_false h59 (.seq ex₂ (.seq ex₃ e₄)))
    by_cases hlt : d₃.nreg 10502 < d₃.nreg 150059
    · have e₄ := Exec.constN (P := P) w₃ 150089 0 (by omega)
      refine hfin _ _ (pre _ _ (.ifLtN_true hlt e₄)) (by have := S.hlen; omega) ?_
        (by config_simp <;> omega)
      config_simp
      simp [zero_ne_one, false_iff, not_and]
      intro _ h; rwo [o10, c59] at hlt
    · by_cases hgt : d₃.nreg 150059 < d₃.nreg 10502
      · have e₄ := Exec.constN (P := P) w₃ 150089 0 (by omega)
        refine hfin _ _ (pre _ _ (.ifLtN_false hlt (.ifLtN_true hgt e₄)))
          (by have := S.hlen; omega) ?_ (by config_simp <;> omega)
        config_simp
        simp [zero_ne_one, false_iff, not_and]
        intro _ h; rwo [o10, c59] at hgt
      · have e₄ := Exec.constN (P := P) w₃ 150089 1 (by omega)
        refine hfin _ _ (pre _ _ (.ifLtN_false hlt (.ifLtN_false hgt e₄)))
          (by have := S.hlen; omega) ?_ (by config_simp <;> omega)
        config_simp
        refine ⟨fun _ => ⟨hnz', ?_⟩, fun _ => trivial⟩
        rwo [o10, c59] at hlt hgt

end

end ShootCut

end Chazelle.Core
