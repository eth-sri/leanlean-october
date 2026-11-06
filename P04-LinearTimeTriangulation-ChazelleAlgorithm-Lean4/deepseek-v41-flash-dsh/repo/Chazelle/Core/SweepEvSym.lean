module

public import Chazelle.Core.SweepPrimAbs
public import Chazelle.Core.SweepIoPrim

/-!
# The sweep (WP-D), stages 2–3: the symbolic point of a tour position (`symAt`)

A shot of the model of `C₁` from an end `a` of a chord of `N₂` (a walk position of the model of
`C₂`) needs `a` as a symbolic point of `Q` (an `Origin.sym`).  `symAt` (a primitive in the calling
convention of `SweepPrimDir`: descriptor in `50200`, position `(e, h)` in `50201, 50202`) returns
it in `50210 … 50212` for a tour position (`6 ≤ e < 2m + 6`) with a normalised height code
(`h = 0` iff the parameter is `0`):

* `h = 0`: the host point of the tour vertex `e - 6` (`tvLoad`);
* `h > 0`: the point `onEdge E (h - 1)` of the edge `E` of `Q` carrying the host edge
  (`edgeIdxS`), which is the point itself (`tour_abs` and the height of the code).

`callSym`: the call from the sweep's registers (`SweepIo.IRS` run step).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-! ## The point -/

/-- **A tour position inside an edge is the point `onEdge E (h - 1)`.** -/
theorem tour_pt {P : Polygon} (hG : GoodEnv P) {H : Host} {C : Chain} (hCP : C.P = H.poly (Qof P))
    (hreg : HostRegular P.n H) (hNn : C.P.n = (H.pts P.n).length) {i : ℕ} (hi : i < 2 * C.m)
    {s₁ s₂ : SymPt}
    (h1 : (H.pts P.n)[(C.s + C.sideIdx C.sideBeta i) % (H.pts P.n).length]? = some s₁)
    (h2 : (H.pts P.n)[(C.s + C.sideIdx C.sideBeta (i + 1)) % (H.pts P.n).length]? = some s₂)
    (hl₁ : s₁.Lt P.n) (hl₂ : s₂.Lt P.n)
    (hv₁ : s₁.eval (Qof P) = (chainModel C).W.vtx (i + 6))
    (hv₂ : s₂.eval (Qof P) = (chainModel C).W.vtx ((i + 1) + 6)) {hc : ℕ}
    (ht : 0 < (chainModel C).param (Qof P) ⟨i + 6, hc⟩) :
    hostEdgeIdx P.n s₁ s₂ < P.n ∧
      (chainModel C).pos (Qof P) ⟨i + 6, hc⟩ =
        (SymPt.onEdge (hostEdgeIdx P.n s₁ s₂) (hc - 1)).eval (Qof P) := by
  obtain ⟨hE, hx⟩ := tour_abs hG hCP hreg hNn hi h1 h2 hl₁ hl₂ hv₁ hv₂ ht
  refine ⟨hE, Prod.ext hx ?_⟩
  have hne := ne_of_param_pos ht
  rw [Model.pos_snd hne]
  have hc1 : 1 ≤ hc := by
    rcases Nat.eq_zero_or_pos hc with rfl | h
    · exact absurd (show (chainModel C).param (Qof P) ⟨i + 6, 0⟩ = 0 from rfl) (ne_of_gt ht)
    · exact h
  obtain ⟨h', rfl⟩ : ∃ h', hc = h' + 1 := ⟨hc - 1, by omega⟩
  rfl

/-! ## The machine -/

/-- Output the point `onEdge (50142) (h - 1)` into `50210 … 50212`. -/
def outS : Stmt := block [.constN 50210 1, .copyN 50211 50142, .subN 50212 50202 50032]

/-- A tour vertex: its host point. -/
def symVtx : Stmt := .seq (.instr (.subN 50120 50201 50081)) (tvLoad 50210)

/-- Inside a tour edge: the point of the edge of `Q` carrying the host edge. -/
def symInt : Stmt :=
  .seq (.instr (.subN 50120 50201 50081)) (.seq (tvLoad 50130)
    (.seq (.instr (.addN 50120 50120 50032)) (.seq (tvLoad 50136) (.seq edgeIdxS outS))))

/-- The core: by the (normalised) height code. -/
def symCore : Stmt := .ifLtN 50202 50032 symVtx symInt

/-- **The primitive `symAt`.** -/
def symAt : Stmt := .seq pHead symCore

theorem wr_symAt : wr Bprim symAt = true := by decide

theorem symVtx_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param (Qof P) ⟨e, hc⟩ = 0) :
    ∃ c' k, Exec P W symVtx c c' k ∧ k ≤ 27 * H.length + 41 ∧
      ∃ s : SymPt, SymPtIn c' 50210 s ∧ s.Lt P.n ∧
        s.eval (Qof P) = (chainModel C).pos (Qof P) ⟨e, hc⟩ := by
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50081
  have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    (by simp [h01, hE.r81]) (by omega) (dst := 50210) (by norm_num)
  have hv : (chainModel C).pos (Qof P) ⟨e, hc⟩ = (chainModel C).W.vtx (e - 6 + 6) := by
    rw [pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero, show e - 6 + 6 = e by omega]
  exact ⟨c₂, _, .seq e₁ e₂, by omega, sp, isp, lsp, by rw [vsp, hv]⟩

theorem symInt_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 6)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W symInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      ∃ s : SymPt, SymPtIn c' 50210 s ∧ s.Lt P.n ∧
        s.eval (Qof P) = (chainModel C).pos (Qof P) ⟨e, hc⟩ := by
  have hW := hE.hW
  have hm1 := C.one_le
  have hNn := hE.n_eq
  have hNW := hE.NW
  have hmN := C.m_lt
  set i := e - 6 with hi
  have hlt : i < 2 * C.m := by omega
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50081
  set c₁ : Config := { c with nreg := upd c.nreg 50120 (c.nreg 50201 - c.nreg 50081) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.step e₁ (by decide)
  have q20 : c₁.nreg 50120 = i := by
    show upd c.nreg 50120 (c.nreg 50201 - c.nreg 50081) 50120 = i
    rw [upd_same, h01, hE.r81]
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c₁ hE₁ (i := i) q20
    hlt.le (dst := 50130) (by norm_num)
  have w₂ := e₂.wb_right
  have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
    (by rw [f₂.1 _ (by decide), q20, hE₂.r32]; omega)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50120 + c₂.nreg 50032) }
    with hc₃
  have hE₃ : CEnv P W H C c₃ := hE₂.step e₃ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
    (by rw [hc₃]; simp [f₂.1 _ (by decide : Btv 50130 50120 = false) ▸ q20, hE₂.r32])
    (by omega) (dst := 50136) (by norm_num)
  have i₁' : SymPtIn c₄ 50130 s₁ := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
    rw [hc₃]; simp [show j ≠ 50120 by omega]) f₄
    (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec (P := P) c₄ e₄.wb_right (by omega)
    hE₄.r32 i₁' i₂ l₁ l₂
  have q02 : c₅.nreg 50202 = hc := by
    rw [r₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide), hc₃]
    simp only
    rw [upd_other _ _ _ (by decide), f₂.1 _ (by decide), hc₁]
    simp only
    rw [upd_other _ _ _ (by decide), h02]
  have q32 : c₅.nreg 50032 = 1 := by
    rw [r₅ _ (by decide) (by decide) (by decide), hE₄.r32]
  have ht' : 0 < (chainModel C).param (Qof P) ⟨i + 6, hc⟩ := by
    rw [show i + 6 = e by omega]; exact ht
  obtain ⟨hEi, hpt⟩ := tour_pt hE.hG hE.hP hreg hNn hlt x₁ x₂ l₁ l₂ v₁ v₂ ht'
  have hc1 : 1 ≤ hc := by
    rcases Nat.eq_zero_or_pos hc with rfl | h
    · exact absurd (show (chainModel C).param (Qof P) ⟨e, 0⟩ = 0 from rfl) (ne_of_gt ht)
    · exact h
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outS c₅ c₆ k₆ ∧ k₆ = 3 ∧
      SymPtIn c₆ 50210 (.onEdge (hostEdgeIdx P.n s₁ s₂) (hc - 1)) := by
    unfold outS
    have hw₅ := e₅.wb_right
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, by config_simp; exact v₅, ?_⟩
    config_simp; rw [q02, q32]
  have ex : Exec P W symInt c c₆ (1 + (k₂ + (1 + (k₄ + (k₅ + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  refine ⟨c₆, _, ex, by have := hE.hlen; omega, _, q, ⟨hEi, by omega⟩, ?_⟩
  rw [show e = i + 6 by omega, hpt]

/-- The input condition of `symAt`: a tour position with a normalised height code, a regular
host. -/
def SymIn (P : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  6 ≤ c.nreg 50201 ∧ c.nreg 50201 < 2 * C.m + 6 ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 50201, c.nreg 50202⟩ ∧
    (c.nreg 50202 = 0 ↔ (chainModel C).param (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩ = 0) ∧
    ∀ H', HostAt c.nmem (c.nmem (c.nreg 50200)) H' → HostRegular P.n H'

/-- The output condition of `symAt`: the symbolic point of the position. -/
def SymOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  ∃ s : SymPt, SymPtIn c' 50210 s ∧ s.Lt P.n ∧
    s.eval (Qof P) = (chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩

/-- **Contract of `symAt`.** -/
theorem symAt_meets : Meets symAt primBands (PrimPre SymIn) (PrimPost SymOut)
    (fun _ _ => 1000 + 60 * 0 + 30000) := by
  refine prim_meets (K := 30200) (fun r h => h) wr_symAt ?_
  intro P W H C c₀ c hC hE ⟨h6, hen, ⟨hp0, hp1, hhn⟩, hnorm, hreg⟩ hinp
  have hregH := hreg H hC.1
  have hlen := hE.hlen
  have i01 := hinp 50201 (by norm_num) (by norm_num)
  have i02 := hinp 50202 (by norm_num) (by norm_num)
  unfold SymOut symCore
  by_cases hz : c.nreg 50202 < c.nreg 50032
  · have hc0 : c₀.nreg 50202 = 0 := by rw [← i02]; rw [hE.r32] at hz; omega
    obtain ⟨c', k, ex, hk, s, hs⟩ := symVtx_exec c hE i01 h6 (by omega) (hnorm.1 hc0)
    exact ⟨c', _, .ifLtN_true hz ex, by omega, s, hs⟩
  · have hc0 : c₀.nreg 50202 ≠ 0 := by rw [← i02]; rw [hE.r32] at hz; omega
    have hpos : 0 < (chainModel C).param (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩ :=
      lt_of_le_of_ne hp0 (fun h => hc0 (hnorm.2 h.symm))
    obtain ⟨c', k, ex, hk, s, hs⟩ := symInt_exec c hE hregH i01 i02 h6 hen hpos hhn
    exact ⟨c', _, .ifLtN_false hz ex, by omega, s, hs⟩

end

end SweepPrim

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A symbolic point survives a copy of its three words. -/
theorem symPtIn_transport {c c' : Config} {r r' : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) : SymPtIn c' r' s := by
  cases s with
  | vtx i => exact ⟨by rw [h0]; exact h.1, by rw [h1]; exact h.2⟩
  | onEdge e k => exact ⟨by rw [h0]; exact h.1, by rw [h1]; exact h.2.1, by rw [h2]; exact h.2.2⟩

/-- `symAt` on the descriptor `dsc`, the position `(re, rh)`, output at `o … o + 2`. -/
def callSym (dsc re rh o : ℕ) : Stmt :=
  callP [(50200, dsc), (50201, re), (50202, rh)] symAt [(o, 50210), (o + 1, 50211), (o + 2, 50212)]

set_option maxRecDepth 20000 in
theorem callSym_irs {dsc re rh o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000)
    (ho : 240700 ≤ o ∧ o + 2 < 250000) (h6 : 6 ≤ c.nreg re) (hen : c.nreg re < 2 * C.m + 6)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg re, c.nreg rh⟩)
    (hnorm : c.nreg rh = 0 ↔ (chainModel C).param (Qof P) ⟨c.nreg re, c.nreg rh⟩ = 0)
    (hroom : c.nreg ALLOC + 31006 ≤ W) :
    IRS P W c₀ (callSym dsc re rh o) c 31006
      (fun c' => (∃ s : SymPt, SymPtIn c' o s ∧ s.Lt P.n ∧
          s.eval (Qof P) = (chainModel C).pos (Qof P) ⟨c.nreg re, c.nreg rh⟩) ∧
        (∀ r, bandOf r ∉ oracleBands → (r < o ∨ o + 2 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(50200, dsc), (50201, re), (50202, rh)])
    (outs := [(o, 50210), (o + 1, 50211), (o + 2, 50212)]) symAt_meets
    primBands_oracle hI
    (nodup3 (by norm_num) (by norm_num) (by norm_num))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨band5_oracle (by norm_num) (by norm_num), band5_oracle (by norm_num) (by norm_num),
          band5_oracle (by norm_num) (by norm_num)⟩)
    (nodup3 (by omega) (by omega) (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g0, g1, g2⟩ := e1
      have hctx₁ := hctx.transport g0 (fun a _ => by rw [hm]) (by rw [hA])
      refine primPre_of hctx₁ ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [g1]; exact h6
      · rw [g1]; exact hen
      · rw [g1, g2]; exact hpp
      · rw [g1, g2]; exact hnorm
      · rw [hm, g0]; exact hctx.hostReg)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g0, g1, g2⟩ := e1
  obtain ⟨k0, k1, k2⟩ := f1
  obtain ⟨H, hC, -⟩ := hctx.2.2.2.1
  have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 50200) (Qof P) H C := by rw [hm, g0]; exact hC
  obtain ⟨s, hs, hsl, hse⟩ := hpost H C hC₁
  rw [g1, g2] at hse
  refine ⟨⟨s, symPtIn_transport hs k0 k1 k2, hsl, hse⟩, fun r hr h0 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega)
    hra, hA, hm'⟩

end

end SweepEv

end Chazelle.Core
