module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoClass

/-!
# The sweep RAM (WP-D), answers: the symbolic point of a tour position

`absKey` (`SweepPrimAbs`) returns, for a walk position of a tour edge or a tour vertex of a chain
model, a symbolic point of `Q` with the abscissa of the position's point.  For these positions the
symbolic point is the point itself: the tour vertex (`tvLoad`), or the point `onEdge E (h - 1)` of
the edge `E` of `Q` carrying the host edge, at the height of the height code.  `symKey_meets` is
the contract of the same program with this stronger output, used for the shots from a query point
of one chain in the model of the other chain, and for height tests.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Chain (sideE sideLeft sidePt)

@[expose] public section

/-- The output of the symbolic point. -/
def SymOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  c'.nreg 50210 = 1 ∧ ∃ sp : SymPt, SymPtIn c' 50211 sp ∧ sp.Lt P.n ∧
    sp.eval (Qof P) = (chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩

/-- The input of the symbolic point: that of `absKey`, and a tour or top position. -/
def SymIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  AbsKeyIn P W C c ∧ ((6 ≤ c.nreg 50201 ∧ c.nreg 50201 < 2 * C.m + 6) ∨
    (c.nreg 50201 = 2 * C.m + 6 ∧
      (chainModel C).param (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩ = 0))

theorem symVtx_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param (Qof P) ⟨e, hc⟩ = 0) :
    ∃ c' k, Exec P W absVtx c c' k ∧ k ≤ 27 * H.length + 45 ∧
      c'.nreg 50210 = 1 ∧ ∃ sp : SymPt, SymPtIn c' 50211 sp ∧ sp.Lt P.n ∧
        sp.eval (Qof P) = (chainModel C).pos (Qof P) ⟨e, hc⟩ := by
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50081
  have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    (by simp [h01, hE.r81]) (by omega) (dst := 50211) (by norm_num)
  have e₃ := Exec.constN (P := P) e₂.wb_right 50210 1 (by have := hE.hW; omega)
  have hv : (chainModel C).pos (Qof P) ⟨e, hc⟩ = (chainModel C).W.vtx (e - 6 + 6) := by
    rw [SweepPrim.pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero, show e - 6 + 6 = e by omega]
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), by omega, by simp, sp,
    symPtIn_of_eq isp fun j h1 h2 => by simp [show j ≠ 50210 by omega], lsp, ?_⟩
  rw [vsp, hv]

theorem symInt_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 6)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) (ht1 : (chainModel C).param (Qof P) ⟨e, hc⟩ < 1)
    (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W absInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      c'.nreg 50210 = 1 ∧ ∃ sp : SymPt, SymPtIn c' 50211 sp ∧ sp.Lt P.n ∧
        sp.eval (Qof P) = (chainModel C).pos (Qof P) ⟨e, hc⟩ := by
  have hW := hE.hW
  have hm1 := C.one_le
  have hNW := hE.NW
  have hNn := hE.n_eq
  have hmN := C.m_lt
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50120 50201 50081,
      .addN 50143 50053 50053]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50120 = e - 6 ∧
        c₁.nreg 50143 = 2 * C.m ∧ ∀ r, r ≠ 50120 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    have hw := hE.wb
    exec_block
    · config_simp; rw [hE.r53]; omega
    · refine ⟨rfl, by config_simp; rw [h01, hE.r81], by config_simp; rw [hE.r53]; ring,
        fun r h1 h2 => by simp [h1, h2]⟩
  obtain ⟨q20, q43, r₁⟩ := q
  have hE₁ : CEnv P W H C c₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50120 || r == 50143) (by decide)).2.2.1
    (fun r hr => r₁ r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide)))
  have hlt : e - 6 < 2 * C.m := by omega
  set i := e - 6 with hi
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
    rw [upd_other _ _ _ (by decide), f₂.1 _ (by decide), r₁ _ (by decide) (by decide), h02]
  have q32 : c₅.nreg 50032 = 1 := by
    rw [r₅ _ (by decide) (by decide) (by decide), hE₄.r32]
  obtain ⟨hEi, hx⟩ := tour_abs hE.hG hE.hP hreg hNn hlt x₁ x₂ l₁ l₂ v₁ v₂
    (hc := hc) (by rw [show i + 6 = e by omega]; exact ht)
  have hc1 : 1 ≤ hc := by
    rcases Nat.eq_zero_or_pos hc with rfl | h
    · exact absurd (show (chainModel C).param (Qof P) ⟨e, 0⟩ = 0 from rfl) (ne_of_gt ht)
    · exact h
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outE c₅ c₆ k₆ ∧ k₆ = 4 ∧
      (c₆.nreg 50210 = 1 ∧ SymPtIn c₆ 50211 (.onEdge (hostEdgeIdx P.n s₁ s₂) (hc - 1))) := by
    unfold outE
    have hw₅ := e₅.wb_right
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, by config_simp, by config_simp; exact v₅, ?_⟩
    config_simp; rw [q02, q32]
  obtain ⟨q10, q11⟩ := q
  have ex : Exec P W absInt c c₆ (k₁ + (k₂ + (1 + (k₄ + (k₅ + k₆))) + 1)) :=
    .seq e₁ (.ifLtN_true (by rw [q20, q43]; exact hlt) (.seq e₂ (.seq e₃ (.seq e₄
      (.seq e₅ e₆)))))
  refine ⟨c₆, _, ex, by have := hE.hlen; omega, q10, _, q11, ⟨hEi, by omega⟩, ?_⟩
  have hne := ne_of_param_pos ht
  have hy : ((chainModel C).pos (Qof P) ⟨e, hc⟩).2 = ((Qof P).vtx (hc - 1)).2 := by
    rw [Model.pos_snd (Q := Qof P) (x := ⟨e, hc⟩) hne]
    obtain ⟨h', rfl⟩ : ∃ h', hc = h' + 1 := ⟨hc - 1, by omega⟩
    rfl
  apply Prod.ext
  · rw [show e = i + 6 by omega, hx]
  · rw [hy]; rfl

/-- **Contract of `absKey` for tour and top positions: the symbolic point of the position.** -/
theorem symKey_meets : Meets absKey primBands (PrimPre SymIn) (PrimPost SymOut)
    (fun _ _ => 16700) := by
  refine prim_meets (K := 15900) (fun r h => h) wr_absKey ?_
  intro P W H C c₀ c hC hE ⟨⟨⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩, hreg⟩, hcls⟩ hinp
  have hregH := hreg H hC.1
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  obtain ⟨c', k, ex, hk, hr⟩ := classify_exec (Kb := 27 * H.length + 50)
    (Kv := 27 * H.length + 45) (Ki := 60 * H.length + 200) (R := SymOut P C c₀) c₀ c hE hinp hen
    hp0 hp1 hhn hy
    (fun c₂ hE₂ g₂ d₂ he hpos => ⋄)
    (fun c₂ hE₂ g₂ h6 hpar => symVtx_exec c₂ hE₂ (g₂ 50201 (⊛) (by norm_num)) h6
      (⋄) hpar)
    (fun c₂ hE₂ g₂ _ h6 hpos => symInt_exec c₂ hE₂ hregH (g₂ 50201 (⊛) (by norm_num))
      (g₂ 50202 (⊛) (by norm_num)) h6 (by
        rcases hcls with ⟨-, h⟩ | ⟨h, h'⟩
        · exact h
        · rw [h'] at hpos; exact absurd hpos (lt_irrefl _)) hpos hp1 hhn)
  exact ⟨c', k, ex, ⋄, hr⟩

end

end SweepIo

end Chazelle.Core
