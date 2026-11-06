module

public import Chazelle.Core.DownPhaseDrvBExpB

/-!
# Down-phase base (D9), RAM: expansion of a host block, part 3 (items)

One host item (`itemS`): load its three words (kind `r212026`, arguments `r212027`,
`r212028`) at the item pointer `r212023`, dispatch on the kind (run `runS`, vertex `wrV`,
edge point `wrE`), advance the item pointer and the item counter `r212024` (`itemS_exec`).
The invariant `IInv` after `q` items: the points of `H.take q` are written.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)

@[expose] public section

/-! ## Host points -/

theorem host_mem_getD {H : Host} {q : ℕ} (hq : q < H.length) :
    H.getD q (.run 0 0) ∈ H := by
  rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq

theorem pts_take_succ (n : ℕ) {H : Host} {q : ℕ} (hq : q < H.length) :
    Host.pts n (H.take (q + 1)) = Host.pts n (H.take q) ++ (H.getD q (.run 0 0)).pts n := by
  unfold Host.pts
  rw [List.take_add_one, List.getElem?_eq_getElem hq, List.getD_eq_getElem _ _ hq,
    List.flatMap_append]
  simp

theorem pts_take_length_le (n : ℕ) (H : Host) (q : ℕ) :
    (Host.pts n (H.take q)).length ≤ (H.pts n).length := by
  unfold Host.pts
  conv_rhs => rw [← List.take_append_drop q H]
  rw [List.flatMap_append, List.length_append]; omega

theorem pts_getD_mid (n : ℕ) {H : Host} {q j : ℕ} (hq : q < H.length)
    (hj : j < ((H.getD q (.run 0 0)).pts n).length) (d : SymPt) :
    (H.pts n).getD ((Host.pts n (H.take q)).length + j) d =
      ((H.getD q (.run 0 0)).pts n).getD j d := by
  have e : H.pts n = (Host.pts n (H.take q) ++ (H.getD q (.run 0 0)).pts n) ++
      Host.pts n (H.drop (q + 1)) := by
    rw [← pts_take_succ n hq]
    unfold Host.pts
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e, List.getD_append _ _ _ _ (by rw [List.length_append]; omega),
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem run_pts_getD (n a ℓ t : ℕ) (ht : t ≤ ℓ) (d : SymPt) :
    ((HostItem.run a ℓ).pts n).getD t d = .vtx ((a + t) % n) := by
  simp [HostItem.pts, List.getD_eq_getElem?_getD, List.getElem?_range (show t < ℓ + 1 by omega)]

/-! ## One item -/

/-- Load the three words of the current item. -/
def loadB : List Instr :=
  [.loadN 212026 212023, .addN 212031 212023 212000, .loadN 212027 212031,
    .addN 212031 212031 212000, .loadN 212028 212031]

/-- Dispatch on the kind of the item. -/
def dispS : Stmt := .ifLtN 212026 212000 runS
  (.ifLtN 212026 212002 (.seq (.instr (.copyN 212030 212027)) wrV) wrE)

/-- Advance the item pointer and the item counter. -/
def incB : List Instr :=
  [.addN 212023 212023 212000, .addN 212023 212023 212000, .addN 212023 212023 212000,
    .addN 212024 212024 212000]

/-- **One host item.** -/
def itemS : Stmt := .seq (block loadB) (.seq dispS (block incB))

theorem wr_loadB : wrM Bexp (block loadB) = true := by decide
theorem wr_incB : wrM Bexp (block incB) = true := by decide
theorem wr_dispS :
    wrM (fun r => decide (r = 212025 ∨ r = 212028 ∨ r = 212029 ∨ r = 212030)) dispS = true := by
  decide

/-- **The invariant of the item loop** after `q` items. -/
def IInv (W n PA HB : ℕ) (li : Bool) (H : Host) (c₀ : Config) (q : ℕ) (e : Config) : Prop :=
  ESt W n PA li (H.pts n) c₀ e (Host.pts n (H.take q)).length ∧ e.nreg 212023 = HB + 1 + 3 * q ∧
    e.nreg 212024 = q

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The dispatch** on the item `q`, after its words are loaded. -/
theorem dispS_exec {PA HB : ℕ} {li : Bool} {H : Host} {c₀ e : Config} {q : ℕ}
    (hH : HostAt c₀.nmem HB H) (hWF : HostWF P.n H) (h2 : c₀.nreg 212002 = 2)
    (hq : q < H.length)
    (hS : ESt W P.n PA li (H.pts P.n) c₀ e (Host.pts P.n (H.take q)).length)
    (h26 : e.nreg 212026 = c₀.nmem (HB + 1 + 3 * q))
    (h27 : e.nreg 212027 = c₀.nmem (HB + 2 + 3 * q))
    (h28 : e.nreg 212028 = c₀.nmem (HB + 3 + 3 * q)) :
    ∃ e' k, Exec P W dispS e e' k ∧ k ≤ 14 * ((H.getD q (.run 0 0)).pts P.n).length + 10 ∧
      ESt W P.n PA li (H.pts P.n) c₀ e' (Host.pts P.n (H.take (q + 1))).length ∧
      FrameM (fun r => decide (r = 212025 ∨ r = 212028 ∨ r = 212029 ∨ r = 212030)) e e' := by
  suffices h : ∃ e' k, Exec P W dispS e e' k ∧
      k ≤ 14 * ((H.getD q (.run 0 0)).pts P.n).length + 10 ∧
      ESt W P.n PA li (H.pts P.n) c₀ e' (Host.pts P.n (H.take (q + 1))).length by
    obtain ⟨e', k, x, hk, hS'⟩ := h
    exact ⟨e', k, x, hk, hS', exec_frameM x wr_dispS⟩
  have hlen := pts_take_length_le P.n H (q + 1)
  rw [pts_take_succ P.n hq] at hlen ⊢
  rw [List.length_append] at hlen ⊢
  have hmid := fun j hj => pts_getD_mid P.n hq (j := j) hj (.vtx 0)
  have h0 := hS.r0
  have r2 : e.nreg 212002 = 2 := (hS.fr.1 _ (by decide)).trans h2
  have hmem := host_mem_getD hq
  have hh := hH.2 q hq
  revert hmid hmem hh hlen
  generalize H.getD q (.run 0 0) = it
  intro hlen hmid hmem hh
  cases it with
  | run a ℓ =>
    obtain ⟨k0, ka, kl⟩ := hh
    obtain ⟨ha, hl⟩ : a < P.n ∧ ℓ < P.n := hWF _ hmem
    have hlr : ((HostItem.run a ℓ).pts P.n).length = ℓ + 1 := by simp [HostItem.pts]
    rw [hlr] at hlen ⊢
    obtain ⟨e', k, x, hk, hS', -⟩ := runS_exec (P := P) hS (h27.trans ka) (h28.trans kl) ha hl
      hlen (fun t ht => by
        rw [hmid t (by rw [hlr]; omega), run_pts_getD _ _ _ _ ht])
    exact ⟨e', k + 1, .ifLtN_true (by rw [h26, k0, h0]; omega) x, by omega, hS'⟩
  | pt x =>
    cases x with
    | vtx j =>
      obtain ⟨k0, kj⟩ := hh
      have hl1 : ((HostItem.pt (.vtx j)).pts P.n).length = 1 := rfl
      rw [hl1] at hlen ⊢
      have hw := hS.wb
      obtain ⟨e₁, x₁⟩ : ∃ e₁, Exec P W (.instr (.copyN 212030 212027)) e e₁ 1 ∧
          ESt W P.n PA li (H.pts P.n) c₀ e₁ (Host.pts P.n (H.take q)).length ∧
          e₁.nreg 212030 = j :=
        ⟨_, Machine.Exec.copyN hw _ _, hS.frame (Machine.Exec.copyN (P := P) hw 212030 212027).wb_right
          ⟨fun r hr => by
            simp only [Bexp, decide_eq_false_iff_not] at hr
            dsimp only; rw [Machine.upd_other]; omega,
            fun _ _ => rfl, rfl, rfl⟩ (by simp) rfl, by simp [h27, kj]⟩
      obtain ⟨x₁, hS₁, h30⟩ := x₁
      obtain ⟨e', k, x, hk, hS', -⟩ := wrV_exec (P := P) hS₁ (by omega)
        (by have := hmid 0 (by simp [HostItem.pts]); rw [Nat.add_zero] at this
            rw [h30, this]; rfl)
      refine ⟨e', 1 + k + 2 + 1, .ifLtN_false (by rw [h26, k0, h0]; omega)
        (.ifLtN_true (by rw [h26, k0, r2]; omega) (.seq x₁ x)), by omega, hS'⟩
    | onEdge ee hh' =>
      obtain ⟨k0, ke, kh⟩ := hh
      have hl1 : ((HostItem.pt (.onEdge ee hh')).pts P.n).length = 1 := rfl
      rw [hl1] at hlen ⊢
      obtain ⟨e', k, x, hk, hS', -⟩ := wrE_exec (P := P) hS (by omega)
        (by have := hmid 0 (by simp [HostItem.pts]); rw [Nat.add_zero] at this
            rw [h27, h28, ke, kh, this]; rfl)
      refine ⟨e', k + 2 + 2, .ifLtN_false (by rw [h26, k0, h0]; omega)
        (.ifLtN_false (by rw [h26, k0, r2]; omega) x), by omega, hS'⟩

/-- **One host item**: its points are written, the item pointer and counter advance. -/
theorem itemS_exec {PA HB : ℕ} {li : Bool} {H : Host} {c₀ e : Config} {q : ℕ}
    (hH : HostAt c₀.nmem HB H) (hWF : HostWF P.n H) (h2 : c₀.nreg 212002 = 2)
    (hHB : HB + 3 * H.length + 1 ≤ PA) (hq : q < H.length)
    (hI : IInv W P.n PA HB li H c₀ q e) :
    ∃ e' k, Exec P W itemS e e' k ∧ IInv W P.n PA HB li H c₀ (q + 1) e' ∧
      k + 30 * ((Host.pts P.n (H.take q)).length + q) ≤
        30 * ((Host.pts P.n (H.take (q + 1))).length + (q + 1)) := by
  obtain ⟨hS, h23, h24⟩ := hI
  have hw := hS.wb
  have h0 := hS.r0
  have hPA : PA ≤ W := by have := hS.hW; omega
  obtain ⟨e₁, k₁, x₁, hk₁, h26, h27, h28, h23', h24', h25', hm'⟩ : ∃ e₁ k₁,
      Exec P W (block loadB) e e₁ k₁ ∧ k₁ ≤ 5 ∧
      e₁.nreg 212026 = c₀.nmem (HB + 1 + 3 * q) ∧ e₁.nreg 212027 = c₀.nmem (HB + 2 + 3 * q) ∧
      e₁.nreg 212028 = c₀.nmem (HB + 3 + 3 * q) ∧ e₁.nreg 212023 = HB + 1 + 3 * q ∧
      e₁.nreg 212024 = q ∧ e₁.nreg 212025 = e.nreg 212025 ∧ e₁.nmem = e.nmem := by
    unfold loadB
    exec_block
    · config_simp; rw [h23, h0]; omega
    · config_simp; rw [h23, h0]; omega
    · refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp
      · rw [h23]; exact hS.mem _ (Or.inl (by omega))
      · rw [h23, h0, show HB + 1 + 3 * q + 1 = HB + 2 + 3 * q by omega]
        exact hS.mem _ (Or.inl (by omega))
      · rw [h23, h0, show HB + 1 + 3 * q + 1 + 1 = HB + 3 + 3 * q by omega]
        exact hS.mem _ (Or.inl (by omega))
      · exact h23
      · exact h24
  have hS₁ := hS.frame x₁.wb_right (exec_frameM x₁ wr_loadB) h25' hm'
  obtain ⟨e₂, k₂, x₂, hk₂, hS₂, f₂⟩ := dispS_exec (P := P) hH hWF h2 hq hS₁ h26 h27 h28
  have r23 : e₂.nreg 212023 = HB + 1 + 3 * q := (f₂.1 _ (by decide)).trans h23'
  have r24 : e₂.nreg 212024 = q := (f₂.1 _ (by decide)).trans h24'
  have hw₂ := hS₂.wb
  have h0' := hS₂.r0
  obtain ⟨e₃, k₃, x₃, hk₃, h23'', h24'', h25'', hm''⟩ : ∃ e₃ k₃,
      Exec P W (block incB) e₂ e₃ k₃ ∧ k₃ ≤ 4 ∧
      e₃.nreg 212023 = HB + 1 + 3 * (q + 1) ∧ e₃.nreg 212024 = q + 1 ∧
      e₃.nreg 212025 = e₂.nreg 212025 ∧ e₃.nmem = e₂.nmem := by
    unfold incB
    exec_block
    · rw [r23, h0']; omega
    · config_simp; rw [r23, h0']; omega
    · config_simp; rw [r23, h0']; omega
    · config_simp; rw [r24, h0']; omega
    · refine ⟨by omega, ?_, ?_, ?_, rfl⟩ <;> config_simp
      · rw [r23, h0']; omega
      · rw [r24, h0']
  have hS₃ := hS₂.frame x₃.wb_right (exec_frameM x₃ wr_incB) h25'' hm''
  refine ⟨e₃, k₁ + (k₂ + k₃), .seq x₁ (.seq x₂ x₃), ⟨hS₃, h23'', h24''⟩, ?_⟩
  rw [pts_take_succ P.n hq, List.length_append]
  nlinarith

end exec

end

end DrvB

end Chazelle.Core
