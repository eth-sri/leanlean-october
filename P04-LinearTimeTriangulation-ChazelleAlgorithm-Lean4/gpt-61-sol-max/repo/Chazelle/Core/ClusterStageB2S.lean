module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterStageB2

/-!
# WP-I, part 48: stage B2 assembled

`stageB2_exec`: the facts `B2F` of the dual search, the preorder intervals and the dual table.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}

/-- **The facts of stage B2.** -/
structure B2F (g : GV) {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin g.μ) F (Fin g.N)}
    {T : SpanTree M} {a : F → Fin g.N} {ha : ∀ f, M.face (a f) = f}
    (C : CoTree (starTree T a ha)) (R : BTree) (preE slot m : ℕ → ℕ) : Prop where
  fpar : ∀ x : Fin g.N, x ≠ C.r0 → m (g.base 26 + x) = enc g.N (C.fpar x)
  fpar_lt : ∀ x, x < g.N → m (g.base 26 + x) < 3 * g.N
  r0 : (C.r0 : ℕ) = 0
  pre : ∀ x, x < g.N → m (g.base 29 + x) = preE x
  sz : ∀ x, x < g.N → m (g.base 28 + x) = (R.sub x).card
  R_ok : R.OK
  R_n : R.n = g.N
  R_up : ∀ x : Fin g.N, R.up x = C.parent x
  R_root : R.root = 0
  R_pre : R.PreInv preE slot R.n
  up_tab : ∀ j, j < g.L → ∀ x, x < g.N →
    m (g.A0 + 54 * g.U + g.L * g.U + j * g.N + x) = R.up^[2 ^ j] x

set_option maxHeartbeats 4000000 in
open Classical in
theorem stageB2_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face (a f) = f} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hA : AF g M T c.nmem) (hB : B1F g M T a ha c.nmem) (hM : M.Connected) (hN : 0 < g.N)
    (hL : 0 < g.L) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageB2 c c' k ∧ k ≤ 280 * g.N + 12 * g.N * g.L + 7 * g.L + 120 ∧
      WordsBounded W c' ∧ PFr StBRG (fun a => g.base 24 ≤ a ∧ a < g.base 32 ∨
        g.A0 + 54 * g.U + g.L * g.U ≤ a ∧ a < g.A0 + 54 * g.U + 2 * (g.L * g.U)) c c' ∧
      ∃ (C : CoTree (starTree T a ha)) (R : BTree) (preE slot : ℕ → ℕ),
        B2F g C R preE slot c'.nmem := by
  have hU := g.U_ge
  have hE := g.END_eq
  have hLU := g.L_le_U
  have hLN : g.L * g.N ≤ g.L * g.U := Nat.mul_le_mul_left _ (by omega)
  have b17 := g.base_eq 17; have b20 := g.base_eq 20; have b24 := g.base_eq 24
  have b26 := g.base_eq 26; have b27 := g.base_eq 27; have b28 := g.base_eq 28
  have b29 := g.base_eq 29; have b30 := g.base_eq 30; have b31 := g.base_eq 31
  have b32 := g.base_eq 32
  have hGR : ∀ {c1 : Config} {Am : ℕ → Prop}, PFr StBRG Am c c1 → GR g c1 := fun hf =>
    hG.frame (fun r hr => hf.1 r (by grind [GRReg, StBRG]))
  set Wr : ℕ → Prop := fun a => g.base 24 ≤ a ∧ a < g.base 32 ∨
    g.A0 + 54 * g.U + g.L * g.U ≤ a ∧ a < g.A0 + 54 * g.U + 2 * (g.L * g.U) with hWr
  unfold stageB2
  -- `DLAB := N`
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hl1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 24 (by omega)) hG.rN hG.rN (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega) (by omega)
  have f1 : PFr StBRG Wr c c1 := hf1.mono (fun r h => by grind [FillRG, StBRG])
    (fun a h => by grind)
  have b3 := g.base_eq 3; have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7
  have hA1 : AF g M T c1.nmem := hA.congr ⟨hO, hR, hV⟩
    (fun x hx => hf1.2.2.2.2 x (by grind [KeepA]))
  have hB1 : B1F g M T a ha c1.nmem := hB.congr (fun x h1 h2 => hf1.2.2.2.2 x (by omega))
  -- the dual search
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, C, hr0, hfpar2, hlt2, hROK, hq0, hRup⟩ :=
    dbfsP_exec (P := P) hw1 (hGR f1) hA1 hB1 hM hN hl1 hW
  have f2 : PFr StBRG Wr c c2 := f1.trans (hf2.mono (fun r h => h) (fun a h => by
    grind))
  -- the preorder intervals
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hsz3, hpre3⟩ := eulerP_exec (P := P) hw2 (hGR f2) hROK hlt2 hW
  have f3 : PFr StBRG Wr c c3 := f2.trans (hf3.mono (fun r h => h) (fun a h => by
    simp only [hWr]; omega))
  have hlt3 : ∀ x, x < g.N → c3.nmem (g.base 26 + x) < 3 * g.N := fun x hx => by
    rw [hf3.2.2.2.2 _ (by omega)]; ram_grind
  -- the dual parent array
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, hp0, hp4⟩ := pfP_exec (P := P) hw3 (hGR f3) hN hlt3 hW
  have f4 : PFr StBRG Wr c c4 := f3.trans (hf4.mono (fun r h => h) (fun a h => by
    simp only [hWr]; omega))
  set R := dtree g c2.nmem with hRdef
  have hRn : R.n = g.N := rfl
  have hRroot : R.root = 0 := hq0
  have hupN : ∀ y, y < g.N → R.up y < g.N := fun y hy => by
    rw [hRup ⟨y, hy⟩]; omega
  have hpf : ∀ y, y < g.N → c4.nmem (g.base 31 + y) = R.up y := by
    intro y hy
    by_cases h0 : y = 0
    · subst h0
      simp only [Nat.add_zero]; grind [BTree.up]
    · rw [hp4 y (by omega) hy]
      unfold BTree.up
      rw [ite_eq_right (by omega)]
      show _ = c2.nmem (g.base 17 + c2.nmem (g.base 26 + y))
      have := hlt2 y hy
      rw [hf3.2.2.2.2 (g.base 26 + y) (by omega), hf3.2.2.2.2 _ (by omega)]
  -- the dual table
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, htab⟩ := updP_exec (P := P) hw4 (hGR f4) hN hL
    (fun y hy => by ram_grind) hW
  have f5 : PFr StBRG Wr c c5 := f4.trans (hf5.mono (fun r h => h) (fun a h => by
    grind))
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq x1 (.seq x2 (.seq x3 (.seq x4 x5))), ?_,
    hw5, f5, C, R, view c3.nmem (g.base 29) g.N, view c3.nmem (g.base 30) g.N, ?_⟩
  · omega
  · have e5 := hf5.2.2.2.2
    have e4 := hf4.2.2.2.2
    have e3 := hf3.2.2.2.2
    clear f1 f2 f3 f4 f5 hf1 hf2 hf3 hf4 hf5
    have k29 : ∀ x, x < g.N → c5.nmem (g.base 29 + x) = c3.nmem (g.base 29 + x) := by
      intro x hx
      have h1 : ¬ (g.A0 + 54 * g.U + g.L * g.U ≤ g.base 29 + x ∧
          g.base 29 + x < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) := by
        ram_grind
      have h2 : ¬ (g.base 31 ≤ g.base 29 + x ∧ g.base 29 + x < g.base 31 + g.N) := by
        ram_grind
      exact (e5 _ h1).trans (e4 _ h2)
    have k28 : ∀ x, x < g.N → c5.nmem (g.base 28 + x) = c3.nmem (g.base 28 + x) := by
      intro x hx
      have h1 : ¬ (g.A0 + 54 * g.U + g.L * g.U ≤ g.base 28 + x ∧
          g.base 28 + x < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) := by
        ram_grind
      have h2 : ¬ (g.base 31 ≤ g.base 28 + x ∧ g.base 28 + x < g.base 31 + g.N) := by
        ram_grind
      exact (e5 _ h1).trans (e4 _ h2)
    have k26 : ∀ x, x < g.N → c5.nmem (g.base 26 + x) = c2.nmem (g.base 26 + x) := by
      intro x hx
      have h1 : ¬ (g.A0 + 54 * g.U + g.L * g.U ≤ g.base 26 + x ∧
          g.base 26 + x < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) := by
        ram_grind
      have h2 : ¬ (g.base 31 ≤ g.base 26 + x ∧ g.base 26 + x < g.base 31 + g.N) := by
        ram_grind
      have h3 : ¬ (g.base 28 ≤ g.base 26 + x ∧ g.base 26 + x < g.base 31) := by
        ram_grind
      exact (e5 _ h1).trans ((e4 _ h2).trans (e3 _ h3))
    have hpreF : ∀ x, x < g.N → c5.nmem (g.base 29 + x) = view c3.nmem (g.base 29) g.N x := by
      intro x hx
      rw [view_lt hx]; exact k29 x hx
    have hfparF : ∀ x : Fin g.N, x ≠ C.r0 → c5.nmem (g.base 26 + x) = enc g.N (C.fpar x) := by
      intro x hx
      rw [k26 x x.2]; exact hfpar2 x hx
    have hltF : ∀ x, x < g.N → c5.nmem (g.base 26 + x) < 3 * g.N := by
      intro x hx
      rw [k26 x hx]; exact hlt2 x hx
    have hszF : ∀ x, x < g.N → c5.nmem (g.base 28 + x) = (R.sub x).card := by
      intro x hx
      rw [k28 x hx]; exact hsz3 x hx
    have htabF : ∀ j, j < g.L → ∀ x, x < g.N →
        c5.nmem (g.A0 + 54 * g.U + g.L * g.U + j * g.N + x) = R.up^[2 ^ j] x := by
      intro j hj x hx
      rw [htab j hj x hx]
      exact (iterate_congr_lt (n := g.N) hpf hupN (2 ^ j) x hx).1
    clear * - hfparF hltF hr0 hpreF hszF hROK hRn hRup hRroot hpre3 htabF
    exact ⟨hfparF, hltF, hr0, hpreF, hszF, hROK, hRn, hRup, hRroot, hpre3, htabF⟩

end proofs

end

end Chazelle.Core.Cluster
