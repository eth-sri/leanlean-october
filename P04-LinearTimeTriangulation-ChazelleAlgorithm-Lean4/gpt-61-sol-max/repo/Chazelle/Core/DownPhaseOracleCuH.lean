module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleCuR7

/-!
# WP-M (E7-B): the interior cutter

`cuI cu`: on a chain descriptor (kind `0`) the chain cutter `cu` itself; on the descriptor of the
interior model (kind `1`) the set-up `frontC` and the query `queryC cu` (one or two sub-queries
through chains of `Q`, each one or two calls of `cu`, recorded as slots, and the assembly of the
translated pieces).

**`interiorCutter_of`**: from a cutter for the chain models (`OkModel`, bands `oracleBands`, piece
bound and cost `G`, granularity bound `H`), `cuI cu` is a cutter for `OkI` (chain models and the
interior model of `Qof P`), with bands `ioBands = insert bUp oracleBands`, piece bound and cost
`GI G γ = 172 G γ + 2408 (⌈log₂ γ⌉ + 1) + 6400`, and the same `H`.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)

@[expose] public section

/-- **The interior cutter.** -/
def cuI (cu : Stmt) : Stmt :=
  .seq (block [.loadN 170099 150000, .constN 170098 1])
    (.ifLtN 170099 170098 cu (.seq frontC (queryC cu)))

/-- The piece bound and cost of the interior cutter. -/
def GI (G : ℕ → ℕ) (γ : ℕ) : ℕ := 172 * G γ + 2408 * (Nat.clog 2 γ + 1) + 6400



section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface}

theorem loadC_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.loadN 170099 150000, .constN 170098 1]) c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem (c.nreg 150000) ∧ c'.nreg 170098 = 1 ∧
      FrameB (fun r => decide (r = 170098 ∨ r = 170099)) c c' := by
  have hwr : wr (fun r => decide (r = 170098 ∨ r = 170099))
      (block [.loadN 170099 150000, .constN 170098 1]) = true := by decide
  suffices h : ∃ c' k, Exec P W (block [.loadN 170099 150000, .constN 170098 1]) c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem (c.nreg 150000) ∧ c'.nreg 170098 = 1 by
    obtain ⟨c', k, e, h1, h2, h3⟩ := h
    exact ⟨c', k, e, h1, h2, h3, exec_frameB e hwr⟩
  exec_block
  · omega
  ram_simp

/-- **The interior cutter.** -/
theorem interiorCutter_of {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H (gradeCtx O) OkModel) :
    CutterOK (cuI cu) ioBands (GI G) H (gradeCtx O) OkI := by
  intro P W c hw hpre hcost
  obtain ⟨hG, hHW, hX, hcap, hMDWF, M, hMD, hOk, hsP, heP, hs1, he1, hin1, hin2, hwt⟩ := hpre
  have hW := hHW
  unfold hostWords at hW
  beta_reduce at hcost
  have hQ : (Qof P).n = P.n := qn'
  obtain ⟨c₁, k₁, e₁, hk₁, a99, a98, F₁⟩ := loadC_exec (P := P) c hw (by omega)
  have w₁ := e₁.wb_right
  have f₁ : ∀ r, r ≠ 170098 → r ≠ 170099 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    F₁.1 r (by simp_all)
  have Fr₁ : Frame ioBands c c₁ k₁ := frameIO_of_frameB (fun r h => load_io h) F₁ k₁
  have rk : ∀ i, i < 20 → rd c₁ bCut i = rd c bCut i := fun i hi =>
    f₁ _ (by omega_nf) (by omega_nf)
  have hm₁ : c₁.nmem = c.nmem := F₁.2.2.1
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by decide) (by decide)
  have r0 := rk 0 (by norm_num)
  have r1 := rk 1 (by norm_num)
  have r2 := rk 2 (by norm_num)
  have r3 := rk 3 (by norm_num)
  have r4 := rk 4 (by norm_num)
  have r9 := rk 9 (by norm_num)
  have r13 := rk 13 (by norm_num)
  by_cases hk : c.nmem (c.nreg 150000) = 0
  · -- a chain descriptor: the chain cutter itself
    have hlt : c₁.nreg 170099 < c₁.nreg 170098 := by omega
    have hOk' := okModel_of_okI hMD hk hOk
    obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hcu P W c₁ w₁ (by
      grind) (by
      grind [GI])
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true hlt e₂), ?_, fun M' hM' => ?_,
      (Fr₁.trans (F₂.mono oracleBands_sub_io le_rfl)).mono (by simp) (by omega)⟩
    · beta_reduce at hk₂ ⊢
      rw [r9] at hk₂
      have : G (rd c bCut 9) + 3 ≤ GI G (rd c bCut 9) := by omega_nf
      omega
    · have hp := hpost M' (by ram_simp)
      simp only [r1, r2, r3, r4, r9, hA₁] at hp
      obtain ⟨p1, p2, p3, prest⟩ := hp
      have : G (rd c bCut 9) ≤ GI G (rd c bCut 9) := by omega_nf
      exact ⟨p1, p2, p3.trans this, prest⟩
  · -- the interior model
    have hge : ¬ c₁.nreg 170099 < c₁.nreg 170098 := by omega
    obtain ⟨hk1, hbit, hMI⟩ : c.nmem (rd c bCut 0) = 1 ∧
        (c.nmem (rd c bCut 0 + 1) = 1 ↔ Mountain.LeftInside (Qof P)) ∧
        M = interiorModel (Qof P) := by
      rcases hMD with ⟨h0, -⟩ | h
      · exact absurd h0 hk
      · exact h
    subst hMI
    have hD : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
    have hn3 : 3 ≤ (Qof P).n := by rw [hQ]; exact Chazelle.Jordan.simple_three_le hG.1
    have hmn : (interiorModel (Qof P)).W.n = (Qof P).n := mi_n
    -- the set-up
    obtain ⟨c₂, k₂, e₂, hk₂, S₂, hfree, hA₂, F₂⟩ := frontC_exec (O := O) c₁ w₁ hG hHW
      (by show (gradeCtx O).holds P c₁.nmem (rd c₁ bCut 13) (c₁.nreg ALLOC)
          simp_all)
      (by omega_nf)
      (by show rd c₁ bCut 0 + 6 ≤ c₁.nreg ALLOC
          rw [hA₁, r0]; exact hMDWF.1)
      (by omega_nf) (by
        grind [GI])
    have w₂ := e₂.wb_right
    have se1 : (statC c₁).e₁ = rd c bCut 1 := r1
    have sh1 : (statC c₁).h₁ = rd c bCut 2 := r2
    have se2 : (statC c₁).e₂ = rd c bCut 3 := r3
    have sh2 : (statC c₁).h₂ = rd c bCut 4 := r4
    have sγ : (statC c₁).γ = rd c bCut 9 := r9
    have q : QFacts (Qof P) (statC c₁).e₁ (statC c₁).h₁ (statC c₁).e₂ (statC c₁).h₂ := by
      grind [Chazelle.Core.IOrc.QFacts]
    obtain ⟨c₃, k₃, ps, e₃, hk₃, hne, hlen, hAL, hq, hLE, hr, hkp, hv, F₃⟩ :=
      queryC_exec (H := H) hcu c₂ w₂ S₂ hfree q (by grind) (by
        grind [GI])
    rw [se1, sh1, se2, sh2] at hkp
    rw [sγ] at hlen hv
    refine ⟨c₃, _, .seq e₁ (.ifLtN_false hge (.seq e₂ e₃)), ?_, fun M' hM' => ?_,
      ((Fr₁.trans F₂).trans F₃).mono (by simp) (by omega)⟩
    · grind [GI]
    · have hM'I : M' = interiorModel (Qof P) := by
        rcases hM' with ⟨h0, -⟩ | ⟨-, -, h⟩
        all_goals omega
      subst hM'I
      set K := (interiorModel (Qof P)).key (Qof P) with hK
      set A := c₃.nreg 150010 with hAd
      
      -- the order facts of the list
      have hsb := pkey_bd (N := P.n) hsP hs1
      have heb := pkey_bd (N := P.n) heP he1
      rw [hmn] at hsb heb
      obtain ⟨-, -, hmod, -, -, -, -, -⟩ := qplan q
      rw [se1, sh1, se2, sh2] at hmod
      have hy1 : (interiorModel (Qof P)).param (Qof P) ⟨rd c bCut 3, rd c bCut 4⟩ < 1 := heP.2.1
      have hle := ee_bound (Q := Qof P) (e₁ := rd c bCut 1) (h₁ := rd c bCut 2) (e₂ := rd c bCut 3)
        (h₂ := nh (Qof P) (rd c bCut 3) (rd c bCut 4)) (by omega) hsP.1
        (by rw [param_nh (by omega)]; exact hy1)
      rw [param_nh (by omega)] at hle
      obtain ⟨o1, o2, o3, o4⟩ := cut_out (s := ⟨rd c bCut 1, rd c bCut 2⟩)
        (e := ⟨rd c bCut 3, rd c bCut 4⟩) hkp hv hne (by rw [key_eq]) (by
          refine ⟨(((rd c bCut 1 + eeOf (Qof P) (rd c bCut 1) (rd c bCut 2) (rd c bCut 3)
            (nh (Qof P) (rd c bCut 3) (rd c bCut 4))) / (Qof P).n : ℕ) : ℤ), ?_⟩
          rw [key_eq]
          set a := rd c bCut 1 + eeOf (Qof P) (rd c bCut 1) (rd c bCut 2) (rd c bCut 3)
            (nh (Qof P) (rd c bCut 3) (rd c bCut 4)) with ha
          have e1 := Nat.mod_add_div a (Qof P).n
          rw [hmod] at e1
          have e2 : ((rd c bCut 3 : ℕ) : ℝ) + (Qof P).n * ((a / (Qof P).n : ℕ) : ℝ) = a := by
            exact_mod_cast e1
          have e3 : (a : ℝ) = rd c bCut 1 + eeOf (Qof P) (rd c bCut 1) (rd c bCut 2) (rd c bCut 3)
              (nh (Qof P) (rd c bCut 3) (rd c bCut 4)) := by grind
          simp only [Int.cast_natCast]
          linarith) hsb heb (by linarith)
      -- the list in memory
      have hlenq : c₃.nmem (rd c₃ bCut 10) = ps.length := hq
      have hpne := List.length_pos_iff.2 hne
      have hvi : ∀ i (hi : i < ps.length), PcV P (interiorModel (Qof P)) c₃.nmem (c₃.nreg ALLOC)
          (H (rd c bCut 9)) (rdPc c₃.nmem A i) := fun i hi => by
        ram_simp
      have hri : ∀ i (hi : i < ps.length), rdPc c₃.nmem A i = ps[i]'hi := hr
      dsimp only
      refine ⟨by rw [hA₁] at hA₂; show c.nreg ALLOC ≤ A; omega,
        by show A + 1 + 7 * c₃.nmem A ≤ c₃.nreg ALLOC; omega,
        by show c₃.nmem A ≤ GI G (rd c bCut 9); rw [hq]; unfold GI; omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show K (rdPc c₃.nmem A 0).s = K ⟨rd c bCut 1, rd c bCut 2⟩
        grind
      · show K (rdPc c₃.nmem A (c₃.nmem A - 1)).e = K ⟨rd c bCut 3, rd c bCut 4⟩
        grind
      · intro i hi
        rw [show c₃.nmem (rd c₃ bCut 10) = ps.length from hq] at hi
        show K (rdPc c₃.nmem A i).e = K (rdPc c₃.nmem A (i + 1)).s
        rw [hri i (by omega), hri (i + 1) hi]; exact o3 i hi
      · intro i hi
        rw [show c₃.nmem (rd c₃ bCut 10) = ps.length from hq] at hi
        show sideInArc (K (rdPc c₃.nmem A i).s) (K ⟨rd c bCut 3, rd c bCut 4⟩)
          (K (rdPc c₃.nmem A i).e)
        rw [hri i (by omega)]; exact o4 i hi
      · intro i hi
        rw [show c₃.nmem (rd c₃ bCut 10) = ps.length from hq] at hi
        exact (hvi i hi).2.2.2.2.2.1
      · intro i hi
        rw [show c₃.nmem (rd c₃ bCut 10) = ps.length from hq] at hi
        exact (hvi i hi).2.2.2.2.2.2
      · intro i hi
        rw [show c₃.nmem (rd c₃ bCut 10) = ps.length from hq] at hi
        have h := hvi i hi
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      · intro i hi
        rw [show c₃.nmem (rd c₃ bCut 10) = ps.length from hq] at hi
        exact (hvi i hi).2.2.2.2.1

end exec

end

end IOrc

end Chazelle.Core
