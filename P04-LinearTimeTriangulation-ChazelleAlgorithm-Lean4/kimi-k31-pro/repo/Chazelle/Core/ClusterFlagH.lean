module

public import Chazelle.Core.ClusterDInit
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# WP-I, part 63: flagging the light levels

`flagS`: for every vertex `v < μ` of a light level (`HL[LEV[v]] = 1`), `DF[v] := 1`; after the
split driver, `DF` then flags `D* = D ∪ H`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- One vertex of the flagging. -/
def flagBody : Stmt := .seq (block [.addN 130891 130033 130890, .loadN 130892 130891,
  .addN 130891 130066 130892, .loadN 130893 130891])
  (.seq (.ifLtN 130893 130001 .skip (block [.addN 130891 130078 130890, .storeN 130891 130001]))
  (.instr (.addN 130890 130890 130001)))

/-- **Flag the light levels.** -/
def flagS : Stmt := .seq (.instr (.constN 130890 0)) (.whileLtN 130890 130011 flagBody)

/-- The registers of the flagging. -/
def FlRG (r : ℕ) : Prop := 130890 ≤ r ∧ r ≤ 130899

section proofs

variable {P : Polygon} {W : ℕ}

theorem flagS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hlt : ∀ v, v < g.μ → c.nmem (g.base 3 + v) < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W flagS c c' k ∧ k ≤ 14 * g.μ + 3 ∧ WordsBounded W c' ∧
      PFr FlRG (fun a => g.base 48 ≤ a ∧ a < g.base 48 + g.μ) c c' ∧
      ∀ v, v < g.μ → c'.nmem (g.base 48 + v) =
        if c.nmem (g.base 36 + c.nmem (g.base 3 + v)) < 1 then c.nmem (g.base 48 + v) else 1 := by
  have hU := g.U_ge; have hE := g.END_eq; have b3 := g.base_eq 3; have b36 := g.base_eq 36
  have b48 := g.base_eq 48
  set Am : ℕ → Prop := fun a => g.base 48 ≤ a ∧ a < g.base 48 + g.μ with hAm
  unfold flagS
  have e1 := Exec.constN (P := P) hw 130890 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130890 0 } with hc1
  have f1 : PFr FlRG Am c c1 :=
    ⟨fun r hr => by simp only [c1, Machine.upd_other _ _ _ (show r ≠ 130890 by
        ufo FlRG at hr)], rfl, rfl, rfl, fun a _ => rfl⟩
  have hG1 : GR g c1 := hG.frame (fun r hr => f1.1 r (by unfold GRReg at hr; ufo FlRG))
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130890) (rn := 130011) (body := flagBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130890 = j ∧ c'.nreg 130011 = g.μ ∧
      PFr FlRG Am c c' ∧
      ∀ v, v < g.μ → c'.nmem (g.base 48 + v) = if j ≤ v then c.nmem (g.base 48 + v) else
        if c.nmem (g.base 36 + c.nmem (g.base 3 + v)) < 1 then c.nmem (g.base 48 + v) else 1)
    g.μ 12 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hm3⟩ => by
      have hG3 : GR g c3 := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; ufo FlRG))
      have r33 := hG3.rbase 3 (by omega); have r66 := hG3.rbase 36 (by omega)
      have r78 := hG3.rbase 48 (by omega); have r1 := hG3.one
      have hlj := hlt j hj
      have ml : c3.nmem (g.base 3 + j) = c.nmem (g.base 3 + j) := hf3.2.2.2.2 _ (by omega)
      have mh : c3.nmem (g.base 36 + c.nmem (g.base 3 + j)) =
          c.nmem (g.base 36 + c.nmem (g.base 3 + j)) := hf3.2.2.2.2 _ (by omega)
      obtain ⟨c4, k4, e4, hk4, hw4, h93, h90, h4r, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
          (block [.addN 130891 130033 130890, .loadN 130892 130891,
            .addN 130891 130066 130892, .loadN 130893 130891]) c3 c4 k4 ∧ k4 = 4 ∧
          WordsBounded W c4 ∧ c4.nreg 130893 = c.nmem (g.base 36 + c.nmem (g.base 3 + j)) ∧
          c4.nreg 130890 = j ∧ (∀ r, ¬ FlRG r → c4.nreg r = c3.nreg r) ∧ c4.nmem = c3.nmem ∧
          c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
        exec_block
        · rwo [r33, hi3]
        · config_simp; rwo [r66, r33, hi3, ml]
        · refine ⟨rfl, ‹_›, by config_simp; rw [r66, r33, hi3, ml, mh], by config_simp; exact hi3,
            fun r hr => ?_, rfl, rfl, rfl, rfl⟩
          simp only; unfold FlRG at hr
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
      have r1' : c4.nreg 130001 = 1 := by rwx [h4r _ (by ufo FlRG)]
      have r78' : c4.nreg 130078 = g.base 48 := by rwx [h4r _ (by ufo FlRG)]
      obtain ⟨c5, k5, e5, hk5, hw5, h5r, h590, hm5, hrr5, hrm5, ho5⟩ : ∃ c5 k5, Exec P W
          (.ifLtN 130893 130001 .skip (block [.addN 130891 130078 130890, .storeN 130891 130001]))
          c4 c5 k5 ∧ k5 ≤ 4 ∧ WordsBounded W c5 ∧ (∀ r, ¬ FlRG r → c5.nreg r = c4.nreg r) ∧
          c5.nreg 130890 = j ∧
          c5.nmem = (if c.nmem (g.base 36 + c.nmem (g.base 3 + j)) < 1 then c4.nmem else
            upd c4.nmem (g.base 48 + j) 1) ∧
          c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output := by
        by_cases hp : c4.nreg 130893 < c4.nreg 130001
        · refine ⟨c4, 0 + 1, .ifLtN_true hp (.skip hw4), by omega, hw4, fun r _ => rfl, h90, ?_,
            rfl, rfl, rfl⟩
          rw [h93, r1'] at hp; rw [ite_eq_left hp]
        · obtain ⟨c6, k6, e6, hk6, hw6, h6r, h690, hm6, hrr6, hrm6, ho6⟩ : ∃ c6 k6, Exec P W
              (block [.addN 130891 130078 130890, .storeN 130891 130001]) c4 c6 k6 ∧ k6 = 2 ∧
              WordsBounded W c6 ∧ (∀ r, ¬ FlRG r → c6.nreg r = c4.nreg r) ∧
              c6.nreg 130890 = j ∧ c6.nmem = upd c4.nmem (g.base 48 + j) 1 ∧
              c6.rreg = c4.rreg ∧ c6.rmem = c4.rmem ∧ c6.output = c4.output := by
            exec_block
            · rwo [r78', h90]
            · refine ⟨rfl, ‹_›, fun r hr => ?_, by config_simp; exact h90,
                by config_simp; rw [r78', h90, r1'], rfl, rfl, rfl⟩
              simp only; unfold FlRG at hr
              repeat (rw [Machine.upd_other _ _ _ (by omega)])
          refine ⟨c6, k6 + 2, .ifLtN_false hp e6, by omega, hw6, h6r, h690, ?_, hrr6, hrm6, ho6⟩
          rw [h93, r1'] at hp; rw [ite_eq_right hp, hm6]
      have e7 := Exec.addN (P := P) hw5 130890 130890 130001 (by
        rwo [h590, h5r _ (by ufo FlRG), r1'])
      refine ⟨_, k4 + (k5 + 1), .seq e4 (.seq e5 e7), by omega, e7.wb_right, ?_, ?_, ?_, ?_⟩
      · simp only [Machine.upd_same]
        rw [h590, h5r _ (by ufo FlRG), r1']
      · simp only [Machine.upd_other _ _ _ (show (130011 : ℕ) ≠ 130890 by omega)]
        rwx [h5r _ (by ufo FlRG), h4r _ (by ufo FlRG)]
      · refine hf3.trans ⟨fun r hr => ?_, by simp only; rw [hrr5, hrr4],
          by simp only; rw [hrm5, hrm4], by simp only; rw [ho5, ho4], fun a ha => ?_⟩
        · simp only
          rw [Machine.upd_other _ _ _ (by ufo FlRG at hr), h5r r hr, h4r r hr]
        · simp only; rw [hm5, hm4]
          split_ifs
          · rfl
          · rw [Machine.upd_other _ _ _ (by sio only [hAm] at ha)]
      · intro v hv
        simp only; rw [hm5, hm4]
        by_cases hvj : v = j
        · subst hvj
          rw [ite_eq_right (show ¬ (v + 1 ≤ v) by omega)]
          by_cases hL : c.nmem (g.base 36 + c.nmem (g.base 3 + v)) < 1
          · rw [ite_eq_left hL, ite_eq_left hL, hm3 v hv, ite_eq_left le_rfl]
          · rw [ite_eq_right hL, ite_eq_right hL, Machine.upd_same]
        · have e : (if c.nmem (g.base 36 + c.nmem (g.base 3 + j)) < 1 then c3.nmem else
              upd c3.nmem (g.base 48 + j) 1) (g.base 48 + v) = c3.nmem (g.base 48 + v) := by
            split_ifs
            · rfl
            · rw [Machine.upd_other _ _ _ (by omega)]
          rw [e, hm3 v hv]
          by_cases hjv : j + 1 ≤ v
          · rw [ite_eq_left (show j ≤ v by omega), ite_eq_left hjv]
          · rw [ite_eq_right (show ¬ j ≤ v by omega), ite_eq_right hjv])
    (j₀ := 0) ⟨e1.wb_right, by simp [c1], hG1.rμ, f1, fun v hv => by simp [c1]⟩ (Nat.zero_le _)
  exact ⟨c', 1 + k, .seq e1 e, by omega, hw', hf', fun v hv => by rw [hm' v hv, ite_eq_right (by omega)]⟩

end proofs

end

end Chazelle.Core.Cluster
