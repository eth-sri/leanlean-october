module

public import Chazelle.Core.ClusterFinal
public import Chazelle.Core.ClusterLabelRam

/-!
# WP-I, part 65: the final labelling

`labS` loads the layout of the labelling of the primal map with the vertex flags `DF`
(slot 48) and runs `labelStmt`: two unflagged vertices get the same label (slot 2) iff they are
joined through unflagged vertices.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator

@[expose] public section

/-- The layout of the labelling: the primal map, the zero dart flags, the vertex flags `DF`. -/
def labLay (g : GV) : Lay := ⟨g.bO, g.bR, g.bV, g.base 0, g.base 1, g.base 48, g.base 2,
  g.base 3, g.base 4, g.base 5, g.μ, g.N⟩

theorem labLay_good {g : GV} {W : ℕ} (hμ : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0)
    (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    (labLay g).Good W := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3
  have b4 := g.base_eq 4; have b5 := g.base_eq 5; have b48 := g.base_eq 48
  refine ⟨fun b n h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [labLay, Disj] at *
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  all_goals first | omega

/-- The layout registers of the labelling. -/
def labCopies : List (ℕ × ℕ) :=
  [(130100, 130021), (130101, 130022), (130102, 130023), (130103, 130030), (130104, 130031),
   (130105, 130078), (130106, 130032), (130107, 130033), (130108, 130034), (130109, 130035),
   (130110, 130011)]

/-- **The labelling.** -/
def labS : Stmt := .seq (copies labCopies) labelStmt

/-- The registers written by `labS`. -/
def LabRG (r : ℕ) : Prop := (130100 ≤ r ∧ r ≤ 130142)

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
theorem labS_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M)
    (hF : ∀ u, u < g.μ → c.nmem (g.base 0 + u) < g.N ∧ c.nmem (g.bV + c.nmem (g.base 0 + u)) = u)
    (hzero : ∀ d, d < g.N → c.nmem (g.base 1 + d) = 0)
    (hμ : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W labS c c' k ∧ k ≤ 120 * g.μ + 50 * g.N + 30 ∧ WordsBounded W c' ∧
      (∀ r, ¬ LabRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      (∀ a, ¬ (g.base 2 ≤ a ∧ a < g.base 6) → c'.nmem a = c.nmem a) ∧
      ∀ x y, x < g.μ → y < g.μ → c.nmem (g.base 48 + x) ≠ 1 → c.nmem (g.base 48 + y) ≠ 1 →
        (c'.nmem (g.base 2 + x) = c'.nmem (g.base 2 + y) ↔
          (primalEnv c.nmem g.bO g.bR g.bV (g.base 0) (g.base 1) (g.base 48) g.μ g.N).Reach x y) := by
  have hU := g.U_ge; have hE := g.END_eq
  have b2 := g.base_eq 2; have b6 := g.base_eq 6; have b5 := g.base_eq 5
  have b3 := g.base_eq 3; have b4 := g.base_eq 4
  set Y := labLay g with hY
  have hYg : Y.Good W := labLay_good hμ hO hR hV hW
  unfold labS
  obtain ⟨c1, e1, hw1, h1, h2, hm1, hr1, hrm1, ho1⟩ := copies_exec (P := P) hw labCopies
    (b := 130090) (by decide) (by decide)
  have g1 : ∀ r, (r < 130100 ∨ 130110 < r) → c1.nreg r = c.nreg r := fun r hr =>
    h2 r (fun p hp h => by
      have := (show ∀ p ∈ labCopies, 130100 ≤ p.1 ∧ p.1 ≤ 130110 by decide) p hp; omega)
  have hG1 : GR g c1 := hG.frame (fun r hr => g1 r (by unfold GRReg at hr; omega))
  have cp : ∀ d s, (d, s) ∈ labCopies → c1.nreg d = c.nreg s := fun d s h => h1 _ h
  have hR0 : Regs0 Y c1 := ⟨hG1.one,
    by rw [cp 130100 130021 (by decide)]; exact hG.rO,
    by rw [cp 130101 130022 (by decide)]; exact hG.rR,
    by rw [cp 130102 130023 (by decide)]; exact hG.rV,
    by rw [cp 130103 130030 (by decide)]; exact hG.rbase 0 (by omega),
    by rw [cp 130104 130031 (by decide)]; exact hG.rbase 1 (by omega),
    by rw [cp 130105 130078 (by decide)]; exact hG.rbase 48 (by omega),
    by rw [cp 130106 130032 (by decide)]; exact hG.rbase 2 (by omega),
    by rw [cp 130107 130033 (by decide)]; exact hG.rbase 3 (by omega),
    by rw [cp 130108 130034 (by decide)]; exact hG.rbase 4 (by omega),
    by rw [cp 130109 130035 (by decide)]; exact hG.rbase 5 (by omega),
    by rw [cp 130110 130011 (by decide)]; exact hG.rμ⟩
  have henv : Y.env c1.nmem =
      primalEnv c.nmem g.bO g.bR g.bV (g.base 0) (g.base 1) (g.base 48) g.μ g.N := by
    rw [hm1]; rfl
  have hok : (Y.env c1.nmem).OK := by rw [henv]; exact primalEnv_ok hmap hF
  have hsym : (Y.env c1.nmem).Sym := by
    rw [henv]
    refine primalEnv_sym hmap (fun d hd => ?_)
    have ho : c.nmem (g.bO + d) < g.N := by rw [(hmap ⟨d, hd⟩).1]; exact (M.opp ⟨d, hd⟩).2
    rw [hzero _ ho, hzero _ hd]
  obtain ⟨c', k, e, hk, hw', hfr, hlt, hlab⟩ := labelStmt_exec (P := P) hYg hw1 hR0 hok hsym
  have hnv : Y.nv = g.μ := rfl
  have hYN : Y.N = g.N := rfl
  refine ⟨c', labCopies.length + k, .seq e1 e, by rw [show labCopies.length = 11 from rfl]; omega, hw', fun r hr => ?_, by rw [hfr.2.1, hr1],
    by rw [hfr.2.2.1, hrm1], by rw [hfr.2.2.2.1, ho1], fun a ha => ?_, fun x y hx hy h1x h1y => ?_⟩
  · rw [hfr.1 r (by unfold LScr Scr; unfold LabRG at hr; omega)]
    exact g1 r (by unfold LabRG at hr; omega)
  · rw [hfr.2.2.2.2 a (by
      simp only [Lay.Written, hY, labLay]
      have : g.μ + 3 ≤ g.U := by omega
      omega), hm1]
  · have hx' : (Y.env c1.nmem).vb x ≠ 1 := by
      show view c1.nmem (g.base 48) g.μ x ≠ 1
      rw [view_lt hx, hm1]; exact h1x
    have hy' : (Y.env c1.nmem).vb y ≠ 1 := by
      show view c1.nmem (g.base 48) g.μ y ≠ 1
      rw [view_lt hy, hm1]; exact h1y
    have := hlab x y (by rw [hnv]; exact hx) (by rw [hnv]; exact hy) hx' hy'
    rw [henv] at this
    simp only [labV, hY, labLay, view_lt hx, view_lt hy] at this
    exact this

end proofs

end

end Chazelle.Core.Cluster
