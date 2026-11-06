module

public import Chazelle.Golf

public import Chazelle.Core.ClusterStageC3

/-!
# WP-I, part 59: stage C — the tables, composed

`stageC`: the halving table (slot 39), the powers of two (slot 40), the residues (slot 33), the
residue counts (slot 34), the least frequent residue `ρ`, and the level tables for the shift
`k' - 1 - ρ` (slots 35–38).
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- **Stage C.** -/
def stageC : Stmt := .seq halfS (.seq powS (.seq resS (.seq rcS (.seq argS lvS))))

/-- The memory written by stage C. -/
def CMem (g : GV) (a : ℕ) : Prop := g.base 33 ≤ a ∧ a < g.base 41

section proofs

variable {P : Polygon} {W : ℕ}


/-- **Stage C.** -/
theorem stageC_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hk : 0 < g.k') (hkμ : g.k' ≤ g.μ) {lev : ℕ → ℕ}
    (hlev : ∀ v, v < g.μ → c.nmem (g.base 3 + v) = lev v) (hlt : ∀ v, v < g.μ → lev v < g.μ)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageC c c' k ∧ k ≤ 80 * g.μ + 6 * g.L + 60 ∧ WordsBounded W c' ∧
      PFr StCRG (CMem g) c c' ∧
      (∀ w, w ≤ g.μ → c'.nmem (g.base 39 + w) = w / 2) ∧
      (∀ j, j < g.L → c'.nmem (g.base 40 + j) = 2 ^ j) ∧
      ∃ ρ, ρ < g.k' ∧ (∀ l, l < g.μ → LvOK g c'.nmem (g.k' - 1 - ρ) l) ∧
        ∀ r, r < g.k' → cntBelow (fun v => lev v % g.k') g.μ ρ ≤
          cntBelow (fun v => lev v % g.k') g.μ r := by
  have hU := g.U_ge; have hE := g.END_eq; have hLU := g.L_le_U
  have b3 := g.base_eq 3; have b33 := g.base_eq 33; have b34 := g.base_eq 34
  have b35 := g.base_eq 35; have b39 := g.base_eq 39; have b40 := g.base_eq 40
  have b41 := g.base_eq 41
  have fr : ∀ {Am : ℕ → Prop} {c1 c2 : Config}, PFr StCRG Am c1 c2 → (∀ a, Am a → CMem g a) →
      PFr StCRG (CMem g) c1 c2 := fun h hA => h.mono (fun r h => h) hA
  have gr : ∀ {c1 : Config}, PFr StCRG (CMem g) c c1 → GR g c1 := fun h =>
    hG.frame (fun r hr => h.1 r (by unfold GRReg at hr; unfold StCRG; omega))
  unfold stageC
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, hh1⟩ := halfS_exec (P := P) hw hG hW
  have f1 : PFr StCRG (CMem g) c c1 := fr hf1 (fun a h => by unfold CMem; omega)
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hp2⟩ := powS_exec (P := P) hw1 (gr f1) hW
  have f2 : PFr StCRG (CMem g) c c2 := f1.trans (fr hf2 (fun a h => by unfold CMem; omega))
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hr3⟩ := resS_exec (P := P) hw2 (gr f2) hk hkμ hW
  have f3 : PFr StCRG (CMem g) c c3 := f2.trans (fr hf3 (fun a h => by unfold CMem; omega))
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hc4⟩ := rcS_exec (P := P) hw3 (gr f3) hk hkμ
    (lev := lev) (fun v hv => by rw [f3.2.2.2.2 _ (by unfold CMem; omega)]; exact hlev v hv) hlt
    hr3 hW
  have f4 : PFr StCRG (CMem g) c c4 := f3.trans (fr hf4 (fun a h => by unfold CMem; omega))
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hρ5, hmin5⟩ := argS_exec (P := P) hw4 (gr f4) hk hkμ hc4
    (fun r hr => cntBelow_le _ _ _) hW
  have f5 : PFr StCRG (CMem g) c c5 := f4.trans (fr hf5 (fun a h => h.elim))
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, -, hlv6⟩ := lvS_exec (P := P) hw5 (gr f5) hk hkμ rfl hρ5 hW
  have f6 : PFr StCRG (CMem g) c c6 := f5.trans (fr hf6 (fun a h => by
    unfold LvMem at h; unfold CMem; omega))
  have k16 : ∀ a, ¬ LvMem g a → ¬ (g.base 33 ≤ a ∧ a < g.base 33 + g.μ) →
      ¬ (g.base 34 ≤ a ∧ a < g.base 34 + g.k') → c6.nmem a = c2.nmem a := fun a h6 h3 h4 => by
    Ξ hf6.2.2.2.2 a h6, hf5.2.2.2.2 a id, hf4.2.2.2.2 a h4, hf3.2.2.2.2 a h3
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + k6)))),
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6)))), ⋄, hw6, f6,
    fun w hw' => ?_, fun j hj => ?_, c5.nreg 130836, hρ5, hlv6, hmin5⟩
  · rw [k16 _ (by unfold LvMem; omega) (⋄) (⋄),
      hf2.2.2.2.2 _ (⋄)]; exact hh1 w hw'
  · rw [k16 _ (by unfold LvMem; omega) (⋄) (⋄)]; exact hp2 j hj

end proofs

end

end Chazelle.Core.Cluster
