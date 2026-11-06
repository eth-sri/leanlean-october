module

public import Chazelle.Core.Lemma41Exec
public import Chazelle.Core.Lemma41Bridge
public import Chazelle.Core.ShootCutGrade

/-!
# WP-J, part 29: Lemma 4.1

`lemma41_of`: the merge package (`MergeSpec`) and the oracles of the merges (`ShootCutSpec O`)
give `Lemma41Spec O`: the program `l41S (mk sh cu)` (`l41_exec`) within
`K (lemma41Nat λ + 1)` steps (`l41Big_le`).
-/

namespace Chazelle.Core.L41

open Machine Chazelle

@[expose] public section

/-- **Lemma 4.1** (WP-J, goal 1). -/
theorem lemma41_of (O : OracleIface) (hM : MergeSpec) (hSC : ShootCutSpec O) :
    Lemma41Spec O := by
  obtain ⟨sh, cu, κs, hsh, hcu⟩ := hSC
  obtain ⟨mk, κM, hmk⟩ := mergeMeets_of hM
  have hMM : MergeMeets (mk sh cu) κM (scF κs) (scG κs) cutGran (gradeCtx O) OkModel :=
    hmk sh cu oracleBands oracleBands (scF κs) (scG κs) cutGran (gradeCtx O) OkModel
      (gradeCtx_capLocal O) (ShootCut.gradeCtx_halves O) (fun _ _ => id) (scF_mono κs) (scG_mono κs) cutGran_mono
      subset_rfl subset_rfl hsh hcu
  refine ⟨l41S (mk sh cu), lvK (κM 4) κs + 400, ?_⟩
  intro P W c hw ⟨hG, hWh, hX, hΛ, h7, han, hL1, hL2⟩ hbud
  have h7'  := h7
  have e : l41Big κM (scF κs) (scG κs) cutGran (rd c bL41 3) (rd c bL41 1) (rd c bL41 2) =
      l41Big (fun _ => κM 4) (scF κs) (scG κs) cutGran (rd c bL41 3) (rd c bL41 1)
        (rd c bL41 2) := rfl
  have hB := l41Big_le (κM 4) κs (a := rd c bL41 1) h7' hL1 hL2
  rw [← e] at hB
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ :=
    l41_exec hG hWh hMM (scF_mono κs) (scG_mono κs) cutGran_mono hw rfl rfl rfl rfl rfl hX hΛ h7'
      han hL1 hL2 (le_trans (Nat.add_le_add_left hB _) hbud)
  exact ⟨c', k, ex, le_trans hk hB, hpost, hfr⟩

end

end Chazelle.Core.L41
