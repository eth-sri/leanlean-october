module

public import Chazelle.Core.RestoreTEnv

/-!
# WP-E, the candidate test on the RAM, part 21: the start of a run

* `tgood_of`: the precondition of `TestOK` gives the fixed data of the run (`TGood`); the walk
  length of a chain model fits the word bound (`hostWords`, `NFLoc.chain_n_le`).
* `tSetup`: the constants `83020 … 83023` (`tSetup_exec`: the run invariant holds after it).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

theorem chainModel_n' (C : Chain) : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _

/-- **The walk of a chain model fits the word bound.** -/
theorem walk_le_W {m : ℕ → ℕ} {MD A : ℕ} (hMD : ModelDescAt m MD (Qof P) M)
    (hwf : ModelDescWF P A m MD) (hW : hostWords P.n ≤ W) {C : Chain} (hM : M = chainModel C) :
    2 * C.m + 7 ≤ W := by
  obtain ⟨hz, H, C', hC, hM'⟩ := chainDesc_of hMD hM
  obtain ⟨hl, hHW, -, -⟩ := (hwf.2 hz).2 H C' hC
  have hN := NFLoc.chain_n_le hC hl hHW
  have hm := C'.m_lt
  have e : C.m = C'.m := by
    have := congrArg (fun M : Model => M.W.n) (hM.symm.trans hM')
    simp only [chainModel_n'] at this
    omega
  unfold hostWords at hW
  omega

/-- **The fixed data of a run** from the precondition of `TestOK`. -/
theorem tgood_of (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hMD : ModelDescAt c₀.nmem (c₀.nreg 83000) (Qof P) M)
    (hwf : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg 83000))
    (hreg : c₀.nmem (c₀.nreg 83000) = 0 → ∀ H C,
      ChainDescAt c₀.nmem (c₀.nreg 83000 + 1) (Qof P) H C → HostRegular (Qof P).n H)
    (hsimp : c₀.nmem (c₀.nreg 83000) = 0 → ∀ H C,
      ChainDescAt c₀.nmem (c₀.nreg 83000 + 1) (Qof P) H C → C.P.Simple)
    (hkind : OkModel P M ∨ M = interiorModel (Qof P)) (hGM : GoodModel M)
    (hN : NFWithin c₀.nmem (c₀.nreg 83001) (c₀.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hr : c₀.nreg 83002 < N.nRegions) (hxe : c₀.nreg 83005 < M.W.n)
    (hxp : ProperPos M (Qof P) P.n ⟨c₀.nreg 83005, c₀.nreg 83006⟩)
    (hxc : c₀.nreg 83006 = 0 ∨ 0 < M.param (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩)
    (hxC : ∀ C : Chain, M = chainModel C → M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩ ∈ C.set)
    (hh : c₀.nreg 83007 < P.n)
    (hy : ((Qof P).vtx (c₀.nreg 83007)).2 = (M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩).2)
    (hσ : c₀.nreg 83008 ≤ 1) : TGood P W M N c₀ :=
  ⟨hG, hW, hMD, hwf, hreg, hsimp, hkind, hGM, fun _C hM => walk_le_W hMD hwf hW hM, hN, hNF, hr, hxe,
    hxp, hxc, hxC, hh, hy, hσ⟩

/-- **The constants of a run.** -/
def tSetup : Stmt :=
  block [.constN 83022 0, .constN 83023 1, .addN 83020 83000 83023, .loadN 83021 83000]

theorem tSetup_exec (hw : WordsBounded W c) (hMD : c.nreg 83000 + 6 ≤ c.nreg ALLOC) :
    ∃ c' k, Exec P W tSetup c c' k ∧ k = 4 ∧ TInv W c c' ∧ RF dBands (c.nreg ALLOC) c c' k := by
  have hAW := hw.1 ALLOC
  obtain ⟨c', k, ex, hk, q22, q23, q20, q21, hr, hrr, hm, hrm, ho⟩ : ∃ c' k, Exec P W tSetup c c' k ∧
      k = 4 ∧ c'.nreg 83022 = 0 ∧ c'.nreg 83023 = 1 ∧ c'.nreg 83020 = c.nreg 83000 + 1 ∧
      c'.nreg 83021 = c.nmem (c.nreg 83000) ∧
      (∀ r, r ≠ 83020 → r ≠ 83021 → r ≠ 83022 → r ≠ 83023 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    unfold tSetup
    exec_block
    · omega
    · omega
    · config_simp; omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, ?_, rfl, rfl,
        rfl, rfl⟩
      intro r h1 h2 h3 h4
      simp [upd, h1, h2, h3, h4]
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by unfold ALLOC; omega)
    (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  refine ⟨c', k, ex, hk, ⟨ex.wb_right, fun q h1 h2 => hr q (by omega) (by omega) (by omega)
    (by omega), by omega, fun a _ => by rw [hm], q20, q21, q22, q23⟩, ?_⟩
  exact rf_of_regs (fun r hr' => hr r (by omega) (by omega) (by omega) (by omega)) hrr hm hrm ho

end

end Restore

end Chazelle.Core
