module

public import Chazelle.Core.Reduction
public import Chazelle.Core.Output
public import Chazelle.Core.Setup
public import Chazelle.Core.RestoreSpecMain
public import Chazelle.Core.RestoreFindOK
public import Chazelle.Core.MergeAsmSpec
public import Chazelle.Core.FuseAsmSpec
public import Chazelle.Core.GranTop
public import Chazelle.Core.NFBuildMain
public import Chazelle.Core.BruteMain
public import Chazelle.Core.OraclePrepMain
public import Chazelle.Core.ShootCutMain
public import Chazelle.Core.UpPhaseOf

/-!
# The reduction of the target after FindSpec

With `Restore.findSpec` proved, `RestoreSpec` holds outright, and `MergeSpec` follows from
`SweepSpecH` alone. With the oracle (`oracleSpec`), the shooter/cutter (`shootCutSpec`), the
brute-force leaves (`brute`) and the up phase (`upPhase_of'`), the target follows from
`SweepSpecH` and the strengthened down phase `DownPhaseSpecH` for the grade context of a valid
oracle (`linear_of_sweep_down`). This records exactly what remains to be proved.
-/

namespace Chazelle.Core

public section

/-- **WP-E: restoring conformality**, unconditionally. -/
theorem restoreSpec : RestoreSpec := restoreSpec_of_find buildNF Restore.findSpec

/-- **The merge (Lemma 3.5) from the sweep.** -/
theorem mergeSpec_of_sweep (hS : SweepSpecH) : MergeSpec :=
  MergeAsm.mergeSpec_of (FuseAsm.fuseSpec_of hS buildNF) restoreSpec (Gran.granularize' buildNF)

/-- **The up phase from the sweep**, for every valid oracle interface. -/
theorem upPhase_of_sweep (hS : SweepSpecH) {O : OracleIface} (hV : O.Valid) :
    UpPhaseSpec (gradeCtx O) :=
  Up.upPhase_of' (mergeSpec_of_sweep hS) hV (ShootCut.shootCutSpec O hV) brute

/-- **Reduction of the main theorem** to the sweep (WP-D) and the down phase (WP-M). -/
theorem linear_of_sweep_down (hS : SweepSpecH)
    (hD : ∀ O : OracleIface, O.Valid → DownPhaseSpecH (gradeCtx O)) :
    LinearTimeTriangulation := by
  obtain ⟨O, hV⟩ := oracleSpec
  exact linear_of_core
    (core_of_phasesH setupSpec ⟨gradeCtx O, upPhase_of_sweep hS hV, hD O hV⟩ outputSpecH
      goodShearExists shearInvariance)
    Chazelle.Final.finalStage shearInvariance

end

end Chazelle.Core
