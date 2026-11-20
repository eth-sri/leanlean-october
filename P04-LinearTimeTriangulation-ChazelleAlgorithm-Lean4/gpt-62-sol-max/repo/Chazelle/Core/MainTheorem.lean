module

public import Chazelle.Core.SpecPhases
public import Chazelle.Core.ShearInv
public import Chazelle.Core.ShearGood
public import Chazelle.Final.Driver
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
public import Chazelle.Core.DownPhaseDrvMain
public import Chazelle.Core.DownPhaseDrvLTMain
public import Chazelle.Core.DownPhaseDrvBTopMain
public import Chazelle.Core.DownPhaseDrvXFinal
public import Chazelle.Core.DownPhaseDrvBLoopMain
public import Chazelle.Core.DownPhaseDrvBRegC
public import Chazelle.Core.DownPhaseDrvBExpD
public import Chazelle.Core.SweepIoMain
public import Chazelle.Core.SweepEvRest
public import Chazelle.Core.SweepIoCand1
public import Chazelle.Core.SweepIoBrute
public import Chazelle.Core.SweepEvKey2Main
public import Chazelle.Core.SweepEvWin
public import Chazelle.Core.SweepEvStepL
public import Chazelle.Core.SweepIoCand0Main
public import Chazelle.Core.SweepIoS0CandFinal
public import Chazelle.Core.SweepIoLab0
public import Chazelle.Core.SweepEvLoopStart
public import Chazelle.Core.SweepEvStopLoop
public import Chazelle.Core.SweepEvStopSort6
public import Chazelle.Core.SweepEvStopRF
public import Chazelle.Core.SweepEvStopM1C5
public import Chazelle.Core.SweepEvStopM2C3
public import Chazelle.Core.SweepEvStopFin8

namespace Chazelle.Core

/-- Assemble the sweep from the stop handlers, event loop, and both candidate queries. -/
private theorem sweepSpec : SweepSpecH := by
  have hOrg := SweepEv.orgTask_of' SweepEv.m2Task SweepEv.m1Task SweepEv.finTask
  have hStop := SweepEv.stopTask_of hOrg SweepEv.sortTask
  have hEv := SweepEv.sweepEvSpec_of_rest hStop SweepEv.winTask SweepEv.keyTask
    SweepEv.loopStartTask SweepEv.stepTask
  exact SweepIo.sweepSpecH_of hEv (SweepIo.cand0Spec_of SweepIo.s0CandSpec SweepIo.lab0)
    (SweepIo.cand1Spec SweepIo.bruteSpec)

/-- **Linear-time triangulation of a simple polygon** (Chazelle). -/
public theorem linearTimeTriangulation : LinearTimeTriangulation := by
  obtain ⟨O, hV⟩ := oracleSpec
  have hSC := ShootCut.shootCutSpec O hV
  have hRestore := Restore.restoreSpec_of_find buildNF Restore.findSpec
  have hMerge := MergeAsm.mergeSpec_of (FuseAsm.fuseSpec_of sweepSpec buildNF)
    hRestore (Gran.granularize' buildNF)
  obtain ⟨s, κ, hR⟩ := DrvB.regStepSpec_of DrvH.hostRamSpec DrvB.expSpec
  have hUp := Up.upPhase_of' hMerge hV hSC brute
  have hDown := DrvR.downPhaseH_of hMerge hV DrvX.extractRamSpec
    (DrvLT.lvTailSpec (IOrc.interiorOracles_of hSC))
    (fun n₀ => DrvB.baseSpec_of_regLoop (DrvB.regLoopSpec_of hR))
  exact linear_of_core
    (core_of_phasesH setupSpec ⟨gradeCtx O, hUp, hDown⟩ outputSpecH goodShearExists shearInvariance)
    Chazelle.Final.finalStage shearInvariance

end Chazelle.Core
