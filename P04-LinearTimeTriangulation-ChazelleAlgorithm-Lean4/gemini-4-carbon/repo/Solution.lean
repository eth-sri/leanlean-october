module

public import Chazelle

public section

open Chazelle.Core in
theorem Chazelle.linear_time_triangulation : Chazelle.LinearTimeTriangulation :=
  let ⟨O, hV⟩ := oracleSpec
  let ⟨_, _, hR⟩ := DrvB.regStepSpec_of DrvH.hostRamSpec DrvB.expSpec
  let hM := MergeAsm.mergeSpec_of
    (FuseAsm.fuseSpec_of
      (SweepIo.sweepSpecH_of
        (SweepEv.sweepEvSpec_of_rest
          (SweepEv.stopTask_of (SweepEv.orgTask_of' SweepEv.m2Task SweepEv.m1Task SweepEv.finTask)
            SweepEv.sortTask)
          SweepEv.winTask SweepEv.keyTask SweepEv.loopStartTask SweepEv.stepTask)
        (SweepIo.cand0Spec_of SweepIo.s0CandSpec SweepIo.lab0)
        (SweepIo.cand1Spec SweepIo.bruteSpec))
      buildNF)
    (restoreSpec_of_find buildNF Restore.findSpec) (Gran.granularize' buildNF)
  let sc := ShootCut.shootCutSpec O hV
  linear_of_core
    (core_of_phasesH setupSpec
      ⟨gradeCtx O, Up.upPhase_of' hM hV sc brute,
        DrvR.downPhaseH_of hM hV DrvX.extractRamSpec
          (DrvLT.lvTailSpec (IOrc.interiorOracles_of sc))
          fun _ => DrvB.baseSpec_of_regLoop (DrvB.regLoopSpec_of hR)⟩
      outputSpecH goodShearExists shearInvariance)
    Chazelle.Final.finalStage shearInvariance

end
