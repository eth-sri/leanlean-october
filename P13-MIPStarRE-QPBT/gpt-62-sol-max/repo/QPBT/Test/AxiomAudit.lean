module

meta import Lean
public import QPBT.Palomar.PauliCompleteness
public import QPBT.Palomar.LowDegreeSoundness
public import QPBT.Palomar.PauliSoundness

/-! Verify the axiom closure of the test results and their key ingredients. -/

meta section

open Lean Elab Command

elab "audit_standard_axioms " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← collectAxioms name
    unless axioms.qsort Name.lt == #[``propext, ``Classical.choice, ``Quot.sound] do
      throwError "'{name}' uses unexpected axioms: {axioms.toList}"
    logInfo m!"axioms of '{name}': {axioms.toList}"

audit_standard_axioms
  MIPStarRE.QPBT.pauli_soundness
  MIPStarRE.QPBT.pauli_soundness_qubit
  MIPStarRE.QPBT.exists_ld_soundness
  MIPStarRE.QPBT.exists_spcc_value_one
  MIPStarRE.QPBT.honestStrategy_isSPCC
  MIPStarRE.QPBT.exists_extendedLinesWitness_established
  MIPStarRE.QPBT.exists_globalPairWitness
  MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound
  MIPStarRE.QPBT.exists_projective_setting_isometry_bounds
  MIPStarRE.QPBT.exists_arbitrary_strategy_isometry_bounds
  MIPStarRE.QPBT.pauli_soundness_deltaQld_ofExtractionWitness
  MIPStarRE.QPBT.Palomar.exists_spcc_value_one
  MIPStarRE.QPBT.Palomar.exists_ld_soundness
  MIPStarRE.QPBT.Palomar.pauli_soundness
  MIPStarRE.QPBT.Palomar.pauli_soundness_qubit
  MIPStarRE.QPBT.fixedFieldModel
