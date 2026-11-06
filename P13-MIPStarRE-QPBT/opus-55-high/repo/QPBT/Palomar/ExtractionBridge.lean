module

public import QPBT.Palomar.Bridge
public import QPBT.Palomar.Definitions
public import QPBT.Test.QubitForm

/-!
# Exact bridges for compact extraction errors

This module converts the existing qudit and qubit soundness witnesses to the
compact extraction witness.  It specializes the generic errors to the raw
prescribed-answer effects and proves exact equality with the established
soundness quantities.  No soundness existence or numerical estimate is added.

The legacy import form is required because the existing soundness modules have
not yet been converted to Lean's module system.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1491`;
`references/qpbt-paper/04_preliminaries.tex:1180-1228`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

namespace PauliSoundnessWitness




end PauliSoundnessWitness

namespace QubitSoundnessWitness




end QubitSoundnessWitness

namespace Palomar









end Palomar

end

end MIPStarRE.QPBT
