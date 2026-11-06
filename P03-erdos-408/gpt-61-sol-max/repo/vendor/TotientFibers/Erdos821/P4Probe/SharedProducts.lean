module
public import Mathlib.Tactic

public import Erdos821.P4Probe.GraphSharedPairing

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}



section
variable (ν : Pattern P J ell m) (g : P.Group)

lemma shared_slot_iff      i  :
    ν.shared g (ν.slot i) ↔ i ∉ ν.changed g := by
  constructor
  · rintro ⟨j, hj, hn⟩
    have hv : (ν.slot j).val = (ν.slot i).val := congrArg Fin.val hj
    have he : j = i := Fin.ext hv
    simpa [he] using hn
  · intro hn
    exact ⟨i, rfl, hn⟩

lemma shared_castAdd_iff      i  :
    ν.shared g (Fin.castAdd ell i) ↔ i ∉ ν.changed g := by
  solve_by_elim [shared_slot_iff]

lemma not_shared_natAdd      i  :
    ¬ν.shared g (Fin.natAdd J i) := by
  rintro ⟨j, hj, _⟩
  have he := congrArg Fin.val hj
  change j.val = J + i.val at he
  
  omega

end

end
end Erdos821.P4Probe
