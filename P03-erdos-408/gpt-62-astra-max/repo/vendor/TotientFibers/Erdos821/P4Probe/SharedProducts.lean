module

public import Erdos821.P4Probe.GraphSharedPairing

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

local instance sharedProductSiteDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (BigSite P M) := Classical.decEq _

lemma shared_slot_iff (ν : Pattern P J ell m) (g : P.Group) (i : Fin J) :
    ν.shared g (ν.slot i) ↔ i ∉ ν.changed g := by
  constructor
  · rintro ⟨j, hj, hn⟩
    have hv : (ν.slot j).val = (ν.slot i).val := congrArg Fin.val hj
    have he : j = i := Fin.ext hv
    simpa [he] using hn
  · intro hn
    exact ⟨i, rfl, hn⟩

lemma shared_castAdd_iff (ν : Pattern P J ell m) (g : P.Group) (i : Fin J) :
    ν.shared g (Fin.castAdd ell i) ↔ i ∉ ν.changed g := by
  have hs : ν.slot i = Fin.castAdd ell i := by apply Fin.ext; rfl
  rw [← hs, shared_slot_iff]

lemma not_shared_natAdd (ν : Pattern P J ell m) (g : P.Group) (i : Fin ell) :
    ¬ν.shared g (Fin.natAdd J i) := by
  rintro ⟨j, hj, _⟩
  have he := congrArg Fin.val hj
  change j.val = J + i.val at he
  have hi := j.isLt
  omega

end
end Erdos821.P4Probe
