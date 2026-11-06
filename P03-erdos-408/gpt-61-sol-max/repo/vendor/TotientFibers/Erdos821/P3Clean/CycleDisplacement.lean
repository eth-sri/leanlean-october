module
public import Mathlib.Tactic

public import Erdos821.P3Clean.ConditionedKernel

/-! The big dilation exponent gives a natural power of one fixed cyclic translation. -/

@[expose] public section

noncomputable section

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

abbrev PendingCycle (P ) (B ) :=
  TranslationCycle (pendingTranslationEquiv (P := P) B 1)

def dilationCycleStep (A : Model F P J m) (B ) (forward : Bool)
    (d : SmallLabels P J)  :=
  ((if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ)) •
    cycleStep (pendingTranslationEquiv (P := P) B 1)

def cycleDisplacement (A : Model F P J m) (B ) (ν : Pattern P J F.ell m)
    (forward : Bool) (d : SmallLabels P J) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J)  :=
  (ν.DBig a u) • dilationCycleStep A B forward d

section
variable (A : Model F P J m) (B : ℕ)

theorem cycleDisplacement_act     (ν : Pattern P J F.ell m)
     forward  (d : SmallLabels P J) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    cycleAct (pendingTranslationEquiv (P := P) B 1)
      (cycleDisplacement A B ν forward d a u) = pendingTranslationEquiv B (bigStep A ν forward d a u) := by
  unfold cycleDisplacement dilationCycleStep
  rw [← natCast_zsmul, ← mul_zsmul]
  rw [cycleAct_step_zsmul]
  have he : (ν.DBig a u : ℤ) *
      ((if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ)) =
      bigStep A ν forward d a u := by unfold bigStep; ring
  rw [he]
  exact (pendingTranslationEquiv_zpow B (bigStep A ν forward d a u)).symm

theorem cycleDisplacement_character    
    [Fintype (CutPendingState P B)] (forward : Bool) (d : SmallLabels P J)
    (psi : AddChar (PendingCycle P B) ℂ) :
    ∃ theta : ℝ, ∀ (ν : Pattern P J F.ell m) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J),
      psi (cycleDisplacement A B ν forward d a u) = phase (theta * (ν.DBig a u : ℝ)) := Exists.casesOn (Erdos821.P3Clean.character_nsmul_phase psi (Erdos821.P3Clean.dilationCycleStep A B forward d)) fun theta ht => Exists.intro theta fun ν a u => ht (ν.DBig a u)

end


end Erdos821.P3Clean
