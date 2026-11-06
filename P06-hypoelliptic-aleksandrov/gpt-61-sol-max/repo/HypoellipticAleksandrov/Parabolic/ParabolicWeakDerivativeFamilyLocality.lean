module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndexBoundCoherence
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal

/-!
# Locality for coherent parabolic weak-derivative families

This module restricts the raw domain of a coherent family and truncates its
parabolic derivative bound while preserving its selected representatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open MeasureTheory

variable {d L : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (F : ParabolicWeakDerivativeFamily d L U u) (hVU : V ⊆ U)

/-- Restrict a coherent weak-derivative family to a smaller raw domain,
without changing its selected representatives. -/
def restrict
     :
    ParabolicWeakDerivativeFamily d L V u where
  representative := F.representative
  memLp beta := (F.memLp beta).mono hVU
  zero_ae := F.zero_ae.filter_mono <|
    ae_mono <| Measure.restrict_mono_set volume hVU
  hasWeakTimeSucc beta h := (F.hasWeakTimeSucc beta h).restrict hVU
  hasWeakVelocitySucc beta i h :=
    (F.hasWeakVelocitySucc beta i h).restrict hVU

/-- Domain restriction preserves every selected representative literally. -/
@[simp] theorem restrict_representative
     (beta : ParabolicDerivativeIndex d L) :
    (restrict F hVU).representative beta = F.representative beta :=
  rfl

variable {d M L : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (F : ParabolicWeakDerivativeFamily d L U u) (hML : M ≤ L)

/-- Truncate a coherent weak-derivative family to a lower parabolic bound,
using the bound cast to retain the same representatives. -/
def truncate
     :
    ParabolicWeakDerivativeFamily d M U u where
  representative := fun beta => F.representative
    (ParabolicDerivativeIndex.castLE hML beta)
  memLp beta := F.memLp (ParabolicDerivativeIndex.castLE hML beta)
  zero_ae := by
    exact F.zero_ae
  hasWeakTimeSucc beta h := by
    exact F.hasWeakTimeSucc (ParabolicDerivativeIndex.castLE hML beta) (h.trans hML)
  hasWeakVelocitySucc beta i h := by
    simpa only [ParabolicDerivativeIndex.castLE_velocitySucc] using
      F.hasWeakVelocitySucc
        (ParabolicDerivativeIndex.castLE hML beta) i (h.trans hML)



end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
