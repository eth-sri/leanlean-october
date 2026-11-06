module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import DedekindZetaZeroFree.MeasureTheory.Lp.MeasurePreservingEquivalences

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/MeasureTheory/Group/Conjugation.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace DedekindZetaZeroFree.TauCeti

variable {G E : Type*} [MeasurableSpace G] [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure G}

section DivInvMonoid

variable [DivInvMonoid G] [MeasurableMul G]

instance instMeasurableConstSMulConjAct : MeasurableConstSMul (ConjAct G) G where
  measurable_const_smul c := by
    simp only [ConjAct.smul_def]
    exact (measurable_id.const_mul _).mul_const _

instance instSMulInvariantMeasureConjAct [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] :
    SMulInvariantMeasure (ConjAct G) G μ where
  measure_preimage_smul c s hs := by
    simp only [ConjAct.smul_def]
    exact ((measurePreserving_mul_right μ (ConjAct.ofConjAct c)⁻¹).comp
      (measurePreserving_mul_left μ (ConjAct.ofConjAct c))).measure_preimage hs.nullMeasurableSet
