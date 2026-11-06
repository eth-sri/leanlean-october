module

public import NearlyMinimax.ProductBoundedDifferences
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Genuine independent label blocks for the actual finite history marks
-/

𝚫
𝚨

variable {J I E : Type*} [Fintype J] [Fintype I] [MeasurableSpace E]

𝗇 𝔇 I → J
𝗇 𝔈 I → E
/-- Reconstruct each actual occurrence mark from the independent vector for its true label.
Unused coordinates give a harmless redundant realization of independent finite label blocks. -/
def labelBlockReconstruct (labels : 𝔇) (blocks : J → 𝔈) : 𝔈 :=
  fun i => blocks (labels i) i

omit [Fintype J] [Fintype I] in
/-- The actual label-block reconstruction is jointly measurable. -/
theorem labelBlockReconstruct_measurable (labels : 𝔇) :
    Measurable $ labelBlockReconstruct labels (E := E) := by
  apply measurable_pi_iff.2
  intro i
  exact 𝘜 $ measurable_pi_apply $ labels i

𝗇 𝔄 if labels i = j then s i else Set.univ
𝗇 𝔅 𝘰
/-- Redundant independent label vectors reproduce exactly the original independent occurrence marks. -/
theorem labelBlockReconstruct_preserving (labels : 𝔇) (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (labelBlockReconstruct labels )
      (Measure.pi fun _ => 𝔅 )
      𝔅 := by
  classical
  refine ⟨labelBlockReconstruct_measurable labels, ?_⟩
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [Measure.map_apply (labelBlockReconstruct_measurable labels) $ MeasurableSet.univ_pi hs ]
  have hp : labelBlockReconstruct labels ⁻¹' Set.univ.pi s =
      Set.univ.pi fun j => Set.univ.pi fun i => 𝔄 := by
    aesop
  rw [hp, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  have he : ∀ j i, π 𝔄 =
      if labels i = j then π $ s i else 1 := by
    bound
  simp_rw [he]
  rw [Finset.prod_comm]
  simp

omit [Fintype J] [Fintype I] [MeasurableSpace E] in
/-- Replacing a label block leaves every occurrence of another label exactly unchanged. -/
theorem labelBlockReconstruct_update_other [DecidableEq J] (labels : 𝔇) (blocks : J → 𝔈)
    (j : J) (new : 𝔈) (i : I) (hi : labels i ≠ j) :
    labelBlockReconstruct labels (Function.update blocks j new) i = labelBlockReconstruct labels blocks i := by
  classical
  simp [labelBlockReconstruct, Function.update_of_ne hi]
