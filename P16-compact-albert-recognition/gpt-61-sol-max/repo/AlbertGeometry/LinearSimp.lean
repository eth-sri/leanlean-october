module
public meta import Lean
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Glennie.Tactic.SimpAttr
@[expose] public section
attribute [clm_eval] ContinuousLinearMap.add_apply ContinuousLinearMap.sub_apply
  ContinuousLinearMap.smul_apply ContinuousLinearMap.comp_apply ContinuousLinearMap.flip_apply
  ContinuousLinearMap.zero_apply ContinuousLinearMap.bilinearComp_apply
  ContinuousLinearMap.smulRight_apply ContinuousLinearMap.id_apply
attribute [clm_eval] map_add map_sub map_smul map_zero map_sum smul_eq_mul
  Pi.smul_apply Pi.add_apply Pi.sub_apply Function.comp_apply Finset.sum_apply

public meta section
/-- Install the canonical real operator norm and scalar action, with stable local names. -/
macro "real_operator_norms " n:ident s:ident X:term:max Y:term:max : command => do
  let a ← `(command| local instance $n:ident : NormedAddCommGroup ($X →L[ℝ] $Y) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := $X) (F := $Y) (σ₁₂ := RingHom.id ℝ))
  let b ← `(command| local instance $s:ident : NormedSpace ℝ ($X →L[ℝ] $Y) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := $X) (F := $Y) (σ₁₂ := RingHom.id ℝ))
  return ⟨Lean.mkNullNode #[a, b]⟩

end
