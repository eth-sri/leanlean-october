module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.WildTensorRankPure
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → Type) [∀i,AddCommGroup (V i)] [∀i,Module ℂ (V i)]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

section

variable (x : ∀i,V i) (hx : ∀i,x i≠0)

include hx in
theorem coordinate_injective (q : ι) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap x q) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  by_contra hn
  let u := Function.update x q v
  have hu : ∀i,u i≠0 := by
    intro i
    by_cases hi:i=q
    · subst i;simpa [u] using hn
    · simpa [u,hi] using hx i
  let φ := fun i =>
    Classical.choose (Module.Projective.exists_dual_eq_one ℂ (hu i))
  have hφ (i) : φ i (u i)=1 :=
    Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (hu i))
  let L := PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ φ)
  have he : L (PiTensorProduct.tprod ℂ u)=1 := by
    simp [L,PiTensorProduct.dualDistrib_apply,hφ]
  change PiTensorProduct.tprod ℂ u=0 at hv
  have hz := congrArg L hv
  simp at hz
  exact one_ne_zero (he.symm.trans hz)

include hx in
theorem local_rank_le_one
    (J : (⨂[ℂ] i,V i) →ₗ[ℂ] ℂ) (hJ : Function.Injective J) (q : ι) :
    Module.rank ℂ (V q)≤1 := by
  let l := J.comp ((PiTensorProduct.tprod ℂ).toLinearMap x q)
  simpa using LinearMap.rank_le_of_injective l (hJ.comp (coordinate_injective V x hx q))

end

theorem local_rank_le_one_of_detected (x : ∀i,V i)
    (J : (⨂[ℂ] i,V i) →ₗ[ℂ] ℂ) (hJ : Function.Injective J)
    (hx : J (PiTensorProduct.tprod ℂ x)≠0) (q : ι) :
    Module.rank ℂ (V q)≤1 := by
  apply local_rank_le_one V x _ J hJ q
  intro i hi
  apply hx
  simp [(PiTensorProduct.tprod ℂ).map_coord_zero i hi]

end DedekindZetaZeroFree.FourierContinuation.WildTensorRankPure

end
