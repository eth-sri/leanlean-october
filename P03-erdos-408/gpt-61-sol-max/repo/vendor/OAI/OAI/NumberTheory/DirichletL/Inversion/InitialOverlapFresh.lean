module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

@[expose] public section

namespace OAI



open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapFresh
variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem overlap_column_interval (I : Finset σ) (lo hi y : σ→ℝ)
    (a b jlo jhi yj yc : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hy : ∀i∈I,y i∈Set.Icc (lo i) (hi i))
    (hjlo : 0<jlo) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc)
    (hsource : yj*yc/(∏i∈I,y i)∈Set.Icc a b) :
    yc∈Set.Icc (a*(∏i∈I,lo i)/jhi) (b*(∏i∈I,hi i)/jlo) := have hyp : ∀ i ∈ I, 0 < y i := fun i hi_1 => LT.lt.trans_le (hlo i hi_1) (hy i hi_1).left;
have hprod : 0 < ∏ i ∈ I, y i := Finset.prod_pos hyp;
⟨(div_le_iff₀ (LT.lt.trans_le (LT.lt.trans_le hjlo hj.left) hj.right)).mpr (mul_comm jhi yc ▸ le_trans (le_trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i hi => LT.lt.le (hlo i hi)) fun i hi_1 => (hy i hi_1).left) (LT.lt.le ha)) ((le_div_iff₀ hprod).mp hsource.left)) (mul_le_mul_of_nonneg_right hj.right (LT.lt.le hc))), (le_div_iff₀ hjlo).mpr (le_trans (le_trans (Eq.symm (mul_comm yc jlo) ▸ mul_le_mul_of_nonneg_right hj.left (LT.lt.le hc)) ((div_le_iff₀ hprod).mp hsource.right)) (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i hi => LT.lt.le (hyp i hi)) fun i hi_1 => (hy i hi_1).right) (LE.le.trans (LT.lt.le ha) hab)))⟩

end SevenEighths.InverseInitialOverlapFresh



end OAI
