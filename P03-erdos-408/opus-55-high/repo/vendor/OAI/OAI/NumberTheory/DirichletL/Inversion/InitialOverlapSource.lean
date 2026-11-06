module

public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier
public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFresh

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseInitialOverlapSource
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def tupleCoordinate (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) (i : σ) : ℝ :=
  if hi:i∈I then y i (q i hi) else 1

omit [DecidableEq ι] in
theorem tupleCoordinate_product (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) :
    (∏i∈I,tupleCoordinate I y q i)=∏i∈I.attach,y i.val (q i.val i.property) := by
  rw [←Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [tupleCoordinate,dite_eq_left i.property]

theorem insert_original_fresh
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (lo hi : σ→ℝ) (W wFresh : ℝ→ℂ) (a₀ b₀ jlo jhi : ℝ)
    (_hW : Function.support W⊆Set.Icc a₀ b₀)
    (ha : ∀i∈I,∀q∈L i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
    (hFresh : ∀(v:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,v i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A : Finset ι) (yj yc : ℝ) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc) :
    wFresh yc*(∑q∈I.pi L,
      (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
        W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))) =
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)=0
  · grind
  by_cases hw : W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))=0
  · grind
  have hcoord : ∀i∈I,tupleCoordinate I y q i∈Set.Icc (lo i) (hi i) := by
    intro i hi
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi⟩ (by simp)
    have hcoeff : a i (q i hi)≠0 := by
      intro he
      apply hn
      split_ifs
      · omega
      · rfl
    simpa only [tupleCoordinate,dite_eq_left hi] using
      ha i hi (q i hi) (by grind) hcoeff
  have hf := hFresh (tupleCoordinate I y q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  grind

end SevenEighths.InverseInitialOverlapSource

end

end OAI
