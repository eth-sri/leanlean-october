module

public import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyBounds

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap
open SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource

variable {ι:Type*}[DecidableEq ι](p:ι→ActualEisensteinCubic.O)

def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:ActualEisensteinCubic.O→*ℂ)(j:ActualEisensteinCubic.O)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · simp_all
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    grind

theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:ActualEisensteinCubic.O→*ℂ)(j:ActualEisensteinCubic.O)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
