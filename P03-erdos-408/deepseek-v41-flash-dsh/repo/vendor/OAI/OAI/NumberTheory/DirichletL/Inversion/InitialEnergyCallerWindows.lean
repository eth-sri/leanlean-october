module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerRanges
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceRelative (x:Source (ι:=ι) 0)(Z D B v θ H:ℝ) : Fin 6→ℝ :=
  relativeNorm (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H

def windowSource (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H:ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>outerCutoff ψ (sourceRelative p x Z D B v θ H)≠0)

omit [DecidableEq ι] in
theorem sourceRelative_four (x:Source (ι:=ι) 0)(N M:Finset ι)
    (Z D B v θ H:ℝ)(i:Fin 4) :
    relativeNorm (coordinates p (sourcePoint x N M)) Z D B v θ H (InverseSecondChildWindows.outerIndex i)=
      sourceRelative p x Z D B v θ H (InverseSecondChildWindows.outerIndex i) := by
  fin_cases i <;> simp only [InverseSecondChildWindows.outerIndex,sourceRelative,relativeNorm,
    coordinates,sourcePoint,physicalCoordinates,secondRelativeNorm,Fin.castLE,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem windowSource_four_nonzero
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ)
    {x:Point ι}(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H))(i:Fin 4) :
    ψ i (relativeNorm (coordinates p x) Z D B v θ H (InverseSecondChildWindows.outerIndex i))≠0 := by
  obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  have ho := (Finset.mem_filter.mp hs).2

  rw [sourceRelative_four]
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  fin_cases i
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_windowSource
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H m:ℝ)(w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ)) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (windowSource p S ψ Z D B v θ H))
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,windowSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ho:outerCutoff ψ (sourceRelative p x Z D B v θ H)=0
  · simp only [ho,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,erase_sourcePoint,
      mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left ho]

end SevenEighths.InverseInitialEnergyCallerWindows

end

end OAI
