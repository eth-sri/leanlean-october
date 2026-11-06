module
public import OAI.NumberTheory.DirichletL.Descent.SecondSquarefree

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

theorem assignedSecondSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S ⊆ T)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSecondSource S J₁ J₂ L₁ L₂ ⊆ assignedSecondSource T J₁ J₂ L₁ L₂ := by
  intro x hx
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,he⟩ := (mem_assignedSecondSource S J₁ J₂ L₁ L₂ x).mp hx
  exact (mem_assignedSecondSource T J₁ J₂ L₁ L₂ x).mpr ⟨y,hST hy,q₁,hq₁,q₂,hq₂,he⟩

theorem actualSecondTriples_mono {Jo Jn : ℕ} (u v : Eisˣ)
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (hST : S ⊆ T) :
    actualSecondTriples p u v S ⊆ actualSecondTriples p u v T :=
  Finset.image_subset_image hST

end
end SevenEighths.InverseMoment

end OAI
