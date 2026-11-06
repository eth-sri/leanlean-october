module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalSplit
public import OAI.NumberTheory.DirichletL.Descent.FirstGlobalPush

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι]

abbrev FirstOriginalOuter (ι ) := Σ _ : CubeCoordinates ι,Σ _ : Finset ι,Finset ι

def firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ))  :=
  (reopenedCubeFamily Q).sigma (fun b=>(pool\b.support).powerset.sigma
    (fun C=>(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset))

lemma mem_firstOriginalOuter (pool : Finset ι)  Q   k  :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

lemma retained_cutoff_enlargement (E : ActualEisensteinCubic.O) (hE : E≠0) (R Y : ℝ) (hRY : R≤Y) (f : ActualEisensteinCubic.O→ℂ) :
    (∑h∈(childFrequencyBall E R).erase 0,f h)=
      ∑h∈nonzeroChildFrequencyBall E Y,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
  have hsub : (childFrequencyBall E R).erase 0⊆nonzeroChildFrequencyBall E Y := by
    intro h hh
    rcases Finset.mem_erase.mp hh with ⟨hn,hm⟩
    exact Finset.mem_erase.mpr ⟨hn,(mem_childFrequencyBall E hE Y h).mpr
      (((mem_childFrequencyBall E hE R h).mp hm).trans hRY)⟩
  calc
    _=∑h∈(childFrequencyBall E R).erase 0,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
      simp_all
    _=_ := Finset.sum_subset hsub (by
      intro h hh hn
      have hne := (Finset.mem_erase.mp hh).1
      simp_all)

variable (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstOriginalWeight (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O)  :=
  reopenedPairCoefficient β k.1 k.2.1 x.1 *
    (UniqueFactorizationMonoid.moebius (∏i∈k.2.2,Ideal.span {p i}):ℂ) *
    (if x.2∈reopenedPhysicalCutoff p k.1 x.1 (R k.1 k.2.1 x.1) k.2.2 then 1 else 0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma firstOriginalWeight_norm_le  β 
     R 
     k   x  :
    ‖firstOriginalWeight p β R k x‖≤‖reopenedPairCoefficient β k.1 k.2.1 x.1‖ := by
  unfold firstOriginalWeight
  split_ifs
  · simp only [mul_one,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (CubicEisenstein.norm_ideal_moebius_le_one _)
  · simp

theorem original_retained_global_index
     pool   Q   labels  (hlabels : ∀I∈labels,I≠0)
     β   Ψ   m 
     mark   W   Φ   K Y 
     R 
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      firstOriginalWeight p β R x.1 x.2 *
      canonicalCubeOuter p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator x.2.1)*
      firstCubePhysicalMode p hp hcop hg pool x.1.1 x.1.2.1 Ψ Ψ m m
        (ConcretePrimeRowBridge.idealGenerator x.2.1) (mark x.1.1.rightExponent) (mark x.1.1.leftExponent)
        W W Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 := by
  simp only [firstGlobalRetainedSource,firstOriginalOuter,Finset.sum_sigma,sum_firstRetainedSource]
  unfold reopenedPhysicalSourceSum reopenedPhysicalRetained
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  have hE := firstPhysicalMultiplier_ne_zero p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit f (hlabels f hf)
  have hRY' := hRY ⟨b,⟨C,D⟩⟩ ((mem_firstOriginalOuter pool Q _).mpr ⟨hb,hC,hD⟩) f hf
  rw [show reopenedPhysicalCutoff p b f (R b C f) D=
    childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R b C f D) from rfl]
  rw [retained_cutoff_enlargement _ hE _ Y hRY']
  apply Finset.sum_congr rfl
  intro h hh
  simp only [firstOriginalWeight,reopenedPhysicalCutoff]
  ac_rfl

end
end SevenEighths.InverseMoment

end OAI
