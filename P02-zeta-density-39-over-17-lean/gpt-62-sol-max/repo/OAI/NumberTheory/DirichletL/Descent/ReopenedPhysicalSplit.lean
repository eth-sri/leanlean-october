module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
public import OAI.NumberTheory.DirichletL.Descent.ReopenedBlocks
public import OAI.NumberTheory.DirichletL.Descent.FirstRetainedPhysical

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [OAI.PrincipalIdealFamily.Maximal p]
  (hcop : OAI.PrincipalIdealFamily.PairwiseCoprime p)
  (hg : OAI.PrincipalIdealFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

def reopenedPhysicalSourceSum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (source : CubeCoordinates ι→Finset ι→Ideal O→ℂ) : ℂ :=
  ∑ b∈reopenedCubeFamily Q,∑ C∈(pool\b.support).powerset,∑ I∈labels,
    reopenedPairCoefficient β b C I*source b C I

def reopenedPhysicalCutoff (b : CubeCoordinates ι) (I : Ideal O)
    (R : Finset ι→ℝ) (D : Finset ι) : Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit I) (R D)

def reopenedPhysicalRetained (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ : O→*ℂ) (m : O) (I : Ideal O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (R : Finset ι→ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ Ψ m m (idealGenerator I)*
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i∈D,Ideal.span {p i}):ℂ)*
      ∑ h∈(reopenedPhysicalCutoff p b I R D).erase 0,
        firstCubePhysicalMode p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
          (mark b.rightExponent) (mark b.leftExponent) W W Φ K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

theorem original_reopened_physical_split
    (hinj : OAI.PrincipalIdealFamily.Distinct p)
    (hc : OAI.PrincipalIdealFamily.CharacteristicNe p 2)
    (hpr : OAI.PrincipalIdealFamily.PrimaryAt p ConcretePrimeRowBridge.goodLambda)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    (∑ I∈labels,∑' z:O,Φ (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z‖^2:ℝ)) =
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W Φ K (R b C I)) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K
        (reopenedPhysicalCutoff p b I (R b C I))) := by
  rw [varying_reopened_smoothed_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m]
  · unfold varyingCanonicalSourceTotal reopenedPhysicalSourceSum
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro C hC
    apply Finset.sum_congr rfl
    intro I hI
    have hCb : Disjoint C b.support := by
      exact Finset.disjoint_left.mpr (fun i hi hib=>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hib)
    have he := canonical_first_physical_split p hp hcop hg hinj hc hpr pool b
      (reopenedCubeFamily_admissible Q b hb) C hCb Ψ Ψ m m I (hlabels I hI)
      (mark I b.rightExponent) (mark I b.leftExponent) W W Φ K hK (R b C I) (hR b hb C hC I hI)
    dsimp only at he
    rw [he]
    simp only [reopenedPhysicalRetained]
    rw [show reopenedPhysicalCutoff p b I (R b C I) =
      (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
        b.leftBit b.rightBit I) (R b C I D)) from rfl]
    ring
  · exact hK

end
end SevenEighths.InverseMoment

end OAI
