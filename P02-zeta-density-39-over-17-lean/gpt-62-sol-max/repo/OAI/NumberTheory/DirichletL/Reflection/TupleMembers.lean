module
public import OAI.NumberTheory.DirichletL.Reflection.ActiveProducts
public import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
public import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable (tuples : Finset (σ→Ideal Eis))
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)

def memberTupleFamily (p : tuples) : PrimeFamily σ where
  ideal := p.val
  maximal := hmax p.val p.property
  good := hgood p.val p.property

lemma tuplePrimeFamily_at_member (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))) (p : tuples) :
    tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val)=memberTupleFamily tuples hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product tuples hne hmax hgood hinj p.val p.property

variable {N a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (D : ∀ P : tuples.image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)

def memberTupleControlled (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  castControlled (congrArg (fun S => (F.reflected K hK S).generator)
    (tuplePrimeFamily_at_member tuples hmax hgood hne hinj p))
    (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp)

lemma memberTupleControlled_value (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X :=
  mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

def memberTupleRow
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0

theorem literalWholeRow_eq_member_tuples
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) :
    literalWholeRow F K hK (tuplePrimeFamily tuples hne hmax hgood) j
      (tuples.image slotTupleProduct) D s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  let hr : ∀ k∈({K}:Finset (Ideal Eis)),Admissible k := fun k hk => (Finset.mem_singleton.mp hk).symm ▸ hK
  let Ds : ∀ k : ({K}:Finset (Ideal Eis)),∀ P : tuples.image slotTupleProduct,IsCoprime k.val P.val→
      ControlledStratumArithmetic (F.reflected k.val (hr k.val k.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode := by
    intro k
    rcases k with ⟨k,hk⟩
    have hh := Finset.mem_singleton.mp hk
    subst k
    exact D
  have he := literalWholeRow_eq_active_tuples F {K} tuples hne hmax hgood hinj
    hr j Ds s hc W θ X r aw ⟨K,Finset.mem_singleton_self K⟩
  convert he using 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : IsCoprime K (slotTupleProduct p.val)
  · simp only [dite_eq_left hk]
    rw [memberTupleControlled_value]
  · simp only [dite_eq_right hk]
section

/-- Energy with the chosen completion in a single row/slot cell of a tuple family. -/
abbrev MemberCellEnergy {N a c : Eis} {mode : Bool}
    (G : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (hne : tuples.Nonempty) (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (X QK QP : ℝ) (E : ℝ→ℝ) : Prop :=
  let S := tuplePrimeFamily tuples hne hmax hgood
  let Pset := tuples.image slotTupleProduct
  ∃ D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
    ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode,
  ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
    1≤QK → 2≤QP →
    (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
    (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
    (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
    (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc j W θ X r aw‖^2)≤E θ

end

end
end SevenEighths.InverseReflectedPhase

end OAI
