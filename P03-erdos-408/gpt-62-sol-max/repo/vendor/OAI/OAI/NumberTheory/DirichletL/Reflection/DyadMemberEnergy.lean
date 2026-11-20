module

public import OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy
public import OAI.NumberTheory.DirichletL.Reflection.MemberEnergySpec
public import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds

@[expose] public section

namespace OAI.SevenEighths.InverseReflectedPhase

open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (X : ℝ)

/-- Member-row bounds for each nonempty dyadic rectangle. -/
abbrev DyadicMemberBounds (E : ℝ→ℝ)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))) : Prop :=
    ∀ i j, (divisorDyadicBin rows Hrow i).Nonempty →
      ∀ (hj : (activeTupleDyad tuples Hslot j).Nonempty),
      let Rc := divisorDyadicBin rows Hrow i
      let Tc := activeTupleDyad tuples Hslot j
      let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
      let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
      let hRi : ∀ K∈Rc,Admissible K := fun K hK => hrows K (divisorDyadicBin_subset rows Hrow i hK)
      let hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→Ideal Eis)) :=
        hinj.mono (activeTupleDyad_subset tuples Hslot j)
      (2*divisorDyadicScale j.val)/2 ≤ Hslot →
      MemberTupleEnergy (N:=N) G Rc hRi Tc hj hm hg hti s hc jF W X
        (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val) E

/-- Apply the member-row estimate to each nonempty pair of dyadic cells. -/
theorem physical_dyads_from_members (E : ℝ→ℝ) (hE : ∀ θ,0≤E θ)
    (hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow)
    (hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (hGN : ∀ f,IsCoprime (Ideal.span {N}) (G.ideal f))
    (hGchar : ∀ f,ringChar (Eis⧸G.ideal f)≠2)
    (hrowcop : ∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal))
    (hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b))
    (hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2)
    (he : DyadicMemberBounds (N:=N) G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X E hinj) :
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : rows,‖∑ p : tuples,
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw K p‖^2)≤
          (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E θ := by
  have htupleNorm (p) (hp : p∈tuples) : 1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot :=
    ⟨QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2),(hPnorm p hp).2⟩
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X E hE
  intro i j hi hj
  let Tc := activeTupleDyad tuples Hslot j
  let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
  let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
  let lift (p : Tc) : tuples := ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩
  let rep (P : Ideal Eis) : tuples := lift ⟨tupleRepresentative Tc hj P,tupleRepresentative_mem Tc hj P⟩
  have hjcap : (2*divisorDyadicScale j.val)/2≤Hslot := by
    linarith [activeTupleDyad_scale_le tuples Hslot htupleNorm j hj]
  obtain ⟨D,hD⟩ := he i j hi hj hjcap hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hj hm hg) (fun P _ => hpair (rep P))
    (fun P _ => hPN (rep P)) (fun P _ => hPchar (rep P))
  refine ⟨fun K p hp => memberTupleControlled Tc hm hg G K.val
    (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property)) hj
    (hinj.mono (activeTupleDyad_subset tuples Hslot j)) (D K) p hp, ?_⟩
  intro θ r aw hr haw
  exact hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert divisorDyadicBin_bounds rows Hrow hrowNorm i K hK using 1 <;> ring_nf)
    (by
      intro P hP
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
      refine ⟨(hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1,?_⟩
      convert activeTupleDyad_bounds tuples Hslot htupleNorm j p hp using 1 <;> ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))

/-- A nonempty residual dyad has a parent supplying its norm and mask bounds. -/
lemma exists_dyadic_parent (parents rows : Finset (Ideal Eis)) (J Q : Ideal Eis) (U Hrow : ℝ)
    (hparents : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (hsub : rows⊆originalResidualRows parents J Q)
    (hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow)
    (i : Fin (columnDyadicLength Hrow+1)) (hi : (divisorDyadicBin rows Hrow i).Nonempty) :
    ∃ I, I≠0 ∧ (Ideal.absNorm I:ℝ)≤U ∧
      rowPowerfulPart J=rowPowerfulPart I ∧ rowMaskPart J Q=rowMaskPart I Q ∧
      (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) ∧
      2*divisorDyadicScale i.val≤2*U := by
  obtain ⟨K,hK⟩ := hi
  obtain ⟨I,hI,heI⟩ := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  obtain ⟨hI0,hIn⟩ := hparents I hIp
  have hlo := (divisorDyadicBin_bounds rows Hrow hrowNorm i K hK).1
  rw [← heI] at hlo
  have hres : (Ideal.absNorm (rowResidualPart I Q):ℝ)≤(Ideal.absNorm I:ℝ) := by
    rw [rowResidualPart_norm I Q hI0]
    exact div_le_self (Nat.cast_nonneg _) (one_le_mul_of_one_le_of_one_le
      (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
      (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)))
  exact ⟨I,hI0,hIn,hpow.symm,hmask.symm,by linarith,by linarith [hres.trans hIn]⟩

end
end OAI.SevenEighths.InverseReflectedPhase
