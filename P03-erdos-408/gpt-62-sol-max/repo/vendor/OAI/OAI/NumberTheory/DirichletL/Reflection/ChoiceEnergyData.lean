module

public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource
public import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport
public import OAI.NumberTheory.DirichletL.Reflection.DyadMemberEnergy

@[expose] public section

namespace OAI.SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable {N a c : Eis} {mode : Bool} (G : PrimeFamily τ) (F : φ → Ideal Eis)
variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
variable (jF : τ → ℕ) (W : ℝ → ℂ) (X : ℝ)
variable (L : σ → Finset (Ideal Eis))
    (hmax : ∀ i P, P ∈ L i → P.IsMaximal)
    (hgood : ∀ i P, P ∈ L i → ConcretePrimeRowBridge.goodLambda ∉ P)

/-- The arithmetic completion attached to an admissible row and a supported
choice of primes from the slots. -/
abbrev ChoiceCompletion (K : Ideal Eis) (hK : Admissible K)
    (p : supportedSlotChoices L F K) :=
  ControlledStratumArithmetic
    (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode

abbrev reflectedChoiceSum (K : Ideal Eis) (hK : Admissible K)
    (D : ∀ p, ChoiceCompletion (N := N) (a := a) (c := c) (mode := mode) G F L hmax hgood K hK p)
    (θ : ℝ) (w : ∀ i, L i → ℂ) : ℂ :=
  ∑ p : supportedSlotChoices L F K,
    let row := G.reflected K hK (slotChoiceFamily L hmax hgood p.val)
    (∏ i, w i (p.val i)) * mixedReflectedValue (D p) s row.generator_ne_zero hc row.generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

variable (rows : Finset (Ideal Eis)) (hr : ∀ K ∈ rows, Admissible K)

/-- Energy bound when all the listed slots are active. -/
def ChoiceEnergy (E : ℝ → ℝ) : Prop :=
  ∃ D : ∀ K : rows, ∀ p, ChoiceCompletion (N := N) (a := a) (c := c) (mode := mode)
    G F L hmax hgood K.val (hr K K.property) p,
    ∀ (θ : ℝ) (w : ∀ i, L i → ℂ), (∀ i P, ‖w i P‖ ≤ 1) →
      (∑ K : rows, ‖reflectedChoiceSum G F s hc jF W X L hmax hgood K.val (hr K K.property)
        (D K) θ w‖ ^ 2) ≤ E θ

/-- Combine the dyadic estimates for the supported choices of slot primes. -/
theorem choice_energy_from_members
    (hdis : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hprime : ∀ i P, P∈L i → Prime P)
    (hpairG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hcross : ∀ b, ∃ f, G.ideal b = F f)
    (H : σ→ℝ) (Hrow Hslot : ℝ)
    (hH : ∀ i P, P∈L i → (Ideal.absNorm P:ℝ)≤H i)
    (hprod : (∏ i, H i)≤Hslot)
    (hGN : ∀ b, IsCoprime (Ideal.span {N}) (G.ideal b))
    (hGchar : ∀ b, ringChar (Eis⧸G.ideal b)≠2)
    (hrowcop : ∀ K∈rows,(∀ b,IsCoprime (G.ideal b) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hLN : ∀ i P, P∈L i → IsCoprime (Ideal.span {N}) P)
    (hLchar : ∀ i P, P∈L i → ringChar (Eis⧸P)≠2)
    (hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow)
    (E Eout : ℝ→ℝ) (hE : ∀ θ,0≤E θ)
    (hcount : ∀ θ, (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E θ≤Eout θ)
    (he : let tuples := fixedSlotTupleSet L F
      DyadicMemberBounds (N:=N) G rows hr tuples (originalTupleMax L F hmax)
        (originalTupleGood L F hgood) Hrow Hslot s hc jF W X E
        (fixedSlotTupleSet_product_injective L F hdis hprime)) :
    ChoiceEnergy (N:=N) G F s hc jF W X L hmax hgood rows hr Eout := by
  let tuples := fixedSlotTupleSet L F
  let hm := originalTupleMax L F hmax
  let hg := originalTupleGood L F hgood
  have htuples : ∀ p∈tuples,∀ i,p i∈L i := fun p hp => ((mem_fixedSlotTupleSet L F p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ hpairG
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      obtain ⟨f',heq⟩ := hcross f
      rw [heq]
      exact (((mem_fixedSlotTupleSet L F p.val).mp p.property).2 f' i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot := by
    intro p hp
    refine ⟨slotTupleProduct_admissible L hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound L H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  obtain ⟨Dc,hDc⟩ := physical_dyads_from_members G rows hr tuples hm hg Hrow Hslot
    s hc jF W X E hE hrowNorm hPnorm (fixedSlotTupleSet_product_injective L F hdis hprime)
    hGN hGchar hrowcop hpair hPN hPchar he
  let D := fun (K : rows) (p : supportedSlotChoices L F K.val) =>
    memberChoiceControlled L F hmax hgood G K.val (hr K.val K.property)
      (dyadicTupleControlled G rows hr tuples hm hg Hrow Hslot Dc K) p
  refine ⟨D,?_⟩
  intro θ w hw
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hr tuples hm hg Hrow Hslot Dc s hc
        jF W θ X (fun _ => 1)
        (fixedTupleCoefficient L w) K p)=
      reflectedChoiceSum G F s hc jF W X
        L hmax hgood K.val (hr K.val K.property) (D K) θ w := by
    simpa only [dyadicPhysicalTerm,reflectedChoiceSum,D,one_mul] using member_source_eq_original_choices L F hmax hgood G K.val
      (hr K.val K.property) (dyadicTupleControlled G rows hr tuples hm hg Hrow Hslot Dc K)
      s hc jF
      (CompletedHeight.normTwistedSource W θ) X 1 w
  have hb := hDc θ (fun _ => 1) (fixedTupleCoefficient L w) (by simp) (fun p hp => fixedTupleCoefficient_norm L w hw p)
  change (∑ K : rows, ‖reflectedChoiceSum G F s hc jF W X
        L hmax hgood K.val (hr K.val K.property) (D K) θ w‖^2) ≤ _
  simp only [←hsource]
  exact hb.trans (hcount θ)

variable (T : Finset σ) (H : σ → ℝ)

/-- Energy bound with the sum over the inactive choices placed outside the
reflected sum and weighted by the reciprocal ideal norms. -/
def InactiveChoiceEnergy (E : ℝ → ℝ) : Prop :=
  ∃ D : ∀ (K : rows), supportedSlotChoices (fun i : {i // i ∉ T} => L i.val) F K.val →
    ∀ p, ChoiceCompletion (N := N) (a := a) (c := c) (mode := mode)
      G F (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val)
      K.val (hr K K.property) p,
    ∀ (θ : ℝ) (w : ∀ i, L i → ℂ), (∀ i P, ‖w i P‖ ≤ 1) →
      (∑ K : rows, ‖∑ b : supportedSlotChoices (fun i : {i // i ∉ T} => L i.val) F K.val,
        ((∏ i : {i // i ∉ T}, (Ideal.absNorm (b.val i).val : ℂ)⁻¹) *
          (∏ i : {i // i ∉ T}, w i.val (b.val i))) *
        reflectedChoiceSum G F s hc jF W X (fun i : T => L i.val)
          (fun i => hmax i.val) (fun i => hgood i.val) K.val (hr K K.property)
          (D K b) θ (fun i => w i.val)‖ ^ 2) ≤
        (∏ i : {i // i ∉ T}, 256 * (columnDyadicLength (H i.val) + 1 : ℝ)) ^ 2 * E θ

theorem inactiveRowSet_subset (b : ∀ i : {i // i ∉ T}, L i.val) :
    inactiveRowSet rows L T F b ⊆ rows :=
  Finset.filter_subset _ _

theorem active_prod_le (hH : ∀ i, 1 ≤ H i) :
    (∏ i : T, H i.val) ≤ ∏ i, H i := by
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
    (fun i _ => zero_le_one.trans (hH i)) (fun i _ _ => hH i)

/-- Apply the active estimate on the rows compatible with each inactive choice
before using the reciprocal-norm energy inequality. -/
theorem inactive_choice_energy_of_active
    (hnz : ∀ i P, P ∈ L i → P ≠ 0)
    (hH : ∀ i P, P ∈ L i → (Ideal.absNorm P : ℝ) ≤ H i)
    (E : ℝ → ℝ) (hE : ∀ θ, 0 ≤ E θ)
    (h : ∀ b : ∀ i : {i // i ∉ T}, L i.val,
      ChoiceEnergy (N := N) G F s hc jF W X (fun i : T => L i.val)
        (fun i => hmax i.val) (fun i => hgood i.val) (inactiveRowSet rows L T F b)
        (fun K hk => hr K (inactiveRowSet_subset F L rows T b hk)) E) :
    InactiveChoiceEnergy (N := N) G F s hc jF W X L hmax hgood rows hr T H E := by
  unfold ChoiceEnergy at h
  choose D hD using h
  let D' := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i // i ∉ T} => L i.val) F K.val) p =>
      D b.val ⟨K.val, Finset.mem_filter.mpr ⟨K.property, b.property⟩⟩ p
  refine ⟨D', fun θ w hw => ?_⟩
  let f (K : rows) (b : supportedSlotChoices (fun i : {i // i ∉ T} => L i.val) F K.val) :=
    reflectedChoiceSum G F s hc jF W X (fun i : T => L i.val) (fun i => hmax i.val)
      (fun i => hgood i.val) K.val (hr K K.property) (D' K b) θ (fun i => w i.val)
  exact supported_inactive_source_energy rows L T F H hnz hH w hw f (E θ) (hE θ)
    (fun b => hD b θ (fun i : T => w i.val) (fun i P => hw i.val P))

end
end OAI.SevenEighths.InverseReflectedPhase
