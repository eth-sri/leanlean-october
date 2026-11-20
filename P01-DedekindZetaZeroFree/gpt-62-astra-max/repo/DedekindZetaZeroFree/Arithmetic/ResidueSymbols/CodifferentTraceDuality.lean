module
public import DedekindZetaZeroFree.Adeles.Characters.TracePhaseUniqueness
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductors

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.ResidueTracePhases
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveRowBoxesAndSchurBounds

@[expose] public section

namespace DedekindZetaZeroFree.CodifferentResidueSieve
noncomputable section
set_option maxHeartbeats 1500000
open scoped Classical NumberField
open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

section

variable (A : SArithmeticData F)

def different : Ideal A.R :=
  Ideal.map (algebraMap (𝓞 F) A.R) (differentIdeal ℤ (𝓞 F))

def codifferent : Set F :=
  {x | ∀ d : A.R, d ∈ different A → (d : F) * x ∈ A.R}

def denominatorScale : ℝ :=
  max 1 (Nat.card (A.R ⧸ different A) : ℝ)

def finiteTrace :
    (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle :=
  fun v => ResidueTrace.localTraceCharacter v.val

def phase (x : F) : ℂ :=
  ProbeAdditive.phase F A.Sf (finiteTrace A) (sLocalDiagonal F A.Sf x)

end

structure TraceDualData (A : SArithmeticData F) : Prop where
  continuous : ∀ v, Continuous (finiteTrace A v)
  compatible : ProbeAdditive.TraceCompatible F A.Sf (finiteTrace A)
  different_nonzero : different A ≠ ⊥
  residue : ∀ (δ : A.R), δ ≠ 0 → Ideal.span {δ} = different A →
    ∀ (q : Ideal A.R) [Fintype (A.R ⧸ q)] (a : A.R),
      a ≠ 0 → Ideal.span {a} = q →
      ∃ psi : AddChar (A.R ⧸ q) ℂ, psi.IsPrimitive ∧
        ∀ m : A.R, psi (Ideal.Quotient.mk q m) =
          phase A (-((m : F) / ((δ : F) * (a : F))))

alias localTraceCharacter_eq_localFiniteCharacter := DedekindZetaZeroFree.ArithmeticContext.TraceCharacterConductors.character_eq_adapter

theorem localTraceCharacter_eq_one_of_integral (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ResidueTrace.localTraceCharacter v x = 1 := by
  rw [localTraceCharacter_eq_localFiniteCharacter]
  exact (rationalPadicCharacter_eq_one_iff _ _).mpr
    (PlaceTraceAdapter.trace_mem_padicIntegers F v x hx)

theorem archPhase_eq_trace (A : SArithmeticData F) (x : InfiniteAdeleRing F) :
    ProbeAdditive.archPhase F x = ∏ w, (archTraceCharacter w (x w) : ℂ) := by apply @DedekindZetaZeroFree.TateSLocalComparison.TracePhaseUniqueness.archPhase_eq_archTraceCharacter_product <;> assumption

theorem phase_eq_fieldTraceCharacter (A : SArithmeticData F) (x : F) :
    phase A x = (A.fieldTraceCharacter x : ℂ) := by
  unfold phase ProbeAdditive.phase
  rw [archPhase_eq_trace A]
  change _ = Circle.coeHom (_ * _)
  rw [map_mul, map_prod, map_prod]
  rfl

theorem canonical_trace_compatible (A : SArithmeticData F) :
    ProbeAdditive.TraceCompatible F A.Sf (finiteTrace A) := by
  intro r
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
      ResidueTrace.localTraceCharacter v
        (algebraMap F (v.adicCompletion F) (r : F)) = 1 := by
    apply localTraceCharacter_eq_one_of_integral
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact Set.integer_valuation_le_one _ _ r hv
  have hprod := finprod_eq_prod_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 F) =>
      ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (r : F)))
     (by
      intro v hv
      by_contra hn
      exact hv (hout v hn))
  have hglobal := ResidueTrace.diagonal_product_formula (r : F)
  rw [hprod] at hglobal
  have hc : A.fieldTraceCharacter (r : F) = 1 := by
    exact (congrArg (fun t : Circle =>
      (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion (r : F))) * t)
      (Finset.prod_coe_sort A.Sf (fun v : HeightOneSpectrum (𝓞 F) =>
        ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (r : F))))).trans hglobal
  rw [sIntegerDiagonal_apply]
  change phase A (r : F) = 1
  rw [phase_eq_fieldTraceCharacter, hc, Circle.coe_one]

theorem mem_codifferent_iff_of_span (A : SArithmeticData F) (δ : A.R)
    (hspan : Ideal.span {δ} = different A) (x : F) :
    x ∈ codifferent A ↔ (δ : F) * x ∈ A.R := by
  constructor
  · intro h
    exact h δ (hspan ▸ Ideal.subset_span (Set.mem_singleton δ))
  · intro h d hd
    rw [← hspan] at hd
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hd
    change (t : F) * (δ : F) * x ∈ A.R
    rw [mul_assoc]
    exact A.R.mul_mem t.property h

theorem residue_of_trace_dual (A : SArithmeticData F)
    (hdual : ∀ x : F, (∀ m : A.R, phase A (x * (m : F)) = 1) ↔ x ∈ codifferent A)
    (δ : A.R) (hδ : δ ≠ 0) (hspan : Ideal.span {δ} = different A)
    (q : Ideal A.R) (a : A.R) (ha : a ≠ 0) (hspanq : Ideal.span {a} = q) :
    ∃ psi : AddChar (A.R ⧸ q) ℂ, psi.IsPrimitive ∧
      ∀ m : A.R, psi (Ideal.Quotient.mk q m) =
        phase A (-((m : F) / ((δ : F) * (a : F)))) := by
  have hδF : (δ : F) ≠ 0 := by exact_mod_cast hδ
  have haF : (a : F) ≠ 0 := by exact_mod_cast ha
  let c := -((δ : F) * (a : F))⁻¹
  let e := Circle.coeHom.compAddChar
    (A.fieldTraceCharacter.compAddMonoidHom
      ((LinearMap.mulLeft F c).toAddMonoidHom.comp A.R.val.toAddMonoidHom))
  have he (m : A.R) : e m = phase A (c * (m : F)) := (phase_eq_fieldTraceCharacter A _).symm
  have hc (m : A.R) : c * (m : F) = -((m : F) / ((δ : F) * (a : F))) := by
    dsimp [c]
    ring
  have hker (m : A.R) (hm : m ∈ q) : e m = 1 := by
    rw [← hspanq] at hm
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    rw [he]
    have hmem : c * ((t * a : A.R) : F) ∈ codifferent A := by
      rw [mem_codifferent_iff_of_span A δ hspan]
      have hcalc : (δ : F) * (c * ((t * a : A.R) : F)) = -(t : F) := by
        dsimp [c]
        push_cast
        field_simp
        <;> ring
      rw [hcalc]
      exact A.R.neg_mem t.property
    simpa using ((hdual _).mpr hmem) (1 : A.R)
  let psi : AddChar (A.R ⧸ q) ℂ := AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift q.toAddSubgroup e.toAddMonoidHom (by
      intro m hm
      change Additive.ofMul (e m) = 0
      rw [hker m hm]
      rfl)
  have hpsi (m : A.R) : psi (Ideal.Quotient.mk q m) = e m := rfl
  refine ⟨psi, ?_, ?_⟩
  · intro k hk hshift
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective k
    have hall : ∀ t : A.R, phase A ((c * (m : F)) * (t : F)) = 1 := by
      intro t
      have h := DFunLike.congr_fun hshift (Ideal.Quotient.mk q t)
      simp only [AddChar.mulShift_apply, AddChar.one_apply, ← map_mul, hpsi, he] at h
      simpa only [Subalgebra.coe_mul, mul_assoc] using h
    have hmem := (mem_codifferent_iff_of_span A δ hspan _).mp ((hdual _).mp hall)
    have hcalc : (δ : F) * (c * (m : F)) = -((m : F) / (a : F)) := by
      dsimp [c]
      field_simp
      <;> ring
    rw [hcalc] at hmem
    let t : A.R := ⟨(m : F) / (a : F), by simpa using A.R.neg_mem hmem⟩
    apply hk
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hspanq]
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact div_mul_cancel₀ _ haF
  · intro m
    rw [hpsi, he, hc]

theorem codiff_global_test (A : SArithmeticData F) (x : F) :
    x ∈ codifferent A ↔ ∀ d : 𝓞 F, d ∈ differentIdeal ℤ (𝓞 F) → (d : F) * x ∈ A.R := by
  constructor
  · intro h d hd
    simpa using h _ (Ideal.mem_map_of_mem (algebraMap (𝓞 F) A.R) hd)
  · intro h d hd
    change d ∈ Ideal.map (algebraMap (𝓞 F) A.R) (differentIdeal ℤ (𝓞 F)) at hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨t, ht, rfl⟩ := hd
      simpa using h t ht
    | zero => simp
    | add d e hd he ihd ihe =>
      simpa only [Subalgebra.coe_add, add_mul] using A.R.add_mem ihd ihe
    | smul t d hd ih =>
      change (t : F) * (d : F) * x ∈ A.R
      rw [mul_assoc]
      exact A.R.mul_mem t.property ih

set_option backward.isDefEq.respectTransparency false in

theorem local_codiff_global_test (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    algebraMap F (v.adicCompletion F) x ∈ localCodifferent F v ↔
      ∀ d : 𝓞 F, d ∈ differentIdeal ℤ (𝓞 F) →
        algebraMap F (v.adicCompletion F) ((d : F) * x) ∈ v.adicCompletionIntegers F := by
  rw [localCodifferent_eq_inverse_different, Submodule.mem_div_iff_forall_mul_mem]
  have hone (y : v.adicCompletion F) :
      y ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔
        y ∈ v.adicCompletionIntegers F := by
    rw [Submodule.mem_one]
    have hr := congrArg (fun s : Set (v.adicCompletion F) => y ∈ s)
      (LocalConductor.target_integerRing_eq F v)
    exact ⟨fun ⟨z,hz⟩ => hr.mp (hz ▸ z.property),
      fun hy => ⟨⟨y,hr.mpr hy⟩,rfl⟩⟩
  simp only [hone, IsLocalization.mem_coeSubmodule]
  have hdiff : localDifferent F v = Ideal.map (TraceBaseChange.integerMap F v) (differentIdeal ℤ (𝓞 F)) :=
    (TraceBaseChange.map_globalDifferent_eq_localDifferent F v).symm
  rw [hdiff]
  constructor
  · intro h d hd
    simpa only [ValuationSubring.algebraMap_apply, TraceBaseChange.integerMap_coe, map_mul, mul_comm] using (h _ ⟨TraceBaseChange.integerMap F v d,
      Ideal.mem_map_of_mem _ hd, rfl⟩)
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := hy
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨t, ht, rfl⟩ := hd
      simpa only [ValuationSubring.algebraMap_apply, TraceBaseChange.integerMap_coe, map_mul, mul_comm] using h t ht
    | zero => simp
    | add d e hd he ihd ihe =>
      simp only [map_add, mul_add] at *
      exact (v.adicCompletionIntegers F).toSubring.add_mem ihd ihe
    | smul t d hd ih =>
      simp only [ValuationSubring.algebraMap_apply] at ih ⊢
      change algebraMap F (v.adicCompletion F) x * ((t : v.adicCompletion F) * (d : v.adicCompletion F)) ∈ _
      rw [mul_left_comm]
      apply (v.adicCompletionIntegers F).toSubring.mul_mem _ ih
      exact (congrArg (fun s : Set (v.adicCompletion F) => (t : v.adicCompletion F) ∈ s)
        (LocalConductor.target_integerRing_eq F v)).mp t.property

theorem codiff_local_test (A : SArithmeticData F) (x : F) :
    x ∈ codifferent A ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      algebraMap F (v.adicCompletion F) x ∈ localCodifferent F v := by
  rw [codiff_global_test]
  simp only [local_codiff_global_test]
  constructor
  · intro h v hv d hd
    exact (mem_sIntegerRing_iff F A.Sf _).mp (h d hd) v hv
  · intro h d hd
    exact (mem_sIntegerRing_iff F A.Sf _).mpr (fun v hv => h v hv d hd)

private theorem integral_outside_support (x : F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (HeightOneSpectrum.Support.finite (𝓞 F) x).toFinset) :
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  simpa only [Set.Finite.mem_toFinset, HeightOneSpectrum.Support, Set.mem_setOf_eq,
    not_lt, RingHom.id_apply] using hv

private theorem phase_outside_product (A : SArithmeticData F) (x : F) (m : A.R) :
    phase A (x * (m : F)) *
      ∏ v ∈ (HeightOneSpectrum.Support.finite (𝓞 F) x).toFinset \ A.Sf,
        (ResidueTrace.localTraceCharacter v
          (algebraMap F (v.adicCompletion F) (x * (m : F))) : ℂ) = 1 := by
  let T := (HeightOneSpectrum.Support.finite (𝓞 F) x).toFinset \ A.Sf
  let f (v : HeightOneSpectrum (𝓞 F)) : Circle :=
    ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (x * (m : F)))
  have hf (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf ∪ T) : f v = 1 := by
    have hvs := fun h => hv (Finset.mem_union.mpr (Or.inl h))
    apply localTraceCharacter_eq_one_of_integral
    rw [map_mul]
    refine (v.adicCompletionIntegers F).toSubring.mul_mem
      (integral_outside_support x v ?_)
      ((mem_sIntegerRing_iff F A.Sf _).mp m.property v hvs)
    intro h
    apply hv
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨h,hvs⟩))
  have hprod := finprod_eq_prod_of_mulSupport_subset f
     (by
      intro v hv
      by_contra hn
      exact hv (hf v hn))
  have hg := ResidueTrace.diagonal_product_formula (x * (m : F))
  change (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion (x * (m : F)))) *
    (∏ᶠ v, f v) = 1 at hg
  rw [hprod, Finset.prod_union (Finset.disjoint_sdiff)] at hg
  have hc := congrArg Circle.coeHom hg
  rw [map_mul, map_mul, map_prod, map_prod, map_prod, map_one] at hc
  unfold phase ProbeAdditive.phase
  rw [archPhase_eq_trace A]
  change ((∏ w : InfinitePlace F,
      (archTraceCharacter w (algebraMap F w.Completion (x * (m : F))) : ℂ)) *
    (∏ v : A.Sf, (f v.val : ℂ))) * (∏ v ∈ T, (f v : ℂ)) = 1
  rw [Finset.prod_coe_sort A.Sf (fun v => (f v : ℂ))]
  change (∏ w : InfinitePlace F,
    (archTraceCharacter w (algebraMap F w.Completion (x * (m : F))) : ℂ)) *
    ((∏ v ∈ A.Sf, (f v : ℂ)) * (∏ v ∈ T, (f v : ℂ))) = 1 at hc
  exact (mul_assoc _ _ _).trans hc

set_option backward.isDefEq.respectTransparency false in

theorem canonical_trace_dual (A : SArithmeticData F) (x : F) :
    (∀ m : A.R, phase A (x * (m : F)) = 1) ↔ x ∈ codifferent A := by
  let T := (HeightOneSpectrum.Support.finite (𝓞 F) x).toFinset \ A.Sf
  have hloc (v : HeightOneSpectrum (𝓞 F)) :
      algebraMap F (v.adicCompletion F) x ∈ localCodifferent F v ↔
        ∀ o : v.adicCompletionIntegers F, ResidueTrace.localTraceCharacter v
          (algebraMap F (v.adicCompletion F) x * (o : v.adicCompletion F)) = 1 := by
    change algebraMap F (v.adicCompletion F) x ∈
      (localCodifferent F v : Set (v.adicCompletion F)) ↔ _
    rw [← localIntegerAnnihilator_eq_codifferent]
    change (∀ a, a ∈ v.adicCompletionIntegers F → localFiniteCharacter F v
      (algebraMap F (v.adicCompletion F) x * a) = 1) ↔ _
    simp only [localTraceCharacter_eq_localFiniteCharacter]
    exact ⟨fun h o => h o o.property, fun h a ha => h ⟨a,ha⟩⟩
  rw [codiff_local_test]
  constructor
  · intro hphase
    let g (y : finiteIntegralAdeles F) : ℂ := ∏ v ∈ T,
      (ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) x *
        (y v : v.adicCompletion F)) : ℂ)
    have hg : Continuous g := by
      apply continuous_finset_prod
      intro v hv
      exact continuous_subtype_val.comp ((ResidueTrace.continuous_localTraceCharacter v).comp
        (continuous_const.mul (continuous_subtype_val.comp (continuous_apply v))))
    have heq : g = fun _ => 1 := (TraceBaseChange.integralProduct_dense F).equalizer hg
      continuous_const (by
        funext d
        have hh := phase_outside_product A x (algebraMap (𝓞 F) A.R d)
        rw [hphase, one_mul] at hh
        change g (integralDiagonal F d) = 1
        convert hh using 1
        apply Finset.prod_congr rfl
        intro v hv
        congr 2
        rw [map_mul, Subalgebra.coe_algebraMap]
        change algebraMap F (v.adicCompletion F) x *
          (algebraMap (𝓞 F) (v.adicCompletionIntegers F) d : v.adicCompletion F) = _
        rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
        rfl)
    intro v hv
    rw [hloc]
    intro o
    by_cases hvt : v ∈ T
    · have hh := congrFun heq (Pi.single v o)
      change (∏ w ∈ T, (ResidueTrace.localTraceCharacter w
        (algebraMap F (w.adicCompletion F) x *
          ((Pi.single v o : finiteIntegralAdeles F) w : w.adicCompletion F)) : ℂ)) = 1 at hh
      rw [Finset.prod_eq_single v] at hh
      · simp only [Pi.single_eq_same] at hh
        exact Subtype.ext hh
      · intro w hw hwv
        simp [Pi.single_eq_of_ne hwv]
      · exact fun hn => False.elim (hn hvt)
    · have hvs : v ∉ (HeightOneSpectrum.Support.finite (𝓞 F) x).toFinset := by
        intro h
        exact hvt (Finset.mem_sdiff.mpr ⟨h,hv⟩)
      exact localTraceCharacter_eq_one_of_integral v _
        ((v.adicCompletionIntegers F).toSubring.mul_mem
          (integral_outside_support x v hvs) o.property)
  · intro hlocal m
    have hh := phase_outside_product A x m
    have hp : (∏ v ∈ T, (ResidueTrace.localTraceCharacter v
      (algebraMap F (v.adicCompletion F) (x * (m : F))) : ℂ)) = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      rw [map_mul]
      have hvs : v ∉ A.Sf := (Finset.mem_sdiff.mp hv).2
      have hm := (mem_sIntegerRing_iff F A.Sf _).mp m.property v hvs
      exact congrArg Circle.coeHom ((hloc v).mp (hlocal v hvs) ⟨_,hm⟩)
    rw [hp, mul_one] at hh
    exact hh

theorem canonical_trace_dual_data (A : SArithmeticData F) : TraceDualData A := by
  have hdual := canonical_trace_dual A
  refine ⟨?_, canonical_trace_compatible A, ?_, ?_⟩
  · intro v
    exact ResidueTrace.continuous_localTraceCharacter v.val
  · intro hbot
    have hne : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    have hinj : Function.Injective (algebraMap (𝓞 F) A.R) := by
      intro x y hxy
      have h : ((algebraMap (𝓞 F) A.R x : A.R) : F) =
          ((algebraMap (𝓞 F) A.R y : A.R) : F) := by rw [hxy]
      simpa only [Subalgebra.coe_algebraMap] using
        (IsFractionRing.injective (𝓞 F) F h)
    exact hne ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)
  · intro δ hδ hspan q _ a ha hspanq
    exact residue_of_trace_dual A hdual δ hδ hspan q a ha hspanq

end
end DedekindZetaZeroFree.CodifferentResidueSieve
