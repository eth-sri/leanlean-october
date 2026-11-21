module

public import DedekindZetaZeroFree.Algebra.RationalEvaluation

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ConditionalCubicResidueReduction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPRankOneShellContinuation KPRankOneGenericComposition
open KPRankOneReverseRegulatorShells
open scoped TensorProduct
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

open RationalEvaluation

private theorem actual_rational_coefficient_numeric
    (α w : ℂ) (r₀ : ℂˣ) (hr₀ : (r₀ : ℂ) = α*w)
    (ε : Sign) (hd : denominator (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀) ≠ 0)
    (n : ℤ) :
    Evaluates w
      ((rationalDenominator (KPExceptionalRaw.LocalField F q) ε (RatFunc.C α*RatFunc.X))⁻¹ *
        (if ε = .plus then RatFunc.C α*RatFunc.X else (RatFunc.C α*RatFunc.X)⁻¹)^n)
      ((denominator (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀))⁻¹ *
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀) : ℂ)^n) := by
  have hv : Evaluates w (RatFunc.C α*RatFunc.X) (r₀ : ℂ) := by
    rw [hr₀]; exact Evaluates.mul (Evaluates.const w α) (Evaluates.var w)
  have hi := Evaluates.inv hv r₀.ne_zero
  have hroot := root_parameter_additiveParameter F q r₀
  have hdv : Evaluates w (rationalDenominator (KPExceptionalRaw.LocalField F q) ε (RatFunc.C α*RatFunc.X))
      (denominator (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀)) := by
    cases ε
    · simpa only [KPRankOneGenericComposition.rationalDenominator,map_one,denominator,ite_true,KPRankOneRootParameter.t,hroot] using
        Evaluates.sub (Evaluates.const w 1)
          (Evaluates.mul (Evaluates.const w (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)⁻¹) (Evaluates.pow hv 6))
    · simpa only [KPRankOneGenericComposition.rationalDenominator,map_one,denominator,show Sign.minus ≠ Sign.plus from by decide,ite_false,hroot] using
        Evaluates.sub (Evaluates.const w 1)
          (Evaluates.mul (Evaluates.const w (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)) (Evaluates.pow hi 6))
  apply Evaluates.mul (Evaluates.inv hdv hd)
  have hunit : (evaluationUnit (KPExceptionalRaw.LocalField F q) ε (additiveParameter F q r₀) : ℂ) =
      if ε = .plus then (r₀ : ℂ) else (r₀ : ℂ)⁻¹ := by
    cases ε <;> simp [evaluationUnit,rUnit,hroot]
  rw [hunit]
  cases ε
  · simpa using Evaluates.zpow hv r₀.ne_zero n
  · simpa using Evaluates.zpow hi (inv_ne_zero r₀.ne_zero) n

private theorem both_standard_denominators_regular
    (α w : ℂ) (hα : α^6=(residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ))
    (hw0 : w ≠ 0) (hw6 : w^6 ≠ 1) :
    ∃ r₀ : ℂˣ, (r₀ : ℂ)=α*w ∧
      denominator (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀) ≠ 0 ∧
      denominator (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀) ≠ 0 := by
  have hq0 : (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (KPExceptionalRaw.LocalField F q))))).ne'
  have hα0 : α ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide)] at hα
    exact hq0 hα.symm
  let r₀ := Units.mk0 (α*w) (mul_ne_zero hα0 hw0)
  have hroot := root_parameter_additiveParameter F q r₀
  have h6 : (r₀ : ℂ)^6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)*w^6 := by
    change (α*w)^6 = _
    rw [mul_pow,hα]
  have h6ne : (r₀ : ℂ)^6 ≠ (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ) := by
    rw [h6]
    intro he
    exact hw6 ((mul_left_cancel₀ hq0) (by simpa using he))
  refine ⟨r₀,rfl,?_,?_⟩
  · simp only [denominator,ite_true, KPRankOneRootParameter.t,hroot]
    apply sub_ne_zero.mpr
    intro he
    apply h6ne
    exact ((inv_mul_eq_one₀ hq0).mp he.symm).symm
  · simp only [denominator,show Sign.minus ≠ Sign.plus from by decide,ite_false,hroot]
    apply sub_ne_zero.mpr
    intro he
    apply h6ne
    have he' : (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)*((r₀ : ℂ)^6)⁻¹ = 1 := by
      simpa only [inv_pow] using he.symm
    exact ((mul_inv_eq_one₀ (pow_ne_zero _ r₀.ne_zero)).mp he').symm

private theorem scalar_regular_locus_infinite
    (C : RatFunc ℂ) :
    {w : ℂ | w ≠ 0 ∧ w^6 ≠ 1 ∧ C.denom.eval w ≠ 0}.Infinite := by
  let bad : Set ℂ := {0} ∪ {w | w^6=1} ∪ {w | C.denom.IsRoot w}
  have hp : (Polynomial.X^6-1 : Polynomial ℂ) ≠ 0 := by
    intro he
    have hv := congrArg (Polynomial.eval (0 : ℂ)) he
    norm_num at hv
  have hroots : {w : ℂ | w^6=1}.Finite := by
    convert Polynomial.finite_setOfPred_isRoot hp using 1
    ext w
    simp [Polynomial.IsRoot,sub_eq_zero]
  have hb : bad.Finite := ((Set.finite_singleton 0).union hroots).union
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero C))
  have hi := Set.infinite_univ.sdiff hb
  apply hi.mono
  intro w hw
  rcases hw with ⟨_,hw⟩
  exact ⟨fun h => hw (Or.inl (Or.inl h)),
    fun h => hw (Or.inl (Or.inr h)),fun h => hw (Or.inr h)⟩

set_option maxHeartbeats 8000000 in
set_option backward.isDefEq.respectTransparency false in

theorem rational_composition_of_regular_values
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (α : ℂ) (hα : α ^ 6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ))
    (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q))
    (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus)
    (C : RatFunc ℂ) (ε : Sign)
    (hn : ∀ w : ℂ, w ≠ 0 → w ^ 6 ≠ 1 → C.denom.eval w ≠ 0 →
      ∀ r₀ : ℂˣ, (r₀ : ℂ) = α * w →
      if ε = .plus then
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id
      else
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id) :
    if ε = .plus then
      (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
        (RatFunc.C α * RatFunc.X)).comp
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (RatFunc.C α * RatFunc.X)) = C • LinearMap.id
    else
      (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
        (RatFunc.C α * RatFunc.X)).comp
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (RatFunc.C α * RatFunc.X)) = C • LinearMap.id := by
  classical
  let v : RatFunc ℂ := RatFunc.C α*RatFunc.X
  let a : ℤ → RatFunc ℂ := fun n =>
    (rationalDenominator (KPExceptionalRaw.LocalField F q) .plus v)⁻¹ * v^n
  let b : ℤ → RatFunc ℂ := fun n =>
    (rationalDenominator (KPExceptionalRaw.LocalField F q) .minus v)⁻¹ * v⁻¹^n
  let U : Set ℂ := {w | w ≠ 0 ∧ w^6 ≠ 1 ∧ C.denom.eval w ≠ 0}
  have hU : U.Infinite := scalar_regular_locus_infinite C
  have hr (w : ℂ) (hw : w ∈ U) := both_standard_denominators_regular F q α w hα hw.1 hw.2.1
  have ha : ∀ w ∈ U, ∀ n ∈ p.support, (a n).denom.eval w ≠ 0 := by
    intro w hw n _
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    exact (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).1
  have hb : ∀ w ∈ U, ∀ n ∈ pRev.support, (b n).denom.eval w ≠ 0 := by
    intro w hw n _
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    exact (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).1
  cases ε with
  | plus =>
    have hn' : ∀ w : ℂ, w ≠ 0 → w^6 ≠ 1 → C.denom.eval w ≠ 0 →
        ∀ r₀ : ℂˣ, (r₀ : ℂ) = α*w →
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw hw6 hC r₀ hr₀
      simpa only [ite_true] using hn w hw hw6 hC r₀ hr₀
    have hspec : ∀ w ∈ U,
        (∑ j ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b j) • pRev j).comp
          (∑ i ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a i) • p i) =
        RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw
      obtain ⟨r₀,he,hp,hm⟩ := hr w hw
      have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
          (denominator (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).2
      have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
          (denominator (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).2
      have ep : (∑ n ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a n) • p n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀) := by
        simp only [ea,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      have em : (∑ n ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b n) • pRev n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀) := by
        simp only [eb,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      rw [ep,em]
      exact hn' w hw.1 hw.2.1 hw.2.2 r₀ he
    have hh := rational_rectangular_composition p.support pRev.support a b p pRev
      C U hU ha hb (fun _ hw => hw.2.2) hspec
    simp only [ite_true]
    simpa only [rationalStandard,Finsupp.sum,Finset.smul_sum,smul_smul,
      ite_true,ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] using hh
  | minus =>
    have hn' : ∀ w : ℂ, w ≠ 0 → w^6 ≠ 1 → C.denom.eval w ≠ 0 →
        ∀ r₀ : ℂˣ, (r₀ : ℂ) = α*w →
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (additiveParameter F q r₀)).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀)) =
          RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw hw6 hC r₀ hr₀
      simpa only [show Sign.minus ≠ Sign.plus from by decide, ite_false] using hn w hw hw6 hC r₀ hr₀
    have hspec : ∀ w ∈ U,
        (∑ j ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a j) • p j).comp
          (∑ i ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b i) • pRev i) =
        RatFunc.eval (RingHom.id ℂ) w C • LinearMap.id := by
      intro w hw
      obtain ⟨r₀,he,hp,hm⟩ := hr w hw
      have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
          (denominator (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .plus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).2
      have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
          (denominator (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀))⁻¹ *
            (evaluationUnit (KPExceptionalRaw.LocalField F q) .minus (additiveParameter F q r₀) : ℂ)^n :=
        (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).2
      have ep : (∑ n ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a n) • p n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
            (additiveParameter F q r₀) := by
        simp only [ea,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      have em : (∑ n ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b n) • pRev n) =
          continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
            (additiveParameter F q r₀) := by
        simp only [eb,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
      rw [ep,em]
      exact hn' w hw.1 hw.2.1 hw.2.2 r₀ he
    have hh := rational_rectangular_composition pRev.support p.support b a pRev p
      C U hU hb ha (fun _ hw => hw.2.2) hspec
    simp only [show Sign.minus ≠ Sign.plus from by decide, ite_false]
    simpa only [rationalStandard,Finsupp.sum,Finset.smul_sum,smul_smul,
      ite_true,ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] using hh

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps.Reverse
