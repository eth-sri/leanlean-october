module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.JacquetDualColumnIndependence
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.ProjectorGermsAndFrequencySupport

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorFrequencyNormalization
open scoped NumberField Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPTameJacquetTestDuality
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

private theorem valuation_integer_eq_finite_ball_zero :
    ((valuation (LocalField F q)).integer : Set (LocalField F q)) = finiteCompletionBall F q 0 := by
  letI : (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ext x
  exact ((ValuativeRel.isEquiv Valued.v
    (valuation (LocalField F q))).le_one_iff_le_one).symm

theorem exists_actual_conductor_frequency :
    ∃ a : (LocalField F q)ˣ,
      HasConductorIntegers F q (KPKirillovProjectorGerms.frequencyCharacter F q a) := by
  letI : (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  let d := (localDifferentExponent F q : ℤ)
  let a := Units.mk0 (finiteCompletionUniformizer F q ^ (-d))
    (zpow_ne_zero _ (finiteCompletionUniformizer_ne_zero F q))
  have ha : Valued.v (a : LocalField F q) = WithZero.exp d := by
    dsimp [a]
    rw [map_zpow₀, finiteCompletionUniformizer_valuation, ← WithZero.exp_zsmul]
    congr 1
    simp
  refine ⟨a, ?_⟩
  intro y
  let valuation₀ := valuation (LocalField F q)
  have he : (∀ x : 𝒪[LocalField F q],
      KPKirillovProjectorGerms.frequencyCharacter F q a
        (Multiplicative.ofAdd (x * y)) = 1) ↔
      a * y ∈ localFiniteAnnihilator F q (finiteCompletionBall F q 0) := by
    rw [mem_localFiniteAnnihilator]
    constructor
    · intro h x hx
      have hi : x ∈ (valuation₀).integer := by
        change x ∈ ((valuation₀).integer : Set (LocalField F q))
        rwa [valuation_integer_eq_finite_ball_zero F q]
      have hz := congrArg (fun z : ℂˣ => (z : ℂ)) (h ⟨x, hi⟩)
      apply Subtype.ext
      simpa only [KPKirillovProjectorGerms.frequencyCharacter_apply,
        Units.val_one, Circle.coe_one, mul_left_comm, mul_comm, mul_assoc] using hz
    · intro h x
      apply Units.ext
      have hz := h x.val (by change x.val ∈ (finiteCompletionBall F q 0 : Set (LocalField F q)); rw [← valuation_integer_eq_finite_ball_zero F q]; exact x.property)
      simpa only [KPKirillovProjectorGerms.frequencyCharacter_apply,
        Units.val_one, Circle.coe_one, mul_left_comm, mul_comm, mul_assoc] using congrArg (fun z : Circle => (z : ℂ)) hz
  rw [he, localFiniteAnnihilator_finiteCompletionBall, mem_finiteCompletionBall,
    map_mul, ha]
  simp only [neg_zero, zero_sub, neg_neg]
  change WithZero.exp d * Valued.v y ≤ WithZero.exp d ↔
    valuation₀ y ≤ 1
  have hi := (ValuativeRel.isEquiv (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ)))
    (valuation₀)).le_one_iff_le_one (x := y)
  rw [← hi]
  simpa using (mul_le_mul_iff_right₀ (show (0 : WithZero (Multiplicative ℤ)) < WithZero.exp d from WithZero.exp_pos))
end DedekindZetaZeroFree.ActualReverseMinorFrequencyNormalization

end
