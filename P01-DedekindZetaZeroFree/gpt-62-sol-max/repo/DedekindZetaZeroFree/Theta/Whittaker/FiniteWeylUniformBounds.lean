module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylSupport
import all DedekindZetaZeroFree.RepresentationTheory.Kirillov.NonarchimedeanWhittakerBounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem finite_weyl_bounds (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    ∃ M D : ℝ, 0 < M ∧ 0 ≤ D ∧ ∀ v (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ),
      ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z‖ ≤
        D * finitePowerMajorant M ‖(z : p.val.adicCompletion F)‖ := by
  haveI : Finite R.A.UnitQuotient := C.sources.finite_companions
  letI : Fintype R.A.UnitQuotient := Fintype.ofFinite _
  let I := R.A.UnitQuotient × R.A.Sf
  have hsupport (i : I) := localWeyl_support R C i.1 i.2
  have hsmall (i : I) := localWeyl_small_norm R C i.1 i.2
  choose m hm hcut using hsupport
  choose d hd hdec using hsmall
  let M : ℝ := 1 + ∑ i : I, m i
  have hsum : 0 ≤ ∑ i : I, m i := Finset.sum_nonneg fun i _ => (hm i).le
  have hM : 0 < M := by dsimp [M]; linarith
  have hmM (i : I) : m i ≤ M := by
    have h := Finset.single_le_sum (fun j _ => (hm j).le) (Finset.mem_univ i)
    dsimp [M]; linarith
  have hann (i : I) : ∃ b : ℝ, ∀ z : (i.2.val.adicCompletion F)ˣ,
      1 ≤ ‖(z : i.2.val.adicCompletion F)‖ → ‖(z : i.2.val.adicCompletion F)‖ ≤ M →
      ‖ThetaExpansion.normalizedLocalWeylValue R C i.1 (Sum.inr i.2.val) z‖ ≤ b := by
    have hc := KPFiniteLocal.norm_annulus_isCompact (K := i.2.val.adicCompletion F) 1 M zero_lt_one
    obtain ⟨b, hb⟩ := hc.exists_bound_of_continuousOn
      (localWeyl_locallyConstant R C i.1 i.2).continuous.continuousOn
    exact ⟨b, fun z h1 h2 => hb z ⟨h1, h2⟩⟩
  choose b hb using hann
  let D : ℝ := ∑ i : I, (d i + max (b i) 0)
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => add_nonneg (hd i).le (le_max_right _ _)
  have hdD (i : I) : d i ≤ D := by
    have hh := Finset.single_le_sum
      (fun j _ => add_nonneg (hd j).le (le_max_right (b j) 0)) (Finset.mem_univ i)
    exact (le_add_of_nonneg_right (le_max_right (b i) 0)).trans hh
  have hbD (i : I) : b i ≤ D := by
    have hh := Finset.single_le_sum
      (fun j _ => add_nonneg (hd j).le (le_max_right (b j) 0)) (Finset.mem_univ i)
    exact (le_max_left _ _).trans ((le_add_of_nonneg_left (hd i).le).trans hh)
  refine ⟨M, D, hM, hD, ?_⟩
  intro v p z
  have hzpos : 0 < ‖(z : p.val.adicCompletion F)‖ := norm_pos_iff.mpr z.ne_zero
  by_cases hzM : ‖(z : p.val.adicCompletion F)‖ ≤ M
  · rw [finitePowerMajorant, if_pos hzM]
    by_cases hz1 : ‖(z : p.val.adicCompletion F)‖ ≤ 1
    · exact (hdec (v, p) z hz1).trans
        (mul_le_mul_of_nonneg_right (hdD (v, p)) (Real.rpow_nonneg hzpos.le _))
    · have h := hb (v, p) z (not_le.mp hz1).le hzM
      have hr : 1 ≤ Real.rpow ‖(z : p.val.adicCompletion F)‖ (1 / 4 : ℝ) :=
        Real.one_le_rpow (not_le.mp hz1).le (by norm_num)
      exact (h.trans (hbD (v, p))).trans (by simpa using mul_le_mul_of_nonneg_left hr hD)
  · rw [finitePowerMajorant, if_neg hzM,
      hcut (v, p) z ((hmM (v, p)).trans_lt (not_le.mp hzM)), norm_zero, mul_zero]

end DedekindZetaZeroFree.SheetRescaling

end
