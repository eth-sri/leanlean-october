module

public import DedekindZetaZeroFree.Algebra.PowerQuotientModules
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitStructureAndLogarithmicRank
public import DedekindZetaZeroFree.Arithmetic.Units.TorsionPowerCoordinates
public import ClassFieldTheory.Definitions.All
public import ClassFieldTheory.Theorems.All

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section

variable (F : Type) [Field F] [NumberField F]
    (A : DedekindZetaZeroFree.SArithmeticData F)

 theorem inc_injective :
    Function.Injective A.ordinaryTorsionInclusion := by
  have hAlg : Function.Injective (algebraMap (𝓞 F) A.R) := by
    intro a b h
    simpa using (congrArg Subtype.val h)
  intro u v huv
  have huv' := huv
  exact Subtype.val_injective (Units.map_injective hAlg huv')

theorem sunitPowerQuotient_finite (n : ℕ+) :
    Finite (PowerQuotient A.Rˣ (n : ℕ)) := by
  exact Finite.of_equiv (PowerQuotient (SUnitGroup A.Sf) (n : ℕ))
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
      A.Rˣ (SUnitGroup A.Sf) (n : ℕ) A.unitEquiv.symm).symm.toEquiv

 def rawStructure : A.Rˣ ≃*
    NumberField.Units.torsion F × Multiplicative (Fin A.sunitRank →₀ ℤ) := by
  have hr : SUnitGroup.logRank A.Sf = A.sunitRank := by
    simp [SUnitGroup.logRank, sunitRank, A.infinitePlace_card]
  exact A.unitEquiv.symm.trans (hr ▸ SUnitGroup.decomposition (K := F) A.Sf)
 theorem rawStructure_snd (u : NumberField.Units.torsion F) :
    (rawStructure F A (A.ordinaryTorsionInclusion u)).2 = 1 := by
  have hv := (MonoidHom.snd _ _).isOfFinOrder ((rawStructure F A).toMonoidHom.isOfFinOrder
    (A.ordinaryTorsionInclusion.isOfFinOrder (isOfFinOrder_of_finite u)))
  exact (isOfFinOrder_iff_eq_one _).mp hv
 def torsionChange : NumberField.Units.torsion F ≃* NumberField.Units.torsion F := by
  let f := (MonoidHom.fst _ _).comp
    ((rawStructure F A).toMonoidHom.comp A.ordinaryTorsionInclusion)
  have hf : Function.Injective f := by
    intro u v h
    have hprod : rawStructure F A (A.ordinaryTorsionInclusion u) =
        rawStructure F A (A.ordinaryTorsionInclusion v) := by
      apply Prod.ext
      · exact h
      · rw [rawStructure_snd, rawStructure_snd]
    exact inc_injective F A ((rawStructure F A).injective hprod)
  exact MulEquiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective).mp hf⟩
 def normalizedStructure : A.Rˣ ≃*
    NumberField.Units.torsion F × Multiplicative (Fin A.sunitRank →₀ ℤ) :=
  (rawStructure F A).trans ((torsionChange F A).symm.prodCongr (MulEquiv.refl _))
set_option maxHeartbeats 800000 in
private theorem normalizedStructure_inc (u : NumberField.Units.torsion F) :
    normalizedStructure F A (A.ordinaryTorsionInclusion u) = (u, 1) := by
  apply Prod.ext
  · exact (torsionChange F A).symm_apply_apply u
  · exact rawStructure_snd F A u
 section

variable (n : ℕ+) (hn : (n : ℕ) ∣ 12)

def coordinates :
    PowerQuotient A.Rˣ (n : ℕ) ≃*
      Multiplicative (ZMod (n : ℕ)) × Multiplicative (Fin A.sunitRank → ZMod (n : ℕ)) :=
  (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv _ _ n
    (normalizedStructure F A)).trans
    ((LocalFieldTheory.nthPowerProductQuotientEquiv _ _ n).trans
      ((A.torsionPowerQuotientEquiv n hn).prodCongr
        (KummerTheory.multiplicativeFinsuppNthPowerQuotientEquivPiZMod A.sunitRank n)))
private theorem coordinates_inc
    (u : NumberField.Units.torsion F) :
    coordinates F A n hn (QuotientGroup.mk (A.ordinaryTorsionInclusion u)) =
      (A.torsionPowerQuotientEquiv n hn (QuotientGroup.mk u), 1) := by
  simp only [coordinates, MulEquiv.trans_apply]
  change ((A.torsionPowerQuotientEquiv n hn).prodCongr
      (KummerTheory.multiplicativeFinsuppNthPowerQuotientEquivPiZMod A.sunitRank n))
    (LocalFieldTheory.nthPowerProductQuotientEquiv _ _ n
      (QuotientGroup.mk (normalizedStructure F A (A.ordinaryTorsionInclusion u)))) = _
  rw [normalizedStructure_inc]
  simp [LocalFieldTheory.nthPowerProductQuotientEquiv,
    LocalFieldTheory.nthPowerProductQuotientHom,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse,
    QuotientGroup.quotientMulEquivOfEq_mk, MulEquiv.trans_apply]
  change (A.torsionPowerQuotientEquiv n hn (QuotientGroup.mk u),
    KummerTheory.multiplicativeFinsuppNthPowerQuotientEquivPiZMod A.sunitRank n
      (QuotientGroup.mk (1 : Multiplicative (Fin A.sunitRank →₀ ℤ)))) = _
  simp

theorem sunitPowerCoordinates_exists :
    ∃ e : Additive (PowerQuotient A.Rˣ (n : ℕ)) ≃ₗ[ZMod (n : ℕ)]
      ZMod (n : ℕ) × (Fin A.sunitRank → ZMod (n : ℕ)),
      ∀ u : NumberField.Units.torsion F,
        e (Additive.ofMul (QuotientGroup.mk (A.ordinaryTorsionInclusion u))) =
          (Multiplicative.toAdd
            (A.torsionPowerQuotientEquiv n hn (QuotientGroup.mk u)), 0) := by
  refine ⟨(addEquivToZModLinearEquiv (n : ℕ) _ _ ((coordinates F A n hn).trans
    (MulEquiv.prodMultiplicative (ZMod (n : ℕ))
      (Fin A.sunitRank → ZMod (n : ℕ))).symm).toAdditiveLeft), ?_⟩
  intro u
  change ((coordinates F A n hn (QuotientGroup.mk (A.ordinaryTorsionInclusion u))).1.toAdd,
    (coordinates F A n hn (QuotientGroup.mk (A.ordinaryTorsionInclusion u))).2.toAdd) = _
  rw [coordinates_inc]
  rfl

include hn in
theorem sunitPowerCoordinatesPi_nonempty :
    Nonempty (Additive (PowerQuotient A.Rˣ (n : ℕ)) ≃ₗ[ZMod (n : ℕ)]
      (Fin (NumberField.InfinitePlace.nrComplexPlaces F + A.Sf.card) →
        ZMod (n : ℕ))) := by
  obtain ⟨e, -⟩ := sunitPowerCoordinates_exists F A n hn
  rw [← A.sunitRank_add_one]
  exact ⟨e.trans (Fin.consLinearEquiv (ZMod (n : ℕ))
    (fun _ : Fin (A.sunitRank + 1) => ZMod (n : ℕ)))⟩

end

theorem finrank_sunitPowerQuotient (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3)
    [Fact (Nat.Prime ℓ)] :
    Module.finrank (ZMod ℓ) (Additive (PowerQuotient A.Rˣ ℓ)) =
      NumberField.InfinitePlace.nrComplexPlaces F + A.Sf.card := by
  have hpos : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
  have hdiv : ℓ ∣ 12 := by rcases hℓ with rfl | rfl <;> norm_num
  obtain ⟨e⟩ := sunitPowerCoordinatesPi_nonempty F A ⟨ℓ, hpos⟩ hdiv
  exact e.finrank_eq.trans
    ((Module.finrank_fintype_fun_eq_card (ZMod ℓ)).trans (Fintype.card_fin _))

theorem sunitSixthPowerQuotient_finite : Finite (PowerQuotient A.Rˣ 6) := by
  exact sunitPowerQuotient_finite F A (6 : ℕ+)

end
end DedekindZetaZeroFree.SArithmeticData
