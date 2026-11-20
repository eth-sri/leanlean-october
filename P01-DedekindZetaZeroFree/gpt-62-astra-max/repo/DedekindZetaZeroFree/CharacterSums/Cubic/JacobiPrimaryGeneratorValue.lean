module

public import DedekindZetaZeroFree.CharacterSums.Cubic.JacobiNormAndPrimaryCongruence
public import DedekindZetaZeroFree.CharacterSums.Cubic.JacobiPrimeReduction
public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.PrimaryGenerators

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

section

variable (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E))
    (hq0 : q ≠ ⊥) (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤)

include hq0 hq6 in
theorem mem_I3_of_sup_span_six_eq_top :
    q ∈ I3 E := by
  refine (mem_I3 E q).mpr ⟨hq0, ?_⟩
  apply top_unique
  rw [← hq6]
  apply sup_le_sup_left
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact ⟨2, by norm_num⟩

def q3 : I3 E :=
  ⟨q, mem_I3_of_sup_span_six_eq_top E q hq0 hq6⟩

end

section

variable (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {3} ℚ E] (ω : E)
    (hω : IsPrimitiveRoot ω 3) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤)

theorem span_Jq :
    Ideal.span {Jq E ω hω q hq0 hqp hq6} = q := by
  obtain ⟨B, hB⟩ := (Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (jacobiSum_ρq_mem E ω hω q hq0 hqp hq6))) : q ∣ Ideal.span {Jq E ω hω q hq0 hqp hq6})
  have habsq : Ideal.absNorm q = residueCard E q hq0 := by
    letI := residueFintype E q hq0
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_eq_fintype_card
  have hBtop := Ideal.absNorm_eq_one_iff.mp (Nat.mul_left_cancel (Nat.pos_of_ne_zero (fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h))) (by rw [mul_one]; exact (by
    rw [← map_mul, ← hB]
    exact ((absNorm_span_Jq E ω hω q hq0 hqp hq6).trans habsq.symm))))
  rw [hB, hBtop, Ideal.mul_top]

theorem Jq_eq_neg_primaryGenerator :
    Jq E ω hω q hq0 hqp hq6 = -primaryGenerator E (q3 E q hq0 hq6) := by
  have hspan :=
    span_Jq E ω hω q hq0 hqp hq6
  let primaryGenerator₀ := primaryGenerator E (q3 E q hq0 hq6)
  have hspanPG : Ideal.span {primaryGenerator₀} = q := by
    rw [span_primaryGenerator]
    rfl
  let Jq₀ := Jq E ω hω q hq0 hqp hq6
  have hxy : Ideal.span {-(Jq₀)} =
      Ideal.span {primaryGenerator₀} := by
    rw [Ideal.span_singleton_neg, hspan, hspanPG]
  have hred : red3 E (-(Jq₀)) = 1 := by
    rw [map_neg, red3_Jq]
    simp
  have hx3unit : IsUnit (red3 E (-(Jq₀))) := by
    rw [hred]
    exact isUnit_one
  have hred3eq : red3 E (-(Jq₀)) =
      red3 E (primaryGenerator₀) := by
    rw [hred, red3_primaryGenerator]
  exact neg_eq_iff_eq_neg.mp (eq_of_span_eq_of_red3_eq E (-(Jq₀))
    (primaryGenerator₀) hxy (by
      rw [Ideal.span_singleton_neg, hspan]
      exact hq0) hx3unit hred3eq)

end

theorem jacobiSum_ρqC_eq_neg_primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    letI := residueFintype E q hq0
    jacobiSum (ρqC E ω hω ι q hq0 hqp hq6) (ρqC E ω hω ι q hq0 hqp hq6) =
      -ιR E ι (primaryGenerator E (q3 E q hq0 hq6)) := by
  letI := residueFintype E q hq0
  simp only [ρqC]
  let ρq₀ := ρq E ω hω q hq0 hqp hq6
  rw [(jacobiSum_ringHomComp (ρq₀) (ρq₀)
    (ιR E ι)), show jacobiSum (ρq₀) (ρq₀) =
      Jq E ω hω q hq0 hqp hq6 from rfl,
    Jq_eq_neg_primaryGenerator E ω hω q hq0 hqp hq6]
  simp

end DedekindZetaZeroFree.Eisenstein
