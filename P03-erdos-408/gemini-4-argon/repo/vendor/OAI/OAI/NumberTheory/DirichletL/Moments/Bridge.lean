module

public import OAI.NumberTheory.DirichletL.Moments.FirstPoisson
public import OAI.NumberTheory.DirichletL.Moments.Primitive

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

def productCharacter (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) :
    MulChar (Residue (a * b)) ℂ where
  toFun x := χa ((principalCRT a b hcop x).1) * χb ((principalCRT a b hcop x).2)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul]; ring
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (principalCRT a b hcop x) := fun h =>
      hx ((isUnit_map_iff (principalCRT a b hcop) x).mp h)
    rw [Prod.isUnit_iff] at hn
    by_cases h : IsUnit (principalCRT a b hcop x).1
    · rw [χb.map_nonunit (fun hb => hn ⟨h, hb⟩), mul_zero]
    · rw [χa.map_nonunit h, zero_mul]

theorem productCharacter_apply (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : Residue (a * b)) :
    productCharacter a b hcop χa χb x =
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productCharacter, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    principalCRT_mk, frequencyReduction_mk]

@[simp] theorem productCharacter_mk (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : O) :
    productCharacter a b hcop χa χb (Ideal.Quotient.mk _ x) =
      χa (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x) := by
  rw [productCharacter_apply, frequencyReduction_mk, frequencyReduction_mk]

end SevenEighths.CenteredMomentBridge
end

end OAI
