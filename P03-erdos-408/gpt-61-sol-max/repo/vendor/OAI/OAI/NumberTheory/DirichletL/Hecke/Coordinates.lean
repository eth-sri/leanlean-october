module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.Family
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
private def pb  := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

private theorem pb_gen : pb.gen = HeckeFamily.omega := hζ.integralPowerBasis_gen

theorem coordinateElement_surjective :
    Function.Surjective (fun n : ℤ × ℤ => coordinateElement n.1 n.2) := by
  intro x
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨(a,b), ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    grind [pb_dim]
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  simpa [a, b, i0, i1, pb_gen, coordinateElement, smul_eq_mul, mul_comm] using hsum

def intQuotientHom (χ : Character)  :=
  (Ideal.Quotient.mk χ.modulus).toAddMonoidHom.comp (Int.castAddHom O)

def zmodQuotientHom (χ : Character)  :=
  ZMod.lift χ.period ⟨intQuotientHom χ, by
    change Ideal.Quotient.mk χ.modulus ((χ.period : ℤ) : O) = 0
    simpa only [Int.cast_natCast] using quotient_period χ⟩

section
variable (χ : Character)

@[simp] theorem zmodQuotientHom_intCast   (a : ℤ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) :=
  ZMod.lift_coe _ _ _

@[simp] theorem zmodQuotientHom_natCast   (a : ℕ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) := by
  simpa only [Int.cast_natCast] using zmodQuotientHom_intCast χ (a : ℤ)

def coordinateQuotientHom (χ : Character) :
    (ZMod χ.period × ZMod χ.period) →+ (O ⧸ χ.modulus) where
  toFun p := zmodQuotientHom χ p.1 +
    zmodQuotientHom χ p.2 * Ideal.Quotient.mk χ.modulus HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

@[simp] theorem coordinateQuotientHom_intCast   (a b : ℤ) :
    coordinateQuotientHom χ (a, b) =
      Ideal.Quotient.mk χ.modulus (coordinateElement a b) := by
  simp_all [coordinateQuotientHom, zmodQuotientHom_intCast, coordinateElement]

theorem coordinateQuotientHom_surjective   :
    Function.Surjective (coordinateQuotientHom χ) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a,b⟩, hab⟩ := coordinateElement_surjective z
  change coordinateElement a b = z at hab
  exact ⟨(a,b), by rw [coordinateQuotientHom_intCast, hab]⟩

theorem coefficients_eq_quotient_character  
     a  :
    coefficients χ a = χ.residue (coordinateQuotientHom χ (a.1, a.2)) := by
  simp [HeckeFamily.coefficients, HeckeFamily.elementCoeff, coordinateQuotientHom,
    coordinateElement]

end

end SevenEighths.HeckeCoordinates

end

end OAI
