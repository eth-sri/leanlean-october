module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

namespace DedekindZetaZeroFree

section

variable (G : Type*) [CommGroup G] (n : ℕ)

abbrev PowerQuotient : Type _ :=
  G ⧸ (powMonoidHom (α := G) n).range

theorem powerQuotient_pow_eq_one
    (q : PowerQuotient G n) : q ^ n = 1 := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simp

end

noncomputable instance instPowerQuotientModule (G : Type*) [CommGroup G] (n : ℕ) :
    Module (ZMod n) (Additive (PowerQuotient G n)) :=
  AddCommGroup.zmodModule (by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow]
    simp [powerQuotient_pow_eq_one G n x.toMul])

def addEquivToZModLinearEquiv (n : ℕ) (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module (ZMod n) M] [Module (ZMod n) N]
    (e : M ≃+ N) : M ≃ₗ[ZMod n] N :=
  { e with
    map_smul' := fun c x => ZMod.map_smul e c x}

end DedekindZetaZeroFree
