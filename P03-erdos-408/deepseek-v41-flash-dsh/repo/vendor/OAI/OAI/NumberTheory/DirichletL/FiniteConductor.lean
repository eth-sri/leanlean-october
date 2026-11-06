module

public import OAI.NumberTheory.DirichletL.FiniteFourier
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

theorem exists_character_factor_iff {G H : Type*} [Group G] [CommGroup H]
    [Finite H] (q : G →* H) (χ : G →* ℂˣ) :
    (∃ φ : H →* ℂˣ, φ.comp q = χ) ↔ q.ker ≤ χ.ker := by
  constructor
  · rintro ⟨φ, rfl⟩ g hg
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hg, map_one]
  · intro hker
    have hker' : q.rangeRestrict.ker ≤ χ.ker := by
      simpa only [MonoidHom.ker_rangeRestrict] using hker
    let θ : q.range →* ℂˣ :=
      MonoidHom.liftOfSurjective q.rangeRestrict q.rangeRestrict_surjective ⟨χ, hker'⟩
    have hθ : θ.comp q.rangeRestrict = χ := MonoidHom.liftOfRightInverse_comp ..
    obtain ⟨φ, hφ⟩ := MonoidHom.domRestrict_surjective ℂ q.range θ
    refine ⟨φ, ?_⟩
    calc
      φ.comp q = (φ.domRestrict q.range).comp q.rangeRestrict := rfl
      _ = θ.comp q.rangeRestrict := by rw [← hφ]; rfl
      _ = χ := hθ

variable {R : Type*} [CommRing R] [Finite R]

def quotientUnits (I : Ideal R) : Rˣ →* (R ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

def FactorsThroughIdeal (χ : MulChar R ℂ) (I : Ideal R) : Prop :=
  ∃ φ : MulChar (R ⧸ I) ℂ,
    φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom

omit [Finite R] in
theorem quotientUnits_eq_one_iff (I : Ideal R) (u : Rˣ) :
    quotientUnits I u = 1 ↔ (u : R) - 1 ∈ I := by
  rw [← Units.val_inj]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

theorem factorsThroughIdeal_iff (χ : MulChar R ℂ) (I : Ideal R) :
    FactorsThroughIdeal χ I ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ I → χ (u : R) = 1 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hfactor : FactorsThroughIdeal χ I ↔
      ∃ φ : (R ⧸ I)ˣ →* ℂˣ, φ.comp (quotientUnits I) = χ.toUnitHom := by
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ.toUnitHom, hφ⟩
    · rintro ⟨φ, hφ⟩
      refine ⟨MulChar.ofUnitHom φ, ?_⟩
      simpa only [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply] using hφ
  rw [hfactor, exists_character_factor_iff]
  constructor
  · intro h u hu
    have hunit := h ((quotientUnits_eq_one_iff I u).mpr hu)
    exact congrArg Units.val hunit
  · intro h u hu
    apply Units.ext
    exact h u ((quotientUnits_eq_one_iff I u).mp hu)

theorem primitiveOnIdeals_iff_no_descent (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by
  simp only [IsPrimitiveOnIdeals, factorsThroughIdeal_iff]
  push Not
  rfl

theorem FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)

omit [Finite R] in

theorem factorization_with_source_mask (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom) (a : R) :
    χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simp only [u.isUnit, ite_true]
    exact (congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ).symm
  · simp only [ha, ite_false, MulChar.map_nonunit _ ha]

end

end SevenEighths.FiniteConductor

end OAI
