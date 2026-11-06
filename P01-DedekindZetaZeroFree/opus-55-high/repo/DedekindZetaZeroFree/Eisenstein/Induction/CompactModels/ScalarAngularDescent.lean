module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

open scoped Classical NumberField Topology
open DedekindZetaZeroFree.KPMsRationalCompactCrossPairing
namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarAngularDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem source_rational (s : ℂ) (f : Source F ζ hζ s)
    (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    f.val (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g) = f.val g := by
  let t : (sourcePolarization F ζ hζ s).H :=
    ⟨KPGlobalTorusFunctionData.s F ζ hζ y, Subgroup.mem_sup_left ⟨y, rfl⟩⟩
  have hc : ((sourcePolarization F ζ hζ s).character t : ℂ) = 1 := by
    change (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ t : ℂ) *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s t.val = 1
    rw [KPGlobalCenterRationalCharacter.lambdaR_rational F ζ hζ y t rfl]
    simp [t, KPGlobalTorusBorelTwistCompatibility.normPower,
      KPGlobalTorusBorelTwistCompatibility.delta_rational]
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf, t,
      KPGlobalTorusBorelTwistCompatibility.delta_rational]
  simpa only [hd, hc, one_mul] using f.property t x g

 theorem eqv_eval {α : Type*} {r : α → α → Prop} {v : α → ℂ}
    (h : ∀ a b, r a b → v a = v b) {a b : α} (hab : Relation.EqvGen r a b) :
    v a = v b := by
  induction hab with
  | rel a b hab => exact h a b hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ij => exact ih.trans ij
