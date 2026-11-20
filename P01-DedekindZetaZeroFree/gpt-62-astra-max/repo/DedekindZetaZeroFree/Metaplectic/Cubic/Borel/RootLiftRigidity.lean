module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGL2BorelAndFlagSpace

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.FiniteCentralBorel

section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem finite_character_trivial
    {C : Type*} [CommGroup C] [Finite C]
    (χ : Multiplicative V →* C) (x : V) :
    χ (Multiplicative.ofAdd x) = 1 := by
  letI := Fintype.ofFinite C
  let m := Fintype.card C
  have hx : m • ((m : ℚ)⁻¹ • x) = x := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by
      exact_mod_cast Fintype.card_ne_zero), one_smul]
  rw [← hx, ofAdd_nsmul, map_pow]
  exact pow_card_eq_one

private lemma correction_trivial
    {G H : Type*} [Group G] [Group H] (π : G →* H) [Finite π.ker]
    (hc : π.ker ≤ Subgroup.center G)
    (f g : Multiplicative V →* G) (hfg : ∀ x, π (f x) = π (g x)) (x : Multiplicative V) :
    f x = g x := by
  letI : CommGroup π.ker :=
    { (inferInstance : Group π.ker) with
      mul_comm := by
        intro a b
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hc a.property) b.val).symm }
  have hker (y : Multiplicative V) : f y * (g y)⁻¹ ∈ π.ker := by
    simp [hfg y]
  let d : Multiplicative V →* π.ker :=
    { toFun := fun y => ⟨f y * (g y)⁻¹, hker y⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [map_mul, mul_inv_rev]
        calc
          _ = f a * (f b * (g b)⁻¹) * (g a)⁻¹ := by group
          _ = f a * (g a)⁻¹ * (f b * (g b)⁻¹) := by rw [mul_assoc, ← (Subgroup.mem_center_iff.mp (hc (hker b)) (g a)⁻¹), ← mul_assoc]}
  exact mul_inv_eq_one.mp (congrArg Subtype.val (finite_character_trivial d (Multiplicative.toAdd x)))

end

open KPRankOneInductionRaw
open IsDedekindDomain NumberField
open scoped Matrix

variable (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))

private lemma ordinary_borel_conjugates (b : upperBorel F v) (x : LocalField F v) :
    b.val * ordinaryUpperRootHom F v (Multiplicative.ofAdd x) * b.val⁻¹ =
      ordinaryUpperRootHom F v (Multiplicative.ofAdd ((borelRatio F v b : LocalField F v) * x)) := by
  obtain ⟨A, hA, hu⟩ := b.property
  have hne : A 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [Matrix.det_fin_two] at hd
    simpa [hu] using (mul_ne_zero_iff.mp (by simpa [hu] using hd : A 0 0 * A 1 1 ≠ 0)).2
  have heq : A * upperRootMatrix F v x =
      upperRootMatrix F v ((borelRatio F v b : LocalField F v) * x) * A := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    change (A * !![1, x; 0, 1]) i j =
      (!![1, (borelRatio F v b : LocalField F v) * x; 0, 1] *
        A) i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hu]
    rw [borelRatio_eq F v b A hA hu]
    field_simp
    <;> ring
  change b.val * upperRootElement F v x * b.val⁻¹ = upperRootElement F v _
  rw [← hA]
  change Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk (upperRootMatrix F v x) *
    (Matrix.ProjGenLinGroup.mk A)⁻¹ = Matrix.ProjGenLinGroup.mk (upperRootMatrix F v _)
  have hp := congrArg (Matrix.ProjGenLinGroup.mk) heq
  simp only [map_mul, upperRootElement] at hp
  rw [hp, mul_assoc, mul_inv_cancel, mul_one]
  rfl

theorem torusLift_conjugates_root
    {G : Type*} [Group G] (π : G →* PGL2 F v) [Finite π.ker]
    (hcentral : π.ker ≤ Subgroup.center G)
    (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (t : G) (ht : π t ∈ diagonalTorus F v)
    (htB : π t ∈ upperBorel F v) (x : LocalField F v) :
    t * n (Multiplicative.ofAdd x) * t⁻¹ =
      n (Multiplicative.ofAdd
        ((borelRatio F v ⟨π t, htB⟩ : LocalField F v) * x)) := by
  let r := (borelRatio F v ⟨π t, htB⟩ : LocalField F v)
  let f := (MulAut.conj t).toMonoidHom.comp n
  let g :=
    n.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft r))
  have hfg (y : Multiplicative (LocalField F v)) : π (f y) = π (g y) := by
    change π (t * n y * t⁻¹) = π (n (Multiplicative.ofAdd (r * Multiplicative.toAdd y)))
    simp only [map_mul, map_inv, hn]
    exact ordinary_borel_conjugates F v ⟨π t, htB⟩ (Multiplicative.toAdd y)
  exact correction_trivial π hcentral f g hfg (Multiplicative.ofAdd x)

end DedekindZetaZeroFree.FiniteCentralBorel

end
