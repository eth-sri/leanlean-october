/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import FixedPointTheorems.brouwer

public section

open Set Topology unitInterval

namespace PottsDiscontinuity.FK.Curves

noncomputable section

section
variable (x : ℝ)
def unitClamp  : ℝ := max 0 (min 1 x)

theorem unitClamp_mem  : unitClamp x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · apply max_le
    · norm_num
    simp

theorem unitClamp_eq_zero_iff  : unitClamp x = 0 ↔ x ≤ 0 := by
  simp [unitClamp]

theorem unitClamp_eq_one_iff  : unitClamp x = 1 ↔ 1 ≤ x := by
  grind [unitClamp_eq_zero_iff, unitClamp]
end

theorem unitClamp_eq_self_of_mem (x y : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (h : unitClamp y = x) : y = x := by
  grind [unitClamp, unitClamp_eq_zero_iff, unitClamp_eq_one_iff]


theorem continuous_unitClamp : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

theorem unitClamp_fixed_zero_of_signs (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h : unitClamp (x - y) = x)
    (hzero : x = 0 → y ≤ 0) (hone : x = 1 → 0 ≤ y) : y = 0 := by
  by_cases hxz : x = 0
  · subst x
    have hneg := (unitClamp_eq_zero_iff _).mp h
    grind
  by_cases hxo : x = 1
  · grind [unitClamp_eq_one_iff]
  · have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      grind
    grind [unitClamp_eq_self_of_mem]

/-- Two continuous paths joining opposite sides of a closed rectangle intersect.
No simplicity, genericity, or nondegeneracy of the rectangle is required. -/
theorem pathRectangle_crossing_intersection
    {a b : ℝ × ℝ} {p₀ p₁ q₀ q₁ : ℝ × ℝ}
    (P : Path p₀ p₁) (Q : Path q₀ q₁)
    (hPbox : ∀ t, a.1 ≤ (P t).1 ∧ (P t).1 ≤ b.1 ∧
      a.2 ≤ (P t).2 ∧ (P t).2 ≤ b.2)
    (hQbox : ∀ t, a.1 ≤ (Q t).1 ∧ (Q t).1 ≤ b.1 ∧
      a.2 ≤ (Q t).2 ∧ (Q t).2 ≤ b.2)
    (hPleft : (P 0).1 = a.1) (hPright : (P 1).1 = b.1)
    (hQbottom : (Q 0).2 = a.2) (hQtop : (Q 1).2 = b.2) :
    ∃ s t : I, P s = Q t := by
  let K : Set (ℝ × ℝ) := Set.Icc (0, 0) (1, 1)
  let fstI : C(K, I) := ⟨fun z => ⟨z.1.1, by
      have hz := z.property
      exact ⟨hz.1.1, hz.2.1⟩⟩,
    Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) (by
      intro z
      have hz := z.property
      exact ⟨hz.1.1, hz.2.1⟩)⟩
  let sndI : C(K, I) := ⟨fun z => ⟨z.1.2, by
      have hz := z.property
      exact ⟨hz.1.2, hz.2.2⟩⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) (by
      intro z
      have hz := z.property
      exact ⟨hz.1.2, hz.2.2⟩)⟩
  let ι := fstI.prodMk sndI
  let f₁ : C(K, ℝ) := ⟨fun z => (P (ι z).1).1 - (Q (ι z).2).1, by fun_prop⟩
  let f₂ : C(K, ℝ) := ⟨fun z => (Q (ι z).2).2 - (P (ι z).1).2, by fun_prop⟩
  have hclamp := continuous_unitClamp
  let T : C(K, K) :=
    ⟨fun z => ⟨(unitClamp (z.1.1 - f₁ z), unitClamp (z.1.2 - f₂ z)), by
      exact ⟨⟨(unitClamp_mem _).1, (unitClamp_mem _).1⟩,
        ⟨(unitClamp_mem _).2, (unitClamp_mem _).2⟩⟩⟩,
      by fun_prop⟩
  obtain ⟨z, hzfix⟩ := brouwer_fixed_point K (convex_Icc (0, 0) (1, 1))
    isCompact_Icc ⟨(0, 0), by norm_num [K]⟩ T
  have hzcoord :=
    congrArg Subtype.val hzfix
  have hf₁ : f₁ z = 0 := by
    apply unitClamp_fixed_zero_of_signs z.1.1 (f₁ z) (ι z).1.property
      (congrArg Prod.fst hzcoord)
    · intro hs
      have hs' : (ι z).1 = 0 := Subtype.ext hs
      change (P (ι z).1).1 - (Q (ι z).2).1 ≤ 0
      have hq := (hQbox (ι z).2).1
      simp_all
    · intro hs
      have hs' : (ι z).1 = 1 := Subtype.ext hs
      change 0 ≤ (P (ι z).1).1 - (Q (ι z).2).1
      have hq := (hQbox (ι z).2).2.1
      simp_all
  have hf₂ : f₂ z = 0 := by
    apply unitClamp_fixed_zero_of_signs z.1.2 (f₂ z) (ι z).2.property
      (congrArg Prod.snd hzcoord)
    · intro ht
      have ht' : (ι z).2 = 0 := Subtype.ext ht
      change (Q (ι z).2).2 - (P (ι z).1).2 ≤ 0
      have hq0 : Q (ι z).2 = q₀ := by simp [ht']
      rw [hq0]
      have hp := (hPbox (ι z).1).2.2.1
      have hsrc : q₀.2 = a.2 := by
        have hpath : (Q 0).2 = q₀.2 := by simp
        linarith
      linarith
    · intro ht
      have ht' : (ι z).2 = 1 := Subtype.ext ht
      change 0 ≤ (Q (ι z).2).2 - (P (ι z).1).2
      have hq1 : Q (ι z).2 = q₁ := by simp [ht']
      rw [hq1]
      have hp := (hPbox (ι z).1).2.2.2
      have htarget : q₁.2 = b.2 := by
        have hpath : (Q 1).2 = q₁.2 := by simp
        linarith
      linarith
  refine ⟨(ι z).1, (ι z).2, ?_⟩
  apply Prod.ext
  · have := congrArg (fun x : ℝ => x) hf₁
    dsimp [f₁] at this
    linarith
  · have := congrArg (fun x : ℝ => x) hf₂
    dsimp [f₂] at this
    linarith

end

end PottsDiscontinuity.FK.Curves
