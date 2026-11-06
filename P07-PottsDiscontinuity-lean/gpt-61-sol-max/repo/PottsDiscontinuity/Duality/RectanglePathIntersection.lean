/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import FixedPointTheorems.brouwer

@[expose] public section

open Set Topology unitInterval

namespace PottsDiscontinuity.FK.Curves

noncomputable section

def unitClamp (x : ℝ)  := max 0 (min 1 x)

lemma unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (0 : ℝ) 1 := by
  grind +locals








lemma continuous_unitClamp : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

lemma unitClamp_fixed_zero_of_signs (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h : unitClamp (x - y) = x)
    (hzero : x = 0 → y ≤ 0) (hone : x = 1 → 0 ≤ y) : y = 0 := by
  grind +locals

/-- Two continuous paths joining opposite sides of a closed rectangle intersect.
No simplicity, genericity, or nondegeneracy of the rectangle is required. -/
theorem pathRectangle_crossing_intersection
    {a b p₀ p₁ q₀ q₁ : ℝ × ℝ}
    (P : Path p₀ p₁) (Q : Path q₀ q₁)
    (hPbox : ∀ t, a.1 ≤ (P t).1 ∧ (P t).1 ≤ b.1 ∧
      a.2 ≤ (P t).2 ∧ (P t).2 ≤ b.2)
    (hQbox : ∀ t, a.1 ≤ (Q t).1 ∧ (Q t).1 ≤ b.1 ∧
      a.2 ≤ (Q t).2 ∧ (Q t).2 ≤ b.2)
    (hPleft : (P 0).1 = a.1) (hPright : (P 1).1 = b.1)
    (hQbottom : (Q 0).2 = a.2) (hQtop : (Q 1).2 = b.2) :
    ∃ s t : I, P s = Q t := by
  let K : Set (ℝ × ℝ) := Set.Icc (0, 0) (1, 1)
  let fstI : C(K, I) := ⟨fun z => ⟨z.1.1, have hz := z.property;
                                          ⟨hz.left.left, hz.right.left⟩⟩,
    Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val)  fun z =>
                                                                          have hz := z.property;
                                                                          ⟨hz.left.left, hz.right.left⟩ ⟩
  let sndI : C(K, I) := ⟨fun z => ⟨z.1.2, have hz := z.property;
                                          ⟨hz.left.right, hz.right.right⟩⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val)  fun z =>
                                                                          have hz := z.property;
                                                                          ⟨hz.left.right, hz.right.right⟩ ⟩
  let ι  := fstI.prodMk sndI
  let f₁ : C(K, ℝ) := ⟨fun z => (P (ι z).1).1 - (Q (ι z).2).1, by fun_prop⟩
  let f₂ : C(K, ℝ) := ⟨fun z => (Q (ι z).2).2 - (P (ι z).1).2, by fun_prop⟩
  have hclamp  := continuous_unitClamp
  
  obtain ⟨z, hzfix⟩ := brouwer_fixed_point K (convex_Icc (0, 0) (1, 1))
    isCompact_Icc ⟨(0, 0), by norm_num [K]⟩  ⟨fun z => ⟨(unitClamp (z.1.1 - f₁ z), unitClamp (z.1.2 - f₂ z)), ⟨⟨(unitClamp_mem _).1, (unitClamp_mem _).1⟩,
                                                                                                          ⟨(unitClamp_mem _).2, (unitClamp_mem _).2⟩⟩⟩,
                                                 by fun_prop⟩ 
  
  
  
  refine ⟨(ι z).1, (ι z).2, ?_⟩
  apply Prod.ext
  · have := congrArg (fun x  => x) (by
                                      apply unitClamp_fixed_zero_of_signs z.1.1 (f₁ z) (ι z).1.property
                                        (congrArg Prod.fst (congrArg Subtype.val hzfix))
                                      · intro hs
                                        have hs' : (ι z).1 = 0 := Subtype.ext hs
                                        change (P (ι z).1).1 - (Q (ι z).2).1 ≤ 0
                                        have hp0 : P (ι z).1 = p₀ := by simp [hs']
                                        rw [hp0]
                                        have hq := (hQbox (ι z).2).1
                                        have hsrc : p₀.1 = a.1 := by
                                          simp_all
                                        linarith
                                      · intro hs
                                        have hs' : (ι z).1 = 1 := Subtype.ext hs
                                        change 0 ≤ (P (ι z).1).1 - (Q (ι z).2).1
                                        have hp1 : P (ι z).1 = p₁ := by simp [hs']
                                        rw [hp1]
                                        have hq := (hQbox (ι z).2).2.1
                                        have htarget : p₁.1 = b.1 := by
                                          simp_all
                                        linarith)
    
    exact sub_eq_zero.mp this
  · have := congrArg (fun x  => x) (by
                                      apply unitClamp_fixed_zero_of_signs z.1.2 (f₂ z) (ι z).2.property
                                        (congrArg Prod.snd (congrArg Subtype.val hzfix))
                                      · intro ht
                                        have ht' : (ι z).2 = 0 := Subtype.ext ht
                                        change (Q (ι z).2).2 - (P (ι z).1).2 ≤ 0
                                        have hq0 : Q (ι z).2 = q₀ := by simp [ht']
                                        rw [hq0]
                                        have hp := (hPbox (ι z).1).2.2.1
                                        have hsrc : q₀.2 = a.2 := by
                                          grind +locals
                                        linarith
                                      · intro ht
                                        have ht' : (ι z).2 = 1 := Subtype.ext ht
                                        change 0 ≤ (Q (ι z).2).2 - (P (ι z).1).2
                                        have hq1 : Q (ι z).2 = q₁ := by simp [ht']
                                        rw [hq1]
                                        have hp := (hPbox (ι z).1).2.2.2
                                        have htarget : q₁.2 = b.2 := by
                                          grind +locals
                                        linarith)
    
    exact (sub_eq_zero.mp this).symm

end

end PottsDiscontinuity.FK.Curves
