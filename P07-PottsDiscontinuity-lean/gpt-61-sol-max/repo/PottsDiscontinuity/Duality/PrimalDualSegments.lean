/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.WholePlaneDualGraph
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

noncomputable section

/-- The midpoint of a normalized bond belongs to its actual segment. -/
theorem LatticeBond.midpoint_mem_segment (e : LatticeBond) (δ : PositiveMesh) :
    e.midpoint δ ∈ segment ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) := by
  rw [segment_eq_image]
  refine ⟨ 1 / 2 , by norm_num, ?_⟩
  
  norm_num
  dsimp [LatticeBond.midpoint]
  ring

/-- The actual center of the unit face whose lower-left lattice corner is `u`. -/
def dualFaceCenter (δ : PositiveMesh) (u : LatticeVertex) : ℂ :=
  latticeEmbed δ u + (δ.val : ℂ) * (1 + Complex.I) / 2

/-- The complete geometric segment of an original primal bond. -/
def primalBondSegment (δ : PositiveMesh) (b : LatticeBond)  :=
  segment ℝ (latticeEmbed δ b.source) (latticeEmbed δ b.target)

/-- The complete geometric segment joining the centers at the source and target
face bases of the normalized dual bond `d`. -/
def dualBondSegment (δ : PositiveMesh) (d : LatticeBond)  :=
  segment ℝ (dualFaceCenter δ d.source) (dualFaceCenter δ d.target)

section

variable (δ : PositiveMesh)
include δ

private theorem segment_coordinate_parameter  {z a b : ℂ}
    (hz : z ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.re / δ.val = (1 - t) * (a.re / δ.val) + t * (b.re / δ.val) ∧
      z.im / δ.val = (1 - t) * (a.im / δ.val) + t * (b.im / δ.val) := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hz
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · have hre := congrArg Complex.re htz
    simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
    grind
  · have him := congrArg Complex.im htz
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at him
    grind

section

variable (u : LatticeVertex)


private theorem latticeEmbed_re_div   :
    (latticeEmbed δ u).re / δ.val = (u.1 : ℝ) := by
  rw [latticeEmbed_re, div_eq_iff δ.property.ne']
  ring

private theorem latticeEmbed_im_div   :
    (latticeEmbed δ u).im / δ.val = (u.2 : ℝ) := by
  rw [latticeEmbed_im, div_eq_iff δ.property.ne']
  ring

private theorem dualFaceCenter_re_div   :
    (dualFaceCenter δ u).re / δ.val = (u.1 : ℝ) + 1 / 2 := by
  simp [dualFaceCenter]
  field_simp [ne_of_gt δ.property]

private theorem dualFaceCenter_im_div   :
    (dualFaceCenter δ u).im / δ.val = (u.2 : ℝ) + 1 / 2 := by
  simp [dualFaceCenter]
  field_simp [ne_of_gt δ.property]

end

section

variable (x y : ℤ) {z : ℂ}


private theorem primal_horizontal_coords  
    (hz : z ∈ primalBondSegment δ ⟨(x, y), .horizontal⟩) :
    (x : ℝ) ≤ z.re / δ.val ∧ z.re / δ.val ≤ (x : ℝ) + 1 ∧
      z.im / δ.val = (y : ℝ) := by
  
  rcases  segment_coordinate_parameter δ hz  with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val = (1 - t) *  x  + t *  (x + 1 : ℤ)  := by
    simpa only [LatticeBond.source, LatticeBond.target, latticeEmbed_re_div] using hre
  have him' : z.im / δ.val = (1 - t) *  y  + t *  y  := by
    grind [LatticeBond.source, LatticeBond.target, latticeEmbed_im_div]
  grind

private theorem primal_vertical_coords  
    (hz : z ∈ primalBondSegment δ ⟨(x, y), .vertical⟩) :
    z.re / δ.val = (x : ℝ) ∧ (y : ℝ) ≤ z.im / δ.val ∧
      z.im / δ.val ≤ (y : ℝ) + 1 := by
  
  rcases  segment_coordinate_parameter δ hz  with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val = (1 - t) *  x  + t *  x  := by
    grind [LatticeBond.source, LatticeBond.target, latticeEmbed_re_div]
  have him' : z.im / δ.val = (1 - t) *  y  + t *  (y + 1 : ℤ)  := by
    simpa only [LatticeBond.source, LatticeBond.target, latticeEmbed_im_div] using him
  grind

private theorem dual_horizontal_coords  
    (hz : z ∈ dualBondSegment δ ⟨(x, y), .horizontal⟩) :
    (x : ℝ) + 1 / 2 ≤ z.re / δ.val ∧
      z.re / δ.val ≤ (x : ℝ) + 1 + 1 / 2 ∧
      z.im / δ.val = (y : ℝ) + 1 / 2 := by
  
  rcases  segment_coordinate_parameter δ hz  with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val =
      (1 - t) * ( x  + 1 / 2) + t * (  x + 1   + 1 / 2) := by
    simp_all [LatticeBond.source, LatticeBond.target, dualFaceCenter_re_div]
  have him' : z.im / δ.val =
      (1 - t) * ( y  + 1 / 2) + t * ( y  + 1 / 2) := by
    simp_all [LatticeBond.source, LatticeBond.target, dualFaceCenter_im_div]
  grind

private theorem dual_vertical_coords  
    (hz : z ∈ dualBondSegment δ ⟨(x, y), .vertical⟩) :
    z.re / δ.val = (x : ℝ) + 1 / 2 ∧
      (y : ℝ) + 1 / 2 ≤ z.im / δ.val ∧
      z.im / δ.val ≤ (y : ℝ) + 1 + 1 / 2 := by
  
  rcases  segment_coordinate_parameter δ hz  with ⟨t, ht0, ht1, hre, him⟩
  have hre' : z.re / δ.val =
      (1 - t) * ( x  + 1 / 2) + t * ( x  + 1 / 2) := by
    simp_all [LatticeBond.source, LatticeBond.target, dualFaceCenter_re_div]
  have him' : z.im / δ.val =
      (1 - t) * ( y  + 1 / 2) + t * (  y + 1   + 1 / 2) := by
    simp_all [LatticeBond.source, LatticeBond.target, dualFaceCenter_im_div]
  grind

end

end

private theorem int_cast_half_impossible (a b : ℤ) (h : (a : ℝ) = (b : ℝ) + 1 / 2) : False := by
  have hh :  2  * a = 2 * b + 1 := by
    exact_mod_cast  show  2  *  a  = 2 * (b : ℝ) + 1 by nlinarith 
  omega

private theorem crossing_of_intersection (δ : PositiveMesh) (b d : LatticeBond)
    (h : (primalBondSegment δ b ∩ dualBondSegment δ d).Nonempty) :
    d = dualBondOfPrimal b := by
  rcases h with ⟨z, hp, hd⟩
  rcases b with ⟨⟨x,y⟩, ab⟩
  rcases d with ⟨⟨u,v⟩, ad⟩
  cases ab <;> cases ad
  · 
    
    exact False.elim (int_cast_half_impossible y v ((primal_horizontal_coords δ x y hp).2.2.symm.trans (dual_horizontal_coords δ u v hd).2.2))
  · 
    
    rcases  primal_horizontal_coords δ x y hp  with ⟨px₁, px₂, py⟩
    rcases  dual_vertical_coords δ u v hd  with ⟨qx, qy₁, qy₂⟩
    have hu₁ :  u  < (x : ℝ) + 1 := by linarith
    have hu₂ :  x  - 1 < (u : ℝ) := by linarith
    have hv₁ :  v  < (y : ℝ) := by linarith
    have hv₂ :  y  < (v : ℝ) + 2 := by linarith
    have hu₁' : u < x + 1 := by exact_mod_cast hu₁
    have hu₂' : x - 1 < u := by exact_mod_cast hu₂
    have hv₁' : v < y := by exact_mod_cast hv₁
    have hv₂' : y < v + 2 := by exact_mod_cast hv₂
    have hu : u = x := by omega
    have hv : v = y - 1 := by omega
    subst u; subst v
    simp [dualBondOfPrimal]
  · 
    
    rcases  primal_vertical_coords δ x y hp  with ⟨px, py₁, py₂⟩
    rcases  dual_horizontal_coords δ u v hd  with ⟨qx₁, qx₂, qy⟩
    have hu₁ :  u  < (x : ℝ) := by linarith
    have hu₂ :  x  < (u : ℝ) + 2 := by linarith
    have hv₁ :  v  < (y : ℝ) + 1 := by linarith
    have hv₂ :  y  - 1 < (v : ℝ) := by linarith
    have hu₁' : u < x := by exact_mod_cast hu₁
    have hu₂' : x < u + 2 := by exact_mod_cast hu₂
    have hv₁' : v < y + 1 := by exact_mod_cast hv₁
    have hv₂' : y - 1 < v := by exact_mod_cast hv₂
    have hu : u = x - 1 := by omega
    have hv : v = y := by omega
    subst u; subst v
    simp [dualBondOfPrimal]
  · 
    
    exact False.elim (int_cast_half_impossible x u ((primal_vertical_coords δ x y hp).1.symm.trans (dual_vertical_coords δ u v hd).1))

/-- A primal unit segment and a dual face-center segment meet exactly when
these normalized bonds cross. -/
theorem primalDualSegments_intersect_iff (δ : PositiveMesh) (b d : LatticeBond) :
    (primalBondSegment δ b ∩ dualBondSegment δ d).Nonempty ↔
      d = dualBondOfPrimal b := by
  constructor
  · exact crossing_of_intersection δ b d
  · intro h
    subst d
    refine ⟨b.midpoint δ, ?_, ?_⟩
    · exact b.midpoint_mem_segment δ
    · have hm : b.midpoint δ =
          midpoint ℝ (dualFaceCenter δ (dualBondOfPrimal b).source)
            (dualFaceCenter δ (dualBondOfPrimal b).target) := by
        rw [midpoint_eq_smul_add]
        rcases b with ⟨⟨x,y⟩, ax⟩
        cases ax <;> apply Complex.ext <;>
          simp [LatticeBond.midpoint, dualBondOfPrimal, LatticeBond.source,
            LatticeBond.target, dualFaceCenter, latticeEmbed,
            Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
      rw [dualBondSegment, hm]
      exact  _root_.midpoint_mem_segment (𝕜 := ℝ) (E := ℂ) _ _ 

/-- No actual primal lattice vertex lies on any dual face-center bond. -/
theorem latticeVertex_not_mem_dualBondSegment (δ : PositiveMesh)
    (u : LatticeVertex) (d : LatticeBond) :
    latticeEmbed δ u ∉ dualBondSegment δ d := by
  rcases u with ⟨x,y⟩
  rcases d with ⟨⟨a,b⟩, ax⟩
  intro hz
  cases ax
  · 
    
    exact False.elim (int_cast_half_impossible y b (by
                                                      simpa only [latticeEmbed_im_div] using (dual_horizontal_coords δ a b hz).2.2))
  · 
    
    exact False.elim (int_cast_half_impossible x a (by
                                                      simpa only [latticeEmbed_re_div] using (dual_vertical_coords δ a b hz).1))

end
end PottsDiscontinuity.FK.Medial
