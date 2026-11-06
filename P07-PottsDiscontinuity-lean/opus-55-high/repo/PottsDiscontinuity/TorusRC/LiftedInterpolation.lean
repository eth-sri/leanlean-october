module

public import Mathlib.Analysis.Convex.Segment
public import FixedPointTheorems.brouwer
public import Mathlib

/-! # Straight-segment interpolation of lifted walks -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Set

noncomputable section

/-- Coordinate embedding of an integer cell in the real plane. -/
def cellEmbed (z : ℤ × ℤ) : ℝ × ℝ := (z.1,z.2)

theorem cellEmbed_injective : Function.Injective cellEmbed := by
  intro u v h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    change (u.1:ℝ) = (v.1:ℝ) at hx
    simp_all
  · have hy := congrArg Prod.snd h
    change (u.2:ℝ) = (v.2:ℝ) at hy
    simp_all

/-- Polygonal interpolation retains every edge and every repeated visit. -/
def polygonWalkPath {V : Type*} {G : SimpleGraph V} (f : V → ℝ × ℝ) :
    {u v : V} → G.Walk u v → Path (f u) (f v)
  | _,_,.nil => Path.refl _
  | u,_,.cons (v := v) _ p => (Path.segment (f u) (f v)).trans (polygonWalkPath f p)

section
variable {V : Type*} {G : SimpleGraph V} (f : V → ℝ × ℝ) {u v : V} (w : G.Walk u v)
include G
theorem polygonWalkPath_range  :
    Set.range (polygonWalkPath f w) ⊆
      {z | ∃ x y : V, x ∈ w.support ∧ y ∈ w.support ∧
        (x = y ∨ G.Adj x y) ∧ z ∈ segment ℝ (f x) (f y)} := by
  induction w with
  | nil =>
    rintro z ⟨t,rfl⟩
    aesop
  | @cons u v z huv p ih =>
    intro x hx
    change x ∈ Set.range ((Path.segment (f u) (f v)).trans (polygonWalkPath f p)) at hx
    rw [Path.trans_range] at hx
    rcases hx with hx | hx
    · exact ⟨u,v,by simp,by simp,Or.inr huv,by simp_all⟩
    · obtain ⟨a,b,ha,hb,hab,hseg⟩ := ih hx
      exact ⟨a,b,by simp_all,by simp_all,hab,hseg⟩

/-- Coordinatewise bounds on all visited vertices bound the entire polygonal
interpolation, including its edge interiors. -/
theorem polygonWalkPath_mem_Icc (a b : ℝ × ℝ)
    (hbox : ∀ z ∈ w.support, f z ∈ Set.Icc a b) :
    ∀ t, polygonWalkPath f w t ∈ Set.Icc a b := by
  intro t
  obtain ⟨x,y,hx,hy,_,hseg⟩ := polygonWalkPath_range f w ⟨t,rfl⟩
  exact (convex_Icc a b).segment_subset (hbox x hx) (hbox y hy) hseg
end

/-- An integer point on a unit diagonal segment must be an endpoint. -/
theorem integer_mem_diagonal_segment {p q z : ℤ × ℤ}
    (hx : |p.1-q.1| = 1) (_hy : |p.2-q.2| = 1)
    (hz : cellEmbed z ∈ segment ℝ (cellEmbed p) (cellEmbed q)) : z = p ∨ z = q := by
  rw [segment_eq_image] at hz
  obtain ⟨t,⟨ht0,ht1⟩,htz⟩ := hz
  have hxeq := congrArg Prod.fst htz
  change (1-t)*(p.1:ℝ)+t*(q.1:ℝ) = (z.1:ℝ) at hxeq
  have hxne : p.1 ≠ q.1 := by aesop
  have hdx : (q.1:ℝ)-(p.1:ℝ) ≠ 0 := sub_ne_zero.mpr (by aesop)
  have hpmin : (0:ℝ) ≤ (p.1:ℝ)-(min p.1 q.1:ℤ) := by simp
  have hqmin : (0:ℝ) ≤ (q.1:ℝ)-(min p.1 q.1:ℤ) := by simp
  have hpmax : (0:ℝ) ≤ (max p.1 q.1:ℤ)-(p.1:ℝ) := by simp
  have hqmax : (0:ℝ) ≤ (max p.1 q.1:ℤ)-(q.1:ℝ) := by simp
  have hzlo : (min p.1 q.1:ℤ) ≤ z.1 := by
    have h : ((min p.1 q.1:ℤ):ℝ) ≤ z.1 := by
      nlinarith
    simp_all
  have hzhi : z.1 ≤ (max p.1 q.1:ℤ) := by
    have h : (z.1:ℝ) ≤ (max p.1 q.1:ℤ) := by
      nlinarith
    simp_all
  have hcoord : z.1 = p.1 ∨ z.1 = q.1 := by
    have h := abs_le.mp (le_of_eq hx)
    omega
  rcases hcoord with heq | heq
  · have heqR : (z.1:ℝ) = p.1 := by simp_all
    have hprod : t*((q.1:ℝ)-p.1) = 0 := by nlinarith
    have ht : t = 0 := by simp_all
    left
    apply cellEmbed_injective
    simp_all
  · have heqR : (z.1:ℝ) = q.1 := by simp_all
    have hprod : (1-t)*((q.1:ℝ)-p.1) = 0 := by nlinarith
    have ht : t = 1 := by have h := (mul_eq_zero.mp hprod).resolve_right hdx; linarith
    right
    apply cellEmbed_injective
    simp_all

end

end PottsDiscontinuity.TorusRC
