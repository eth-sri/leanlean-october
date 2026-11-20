/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Congruence

public section

namespace OAI.EuclideanRamsey

private theorem floor_gap (x y : Fin 9 → ℝ) (hx : ∑ i, x i = 10) (hy : ∑ i, y i = 0)
    (h : ∀ i, (⌊x i⌋ : ZMod 20) = ⌊y i⌋) : False := by
  let F (v : Fin 9 → ℝ) := ∑ i, ⌊v i⌋
  have bound (v : Fin 9 → ℝ) : (F v : ℝ) ≤ ∑ i, v i ∧ ∑ i, v i ≤ F v + 9 := by
    simp only [F,Int.cast_sum]
    exact ⟨Finset.sum_le_sum fun i _ => Int.floor_le _,by
      simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (Int.lt_floor_add_one (v i)).le)⟩
  have hx' := bound x; have hy' := bound y
  simp only [hx,hy] at hx' hy'
  norm_cast at hx' hy'
  have dvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (F y) (F x) 20).mp (by simp [F,h])
  omega

/-- A sum of one-coordinate potentials recovering a squared chord on affine
images yields a finite coloring with no monochromatic congruent copy. -/
theorem obstruct {d} {a : Fin 9 → Space d} (hne : a 1 ≠ a 0) (f : Fin 9 → ℝ → ℝ)
    (H : ∀ b : Fin 9 → ℝ, AffineRow a b → ∑ i, f i (b i) = (b 1-b 0)^2) : ¬ Ramsey a := by
  intro hR
  let Colors := Fin 9 → ZMod 20
  obtain ⟨D,_,hD⟩ := hR (Fintype.card Colors) (by aesop)
  let h (i : Fin 9) (b : Space D) := 10/(dist (a 1) (a 0))^2*∑ j, f i (b j)
  let c (b : Space D) (i : Fin 9) : ZMod 20 := ⌊h i b⌋
  obtain ⟨b,hb,k,hk⟩ := hD fun x => Fintype.equivFin Colors (c x)
  have sumH (v : Fin 9 → Space D) (hv : ∀ j, AffineRow a (fun i => v i j)) :
      ∑ i, h i (v i) = 10/(dist (a 1) (a 0))^2 * dist (v 1) (v 0)^2 := by
    simp [h,←Finset.mul_sum]; rw [Finset.sum_comm]
    simp [fun j => H _ (hv j), dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  apply floor_gap (fun i => h i (b i)) (fun i => h i (b 0))
  · rw [sumH _ (column hb),hb]; simp [*]
  · simpa using sumH (fun _ => b 0) (fun j => ⟨b 0 j,0,by simp⟩)
  · intro i
    exact congrFun ((Fintype.equivFin Colors).injective ((hk i).trans (hk 0).symm)) i

end OAI.EuclideanRamsey
