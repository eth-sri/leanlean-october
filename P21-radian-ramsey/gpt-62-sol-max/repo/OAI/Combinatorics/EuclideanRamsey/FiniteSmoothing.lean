module

public import OAI.Combinatorics.EuclideanRamsey.LatticeDistributions

@[expose] public section

open Finset
open scoped Pointwise Topology
open Filter

namespace OAI.EuclideanRamsey.Discrete

noncomputable section

variable {k : Type} {d : ℕ}

lemma smooth_stencil [Fintype k] (U : Projection k d) (ν : LatticeRing k) (c : k → ℚ)
    (hc : ν-stencil c ∈ (augmentationIdeal : Ideal (LatticeRing k))^3)
    {η : ℝ} (hη : (∑ j, max (-(c j:ℝ)) 0 * ‖U (axis j)‖^2) < η) :
    ∃ b : LatticeRing k, mass b = 1 ∧ energy U (ν*b)⁻ < η := by
  let w : ℚ := 1 + ∑ j, |c j|
  let A (r : ℚ) (j : k) : LatticeRing k := r⁺ • sample (axis j) + r⁻ • 1
  let F (r : k → ℚ) : LatticeRing k := w⁻¹ • (1 + ∑ j, A (r j) j)
  have hw : 0 < w := by dsimp [w]; positivity
  have hA (r : ℚ) (j : k) : 0 ≤ A r j :=
    add_nonneg (smul_nonneg (posPart_nonneg _) (Probability.sample _).pos)
      (smul_nonneg (negPart_nonneg _) zero_le_one)
  have hF (r : k → ℚ) (hr : ∀ j, |r j| = |c j|) : Probability (F r) := by
    refine ⟨smul_nonneg (by positivity) (add_nonneg zero_le_one (sum_nonneg fun j _ => hA _ _)),
      fun f => by simp [F,A],?_⟩
    simpa [F,A,posPart_add_negPart,hr,mul_add,w] using inv_mul_cancel₀ hw.ne'
  let p := F c
  let q := F (-c)
  have hp : Probability p := hF _ fun _ => rfl
  have hq : Probability q := hF _ (by simp)
  let g := w • (p-q)
  have hg₀ : g = stencil c := by
    simp only [g,p,q,F,← smul_sub,smul_inv_smul₀ hw.ne',add_sub_add_left_eq_sub,← sum_sub_distrib,stencil]
    refine sum_congr rfl fun j _ => ?_
    simp only [A,Pi.neg_apply,posPart_neg,negPart_neg]
    conv_rhs => rw [← posPart_sub_negPart (c j)]
    module
  have hwq : (w:ℝ)*energy U q < η := by
    convert hη using 1
    simp [q,F,A,negPart_def,Rat.cast_max,Rat.smul_def,Rat.cast_ne_zero.mpr hw.ne']
  obtain ⟨J,K,hkern⟩ := smooth_of_cube (U:=U) (hg₀.symm ▸ hc)
  let S := energy U p + energy U q
  let E (x : ℝ) := (w:ℝ)*energy U q + (w:ℝ)*J*x + K*(J*x+S)*x
  have hlim :=
    (show Continuous E by unfold E; fun_prop).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  obtain ⟨t,ht,htE⟩ := ((eventually_gt_atTop (0:ℕ)).and
    (hlim.eventually_lt_const (by simpa [E] using hwq))).exists
  let L := t^2
  let N := t^5
  have hL : 0<L := pow_pos ht _
  have hN : 0<N := pow_pos ht _
  obtain ⟨b,hb,hbm,hbE,hrm,hrE⟩ := hkern L hL
  let r : LatticeRing k := |(ν-g)*b|
  have hr : 0 ≤ r := abs_nonneg _
  let A := geomKernel p q N
  have hprob (j : ℕ) : Probability (p^j*q^(N-1-j)) := (hp.pow j).mul (hq.pow _)
  have hA : Probability A := ⟨latticeAverage_pos _ fun j _ => (hprob j).pos,
    by intro f; simp [A,geomKernel,latticeAverage,fun j => (hprob j).center f],
    latticeAverage_mass hN fun j _ => (hprob j).mass_eq⟩
  let B := b*A
  let z := (ν-g)*B
  let C (x : LatticeRing k) := (w/(N:ℚ)) • (x^N*b)
  have hC {x : LatticeRing k} (hx : Probability x) : 0 ≤ C x :=
    smul_nonneg (by positivity) (mul_nonneg (hx.pow N).pos hb)
  have he : |z| ≤ A*r := by
    rw [mul_comm A r]
    simpa [mul_assoc] using abs_mul_le_of_nonneg ((ν-g)*b) hA.pos
  have hg : C p - C q = g*B := by
    dsimp [C]
    rw [← smul_sub,← sub_mul,div_eq_mul_inv,← smul_smul,← smul_mul_assoc,← geomKernel_sub]
    simp only [g,B,A,smul_mul_assoc]; congr 1; ac_rfl
  have hν : ν*B = C p-C q+z := by grind
  refine ⟨B,by simp [B,hbm,hA.mass_eq],lt_of_le_of_lt (energy_mono U (b:=C q+A*r) ?_) ?_⟩
  · refine sup_le ?_ (add_nonneg (hC hq) (mul_nonneg hA.pos hr))
    rw [hν,neg_add,neg_sub]
    exact add_le_add (sub_le_self _ (hC hp)) ((neg_le_abs _).trans he)
  apply lt_of_le_of_lt ?_ htE
  simp only [C,map_add,map_smul,energy_mul_center U (hq.pow N).center,
    energy_mul_center U hA.center,hq.energy_pow U,(hq.pow N).mass_eq,hbm,hA.mass_eq,
    Rat.smul_def,Rat.cast_div,Rat.cast_natCast,Rat.cast_one,one_mul]
  calc
    _ ≤ ((w:ℝ)/N)*(J*(L:ℝ)^2+(N:ℝ)*energy U q) + (J*K/L+(K/(L:ℝ)^3)*(N*S)) := by
      have hK := (by exact_mod_cast mass_nonneg hr : (0:ℝ) ≤ mass r).trans hrm
      have haE : energy U A ≤ N*S := by
        apply latticeAverage_le hN
        intro j hj
        rw [(hp.pow j).energy_mul U (hq.pow _), hp.energy_pow U, hq.energy_pow U, mul_add]
        gcongr
        · exact energy_pos U hp.pos
        · exact_mod_cast (mem_range.mp hj).le
        · exact energy_pos U hq.pos
        · omega
      have ha₀ := energy_pos U hA.pos
      gcongr
    _ = _ := by
      simp only [Function.comp_apply,E,L,N,Nat.cast_pow]
      field_simp
      ring

end
end OAI.EuclideanRamsey.Discrete
