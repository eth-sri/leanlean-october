module
public import GS.Topology.ConeRetract
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
@[expose] public section

/-! Add the squares of the complex columns. On the rank cone this detects
zero, since all columns are real multiples of one vector. The section is the
symmetric two-column lift of a doubled angle, extended over the origin. -/
noncomputable section
open Matrix Filter GS.Local
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace GS.RankLocus
variable {d : ℕ}
def angle (X : Locus 2 (Fin d)) : ℂ := ∑ j, (⟨X.val 0 j,X.val 1 j⟩ : ℂ)^2
lemma angle_outer (u : Fin 2 → ℝ) (v : Fin d → ℝ) : angle (outer u v) = (⟨u 0,u 1⟩ : ℂ)^2 * ((∑ j,v j^2 : ℝ):ℂ) := by
  simp only [Complex.ofReal_sum,Complex.ofReal_pow,Finset.mul_sum,angle,← mul_pow]
  apply Finset.sum_congr rfl; intro j _
  apply congrArg (·^2); apply Complex.ext <;> simp [outer,vecMulVec]
lemma angle_zero (X : Locus 2 (Fin d)) : angle X = 0 ↔ X = tip := by
  constructor
  · obtain ⟨u,v,rfl⟩ := factors X
    rw [angle_outer]; rintro h; rcases mul_eq_zero.mp h with h | h
    · have hz := eq_zero_of_pow_eq_zero h; have hu : u = 0 := by ext i; fin_cases i <;> first | exact congrArg Complex.re hz | exact congrArg Complex.im hz
      simp [hu]
    · have hz : ∑ j, v j^2 = 0 := by exact_mod_cast h
      have hv : v = 0 := funext fun i => (Finset.sum_sq_eq_zero_iff _ _).mp hz i (Finset.mem_univ _)
      simp [hv]
  · rintro rfl; simp [angle,tip,Complex.mk_eq_add_mul_I]

/-- Inverse of radial squaring. Its norm formula proves continuity also at zero. -/
def rootRad (z : ℂ) := (√‖z‖)⁻¹ • z
lemma norm_rootRad (z : ℂ) : ‖rootRad z‖ = √‖z‖ := by
  rw [rootRad,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hz : z=0
  · simp [hz]
  grind
lemma cont_rootRad : Continuous rootRad := continuous_iff_continuousAt.mpr fun z => by
  by_cases hz : z=0
  · subst z; rw [ContinuousAt,show rootRad 0 = 0 by simp [rootRad],tendsto_zero_iff_norm_tendsto_zero]
    simpa [ContinuousAt,norm_rootRad] using! (Real.continuous_sqrt.comp continuous_norm).continuousAt (x := (0:ℂ))
  · unfold rootRad; fun_prop (disch := positivity)

def row := ![Complex.reCLM,Complex.imCLM]
def column : Fin (d+2) → ℂ →L[ℝ] ℝ := Fin.cons Complex.reCLM (Fin.cons Complex.imCLM 0)
def gram (d : ℕ) (w : ℂ) : Locus 2 (Fin (d+2)) := outer (fun i => row i w) (fun j => column j w)
lemma gram_cont : Continuous (gram d) := Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ((row i).continuous.mul (column j).continuous)) _
lemma gram_neg (w : ℂ) : gram d (-w) = gram d w := Subtype.ext (by ext; simp [gram,outer,vecMulVec])

/-- Squaring is a closed quotient on the complex plane. The Gram matrix of
a root is independent of the sign, so it descends *continuously* without
making a branch choice. -/
lemma planeRetract (d : ℕ) : ∃ R : Retract (tip : Locus 2 (Fin (d+2))) ℂ, ∀ z, 0 ≤ (R.lift z).val 0 0 := by
  let sqr : C(ℂ,ℂ) := ⟨(·^2),by fun_prop⟩
  have hq : Topology.IsQuotientMap sqr := (isClosedMap_pow ℂ 2).isQuotientMap sqr.continuous (fun z => IsAlgClosed.exists_pow_nat_eq z (by decide : 0<2))
  let G : C(ℂ,Locus 2 (Fin (d+2))) := ⟨gram d,gram_cont⟩
  have sign : Function.FactorsThrough G sqr := fun {a b} h => (sq_eq_sq_iff_eq_or_eq_neg.mp h).elim (congrArg G) (fun e => e ▸ gram_neg b)
  let L := hq.lift G sign
  have can (z) : angle (L z) = ‖z‖ • z := by
    obtain ⟨w,rfl⟩ := hq.surjective z
    rw [show L (sqr w) = gram d w from ContinuousMap.congr_fun (hq.lift_comp G sign) w,gram,angle_outer]
    change _ = ‖w^2‖ • w^2
    rw [norm_pow,Complex.sq_norm,Complex.normSq_apply]
    simp [row,column,Fin.sum_univ_succ,Complex.real_smul,pow_two,mul_comm]
  refine ⟨⟨⟨angle,by unfold angle; simp_rw [Complex.mk_eq_add_mul_I]; fun_prop⟩, L.comp ⟨rootRad,cont_rootRad⟩,fun z => ?_,angle_zero⟩,fun z => ?_⟩
  · change angle (L (rootRad z)) = z
    rw [can,norm_rootRad,rootRad]; by_cases hz : z=0 <;> simp_all
  · obtain ⟨w,hw⟩ := hq.surjective (rootRad z); change 0 ≤ (L (rootRad z)).val 0 0
    rw [← hw,show L (sqr w) = gram d w from ContinuousMap.congr_fun (hq.lift_comp G sign) w]; exact mul_self_nonneg w.re

theorem two_row_bad (e d : ℕ) (hd : 2 ≤ d) : ¬Euclidean ((0,tip) : Space e 2 (Fin d)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨R,h⟩ := planeRetract k
  apply obstruction R e (-1); rintro t ht ⟨z,hz⟩
  have hh := hz ▸ h z; change 0 ≤ (-1:ℝ) * t at hh; linarith
end GS.RankLocus
