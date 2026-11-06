module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem cubicGauss_normalized_cube_breveE
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
     hp  (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp eisEmbedding)
      (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  subst P
  exact cubicGauss_normalized_cube_eis (Ideal.span {p}) hgood p rfl hprimary
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)

end

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveGamma2 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 2)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

section
variable (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
include P hgood

theorem canonicalSextic_pow_two    
      :
    canonicalSextic P hgood ^ 2 =
      (cubicChar P hgood).ringHomComp eisEmbedding := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 2 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).1]

theorem breveGamma2_cube    
       p   hP 
     hp  (hprimary : lambda ^ 2 ∣ p - 1) :
    (breveGamma2 P hgood p hP hp) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  simp_all [breveGamma2, canonicalSextic_pow_two, cubicGauss_normalized_cube_breveE]

end

end ActualEisensteinCubic

namespace ShortDraftLocal

 

section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
include F χ ψ j

theorem general_inversion_gauss        
           a  :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (y⁻¹)) *
          ψ (a * (y : F)) := by
            apply Fintype.sum_equiv (Equiv.inv Fˣ)
            intro y
            simp
    _ = ∑ y : Fˣ, (χ ^ (j + 2)) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      congr 1
      have hchar : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
      rw [← hchar, MulChar.inv_apply']
    _ = gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem sextic_fourier_theta_row_general
           
         
    (hχj : χ ^ j ≠ 1) (hχj2 : χ ^ (j + 2) ≠ 1)
    (σ : Fˣ)  ε x  :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        (∑ h : Fˣ,
          (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ j) ψ hχj h, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, general_inversion_gauss χ ψ j (ε * x),
    gaussSum_mulShift_any (χ ^ (j + 2)) ψ hχj2 (ε * x), map_mul]
  ring

end

end ShortDraftLocal

namespace ActualEisensteinCubic

section

 

theorem canonical_A5_nonexceptional (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ)  j 
    (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4)
    (σ : (O ⧸ P)ˣ)  ε x  :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχj : χ ^ j ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar hj0 hj6
  have hχj2 : χ ^ (j + 2) ≠ 1 := by
    have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (3:ℕ) ≠ 0) (by decide : (3:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (5:ℕ) ≠ 0) (by decide : (5:ℕ) < 6)
    · have hχ1 : χ ≠ 1 := by
        aesop
      have hχ7 : χ ^ (5 + 2) = χ := by
        calc
          χ ^ (5 + 2) = χ ^ (6 + 1) := by congr 1
          _ = χ ^ 6 * χ := by rw [pow_add, pow_one]
          _ = χ := by rw [canonicalSextic_pow_six P hgood, one_mul]
      rw [hχ7]
      exact hχ1
  dsimp
  rw [Nat.card_eq_fintype_card]
  solve_by_elim [ShortDraftLocal.sextic_fourier_theta_row_general]

end

open ConcreteTraceCRT PrimitiveTrace

end ActualEisensteinCubic

namespace AnalyticBridge

theorem schwartz_fourier_one_plus_integrable
    (g : 𝓢(ℝ, ℂ))  J  :
    Integrable (fun t : ℝ =>
      (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) volume := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa [b] using b.integrable_pow_mul volume 0
  have hIJ : Integrable
      (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hR : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hcont : Continuous
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
    fun_prop
  exact hR.mono_nonneg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (by intro t; positivity))
    (Filter.Eventually.of_forall hpoint)

end AnalyticBridge

namespace JacobiQuadratic

 

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def affineDouble (hchar : ringChar F ≠ 2) : F ≃ F where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
  right_inv := by
    intro t
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring

private def oneSub : F ≃ F where
  toFun y := 1 - y
  invFun y := 1 - y
  left_inv := by intro y; ring
  right_inv := by intro y; ring

section
variable (χ : MulChar F ℂ)
include χ

section
variable (hchar : ringChar F ≠ 2)
include hchar

private theorem square_fiber  
      :
    (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, ((quadraticChar F y : ℂ) + 1) * χ (1 - y) := by
  classical
  have hfiber : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, (#{t : F | t ^ 2 = y}.toFinset : ℂ) * χ (1 - y) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun t : F => t ^ 2) (f := fun t : F => χ (1 - t ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht])]
    simp
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact_mod_cast quadraticChar_card_sqrts hchar y

theorem jacobi_quadratic  
      (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by
  classical
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hsum0 : (∑ y : F, χ (1 - y)) = 0 := by
    have ht := (Equiv.sum_comp (oneSub (F := F)) χ)
    change (∑ y : F, χ ((oneSub (F := F)) y)) = 0
    exact ht.trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hfiber := square_fiber χ hchar
  have hsq : (∑ t : F, χ (1 - t ^ 2)) = jacobiSum χ q := by
    rw [hfiber]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul, hsum0, add_zero]
    exact jacobiSum_comm q χ
  have hchange : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ x : F, χ (4 * x * (1 - x)) := by
    have ht := Equiv.sum_comp (affineDouble (F := F) hchar)
      (fun t : F => χ (1 - t ^ 2))
    convert ht.symm using 1
    · apply Finset.sum_congr rfl
      intro x _
      congr 1
      change 4 * x * (1 - x) = 1 - (2 * x - 1) ^ 2
      ring
  calc
    jacobiSum χ q = ∑ x : F, χ (4 * x * (1 - x)) := hsq.symm.trans hchange
    _ = χ (4 : F) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ map_mul]
      ring

end

section
variable (ψ : AddChar F ℂ) (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive) (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1) (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ)) (hχ6 : χ ^ 6 = 1)
include ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6

theorem gauss_sextic_relation    
       
         
     
      :
    χ (4 : F) * gaussSum χ ψ * (Fintype.card F : ℂ) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 2 := by

  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let J11 := jacobiSum χ χ
  let J13 := jacobiSum χ (χ ^ 3)
  have hprod2 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have hprod4 : χ * χ ^ 3 = χ ^ 4 := by group
  have hJ12 : g2 * J11 = g1 * g1 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod2]; exact hχ2) ψ
      (χ := χ) (φ := χ)
    rw [hprod2] at h
    exact h
  have hJ13 : g4 * J13 = g1 * g3 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod4]; exact hχ4) ψ
      (χ := χ) (φ := χ ^ 3)
    rw [hprod4] at h
    exact h
  have hJquad : J13 = χ (4 : F) * J11 := by
    grind [jacobi_quadratic]
  have hg1ne : g1 ≠ 0 := by
    apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hχ1
    · exact hψ
  have h4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ ^ 2 * χ ^ 4 = χ ^ 6 := by group
      _ = 1 := hχ6
  have h4minus : (χ ^ 4) (-1 : F) = 1 := by
    rw [χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), ← map_pow,
      show (-1 : F) ^ 4 = 1 by ring, map_one]
  have hG4inv : gaussSum (χ ^ 4) ψ⁻¹ = g4 := by
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [h4minus, one_mul] at h
    exact h
  have hG24 : g2 * g4 = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← h4inv, hG4inv] at h
    exact h
  
  grind

theorem normalized_gauss_sextic_relation    
       
         
     
     
     s  (hs : s ^ 2 = (Fintype.card F : ℂ)) (hs0 : s ≠ 0) :
    χ (4 : F) * (gaussSum χ ψ / s) * (gaussSum (χ ^ 2) ψ / s) =
      (gaussSum (χ ^ 3) ψ / s) * (gaussSum (χ ^ 2) ψ / s) ^ 3 := by
  have hraw := gauss_sextic_relation χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6
  grind

end

end

end JacobiQuadratic

end

end OAI
