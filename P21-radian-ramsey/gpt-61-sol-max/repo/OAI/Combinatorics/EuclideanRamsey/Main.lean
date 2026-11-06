/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Main.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CorrectionPaths
public import Mathlib.RingTheory.Localization.BaseChange

public section

open scoped MatrixOrder ContDiff Topology Pointwise
open Filter MeasureTheory
open Matrix
namespace OAI.EuclideanRamsey





set_option maxHeartbeats 0 in
theorem realCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : RealCriterion a) : Ramsey a := by
  intro r hr
  classical
  let A := fun i => FiniteEuclidean.embed d (a i)
  have hmono (coloringInput : FiniteEuclidean → Fin r) :
      ∃ b : Fin s → FiniteEuclidean,(∀ i j,‖b i-b j‖=‖A i-A j‖) ∧
        ∃ k : Fin r,∀ i,coloringInput (b i)=k := by
    obtain ⟨β,hβ,hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) (Fin r)
    let := hβ
    let n := Fintype.card β+1
    have hn : 1 ≤ n := by omega
    let η : ℝ := 1/(2*n)
    let δ : ℝ := 1/(2*n*s)
    have hη : 0<η := by dsimp [η]; positivity
    have hδ : 0<δ := by dsimp [δ]; positivity
    obtain ⟨P,hP,hG⟩ := h
    let T  := affineArray.symm P
    have hT  := affineArray.apply_symm_apply P
    obtain ⟨k,w,C,hC,hrep⟩ := exists_symmetric_tensor_presentation T
    have hsp : spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) = 1 := by
      rw [hrep,map_smul,map_add,map_smul,map_add,spatialMultiply_comm,hT,hG]
      ext α β
      simp [Matrix.one_apply]
      by_cases hh : α = β <;> norm_num [hh,eq_comm,Rat.smul_def]
    let U : Matrix (Fin d) (Fin k) ℝ := fun α j => w j (some α)
    have hU : U * C.map (Rat.cast : ℚ → ℝ) * U.transpose = 1 := by
      rw [← hsp]
      symm
      ext α β
      simp [Matrix.sum_apply, spatialMultiply]
      change (∑ j, ∑ l, (C j l:ℝ)*(w j (some α)*w l (some β))) = _
      change _ = ∑ l, (∑ j, w j (some α) * (C j l : ℝ)) * w l (some β)
      simp [Finset.sum_mul]
      rw [Finset.sum_comm]
      grind
    have hquot i : quotientTensor
        (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))
        (matrixTensor C) = 0 := by
      apply quotientTensor_zero_of_evaluation
      rw [TensorProduct.map_comp,LinearMap.comp_apply,matrixTensor_map_family]
      rw [← arrayEvaluation_affineArray,hrep,map_smul,map_add,map_smul,map_add]
      simp only [arrayEvaluation_affineArray,TensorProduct.map_comm]
      simp only [← arrayEvaluation_affineArray,T,hT,hP,map_zero,add_zero,smul_zero]
    let φ i : Lattice k →+ ℝ :=
      ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize
    let Λ i := (φ i).ker
    obtain ⟨ν,hcos,hzero,hfirst,hsecond⟩ :=
      finite_lattice_identity Λ C hC hquot
    obtain ⟨b,hb,hbc,hbI,hbη⟩ := compact_smoothing hd (C.map (Rat.cast : ℚ → ℝ)) U
      (hC.map _) hU hη
    let Cr := C.map (Rat.cast : ℚ → ℝ)
    let S := ν.coeff.support
    let q : Lattice k → ℝ := fun γ => ν.coeff γ
    have hz : ∑ γ ∈ S,q γ = 0 := by
      simpa [S, q, mass, AddMonoidAlgebra.lift_apply, Finsupp.sum] using congrArg (Rat.cast : ℚ → ℝ) hzero
    have hf j : ∑ γ ∈ S,q γ*(γ j:ℝ) = 0 := by
      dsimp [S, q]
      exact_mod_cast hfirst j
    have hsecondCast j l : ∑ γ ∈ S,q γ*(γ j:ℝ)*(γ l:ℝ) = Cr j l := by
      simpa [S, q, Cr, secondMoment, coefficientFunctional, Finsupp.linearCombination_apply,
        Finsupp.sum, mul_assoc] using congrArg (Rat.cast : ℚ → ℝ) (hsecond j l)
    have hZ := lattice_riemann hb.continuous hbc
    let v : (Fin k → ℤ) → Fin k → ℝ := fun γ j => γ j
    have hN : Tendsto (fun N : ℕ => (∑' δ : Fin k → ℤ,
        max (-((N:ℝ)^2*∑ γ ∈ S,q γ*b (latticeSample N δ+(-(N:ℝ)⁻¹) • v γ))) 0 *
          gradientWeight U (latticeSample N δ))/(N:ℝ)^k) atTop
        (𝓝 (∫ x,max (-stencilDifferential Cr b x) 0*gradientWeight U x)) := by
      classical
      let f := fun x => max (-stencilDifferential Cr b x) 0*gradientWeight U x
      let g := fun (N : ℕ) x => max (-((N:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(N:ℝ)⁻¹) • v γ))) 0*
        gradientWeight U x
      have hc : Continuous f := by
        have hh := hb.continuous_iteratedFDeriv (m := 2) (by norm_cast)
        unfold f gradientWeight stencilDifferential
        fun_prop
      have hs : Function.support f ⊆ tsupport b := by
        intro x hx
        by_contra h
        have hz : iteratedFDeriv ℝ 2 b x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hx => h (tsupport_iteratedFDeriv_subset 2 hx))
        exact hx (by simp [f,stencilDifferential,hz])
    
      have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hbc hs
      obtain ⟨r,hr,hbr⟩ := hbc.isBounded.exists_pos_norm_lt
      let V := ∑ γ ∈ S,‖v γ‖
      have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      have hv γ hγ : ‖v γ‖ ≤ V := Finset.single_le_sum (fun _ _ => norm_nonneg _) hγ
      let R := r+V+1
      have hR : 0 < R := by dsimp [R]; linarith
      have hfr : Function.support f ⊆ Metric.closedBall 0 R := by
        intro x hx
        rw [Metric.mem_closedBall,dist_zero_right]
        exact (hbr x (hs hx)).le.trans (by dsimp [R]; linarith)
      have hgr N : Function.support (g N) ⊆ Metric.closedBall 0 R := by
        intro x hx
        rw [Metric.mem_closedBall,dist_zero_right]
        have hsample : N ≠ 0 := by rintro rfl; exact hx (by simp [g])
        obtain ⟨γ,hγ,hbγ⟩ := Finset.exists_ne_zero_of_sum_ne_zero
          (show (∑ γ ∈ S,q γ*b (x+(-(N:ℝ)⁻¹) • v γ)) ≠ 0 by
            intro h; exact hx (by dsimp only [g]; rw [h]; simp))
        have hn1 : (1:ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hsample)
        have hni : |(N:ℝ)⁻¹| ≤ 1 := by
          rw [abs_inv,abs_of_nonneg (by positivity)]
          exact inv_le_one_of_one_le₀ hn1
        have hshift : ‖(-(N:ℝ)⁻¹) • v γ‖ ≤ V := by
          rw [norm_smul,Real.norm_eq_abs,abs_neg]
          exact (mul_le_mul_of_nonneg_right hni (norm_nonneg _)).trans (by simpa using hv γ hγ)
        have hbγ := hbr _ (subset_tsupport b (mul_ne_zero_iff.mp hbγ).2)
        have hx' := norm_le_norm_add_norm_sub (x+(-(N:ℝ)⁻¹) • v γ) x
        simp only [add_sub_cancel_left] at hx'
        dsimp [R]
        linarith
      obtain ⟨W,hW⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_bound_of_continuousOn
        (show Continuous (gradientWeight U) by unfold gradientWeight; fun_prop).continuousOn
      obtain ⟨K,hK,hTaylor⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ x,
          |t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential Cr b x| ≤ K/t := by
        obtain ⟨K,hK,hTaylor⟩ := compact_taylor_bound hb hbc
        refine ⟨∑ γ ∈ S, |q γ| *K*‖v γ‖^3,Finset.sum_nonneg (fun _ _ => by positivity),?_⟩
        intro t ht x
        have hv : ∑ γ ∈ S,q γ • v γ = 0 := by ext j; simpa [v] using hf j
        have hl := congrArg (fderiv ℝ b x) hv
        simp only [map_sum,map_smul,smul_eq_mul,map_zero] at hl
        have hb' := bilinear_moment_contract S q v (hessianB b x)
        simp only [v,hsecondCast,hessianB_eq] at hb'
        let r γ := b (x+(-t⁻¹) • v γ)-b x-
          fderiv ℝ b x ((-t⁻¹) • v γ)-
          (1/2:ℝ)*iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ]
        have hr γ : |r γ| ≤ K*(t⁻¹)^3*‖v γ‖^3 := by
          have hh := hTaylor x ((-t⁻¹) • v γ)
          simpa only [r,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos ht,mul_pow,
            mul_assoc] using hh
        have hrEq : t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential Cr b x =
            t^2*∑ γ ∈ S,q γ*r γ := by
          have hscale γ : iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ] =
              (t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ] := by
            simp only [← hessianB_eq,map_smul,_root_.smul_apply,smul_eq_mul]
            ring
          simp only [r,mul_sub,Finset.sum_sub_distrib,map_smul,smul_eq_mul,hscale]
          simp_rw [mul_left_comm (q _) (-t⁻¹), mul_left_comm (q _) (1/2:ℝ),
            mul_left_comm (q _) ((t⁻¹)^2)]
          simp only [← Finset.sum_mul, ← Finset.mul_sum, v, hz, hl, hb', zero_mul, mul_zero,
            sub_zero, stencilDifferential]
          field_simp
        rw [hrEq,abs_mul,abs_of_nonneg (sq_nonneg t)]
        calc
          _ ≤ t^2 * ∑ γ ∈ S, |q γ| *|r γ| := by
            gcongr
            simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun γ => q γ*r γ) S
          _ ≤ t^2 * ∑ γ ∈ S, |q γ| *(K*(t⁻¹)^3*‖v γ‖^3) := by
            gcongr with γ hγ
            exact hr γ
          _ = (∑ γ ∈ S,|q γ| *K*‖v γ‖^3)/t := by
            rw [Finset.mul_sum,Finset.sum_div]
            congr! 1 with γ hγ
            field_simp
      have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp [hR.le]))
      let error (N : ℕ) : ℝ := K*W/(N:ℝ)
      have hε : Tendsto error atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hbound (N : ℕ) (hsample : 1 ≤ N) (x) : |g N x-f x| ≤ error N := by
        by_cases hx : x ∈ Metric.closedBall (0 : Fin k → ℝ) R
        · have hw : |gradientWeight U x| ≤ W := by simpa [Real.norm_eq_abs] using hW x hx
          have hn0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          have he := hTaylor N hn0 x
          have hm := abs_max_sub_max_le_abs
            (-((N:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(N:ℝ)⁻¹) • v γ))) (-stencilDifferential Cr b x) 0
          have hm' : |max (-((N:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(N:ℝ)⁻¹) • v γ))) 0-
              max (-stencilDifferential Cr b x) 0| ≤ K/N := by
            apply hm.trans
            simpa only [neg_sub_neg,abs_sub_comm] using he
          dsimp [g,f]
          rw [← sub_mul,abs_mul]
          calc
            _ ≤ (K/N)*W := mul_le_mul hm' hw (abs_nonneg _) (by positivity)
            _ = _ := by ring
        · have hf0 : f x = 0 := by by_contra hh; exact hx (hfr hh)
          have hg0 : g N x = 0 := by by_contra hh; exact hx (hgr N hh)
          rw [hf0,hg0,sub_self,abs_zero]
          positivity
      let s := Metric.closedBall (0 : Fin k → ℝ) R
      have hfront : volume (frontier s) = 0 :=
        measure_mono_null Metric.frontier_closedBall_subset_sphere
          (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
      have hgrid := tendsto_card_div_pow_atTop_volume s Metric.isBounded_closedBall
        measurableSet_closedBall hfront
      have hlim := hε.mul hgrid
      rw [zero_mul] at hlim
      have hdiff : Tendsto (fun n : ℕ =>
          (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k-
          (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k) atTop (𝓝 0) := by
        apply squeeze_zero_norm' _ hlim
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : n ≠ 0 := by omega
        let G := ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)))
        let : Fintype G := (bounded_grid_finite hn0 Metric.isBounded_closedBall).fintype
        rw [Real.norm_eq_abs, lattice_tsum_eq_grid hn0 s (g n) (hgr n),
          lattice_tsum_eq_grid hn0 s f hfr, ← sub_div, abs_div,
          abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^k)]
        rw [tsum_fintype,tsum_fintype,← Finset.sum_sub_distrib]
        calc
          _ ≤ (∑ _x : G, error n)/(n:ℝ)^k := by
            gcongr
            exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => hbound n hn x))
          _ = _ := by simp [Nat.card_eq_fintype_card]; ring
    
      convert hdiff.add (lattice_riemann hc hfc) using 1
      · ext n; ring
      · simp [f]
    have he := hN.eventually_lt (tendsto_const_nhds.mul hZ) hbη
    have hp := (tendsto_const_nhds.eventually_lt hZ hbI)
    obtain ⟨N,hsample,hp,he⟩ := (eventually_ge_atTop 1 |>.and (hp.and he)).exists
    let weight := fun γ : Fin k → ℤ => b (latticeSample N γ)
    have hnf : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hfinite : Function.HasFiniteSupport weight := latticeSample_finite_support (by omega) hbc
    have hshift (δ γ : Fin k → ℤ) : latticeSample N δ+(-(N:ℝ)⁻¹) • (fun j => (γ j:ℝ)) =
        latticeSample N (δ-γ) := by
      ext j
      simp only [latticeSample,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Int.cast_sub]
      ring
    simp only [v,hshift] at he
    have hscale δ :
        max (-((N:ℝ)^2*∑ γ ∈ S,q γ*weight (δ-γ))) 0*gradientWeight U (latticeSample N δ) =
        (N:ℝ)^2*(max (-(∑ γ ∈ S,q γ*weight (δ-γ))) 0*gradientWeight U (latticeSample N δ)) := by
      rw [← mul_neg,← mul_zero ((N:ℝ)^2),← mul_max_of_nonneg _ _ (sq_nonneg (N:ℝ))]
      rw [mul_assoc, mul_zero]
    change (∑' δ,max (-((N:ℝ)^2*∑ γ ∈ S,q γ*weight (δ-γ))) 0*
      gradientWeight U (latticeSample N δ))/(N:ℝ)^k < η*((∑' γ,weight γ)/(N:ℝ)^k) at he
    simp only [hscale,tsum_mul_left] at he
    have hp' := (div_pos_iff_of_pos_right (pow_pos hnf k)).mp hp
    have hap : 0 < (∑' γ,weight γ)/(N:ℝ)^2 := by positivity
    have han : (∑' δ,max (-(∑ γ ∈ S,q γ*weight (δ-γ))) 0*gradientWeight U (latticeSample N δ)) <
        η*((∑' γ,weight γ)/(N:ℝ)^2) := by
      have hh : (N:ℝ)^2*(∑' δ,max (-(∑ γ ∈ S,q γ*weight (δ-γ))) 0*
          gradientWeight U (latticeSample N δ)) < η*(∑' γ,weight γ) := by
        apply (div_lt_div_iff_of_pos_right (pow_pos hnf k)).mp
        simpa only [mul_div_assoc] using he
      rw [← mul_div_assoc]
      apply (lt_div_iff₀ (sq_pos_of_pos hnf)).mpr
      simpa only [mul_comm] using hh
  
    let weightMoment := fun δ : Lattice k => gradientWeight U (latticeSample N δ)
    let t := (N:ℝ)^2
    let E := hfinite.toFinset
    let K := ν.coeff.support+E
    let ext (d : E → ℝ) γ := if h : γ ∈ E then d ⟨γ,h⟩ else 0
    let ζ (d : E → ℝ) := (∑ γ : E,d γ)/t
    let negativeSum d := ∑ δ ∈ K,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*weightMoment δ
    have hcast : Continuous ζ := by unfold ζ; fun_prop
    have hExt γ : Continuous (fun d : E → ℝ => ext d γ) := by
      dsimp [ext]
      split_ifs <;> fun_prop
    have hN : Continuous negativeSum := by unfold negativeSum; fun_prop
    have hsum d : ∑' γ,ext d γ = ∑ γ : E,d γ := by
      rw [tsum_eq_sum (s := E)]
      · rw [← Finset.sum_coe_sort]
        congr! 1 with γ hγ
        simp [ext, dite_eq_left γ.property]
      · intro γ hγ
        simp [ext,hγ]
    have hNeg d : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*weightMoment δ) = negativeSum d := by
      apply tsum_eq_sum
      intro δ hδ
      have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ) = 0 := by
        apply Finset.sum_eq_zero
        intro γ hγ
        have hE : δ-γ ∉ E := by
          intro h
          exact hδ (Finset.mem_add.mpr ⟨γ,hγ,δ-γ,h,by abel⟩)
        simp [ext,hE]
      simp [hz]
    let aE : E → ℝ := fun γ => weight γ
    have haE : ext aE = weight := by
      funext γ
      by_cases h : weight γ = 0
      · simp [ext, aE, h]
      · simp [ext, aE, show γ ∈ E from hfinite.mem_toFinset.mpr h]
    have hpE : 0 < ζ aE := by
      change 0 < (∑ γ : E,aE γ)/t
      rw [← hsum aE,haE]
      exact hap
    have hnE : negativeSum aE < η*ζ aE := by
      rw [← hNeg,haE]
      change _ < η*((∑ γ : E,aE γ)/t)
      rw [← hsum aE,haE]
      exact han
    have hDense : DenseRange (fun q : E → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    obtain ⟨q,hq0,hqN⟩ := hDense.exists_mem_open
      ((isOpen_lt continuous_const hcast).inter (isOpen_lt hN (continuous_const.mul hcast))) ⟨aE,hpE,hnE⟩
    let p : AddMonoidAlgebra ℚ (Lattice k) := .ofCoeff <| Finsupp.onFinset E
      (fun γ => if h : γ ∈ E then q ⟨γ,h⟩ else 0) (by aesop)
    have hb γ : (p.coeff γ : ℝ) = ext (fun i => (q i:ℝ)) γ := by
      by_cases h : γ ∈ E <;> simp [p, ext, h]
    have hbMass : ((p.coeff.sum fun _ q => q : ℚ):ℝ) = ∑ γ : E,(q γ:ℝ) := by
      simp only [p]
      rw [Finsupp.sum_onFinset _ _ _ _ (by simp), Rat.cast_sum, ← Finset.sum_attach E]
      simp
    have hp0 : 0 < ((p.coeff.sum fun _ q => q : ℚ):ℝ)/t := by
      simpa [hbMass, ζ] using hq0
    have hpη : (∑' δ,max (-((ν*p).coeff δ:ℝ)) 0*weightMoment δ) <
        η*(((p.coeff.sum fun _ q => q : ℚ):ℝ)/t) := by
      have hc δ : ((ν*p).coeff δ:ℝ) = ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext (fun i => (q i:ℝ)) (δ-γ) := by
        rw [AddMonoidAlgebra.coeff_mul_apply_left]
        simp [Finsupp.sum, sub_eq_neg_add, hb]
      simp [hc, hNeg, hbMass]
      exact hqN
  
    let ζ  := mass p/(N:ℚ)^2
    have hζ : 0 < ζ := by
      have hp' : (0:ℝ) < (ζ:ℝ) := by simpa [ζ, mass, AddMonoidAlgebra.lift_apply, weightMoment, t] using hp0
      exact_mod_cast hp'
    let μ := ν*p
    have hcos (i) : cosetPushforward (Λ i) μ = 0 := by simp [μ,hcos i]
    have hmom (j l) : secondMoment μ j l/(N:ℚ)^2 = ζ*C j l := by
      dsimp only [μ]
      simp [secondMoment_mul, hzero, hfirst, hsecond, zero_mul]
      dsimp [ζ]
      ring
    have hneg : (∑' δ : Lattice k,max (-(μ.coeff δ:ℝ)) 0*gradientWeight U (latticeSample N δ)) < η*ζ := by
      simpa [μ,ζ, mass, AddMonoidAlgebra.lift_apply, weightMoment, t] using hpη
    let f := μ.coeff
    let v (γ : Lattice k) : ℝ := ∑ j,(γ j:ℝ)/(N:ℝ)*w j none
    let g γ α : ℝ := ∑ j,U α j*latticeSample N γ j
    have heval i : f.mapDomain (fun γ => v γ+∑ α,a i α*g γ α)=0 := by
      have heq : (fun γ => φ i γ/(N:ℝ)) = (fun γ => v γ+∑ α,a i α*g γ α) := by
        funext γ
        simp only [φ, v, g, U, latticeSample, AddMonoidHom.comp_apply,
          LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, Fintype.linearCombination_apply,
          map_sum, map_smul, rationalize,Rat.smul_def,
          rowEvaluation,dotProductBilin,dotProduct, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_option,
          realAugmented, one_mul]
        change (∑ j, (γ j:ℝ)*(w j none+∑ α,a i α*w j (some α)))/(N:ℝ) = _
        simp [div_eq_mul_inv,mul_add,Finset.sum_add_distrib,
          Finset.mul_sum,mul_comm,mul_assoc,mul_left_comm]
        rw [Finset.sum_comm]
      rw [← heq]
      let fq := QuotientAddGroup.lift (φ i).ker (φ i) le_rfl
      have he : (fun γ => φ i γ/(N:ℝ)) =
          (fun y => fq y/(N:ℝ)) ∘ QuotientAddGroup.mk' (φ i).ker := rfl
      rw [he,Finsupp.mapDomain_comp]
      change Finsupp.mapDomain _ (cosetPushforward (Λ i) μ).coeff = 0
      simp [hcos i]
    have hmoment α β : f.sum (fun γ q => (q:ℝ)*g γ α*g γ β) =
        (ζ:ℝ)*(if α=β then 1 else 0) := by
      change _ = (ζ:ℝ)*(1 : Matrix (Fin d) (Fin d) ℝ) α β
      rw [← hU]
      have hm j l : ∑ γ ∈ f.support,
          (f γ:ℝ)*latticeSample N γ j*latticeSample N γ l = (ζ:ℝ)*(C j l:ℝ) := by
        have h := congrArg (Rat.cast : ℚ → ℝ) (hmom j l)
        simp [secondMoment, coefficientFunctional, Finsupp.linearCombination_apply, Finsupp.sum] at h
        rw [← h,Finset.sum_div]
        congr! 1 with γ hγ
        simp [latticeSample]
        ring
      let L a := (dotProductBilin ℝ ℝ (U a)).toContinuousLinearMap
      have h := bilinear_moment_contract f.support (fun γ => (f γ : ℝ))
        (latticeSample N) ((L α).smulRight (L β))
      simp only [hm] at h
      simp [L,dotProductBilin,dotProduct,Pi.single_apply,mul_ite,mul_assoc] at h
      convert h using 1
      · simp only [g, Finsupp.sum, mul_assoc]
      · simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
          Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        congr! 2 with j _ l _
        ring
    have hnegative : f.sum (fun γ q => max (-(q:ℝ)) 0*(∑ α,(g γ α)^2)) < η*(ζ:ℝ) := by
      rw [tsum_eq_sum (s := f.support)] at hneg
      · exact hneg
      · intro γ hγ
        have hz := Finsupp.notMem_support_iff.mp hγ
        change μ.coeff γ = 0 at hz
        simp [hz]
    clear_value f g v ζ
    clear * - hHJ a ha hs hn η δ hη hδ heval hmoment hnegative hζ f g v
    obtain ⟨den,z₀,hz₀⟩ := IsLocalizedModule.exists_integer_multiple (nonZeroDivisors ℤ)
      (Finsupp.mapRange.linearMap (α:=Lattice k) (Algebra.linearMap ℤ ℚ)) f
    let M := (den:ℤ).natAbs
    let z := (den:ℤ).sign • z₀
    have hM : 0 < M := Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero den.prop)
    have hz (a) : (z a:ℝ) = M*(f a:ℝ) := by
      have h := congrArg (fun g : Lattice k →₀ ℚ => (g a:ℝ)) hz₀
      simp at h
      simp only [z,Finsupp.smul_apply,smul_eq_mul,Int.cast_mul]
      rw [h,← mul_assoc,← Int.cast_mul,Int.sign_mul_self]
      simp [M]
    clear_value M z
    let pos := z.mapRange Int.toNat (by simp)
    let negCount := z.mapRange (fun n => (-n).toNat) (by simp)
    let m := pos.toMultiset
    let neg := negCount.toMultiset
    have hsum_count (c : Lattice k →₀ ℕ) (f : Lattice k → ℝ) :
        (∑ x : c.toMultiset,f x) = c.sum (fun a n => (n:ℝ)*f a) := by
      rw [Finset.sum_eq_multiset_sum,Multiset.map_univ,Finsupp.toMultiset_map,Finsupp.sum_toMultiset,
        Finsupp.sum_mapDomain_index]
      · simp
      · intro a; simp
      simp [add_mul]
    have hcounts : pos.mapRange (Nat.cast : ℕ → ℝ) (by simp) -
        negCount.mapRange (Nat.cast : ℕ → ℝ) (by simp) =
        (M:ℝ) • f.mapRange (Rat.cast : ℚ → ℝ) (by simp) := by
      ext a
      change (↑(z a).toNat : ℝ) - ↑(-z a).toNat = (M:ℝ)*(f a:ℝ)
      rw [← hz]
      exact_mod_cast Int.toNat_sub_toNat_neg (z a)
    have hsum (g : (Lattice k) → ℝ) : (∑ x : m,g x)-(∑ x : neg,g x) = M*f.sum (fun a q => (q:ℝ)*g a) := by
      have h := congrArg (Finsupp.linearCombination ℝ g) hcounts
      simp only [map_sub, map_smul] at h
      simpa [m, neg, hsum_count, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index, smul_eq_mul, mul_assoc] using h
    have hnegativeSum (g : (Lattice k) → ℝ) : (∑ x : neg,g x) =
        M*f.sum (fun a q => max (-(q:ℝ)) 0*g a) := by
      have he : negCount.mapRange (Nat.cast : ℕ → ℝ) (by simp) =
          (M:ℝ) • f.mapRange (fun q : ℚ => max (-(q:ℝ)) 0) (by simp) := by
        ext a
        have hc : (negCount a : ℝ) = max (-(z a:ℝ)) 0 := by
          change ((-(z a)).toNat:ℝ) = _
          exact_mod_cast Int.toNat_eq_max (-(z a))
        simp [Finsupp.smul_apply, hc, hz, ← mul_neg,
          mul_max_of_nonneg _ _ (Nat.cast_nonneg M), mul_zero]
      have h := congrArg (Finsupp.linearCombination ℝ g) he
      simp only [map_smul] at h
      simpa [m, neg, hsum_count, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index, smul_eq_mul, mul_assoc] using h
    let row (i : Fin s) (x : Lattice k) := v x+∑ j,a i j*g x j
    have hmap (i) : m.map (row i) = neg.map (row i) := by
      simp only [m, neg, Finsupp.toMultiset_map]
      congr 1
      apply Finsupp.mapRange_injective (Nat.cast : ℕ → ℝ) (by simp) Nat.cast_injective
      apply sub_eq_zero.mp
      rw [← Finsupp.mapDomain_mapRange _ _ _ _ (fun x y => Nat.cast_add x y),
        ← Finsupp.mapDomain_mapRange _ _ _ _ (fun x y => Nat.cast_add x y),
        ← Finsupp.mapDomain_sub,hcounts,Finsupp.mapDomain_smul,
        Finsupp.mapDomain_mapRange _ _ _ _ (fun x y => Rat.cast_add x y),heval i]
      simp
    let e (i) := (m.mapEquiv (row i)).trans
      ((Multiset.cast (hmap i)).trans (neg.mapEquiv (row i)).symm)
    have he (i) (x : m) : row i (e i x) = row i x := by
      have ht := (neg.mapEquiv (row i)).apply_symm_apply
        ((Multiset.cast (hmap i)) (m.mapEquiv (row i) x))
      have hh := congrArg (fun y : neg.map (row i) => (y : ℝ)) ht
      simp only [Multiset.mapEquiv_apply] at hh
      exact hh.trans (Multiset.mapEquiv_apply m (row i) x)
    clear_value e
    let e₀ := e ⟨0,by omega⟩
    have hMp : (0:ℝ)<M := by exact_mod_cast hM
    let U : Matrix (Fin d) m ℝ := fun j x => g x j
    let V : Matrix (Fin d) m ℝ := fun j x => g (e₀ x) j
    have hu j l : (U*U.transpose) j l = ∑ x : m,g x j*g x l := rfl
    have hv j l : (V*V.transpose) j l = ∑ x : neg,g x j*g x l := by
      exact e₀.sum_comp (fun x : neg => g x j*g x l)
    let Z := (M:ℝ)*ζ
    have hZ : 0 < Z := by positivity
    have hdiff : U*U.transpose-V*V.transpose=Z • 1 := by
      ext j l
      simp only [Matrix.sub_apply,hu,hv]
      have hm' := hsum (fun x => g x j*g x l)
      change (∑ x : m,g x j*g x l)-(∑ x : neg,g x j*g x l) = _ at hm'
      rw [hm']
      have hm := hmoment j l
      simp only [mul_assoc] at hm
      rw [hm]
      simp [Z, Matrix.one_apply]
    have htrace : (V*V.transpose).trace < η*Z := by
      have ht : (V*V.transpose).trace = (M:ℝ)*
          f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) := by
        change (∑ j,(V*V.transpose) j j) = _
        simp only [hv]
        rw [Finset.sum_comm]
        simp only [← pow_two]
        have hn' := hnegativeSum (fun x => ∑ j,(g x j)^2)
        change (∑ x : neg,∑ j,(g x j)^2) = _ at hn'
        rw [hn']
      rw [ht]
      simpa [Z, mul_assoc, mul_left_comm, mul_comm] using mul_lt_mul_of_pos_left hnegative hMp
    have hperm i : ∃ σ : Equiv.Perm m,∀ x,
        v (e₀ (σ x))+∑ j,a i j*V j (σ x) = v x+∑ j,a i j*U j x := by
      refine ⟨(e i).trans e₀.symm,?_⟩
      intro x
      simpa [U,V,Equiv.trans_apply,e₀,row] using he i x
    let τ := m.ToType
    let vp : τ → ℝ := fun x => v x
    let vn : τ → ℝ := fun x => v (e₀ x)
    let B := V*V.transpose
    have hB : B.PosSemidef := by simpa [B] using Matrix.posSemidef_self_mul_conjTranspose V
    have hP : ((η*Z) • (1 : Matrix (Fin d) (Fin d) ℝ)-B).PosSemidef := by
      apply Matrix.nonneg_iff_posSemidef.mp
      apply sub_nonneg.mpr
      rw [← Algebra.algebraMap_eq_smul_one]
      apply le_algebraMap_of_spectrum_le (R := ℝ) (ha := hB.1)
      intro x hx
      obtain ⟨i,rfl⟩ := hB.1.spectrum_real_eq_range_eigenvalues ▸ hx
      apply le_trans _ htrace.le
      rw [hB.1.trace_eq_sum_eigenvalues]
      exact Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)
    let P := (η*Z) • (1 : Matrix (Fin d) (Fin d) ℝ)-B
    let R := CFC.sqrt P
    have hR : R*R.transpose=(η*Z) • 1-V*V.transpose := by
      have hr : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial,hr.1.eq]
      exact CFC.sqrt_mul_sqrt_self P hP.nonneg
    let c := (Real.sqrt ((1+η)*Z))⁻¹
    let Up := c • U.fromCols R
    let Un := c • V.fromCols R
    have he (A : Matrix (Fin d) τ ℝ) :
        (c • A.fromCols R)*(c • A.fromCols R).transpose =
        (1/((1+η)*Z)) • (A*A.transpose+R*R.transpose) := by
      rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
        Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]
      congr 1
      dsimp [c]
      rw [← _root_.mul_inv_rev,← sq,Real.sq_sqrt (by positivity)]
      simp
    have hU : U*U.transpose+((η*Z) • 1-V*V.transpose)=((1+η)*Z) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [add_mul,one_mul,add_smul,← hdiff]
      abel
    have hV : V*V.transpose+((η*Z) • 1-V*V.transpose)=(η*Z) • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
    have hsc : (1/((1+η)*Z))*(η*Z)=η/(1+η) := by field_simp
    obtain ⟨hR1,hR2⟩ : Up*Up.transpose=1 ∧ Un*Un.transpose=(η/(1+η)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      change (c • U.fromCols R)*(c • U.fromCols R).transpose=1 ∧
        (c • V.fromCols R)*(c • V.fromCols R).transpose=_
      rw [he,he,hR,hU,hV,smul_smul,smul_smul,
        one_div_mul_cancel (by positivity : (1+η)*Z ≠ 0),one_smul,hsc]
      trivial
    let cp : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vp (fun _ => 0) x
    let cn : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vn (fun _ => 0) x
    let ip i x := cp x+∑ j,a i j*Up j x
    let ineg i x := cn x+∑ j,a i j*Un j x
    have hperm' i : ∃ σ : Equiv.Perm (τ ⊕ Fin d),∀ x,ineg i (σ x)=ip i x := by
      obtain ⟨σ,hσ⟩ := hperm i
      refine ⟨Equiv.sumCongr σ (Equiv.refl _),?_⟩
      intro x
      cases x with
      | inl x =>
        have h := congrArg (fun r : ℝ => c*r) (hσ x)
        change c*v (e₀ (σ x))+∑ j,a i j*(c*V j (σ x)) = c*v x+∑ j,a i j*(c*U j x)
        simpa only [Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm] using h
      | inr x => rfl
    let e := Fintype.equivFin (τ ⊕ Fin d)
    let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
    let embed (v : τ ⊕ Fin d → ℝ) (U : Matrix (Fin d) (τ ⊕ Fin d) ℝ) i :=
      reindex (WithLp.toLp 2 (fun x => v x+∑ j,a i j*U j x))
    have distance v U q
        (hU : U*U.transpose=q • 1) i i' :
        ‖embed v U i-embed v U i'‖^2 = q*‖a i-a i'‖^2 := by
      dsimp only [embed]
      rw [← map_sub, LinearIsometryEquiv.norm_map]
      simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
        WithLp.ofLp_sub, Pi.sub_apply]
      have he x : (v x+∑ j,a i j*U j x)-(v x+∑ j,a i' j*U j x) =
          (U.transpose *ᵥ ((a i).ofLp-(a i').ofLp)) x := by
        simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,Pi.sub_apply,
          mul_sub,Finset.sum_sub_distrib]
        simp only [mul_comm]
        ring
      simp only [he,pow_two]
      change (U.transpose *ᵥ ((a i).ofLp-(a i').ofLp)) ⬝ᵥ (U.transpose *ᵥ ((a i).ofLp-(a i').ofLp)) = _
      nth_rw 1 [← Matrix.vecMul_transpose U.transpose ((a i).ofLp-(a i').ofLp)]
      rw [← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec,Matrix.transpose_transpose,hU,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
      rfl
    let f' := embed cp Up
    let g' := embed cn Un
    have hf (i j) : ‖f' i-f' j‖^2=‖a i-a j‖^2 := by
      simpa only [one_mul] using
        distance cp Up 1 (by simp [*]) i j
    have hg : ∀ i j,‖g' i-g' j‖^2=(η/(1+η))*‖a i-a j‖^2 :=
      distance cn Un (η/(1+η)) hR2
    have hperm (i) : ∃ σ : Equiv.Perm _,∀ x,g' i (σ x)=f' i x := by
      obtain ⟨σ,hσ⟩ := hperm' i
      refine ⟨e.symm.trans (σ.trans e),?_⟩
      intro x
      simpa [f',g',embed,reindex,Equiv.trans_apply] using hσ (e.symm x)
    have hq : 0<η/(1+η) := by positivity
    clear_value f' g'
    obtain ⟨W,hW⟩ : ∃ W,∀ t : ℕ,1 ≤ t → t ≤ n → Path A W (1/(t:ℝ)) := by
      clear * - a hs ha η δ hη hδ hf hg hperm hq hn n f' g' A
      let ℓ := Fintype.card (τ ⊕ Fin d)
      let f := f'
      let g := g'
      let q := η/(1+η)
      choose σ hσ using hperm
      let H := Equiv.Perm (Fin ℓ)
      let permute (σ : H) := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
      let X := H×Fin s
      let : MulAction H X :=
        { smul := fun h x => (h*x.1,x.2)
          one_smul := by aesop
          mul_smul := by aesop }
      let z : X → FiniteEuclidean := fun x => FiniteEuclidean.embed ℓ (permute x.1 (f x.2))
      have hσ' (i : Fin s) : permute (σ i) (f i)=g i := by
        ext j
        simpa [permute] using (hσ i ((σ i).symm j)).symm
      let fp (i : Fin s) : X := (1,i)
      let fm (i : Fin s) : X := (σ i,i)
      let A := fun i => FiniteEuclidean.embed d (a i)
      have hfcopy (h : H) : CopyPath A 1 (fun i => z (h • (fp i))) := by
        refine ⟨zero_le_one,?_⟩
        intro i j
        change ‖FiniteEuclidean.embed ℓ (permute (h*1) (f i))-
          FiniteEuclidean.embed ℓ (permute (h*1) (f j))‖^2=_
        simp only [mul_one,← map_sub,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map,one_mul]
        simpa only [A,← map_sub,LinearIsometry.norm_map] using hf i j
      have hgcopy (h : H) : CopyPath A q (fun i => z (h • (fm i))) := by
        refine ⟨hq.le,?_⟩
        intro i j
        change ‖FiniteEuclidean.embed ℓ (permute h (permute (σ i) (f i)))-
          FiniteEuclidean.embed ℓ (permute h (permute (σ j) (f j)))‖^2=_
        rw [hσ' i,hσ' j]
        simp only [← map_sub,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]
        simpa only [A,← map_sub,LinearIsometry.norm_map] using hg i j
      let N := AugKernel FiniteEuclidean
      let L := Derived N (s-2)
      let P := unitGraded A
      have hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i := by
        apply derived_subset_single N (s-2) (Fin s) P.monoid P.diagonal
          (unit_pair_inverse A) (unit_pair_coverage A ((FiniteEuclidean.embed d).injective.comp ha))
        simp only [Fintype.card_fin]
        omega
      let c := P.normalCost L hL
      obtain ⟨w,m,hw,hm,hwm⟩ := finite_group_averaging (H:=H) N (s-2)
        c (fun x => FreeGroup.of (z x)) (fun x y => by rfl) δ hδ
      let Dp := fun i => w (fp i)
      let Dm := fun i => w (fm i)
      have hp : Path A Dp (m:ℝ) := by simpa using hw.path z fp 1 hfcopy
      have hmPath := hw.path z fm q hgcopy
      let r  := Dp⁻¹*Dm
      have hrc : ∀ i,r i∈L ∧ c.cost (r i) ≤ δ*m := by
        intro i
        obtain ⟨hmem,hcost⟩ := hwm (fp i) (fm i) (show (σ i,i) ∈ MulAction.orbit H (fp i) from ⟨σ i,by rfl⟩)
        have he : r i=(w (fp i))⁻¹*(w (fp i)*(w (fm i))⁻¹)⁻¹*((w (fp i))⁻¹)⁻¹ := by
          dsimp [r,Dp,Dm]; group
        rw [he]
        refine ⟨(inferInstance : L.Normal).conj_mem _ (L.inv_mem hmem) _,?_⟩
        rw [c.conj _ (L.inv_mem hmem),c.inv _ hmem]
        exact hcost
      obtain ⟨u,v,b,e,hu,hv,he,hbe⟩ := P.bounded_tuple r _
        (fun i => P.singleCost_bounded i (hL i (hrc i).1))
      have heq : Dp*u=Dm*v := by
        have ht := congrArg (fun t => Dp*t*v) he
        simpa [r,mul_assoc] using ht.symm
      have h₁ := hp.mul hu
      have h₂ : Path A (Dp*u) (q*m+e) := by rw [heq]; exact hmPath.mul hv
      let lmb := (m:ℝ)+b
      let μ := q*m+e
      have hlmb : 0 < lmb := by positivity
      have hr : μ/lmb ≤ η/(1+η)+s*δ := by
        apply (div_le_iff₀ hlmb).mpr
        have hc' : (b:ℝ)+e ≤ (s:ℝ)*(δ*m) := by
          calc
            (b:ℝ)+e ≤ ∑ i,(P.singleCost i (r i):ℝ) := by exact_mod_cast hbe
            _ ≤ ∑ i,δ*m := Finset.sum_le_sum (fun i _ =>
              (Nat.cast_le.mpr (P.single_le_maxCost i (r i))).trans (hrc i).2)
            _ = _ := by simp
        have hcd : 0 ≤ (s:ℝ)*δ := by positivity
        dsimp [μ,lmb,q]
        nlinarith
      have hratio : μ/lmb < 1/(n:ℝ) := by
        apply lt_of_le_of_lt hr
        have hq' : η/(1+η)<η := div_lt_self hη (by linarith)
        have he : η+(s:ℝ)*δ=1/n := by
          dsimp [η,δ]
          field_simp
          ring
        rw [← he]
        linarith
      exact synchronize_paths n hn h₁ h₂ hlmb hratio
    obtain ⟨p,Ψ,hgen⟩ := exists_corner_map
    let coloring : Strings → (Fin r) := fun x => coloringInput (FiniteEuclidean.flatten x.toList)
    let L : List β := Finset.univ.toList
    let C : (β → Fin s) → (Fin r) := fun x => (ultraColor coloring ((L.map (fun j => Ψ (W (x j)))).prod)).val
    obtain ⟨line,k,hline⟩ := hHJ C
    let S  := Finset.univ.filter (fun j => line.idxFun j=none)
    let t := S.card
    have ht : 1 ≤ t := by
      apply Finset.card_pos.mpr
      obtain ⟨j,hj⟩ := line.proper
      exact ⟨j,by simp [S,hj]⟩
    have htn := le_trans (Finset.card_le_univ S) (Nat.le_succ _)
    let u j : ℝ := if line.idxFun j=none then 1/(t:ℝ) else 0
    have hcol j : UltraFamily A (fun i => Ψ (W (line i j))) (u j) := by
      cases he : line.idxFun j with
      | none => simpa [u,he,Combinatorics.Line.coe_apply] using (hW t ht htn).ultra Ψ p hgen
      | some i => simpa [u,he,Combinatorics.Line.coe_apply] using UltraFamily.common A (Ψ (W i))
    have hweight : (L.map u).sum=1 := by
      simp only [L,Finset.sum_map_toList,u,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (show t ≠ 0 by omega))
    have hfull : UltraFamily A (fun i => (L.map (fun j => Ψ (W (line i j)))).prod) 1 := by
      convert UltraFamily.list_prod L (fun j i => Ψ (W (line i j))) u (fun j _ => hcol j) using 1
      exact hweight.symm
    have hmem : ∀ i,{x : Strings | coloring x=k} ∈
        ((L.map (fun j => Ψ (W (line i j)))).prod : Ultrafilter Strings) := by
      intro i
      exact hline i ▸ (ultraColor coloring ((L.map (fun j => Ψ (W (line i j)))).prod)).property
    obtain ⟨x,hx,hxB⟩ := hfull (fun _ => {x : Strings | coloring x=k}) hmem
    exact ⟨fun i => FiniteEuclidean.flatten (x i).toList,hx.congruent,k,hxB⟩
  by_contra hbad
  have hc : ∀ n : ℕ,∃ c : EuclideanSpace ℝ (Fin (n+1)) → Fin r,
      ¬ ∃ b : Fin s → EuclideanSpace ℝ (Fin (n+1)),
        Congruent a b ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
    intro n
    by_contra hh
    push Not at hh
    exact hbad ⟨n+1,by omega,hh⟩
  choose c hc using hc
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let C := fun z => (ultraColor
    (fun n => c n (FiniteEuclidean.truncate (n+1) z)) U).val
  obtain ⟨b,hb,k,hbk⟩ := hmono C
  have hcolor : ∀ᶠ n in (U : Filter ℕ),∀ i,c n (FiniteEuclidean.truncate (n+1) (b i))=k := by
    apply Filter.eventually_all.mpr
    intro i
    exact hbk i ▸ (ultraColor (fun n => c n (FiniteEuclidean.truncate (n+1) (b i))) U).property
  have he : ∀ᶠ n in (U : Filter ℕ),∀ i,FiniteEuclidean.embed (n+1)
      (FiniteEuclidean.truncate (n+1) (b i))=b i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Ultrafilter.of_le Filter.atTop) (FiniteEuclidean.eventually_embed_truncate (b i))
  obtain ⟨n,hn,hcol⟩ := (he.and hcolor).exists
  apply hc n
  refine ⟨fun i => FiniteEuclidean.truncate (n+1) (b i),?_,k,hcol⟩
  intro i j
  rw [dist_eq_norm,dist_eq_norm,← (FiniteEuclidean.embed (n+1)).norm_map, map_sub,hn i,hn j,hb,
    ← map_sub,LinearIsometry.norm_map]

end OAI.EuclideanRamsey
