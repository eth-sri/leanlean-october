module

public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

def scaleSupport (upper b : ℝ)  := idealsUpTo ⌈Real.exp upper*b⌉₊

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

section
variable {ι : Type*} (rows : Finset ι) (χ : ι→Character) (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi)
include ι rows χ W a b hb hWs hW lo hi E hlh

theorem rowwise_scales      
           
          (l : ι→ℝ)
    (hl : ∀ i∈rows, l i∈Icc lo hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp (l i)) 0 0‖^2≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hsp := scaleProfile_support W a b hWs
  have eq0 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) W S t (scaleSupport_cover W a b hi t hb hWs ht.2)
  have eq1 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) (scaleProfile W) S t
      (scaleSupport_cover (scaleProfile W) a b hi t hb hsp ht.2)
  have hh := rowwise_energy rows (fun i => scaleSum (χ i) W S)
    (fun i => scaleSum (χ i) (scaleProfile W) S)
    (fun i hi => scaleSum_continuous (χ i) W S hW.continuous)
    (fun i hi => scaleSum_continuous (χ i) (scaleProfile W) S (scaleProfile_continuous W hW))
    (fun i hi t => scaleSum_deriv (χ i) W S (hW.differentiable (by simp)) t)
    lo hi E hlh l hl
    (fun t ht => by simpa only [eq0 _ t ht] using h0 t ht)
    (fun t ht => by simpa only [eq1 _ t ht] using h1 t ht)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [eq0 i (l i) (hl i hi)]

theorem exists_scale_majorant      
           
         
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∃ B : ι→ℝ, (∀ i, 0≤B i) ∧
      (∀ i, ∀ t∈Icc lo hi, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤B i) ∧
      (∑ i∈rows, B i)≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hm (i : ι) : ∃ t∈Icc lo hi, ∀ u∈Icc lo hi,
      ‖scaleSum (χ i) W S u‖^2≤‖scaleSum (χ i) W S t‖^2 := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlh)
      ((scaleSum_continuous (χ i) W S hW.continuous).norm.pow 2).continuousOn
  choose t ht hmax using hm
  refine ⟨fun i => ‖polynomial (χ i) true W (Real.exp (t i)) 0 0‖^2,
    fun i => sq_nonneg _,?_,?_⟩
  · intro i u hu
    have hh := hmax i u hu
    rw [scaleSum_eq_polynomial (χ i) W S u (scaleSupport_cover W a b hi u hb hWs hu.2),
      scaleSum_eq_polynomial (χ i) W S (t i) (scaleSupport_cover W a b hi (t i) hb hWs (ht i).2)] at hh
    exact hh
  · exact rowwise_scales rows χ W a b hb hWs hW lo hi E hlh t (fun i hi => ht i) h0 h1

end

end SevenEighths.HeckeInverseAmplification

end

end OAI
