module

public import Erdos821.Blueprint.Classical
public import PrimeNumberTheoremAnd.Erdos970.MertensClassical

@[expose] public section

open Filter Asymptotics

namespace Erdos821.P1

private noncomputable def primeRecipSum (y : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 : ℝ) / (p : ℝ)

private noncomputable def primeProd (y : ℝ) : ℝ :=
  ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 - (1 : ℝ) / (p : ℝ))

private theorem primesUpTo_eq (y : ℝ) :
    Erdos821.Blueprint.primesUpTo y = (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
  ext p
  simp only [Erdos821.Blueprint.primesUpTo, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc]
  grind

private theorem primeRecipSum_eq (y : ℝ) :
    (∑ p ∈ Erdos821.Blueprint.primesUpTo y, (p : ℝ)⁻¹) = primeRecipSum y := by
  rw [primeRecipSum, ← primesUpTo_eq]
  simp

private theorem sieveProduct_eq (y : ℝ) :
    Erdos821.Blueprint.sieveProduct y = primeProd y := by
  rw [Erdos821.Blueprint.sieveProduct, primeProd, primesUpTo_eq]
  simp

theorem mertens_proof : Erdos821.Blueprint.MertensEstimates := by
  constructor
  · obtain ⟨K, hK⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
    refine ⟨K, fun y hy => ?_⟩
    rw [primeRecipSum_eq]
    exact hK y hy
  · have hthird : (fun y : ℝ => primeProd y) ~[atTop]
        (fun y => Real.exp (-Real.eulerMascheroniConstant) / Real.log y) := by
      simpa only [primeProd] using Erdos970.Mertens.E₃.bound''
    have hthird' : (fun y : ℝ => Erdos821.Blueprint.sieveProduct y) ~[atTop]
        (fun y => Real.exp (-Real.eulerMascheroniConstant) / Real.log y) :=
      hthird.congr_left (Filter.Eventually.of_forall fun y => (sieveProduct_eq y).symm)
    have hlog : (fun y : ℝ => Real.log y) ~[atTop] fun y => Real.log y := IsEquivalent.refl
    have hmul : (fun y : ℝ => Real.log y * Erdos821.Blueprint.sieveProduct y) ~[atTop]
        (fun y => Real.log y * (Real.exp (-Real.eulerMascheroniConstant) / Real.log y)) :=
      hlog.mul hthird'
    have hcancel : (fun y : ℝ => Real.log y *
        (Real.exp (-Real.eulerMascheroniConstant) / Real.log y)) =ᶠ[atTop]
        (fun _ => Real.exp (-Real.eulerMascheroniConstant)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      have hlog := (Real.log_pos hy).ne'
      calc
        Real.log y * (Real.exp (-Real.eulerMascheroniConstant) / Real.log y) =
            Real.exp (-Real.eulerMascheroniConstant) * (Real.log y / Real.log y) := by ring
        _ = Real.exp (-Real.eulerMascheroniConstant) := by simp_all
    have hlim : Tendsto (fun y : ℝ => Real.log y *
        (Real.exp (-Real.eulerMascheroniConstant) / Real.log y)) atTop
        (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
      (tendsto_congr' hcancel).2 tendsto_const_nhds
    exact hmul.symm.tendsto_nhds hlim

end Erdos821.P1
