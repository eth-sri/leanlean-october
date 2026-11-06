module

public import NearlyMinimax.FinePairFactorialEnergy
public import NearlyMinimax.LowerAliasScale


@[expose] public section

/-! The actual fine-pair alias cutoff loses a fixed exp(L M), which is
absorbed into the factorial-tail constant before the saddle shift is chosen. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem fine_pair_alias_cutoff_inverse {d : ℕ} (hd : 4 ≤ d)
    {N ell c0 D } (hN : 0 < N) (hell : ell=N*Real.exp (-c0*D)) :
    1/ell^(d-4) = N^(4-(d : ℝ))*Real.exp (c0*D*(d-4)) := by
  have hnat : ((d-4 : ℕ) : ℝ) = (d : ℝ)-4 := by
    simp_all
  have hpow : N^(4-(d : ℝ)) = (N^(d-4))⁻¹ := by
    rw [show (4 : ℝ)-d = -((d : ℝ)-4) by ring, Real.rpow_neg hN.le,
      ← hnat, Real.rpow_natCast]
  rw [hell, mul_pow, ← Real.exp_nat_mul, hpow, one_div, mul_inv_rev, ← Real.exp_neg,
    mul_comm (Real.exp _)]
  
  rw [hnat]
  ring

def finePairSaddleAliasExponent (d : ℕ) c0 K  :=
  2*c0+c0*K*((d : ℝ)-4)

theorem fine_pair_alias_cutoff_scale_le {d M : ℕ} (hd : 4 ≤ d)
    {N ell tau c0 D K } (hN : 0 < N) (hell : ell=N*Real.exp (-c0*D))
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (htau : tau ≤ c0) (hD : D ≤ K*M) :
    Real.exp (2*tau*M)/ell^(d-4) ≤
      N^(4-(d : ℝ))*Real.exp (finePairSaddleAliasExponent d c0 K*M) := by
  rw [div_eq_mul_inv, ← one_div, fine_pair_alias_cutoff_inverse hd hN hell]
  rw [← mul_assoc, mul_comm (Real.exp _) (N^_), mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
  apply Real.exp_le_exp.mpr
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hT := mul_le_mul_of_nonneg_right htau (by positivity : 0 ≤ (2 : ℝ)*M)
  have hDK := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ c0*((d : ℝ)-4))
  unfold finePairSaddleAliasExponent
  nlinarith only [hT,hDK]

def finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs  :=
  aliasTailConstant
    (finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d)
    Cs (finePairAliasGeometricBase d bD*2^8) (finePairSaddleAliasExponent d c0 K)

theorem finite_fine_pair_saddle_alias_budget_le {d } (hd : 4 ≤ d)
    {aD bD ad bd c0 K : ℝ} (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M D q J : ℕ)
    C a rho eta ell N Cs mu (hN : 0 < N)
    (hell : ell=N*Real.exp (-c0*D)) (hD : D ≤ K*M)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Cs*mu) (M+1+j) *
      finePairAliasActionSpatialBudget d (M+1+j) M q ad bd C a rho eta ell) ≤
      finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs *
        (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs*mu) (M+1) := by
  have hellpos : 0 < ell := by rw [hell]; positivity
  let A := finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d
  have hA : 0 ≤ A := by
    
    positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0,
      spatialInverseFourConstant_nonneg d]
  have hBase  := finePairAliasGeometricBase_nonneg d bD
  have hL : 0 ≤ finePairSaddleAliasExponent d c0 K := by
    unfold finePairSaddleAliasExponent
    have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  
  apply finite_alias_energy_tail_le hA (by positivity : 0 ≤ eta^4*N^(4-(d : ℝ))) hCs
    (by positivity) hL
    hmu hmu1 M J (fun n => finePairAliasActionSpatialBudget d n M q ad bd C a rho eta ell)
  intro j _
  let n := M+1+j
  have h := finePairAliasActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d n M q C a rho eta ell hellpos
  have hs := fine_pair_alias_cutoff_scale_le hd hN hell hc0 hK htau hD
  have hp := polynomial_count_factor_le n 8
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ A*finePairAliasGeometricBase d bD^n*(n : ℝ)^8*eta^4)
  have hm' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ A*finePairAliasGeometricBase d bD^n*eta^4*N^(4-(d : ℝ))*
      Real.exp (finePairSaddleAliasExponent d c0 K*M))
  apply h.trans
  calc
    _ ≤ A*finePairAliasGeometricBase d bD^n*(n : ℝ)^8*eta^4 *
        (N^(4-(d : ℝ))*Real.exp (finePairSaddleAliasExponent d c0 K*M)) := by
      convert hm using 1 <;> dsimp [A] <;> ring
    _ ≤ A*(eta^4*N^(4-(d : ℝ)))*Real.exp (finePairSaddleAliasExponent d c0 K*M)*
        (finePairAliasGeometricBase d bD*2^8)^n := by
      convert hm' using 1 <;> (skip) <;> ring

end NearlyMinimax
