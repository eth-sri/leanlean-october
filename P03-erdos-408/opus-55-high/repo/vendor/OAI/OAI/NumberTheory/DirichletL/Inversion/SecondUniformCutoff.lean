module

public import OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale
public import OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
public import OAI.NumberTheory.DirichletL.Descent.ActualChildStateRadius
public import OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseSecondUniformCutoff
open FirstPassCubeLabels
open InverseMoment InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)

def uniformSecondRadius {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ) : ℝ :=
  Z^(delta+eta)*(primeProductNorm p E/primeProductNorm p G)^2*L^2*H/Y

lemma uniformSecondRadius_nonneg {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ)
    (hZ : 0≤Z) (hY : 0≤Y) (hH : 0≤H) :
    0≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold uniformSecondRadius
  positivity

theorem correlated_le_uniform {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O)
    (Z delta eta : ℝ) (d : ActualEisensteinCubic.O) (G E : Finset ι) (L Y H : ℝ)
    (hY : 0<Y) (hH : 0≤H) (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta)) :
    correlatedSecondRadius p d G E L Y H≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold correlatedSecondRadius uniformSecondRadius
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (sq_nonneg _)) (sq_nonneg _)) hH) hY.le

theorem uniform_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z delta theta g s Hc eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(s+4*eta)) :
    uniformSecondRadius p Z delta eta G E L (Z^(Hc+12*eta+tau)) (Z^tau)≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G≤Z^(theta-g+2*eta) := by
    calc
      _≤Z^(theta+eta)/Z^(g-eta):=div_le_div₀
        (by positivity) hE (by positivity) hG
      _= _:=by rw [←Real.rpow_sub hZ];ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _≤Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*Z^tau/Z^(Hc+12*eta+tau):=by
      unfold uniformSecondRadius
      gcongr
    _= _:=by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      ring

theorem uniform_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z M r ell V delta A B j t g theta eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(r-A-B-t+4*eta)) :
    uniformSecondRadius p Z delta eta G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb:=uniform_radius_bound p hp G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hE hG hL
  convert hb using 1
  congr 1
  unfold childM decrease firstPhysicalHeight
  ring

theorem actual_cell_uniform_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs:=cell_subset p source d hx
  have hE:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr:=uniform_radius_childM p hp x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 (by simpa) (by simpa) hL
  have hb:=(mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp (hgate x hxs)
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

end SevenEighths.InverseSecondUniformCutoff
end

end OAI
