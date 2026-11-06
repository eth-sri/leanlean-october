module
import Mathlib
public import OAI.NumberTheory.DirichletL.Descent.ShortReflectedPower
public import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CanonicalRowCompletion

open scoped EisensteinEis
lemma normalization_norm_sq (Z N V : ℝ) (hZ : 0<Z) (x : ℂ) :
    ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*x‖^2 =
      Z^(-V)*‖x‖^2 := by
  have hn : 0≤Z^(-(N+V)/2) := Real.rpow_nonneg hZ.le _
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg hn,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,mul_pow,
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),←Real.rpow_mul_natCast hZ.le _ 2,
    ←Real.rpow_add hZ]
  congr 2
  norm_num

lemma divisor_weight_sum (K : ℕ) (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z V : ℝ),1≤Z → 0≤V → V≤L →
      ∀ labels : Finset (Ideal Eis),
      (∀ f∈labels,f≠0 ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
      (∑ f∈labels,((idealDivisors f).card:ℝ)^(9+4*K))≤C*Z^(V+ε) := by
  let n := 9+4*K
  have hn : (0:ℝ)<n := by dsimp [n]; positivity
  let δ := ε/((L+1)*(n:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*D^n,by positivity,?_⟩
  intro Z V hZ hV hVL labels hf
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hbudget : L*(δ*(n:ℝ))≤ε := by
    have heq : (L+1)*(δ*(n:ℝ))=ε := by dsimp [δ]; field_simp
    nlinarith [mul_pos hδ hn]
  have hb (f : Ideal Eis) (hfl : f∈labels) :
      ((idealDivisors f).card:ℝ)^n≤D^n*Z^ε := by
    have hfN : (Ideal.absNorm f:ℝ)≤Z^L :=
      (hf f hfl).2.trans (Real.rpow_le_rpow_of_exponent_le hZ hVL)
    calc
      _ ≤ (D*(Ideal.absNorm f:ℝ)^δ)^n := by gcongr; exact hd f (hf f hfl).1
      _ = D^n*(Ideal.absNorm f:ℝ)^(δ*(n:ℝ)) := by
        rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      _ ≤ D^n*(Z^L)^(δ*(n:ℝ)) := by gcongr
      _ = D^n*Z^(L*(δ*(n:ℝ))) := by rw [←Real.rpow_mul hz.le]
      _ ≤ _ := by gcongr
  have hc := DescentFiberCost.finite_ideal_count_real labels (Z^V)
    (Real.one_le_rpow hZ hV) (fun f hfl => (hf f hfl).1) (fun f hfl => (hf f hfl).2)
  calc
    _ ≤ ∑ _f∈labels,D^n*Z^ε := Finset.sum_le_sum (fun f hfl => hb f hfl)
    _ = (labels.card:ℝ)*(D^n*Z^ε) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (128*Z^V)*(D^n*Z^ε) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (128*D^n)*Z^(V+ε) := by rw [Real.rpow_add hz]; ring

lemma rowTwist_label_transfer (Ψ : Eis→*ℂ) (m a f k : Eis) :
    CanonicalRowCompletion.rowTwist Ψ m (a*f) k =
      CanonicalRowCompletion.rowTwist Ψ m f (a^4*k) := by
  have he : m^6*(a*f)^4*k=m^6*f^4*(a^4*k) := by ring
  unfold CanonicalRowCompletion.rowTwist
  rw [he]

lemma label_eq_rowUnit_generator (f : Ideal Eis) (hf : f≠0) (g : Eis)
    (hg : Ideal.span {g}=f) :
    g=(CompletedUnitRows.rowUnit g).val*ConcretePrimeRowBridge.idealGenerator f := by
  have hgn : g≠0 := by
    intro he
    apply hf
    rw [←hg,he,Ideal.span_singleton_zero]
    rfl
  have hh := CompletedUnitRows.rowUnit_spec g hgn
  rw [hg] at hh
  exact hh.symm

local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe v






