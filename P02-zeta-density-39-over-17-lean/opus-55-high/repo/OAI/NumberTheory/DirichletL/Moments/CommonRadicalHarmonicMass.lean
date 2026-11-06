module
public import OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonRadicalHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentWholeDivisorShell CenteredMomentDyadicCount CenteredMomentSectorLocalization
open CenteredMomentCommonHarmonicMass (Label Valid commonRadical_norm_le norm_scale_bounds log_square_subpower)
local notation "O" => ActualEisensteinCubic.O

def weight (v : Label) : ℝ := 1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)
def key (v : Label) : ℤ := normKey (commonRadical v.1.1 v.1.2)
def keys (S : Finset Label) : Finset ℤ := S.image key
def shell (S : Finset Label) (n : ℤ) : Finset Label := S.filter (fun v=>key v=n)

lemma radical_ne_zero (v : Label) : commonRadical v.1.1 v.1.2≠0 :=
  Squarefree.ne_zero (commonRadical_squarefree _ _)

lemma shell_scalar (e Y T : ℝ) (he : 0<e) (hT : 0<T) (hTY : T≤Y) :
    (2*T)^(1+e)/T≤2^(1+e)*Y^e := by
  pm_7071 hT.le hT
  calc
    _ = 2^(1+e)*T^e := by field_simp
    _ ≤ 2^(1+e)*Y^e := by gcongr

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) → ∀Y T : ℝ,0<T → T≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
        (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*T) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  pm_2944
  intro s hs hs0 S hS Y T hT hTY hN hshell
  have hY : 0<Y := hT.trans_le hTY
  pm_2943
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*T) hY hY (by positivity) hN
    (fun v hv=>(hshell v hv).2.le)
  calc
    _ ≤ ∑_v∈S,1/T := by
      apply Finset.sum_le_sum
      intro v hv
      exact one_div_le_one_div_of_le hT (hshell v hv).1
    _ = (S.card:ℝ)/T := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*T)^(1+e)/(s.absNorm:ℝ))/T :=
      div_le_div_of_nonneg_right hc hT.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*T)^(1+e)/T) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T he hT hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      pm_1546

lemma shell_norm_bounds (S : Finset Label) (n : ℤ) (v : Label) (hv : v∈shell S n) :
    dyadicScale n≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
    (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*dyadicScale n := by
  exact (normKey_eq_iff _ (radical_ne_zero v) n).mp (Finset.mem_filter.mp hv).2

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v :=
  (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z ^B ∧ (v.1.2.absNorm:ℝ)≤Z ^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  pm_242 hY Z B hZ hB
  have hsub : keys S ⊆ indices 1 (Z ^B) := by
    pm_67 n hn v hv Finset.mem_image.mp
    have hr := (commonRadical_norm_le _ _ (h0 v hv).1 (h0 v hv).2).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z ^B) hr
    exact (mem_indices_iff_scale 1 (Z ^B) (by norm_num) (by positivity) _).mpr
      ⟨hc.1,hc.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z ^B)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hi := indices_card_log_bound 1 B Z 1 (Z ^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  exact hc.trans hi

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z ^B ∧ (v.1.2.absNorm:ℝ)≤Z ^B) →
      (∑v∈S,weight v)≤C*Z ^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
  pm_2946
  refine ⟨C*K,by positivity,?_⟩
  pm_6252
  pm_2943
  have hb (n : ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z ^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z ^B) hr
    have hm : dyadicScale n≤Z ^B := by
      exact hkey ▸ hc.2
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z ^B) (dyadicScale n) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z ^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z ^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K*(1+Real.log Z))*(C*(Z ^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K)*Z ^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
      pm_1278

theorem common_radical_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z ^B ∧ (v.1.2.absNorm:ℝ)≤Z ^B) →
      (∑v∈S,1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ))≤C*Z ^δ/(s.absNorm:ℝ) := by
  pm_2948
  have hl : 1+Real.log Z≤D *Z ^(δ/2) := by
    have hn := Real.log_nonneg hZ1
    exact (show 1+Real.log Z≤(1+Real.log Z)^2 by nlinarith).trans (hlog Z hZ1)
  calc
    _ ≤ C*Z ^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z ^(3*B*e)*(D *Z ^(δ/2))/(s.absNorm:ℝ) := by gcongr
    _ = (C*D)*Z ^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z ^δ/(s.absNorm:ℝ) := by
      pm_6454

end SevenEighths.CenteredMomentCommonRadicalHarmonicMass

end

end OAI
