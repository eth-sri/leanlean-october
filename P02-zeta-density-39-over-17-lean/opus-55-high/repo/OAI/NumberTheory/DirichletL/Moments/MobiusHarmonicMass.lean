module
public import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
public import OAI.NumberTheory.DirichletL.Moments.DivisorBoundary
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentMobiusHarmonicMass
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentDivisorBoundary CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma shell_mass (Ds:Finset (Ideal O)) (n:ℤ) (hn:n∈selectedShells Ds) :
    (∑D∈shell Ds n,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤256 := by
  have ht:1≤dyadicScale n:=
    (selected_scale_bounds Ds (∑D∈Ds,(Ideal.absNorm D:ℝ))
      (fun D hD _=>Finset.single_le_sum (fun D _=>Nat.cast_nonneg _) hD) n hn).1
  have htp:0<dyadicScale n:=zero_lt_one.trans_le ht
  have hcard:=divisor_dyad_card (shell Ds n) (dyadicScale n) ht
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.1)
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.2)
  calc
    _≤∑D∈shell Ds n,1/dyadicScale n:=by
      apply Finset.sum_le_sum
      intro D hd
      have hh:=(shell_member_data Ds n D hd).2.2.2.2.1
      exact div_le_div₀ (by norm_num) (moebius_norm_le_one D) htp hh
    _=((shell Ds n).card:ℝ)/dyadicScale n:=by aesop
    _≤256:=(div_le_iff₀ htp).mpr hcard

 theorem full_mass_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (Ideal.absNorm D:ℝ)≤Z ^B) →
      (∑D∈Ds,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z ^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower B δ hB hδ
  refine ⟨256*C,by positivity,?_⟩
  pm_168 hbound
  intro Ds hn
  have he:=sum_norm_moebius_shells Ds (fun D =>1/(Ideal.absNorm D:ℝ))
  simp only [mul_one_div] at he
  rw [he]
  calc
    _≤∑n∈selectedShells Ds,(256:ℝ):=Finset.sum_le_sum (fun n hn=>shell_mass Ds n hn)
    _=((selectedShells Ds).card:ℝ)*256:=by simp
    _≤(C*Z ^δ)*256:=mul_le_mul_of_nonneg_right (hZ.2 Ds hn) (by norm_num)
    _=_:=by ring

end SevenEighths.CenteredMomentMobiusHarmonicMass

end

end OAI
