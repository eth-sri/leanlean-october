module

public import OAI.NumberTheory.DirichletL.Detector.LowInverseEnergy
public import OAI.NumberTheory.DirichletL.Detector.LowActualEnergies

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcretePrimeRowBridge
local notation "Id" => Ideal ActualEisensteinCubic.O
local instance : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowElementRowPoint (m : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ×Id :=
  (InitialMeanSquare.sourceLabelUnit m,Ideal.span {m})

def lowIdealRowElement (p : ActualEisensteinCubic.Oˣ×Id) : ActualEisensteinCubic.O := p.1.val*idealGenerator p.2

lemma lowIdealRowElement_point (m : ActualEisensteinCubic.O) : lowIdealRowElement (lowElementRowPoint m)=m :=
  (InitialMeanSquare.sourceLabelUnit_spec m).symm

lemma lowElementRowPoint_injective : Function.Injective lowElementRowPoint :=
  Function.LeftInverse.injective lowIdealRowElement_point

def lowIdealRows (R : Finset ActualEisensteinCubic.O) : Finset Id := R.image (fun m=>Ideal.span {m})

lemma lowIdealRows_nonzero (R : Finset ActualEisensteinCubic.O) (hR : ∀m∈R,m≠0) (I : Id) (hI : I∈lowIdealRows R) : I≠0 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact Ideal.span_singleton_eq_bot.not.mpr (by grind)

lemma lowIdealRows_norm_bound (R : Finset ActualEisensteinCubic.O) (Q : ℝ) (hR : ∀m∈R,elementNorm m≤Q)
    (I : Id) (hI : I∈lowIdealRows R) : (Ideal.absNorm I:ℝ)≤Q := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact hR m hm

theorem low_element_energy_le_units (R : Finset ActualEisensteinCubic.O) (_hR : ∀m∈R,m≠0) (F : ActualEisensteinCubic.O→ℂ) :
    (∑m∈R,‖F m‖^2)≤∑u : ActualEisensteinCubic.Oˣ,∑I∈lowIdealRows R,‖F (u.val*idealGenerator I)‖^2 := by
  let P : Finset (ActualEisensteinCubic.Oˣ×Id) := Finset.univ×ˢlowIdealRows R
  have hsub : R.image lowElementRowPoint⊆P := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨m,hm,rfl⟩⟩
  have he : (∑m∈R,‖F m‖^2)=∑p∈R.image lowElementRowPoint,‖F (lowIdealRowElement p)‖^2 := by
    rw [Finset.sum_image (fun m _ n _ h=>lowElementRowPoint_injective h)]
    simp only [lowIdealRowElement_point]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _=>sq_nonneg ‖F (lowIdealRowElement p)‖)
  simpa only [P,Finset.sum_product,lowIdealRowElement] using hh

lemma low_rowTwist_label_one (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) (I : Id) :
    CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)=
      CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id))
        (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I) := by
  have he : (InitialMeanSquare.sourceLabelUnit (1:ActualEisensteinCubic.O)).val*idealGenerator (1:Id)=1 := by
    simpa only [Ideal.span_singleton_one,Ideal.one_eq_top] using (InitialMeanSquare.sourceLabelUnit_spec (1:ActualEisensteinCubic.O)).symm
  have harg : m^6*(idealGenerator (1:Id))^4*
      (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I)=m^6*1^4*(u.val*idealGenerator I) := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,one_pow]
    calc
      _=m^6*((InitialMeanSquare.sourceLabelUnit (1:ActualEisensteinCubic.O)).val*idealGenerator (1:Id))^4*(u.val*idealGenerator I) := by ring
      _=_ := by simp_all
  unfold CanonicalRowCompletion.rowTwist
  simp_all

lemma low_units_label_one_sum (F : (ActualEisensteinCubic.O→*ℂ)→ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (I : Id) :
    (∑u : ActualEisensteinCubic.Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)))=
      ∑u : ActualEisensteinCubic.Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)) := by
  simp_rw [low_rowTwist_label_one]
  exact Equiv.sum_comp (Equiv.mulLeft ((InitialMeanSquare.sourceLabelUnit (1:ActualEisensteinCubic.O))^4))
    (fun u : ActualEisensteinCubic.Oˣ=>F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)))

lemma low_element_rowTwist_energy (R : Finset ActualEisensteinCubic.O) (hR : ∀z∈R,z≠0)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (F : (ActualEisensteinCubic.O→*ℂ)→ℂ) :
    (∑z∈R,‖F (CanonicalRowCompletion.rowTwist Ψ m 1 z)‖^2)≤
      ∑u : ActualEisensteinCubic.Oˣ,∑I∈lowIdealRows R,
        ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2 := by
  apply (low_element_energy_le_units R hR (fun z=>F (CanonicalRowCompletion.rowTwist Ψ m 1 z))).trans_eq
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun (u : ActualEisensteinCubic.Oˣ) (I : Id)=>
    ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2)]
  apply Finset.sum_congr rfl
  intro I hI
  exact low_units_label_one_sum (fun Ψ=>‖F Ψ‖^2) Ψ m I

lemma lowNumeratorRows_nonzero (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : ActualEisensteinCubic.O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : z≠0 := by
  intro he
  have hh := (lowNumeratorRows_mem a b ha hb Q hQ z).mp hz
  rw [he,elementNorm,Ideal.span_singleton_zero,Ideal.absNorm_bot,Nat.cast_zero,zero_div] at hh
  exact hh (lowOuterCutoff_small a b ha 0 (by positivity))

lemma lowNumeratorRows_norm_bound (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : ActualEisensteinCubic.O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : elementNorm z≤2*b*Q := by
  have hh := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ z).mp hz)).2
  exact (div_le_iff₀ hQ).mp hh

lemma low_unit_card : Fintype.card ActualEisensteinCubic.Oˣ=6 := by
  simpa using PrimaryIdealUnitReindex.card_units_eq_six

end SevenEighths.ProbePhysical
end

end OAI
