module

public import OAI.NumberTheory.DirichletL.Detector.EulerFinsupp

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β) : ℂ :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β) : ℂ :=
  (if a∈T then m a b else 1)*f a b

lemma markedArray_finite (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (v : α→₀β) (hv : v.support⊆S) :
    markedArray T m f v=∏a∈S,markedLocal T m f a (v a) := by
  simp only [markedArray,markedLocal,Finset.prod_mul_distrib]
  congr 1
  · symm
    rw [←Finset.prod_subset hTS]
    · simp
    simp_all
  · exact Finsupp.prod_of_support_subset v hv _ (by grind)

lemma markedArray_norm_le (T : Finset α) (m f : α→β→ℂ)
    (hm : ∀a∈T,∀b,‖m a b‖≤1) (v : α→₀β) :
    ‖markedArray T m f v‖≤‖v.prod f‖ := by
  rw [markedArray,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (by simp) (by grind)

lemma marked_finiteEuler (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (hf : ∀a,Summable (fun b=>‖f a b‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    (∑'v : {v : α→₀β // (v.support:Set α)⊆S},markedArray T m f v.val)=
      ∏a∈S,∑'b,markedLocal T m f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      markedArray T m f v.val=∏a:S,markedLocal T m f a.val (e v a) := by
    rw [markedArray_finite T S hTS m f h0 v.val v.property]
    exact (Finset.prod_coe_sort S _).symm
  have hg (a : α) : Summable (fun b=>‖markedLocal T m f a b‖) := by
    apply Summable.of_nonneg_of_le (by simp) _ (hf a)
    intro b
    rw [markedLocal,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    split_ifs with ha
    · simp_all
    · simp
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏a:S,markedLocal T m f a.val (v a))]
  rw [(finitePi (fun a:S=>markedLocal T m f a.val) (fun a=>hg a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑'b,markedLocal T m f a b)

theorem marked_hasProd (T : Finset α) (m f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    HasProd (fun a=>∑'b,markedLocal T m f a b) (∑'v : α→₀β,markedArray T m f v) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑'v : α→₀β,
      if v.support⊆S then markedArray T m f v else 0) atTop
      (𝓝 (∑'v : α→₀β,markedArray T m f v)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp_all
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact markedArray_norm_le T m f hm v
      simp
  change Tendsto (fun S : Finset α=>∏a∈S,∑'b,markedLocal T m f a b) atTop _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with S hTS
  rw [←marked_finiteEuler T S hTS m f h0 hf hm]
  trans ∑'v : α→₀β,{v : α→₀β | (v.support:Set α)⊆S}.indicator (markedArray T m f) v
  · apply tsum_congr
    intro v
    simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
  · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (markedArray T m f)).symm

end SevenEighths.ProbeEulerFinsupp
end

end OAI
