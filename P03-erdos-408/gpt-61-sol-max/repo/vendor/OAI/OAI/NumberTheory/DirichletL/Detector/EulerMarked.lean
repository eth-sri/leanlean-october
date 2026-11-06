module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.EulerFinsupp

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β)  :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β)  :=
  (if a∈T then m a b else 1)*f a b

section
variable (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ) (h0 : ∀a,f a 0=1) (hf : ∀a,Summable (fun b=>‖f a b‖)) (hs : Summable (fun v : α→₀β=>‖v.prod f‖)) (hm : ∀a∈T,∀b,‖m a b‖≤1) (v : α→₀β)


include hTS h0 in
lemma markedArray_finite      
        (hv : v.support⊆S) :
    markedArray T m f v=∏a∈S,markedLocal T m f a (v a) := by
  simp only [markedArray,markedLocal,Finset.prod_mul_distrib]
  congr 1
  · symm
    rw [←Finset.prod_subset hTS]
    · simp_all
    · intro a ha hna
      simp only [ite_eq_right hna]
  · exact Finsupp.prod_of_support_subset v hv _ (fun a _=>h0 a)

include hm in
lemma markedArray_norm_le    
        :
    ‖markedArray T m f v‖≤‖v.prod f‖ := by
  rw [markedArray,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun a ha=>hm a ha _)

include hTS h0 hf hm in
lemma marked_finiteEuler      
       
      :
    (∑'v : {v : α→₀β // (v.support:Set α)⊆S},markedArray T m f v.val)=
      ∏a∈S,∑'b,markedLocal T m f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      markedArray T m f v.val=∏a:S,markedLocal T m f a.val (e v a) := by
    rw [markedArray_finite T S hTS m f h0 v.val v.property]
    exact (Finset.prod_coe_sort S _).symm
  have hg (a : α) : Summable (fun b=>‖markedLocal T m f a b‖) := by
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (hf a)
    intro b
    rw [markedLocal,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    split_ifs with ha
    · exact hm a ha b
    · simp
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏a:S,markedLocal T m f a.val (v a))]
  rw [(finitePi (fun a:S=>markedLocal T m f a.val) (fun a=>hg a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑'b,markedLocal T m f a b)

include h0 hs hm in
theorem marked_hasProd      
     
      :
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
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact markedArray_norm_le T m f hm v
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  change Tendsto (fun S : Finset α=>∏a∈S,∑'b,markedLocal T m f a b) atTop _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with S hTS
  rw [←marked_finiteEuler T S hTS m f h0 hf hm]
  trans ∑'v : α→₀β,{v : α→₀β | (v.support:Set α)⊆S}.indicator (markedArray T m f) v
  · simp_all [Set.indicator]
  · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (markedArray T m f)).symm

end

end SevenEighths.ProbeEulerFinsupp
end

end OAI
