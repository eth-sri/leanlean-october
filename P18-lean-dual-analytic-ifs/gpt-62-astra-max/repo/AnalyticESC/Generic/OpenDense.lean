module
public import AnalyticESC.Generic.Density
public import AnalyticESC.Generic.Interior
public import AnalyticESC.Main.Dichotomy

@[expose] public section
namespace AnalyticESC
open Set Metric
variable {N : ℕ}

/-- Contains a relatively `C²`-open dense subset of the union class. -/
def Generic (P : Maps N → Prop) := ∃ U : Set (Maps N), (∀ f ∈ U, InUnionClass f ∧ P f) ∧
  (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
  (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r)

/-- Project an open dense region of bundled systems back to the union class. -/
lemma generic_region {P : Maps N → Prop} {U : Set (IFS N)} (ho : IsOpen U) (hd : Dense U)
    (h : ∀ Φ ∈ U, P Φ.f) : Generic P := by
  refine ⟨IFS.f '' U,?_,?_,?_⟩
  · rintro _ ⟨Φ,hΦ,rfl⟩; exact ⟨⟨Φ.ε,Φ.ε_pos,Φ.inClass⟩,h Φ hΦ⟩
  · rintro _ ⟨Φ,hΦ,rfl⟩
    obtain ⟨r,hr,sub⟩ := Metric.isOpen_iff.mp ho Φ hΦ
    refine ⟨r,hr,fun g ⟨ε,hε,hg⟩ d => ⟨⟨g,hε,hg⟩,sub (mem_ball'.mpr ?_),rfl⟩⟩
    rwa [IFS.dist_eq_d2]
  · rintro f ⟨ε,hε,hf⟩ r hr
    obtain ⟨Ψ,hΨ,u⟩ := Metric.dense_iff.mp hd (⟨f,hε,hf⟩ : IFS N) r hr
    exact ⟨Ψ.f,mem_image_of_mem _ u,(IFS.dist_eq_d2 ⟨f,hε,hf⟩ Ψ) ▸ mem_ball'.mp hΨ⟩

lemma sesc_region (N : ℕ) : ∃ U : Set (IFS N), IsOpen U ∧ Dense U ∧ ∀ Φ ∈ U, Φ.SESC := by
  let U (p : {p : Fin N × Fin N // p.1 ≠ p.2}) := IFS.Good p.val.1 p.val.2
  have ho p : IsOpen (U p) := IFS.good_open ..
  have hd p : Dense (U p) := IFS.good_dense p.2
  refine ⟨⋂ p, U p,isOpen_iInter_of_finite ho,sInter_range U ▸ (finite_range U).dense_sInter (forall_mem_range.mpr ho) (forall_mem_range.mpr hd),?_⟩
  intro Φ h; apply Φ.sesc_of_separated; intro i j hij
  have H := mem_iInter.mp h ⟨(i 0,j 0),hij⟩
  exact fun e => H ⟨(i,j),rfl,rfl,e⟩

theorem theorem_1_4 (N : ℕ) : Generic (@Challenge.SESC N) := by
  obtain ⟨U,ho,hd,h⟩ := sesc_region N; exact generic_region ho hd h

end AnalyticESC
