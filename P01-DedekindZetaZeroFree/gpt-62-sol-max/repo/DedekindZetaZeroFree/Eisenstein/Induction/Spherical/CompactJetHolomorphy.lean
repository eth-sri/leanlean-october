module

public import DedekindZetaZeroFree.Eisenstein.Sections.SmoothIwasawaLogNorm
public import DedekindZetaZeroFree.Adeles.Quotients.CompactOpenFiniteLevels

public import DedekindZetaZeroFree.Analysis.Calculus.ParameterJets

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
open scoped Classical NumberField NNReal

namespace DedekindZetaZeroFree.KPContFlatStageJetHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev JetSpace (n : ℕ) :=
  ContinuousMultilinearMap ℝ
    (fun _ : Fin n => KPGlobalTorusBorelTwistCompatibility.GroupArch F) ℂ

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [hfd : FiniteDimensional ℂ S]
  (ι : S →ₗ[ℂ] KPMsRationalCompactCrossPairing.Vplus F ζ hζ
    (KPContFlatSourceRecipe.D F ζ hζ))

def L (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v)).val g

def spatialJet (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (s : ℂ) (v : S) : KPGlobalTorusBorelTwistCompatibility.GroupArch F → JetSpace F n :=
  iteratedFDerivWithin ℝ n
    (fun z => L F ζ hζ ι s v
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)

def parameterSection (m : ℕ) (s : ℂ) (v : S)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ) ^ m * L F ζ hζ ι s v g


open ParameterJets

 lemma L_formula (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    L F ζ hζ ι s v g =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * (ι v).val.val g := by
  unfold L
  rw [KPContFlatSourceRecipe.flatR_formula]

private lemma induced_chart_contDiffOn (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ P)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hf := f.property
  change f.val ∈ ⨆ J, KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction
    (motive := fun x : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P =>
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z => (x.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
        (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F))
    (fun J => KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J) hf
    (fun J x hx => hx.1 g) contDiffOn_const (fun x y hx hy => hx.add hy)

private lemma scalarSection_chart_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (ι v).val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  obtain ⟨f, hf⟩ := hSmooth v
  have hfun : (fun z => (ι v).val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => (f.val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1) := by
    funext z
    rw [← hf, KPGlobalTorusBorelTwistCompatibility.scalarSection_formula]
  rw [hfun]
  exact induced_chart_contDiffOn F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) f g

private lemma alpha_chart_contDiffOn (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (KPContFlatSourceRecipe.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (KPContFlatLogNormSmooth.alpha_groupArchChart_mul_contDiffOn F ζ hζ g)).of_le le_top

private lemma exp_alpha_chart_contDiffOn (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  ((contDiffOn_const (c := s)).mul (alpha_chart_contDiffOn F ζ hζ g)).cexp

private lemma L_chart_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (v : S) (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => L F ζ hζ ι s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hfun : (fun z => L F ζ hζ ι s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)) *
        ((ι v).val.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))) := by
    funext z
    rw [L_formula]
  rw [hfun]
  exact (exp_alpha_chart_contDiffOn F ζ hζ s g).mul
    (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth v g)

private lemma L_chart_varying_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (f : ℂ → S) (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => L F ζ hζ ι s (f s)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hfun : (fun z => L F ζ hζ ι s (f s)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)) *
        ((ι (f s)).val.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))) := by
    funext z
    rw [L_formula]
  rw [hfun]
  exact (exp_alpha_chart_contDiffOn F ζ hζ s g).mul
    (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth (f s) g)

 lemma parameterSection_chart_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m : ℕ) (s : ℂ) (v : S) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => parameterSection F ζ hζ ι m s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hfun : (fun z => parameterSection F ζ hζ ι m s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => ((KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ) ^ m) *
        (Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)) *
        ((ι v).val.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)))) := by
    funext z
    unfold parameterSection
    rw [L_formula]
  rw [hfun]
  exact ((alpha_chart_contDiffOn F ζ hζ g).pow m).mul
    ((exp_alpha_chart_contDiffOn F ζ hζ s g).mul
      (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth v g))

variable (hSmooth : ∀ v : S, (ι v).val ∈
  KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))

include hSmooth hfd



 def levelInter (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩

omit hSmooth hfd in
private lemma induced_uniform_level
    (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ P) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        f.val.val (g * j.val) = f.val.val g := by
  obtain ⟨U, _⟩ := KPCompactFiniteLevel.exists_level F ζ hζ
  have hf := f.property
  change f.val ∈ ⨆ J, KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction
    (motive := fun x : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P =>
      ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
          x.val (g * j.val) = x.val g)
    (fun J => KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J) hf
    (fun J x hx => ⟨J, hx.2⟩) ⟨U, fun _ _ => rfl⟩ (by
      intro x y hx hy
      obtain ⟨J, hJ⟩ := hx
      obtain ⟨K, hK⟩ := hy
      refine ⟨levelInter F ζ hζ J K, ?_⟩
      intro g j
      have hleft : KPGlobalTorusFunctionData.globalLevel F ζ hζ (levelInter F ζ hζ J K) ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ J := Subgroup.map_mono inf_le_left
      have hright : KPGlobalTorusFunctionData.globalLevel F ζ hζ (levelInter F ζ hζ J K) ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ K := Subgroup.map_mono inf_le_right
      change x.val (g * j.val) + y.val (g * j.val) = _
      rw [hJ g ⟨j.val, hleft j.property⟩, hK g ⟨j.val, hright j.property⟩]
      rfl)

private lemma scalar_uniform_level (v : S) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        (ι v).val.val (g * j.val) = (ι v).val.val g := by
  obtain ⟨f, hf⟩ := hSmooth v
  obtain ⟨J, hJ⟩ := induced_uniform_level F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) f
  refine ⟨J, ?_⟩
  intro g j
  rw [← hf, KPGlobalTorusBorelTwistCompatibility.scalarSection_formula,
    KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, hJ g j]

theorem stage_uniform_right_level :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
        (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        L F ζ hζ ι s v (g * j.val) = L F ζ hζ ι s v g := by
  let e := Module.finBasis ℂ S
  obtain ⟨U, hU⟩ := KPCompactFiniteLevel.exists_level F ζ hζ
  have hfinite (A : Finset (Fin (Module.finrank ℂ S))) :
      ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        KPGlobalTorusFunctionData.globalLevel F ζ hζ J ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
        ∀ i ∈ A, ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
          (ι (e i)).val.val (g * j.val) = (ι (e i)).val.val g := by
    induction A using Finset.induction_on with
    | empty => exact ⟨U, hU, by simp⟩
    | @insert i A hi ih =>
      obtain ⟨J, hJK, hJ⟩ := ih
      obtain ⟨K, hK⟩ := scalar_uniform_level F ζ hζ ι hSmooth (e i)
      let W := levelInter F ζ hζ J K
      have hWJ : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ J := Subgroup.map_mono inf_le_left
      have hWK : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ K := Subgroup.map_mono inf_le_right
      refine ⟨W, hWJ.trans hJK, ?_⟩
      intro k hk g j
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hK g ⟨j.val, hWK j.property⟩
      · exact hJ k hk g ⟨j.val, hWJ j.property⟩
  obtain ⟨J, hJK, hJ⟩ := hfinite Finset.univ
  refine ⟨J, ?_⟩
  intro s v g j
  have hscalar : (ι v).val.val (g * j.val) = (ι v).val.val g := by
    conv_lhs => rw [← e.sum_repr v]
    conv_rhs => rw [← e.sum_repr v]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Finset.sum_fn, Pi.smul_apply, smul_eq_mul]
    change (∑ i, e.repr v i * (ι (e i)).val.val (g * j.val)) =
      ∑ i, e.repr v i * (ι (e i)).val.val g
    apply Finset.sum_congr rfl
    intro i hi
    rw [hJ i hi g j]
  have ha := KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g ⟨j.val, hJK j.property⟩
  rw [L_formula, L_formula, hscalar]
  exact congrArg (fun a : ℝ => Complex.exp (s * (a : ℂ)) * (ι v).val.val g) ha

theorem parameterSection_contDiffOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m : ℕ) (s : ℂ) (v : S) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => parameterSection F ζ hζ ι m s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  parameterSection_chart_contDiffOn F ζ hζ ι hSmooth g m s v

theorem L_contDiffOn (f : ℂ → S) (s : ℂ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => L F ζ hζ ι s (f s)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  L_chart_varying_contDiffOn F ζ hζ ι hSmooth f s g


theorem spatialJet_continuousOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    ContinuousOn (spatialJet F ζ hζ ι g n s v) C.set :=
  ((L_chart_contDiffOn F ζ hζ ι hSmooth v s g).continuousOn_iteratedFDerivWithin
    (m := n) (by simp)
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).uniqueDiffOn).mono C.inside

def compactJet (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    C(C.set, JetSpace F n) :=
  ⟨fun z => spatialJet F ζ hζ ι g n s v z.val,
    (spatialJet_continuousOn F ζ hζ ι hSmooth g n C s v).restrict⟩






end DedekindZetaZeroFree.KPContFlatStageJetHolomorphy

end
