module

public import Mathlib

public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaNormTransport
public import DedekindZetaZeroFree.Eisenstein.Induction.TwistedAveragingAndSmoothLevels

@[expose] public section


open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := @_root_.DedekindZetaZeroFree.KPGlobalTorusFunctionData.G
abbrev E := @_root_.DedekindZetaZeroFree.KPGlobalTorusFunctionData.E

abbrev ModelData := @_root_.DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse.ModelData

abbrev Polarization := @_root_.DedekindZetaZeroFree.KPGlobalTorusFunctionData.Polarization

section
variable (s : ℂ)
include s
def normPower   (t : E F ζ hζ)  :=
  Complex.exp (s * (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t) : ℝ)) : ℂ))

theorem normPower_mul   (a b : E F ζ hζ) :
    normPower F ζ hζ s (a * b) = normPower F ζ hζ s a * normPower F ζ hζ s b := by
  unfold normPower
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul]
  · simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
  · exact_mod_cast Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ a)
  · exact_mod_cast Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ b)

 theorem normPower_neg   (a : E F ζ hζ) :
    normPower F ζ hζ (-s) a = (normPower F ζ hζ s a)⁻¹ := by
  simp only [normPower, neg_mul, Complex.exp_neg]

 theorem normPower_continuous   : Continuous (normPower F ζ hζ s) := by
  have hd : Continuous (fun t : E F ζ hζ =>
      (((KPGlobalTorusFunctionData.delta F ζ hζ t) : ℝ))) := by
    have h : (fun t : E F ζ hζ =>
        (((KPGlobalTorusFunctionData.delta F ζ hζ t) : ℝ))) =
        (fun t => (((KPGlobalCenterRationalCharacter.nu F ζ hζ t) : ℝ)) ^ 6) := by
      funext t
      simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
        KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map, NNReal.rpowMonoidHom_apply,
        NNReal.coe_rpow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _)]
      norm_num
    rw [h]
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))).pow 6
  have hn : ∀ t : E F ζ hζ,
      (((KPGlobalTorusFunctionData.delta F ζ hζ t) : ℝ)) ≠ 0 := by
    intro t
    exact_mod_cast Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (hd.log hn)))

def normCharacter   : E F ζ hζ →ₜ* ℂˣ where
  toFun t := Units.mk0 (normPower F ζ hζ s t) (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.val_injective
    change normPower F ζ hζ s 1 = 1
    simp [normPower]
  map_mul' := by
    intro a b
    apply Units.val_injective
    apply normPower_mul
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · apply normPower_continuous
    · change Continuous (fun t => (normPower F ζ hζ s t)⁻¹)
      simp only [← normPower_neg]
      apply normPower_continuous
end


 alias delta_rational := _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.delta_rational

 theorem normCharacter_rational (s : ℂ) (y : Fˣ) :
    normCharacter F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1 := by
  apply Units.val_injective
  change normPower F ζ hζ s (KPGlobalTorusFunctionData.s F ζ hζ y) = 1
  simp [normPower, delta_rational]

def twist (P : Polarization F ζ hζ) (s : ℂ) : Polarization F ζ hζ where
  H := P.H
  closed := P.closed
  abelian := P.abelian
  contains_center := P.contains_center
  character := P.character * (normCharacter F ζ hζ s).comp
    ⟨P.H.subtype, continuous_subtype_val⟩

abbrev Smooth := @_root_.DedekindZetaZeroFree.KPGlobalTorusFunctionData.TorusSmoothUnion

local instance smoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

abbrev rationalModel := @_root_.DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse.rationalModel

abbrev GroupArch := InfinitePlace F → Fin 3 → ℂ

def groupArchDomain : Set (GroupArch F) := {z | ∀ w, z w 1 ≠ 0}

def groupArchTuple (z : GroupArch F) : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ := by
  refine ⟨fun v => ?_, ?_⟩
  · cases v with
    | inl w =>
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)
      let y : w.Completionˣ := if h : z w 1 = 0 then 1
        else Units.mk0 (e.symm (z w 1)) (by
          intro h0
          apply h
          simpa using congrArg e h0)
      exact KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (z w 0)) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) y *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (z w 2))
    | inr q => exact 1
  · apply Filter.Eventually.of_forall
    intro v
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q => exact Subgroup.one_mem _

def groupArchChart (z : GroupArch F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (groupArchTuple F ζ hζ z))

 theorem groupArchDomain_open : IsOpen (groupArchDomain F) := by
  rw [groupArchDomain, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun (show Continuous (fun z : GroupArch F => z w (1)) by fun_prop)
    continuous_const

def InducedFunctions (P : Polarization F ζ hζ) :
    Submodule ℂ (G F ζ hζ → Smooth F ζ hζ P) where
  carrier := {f | ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ),
    f ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t •
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f g)}
  zero_mem' := by
    intros
    simp
  add_mem' := by
    intro f k hf hk t x g
    simp only [Pi.add_apply, hf t x g, hk t x g, map_add, smul_add]
  smul_mem' := by
    intro c f hf t x g
    simp only [Pi.smul_apply, hf t x g, map_smul]
    exact smul_comm c _ _

def InducedLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Submodule ℂ (InducedFunctions F ζ hζ P) where
  carrier := {f | (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val (groupArchChart F ζ hζ z * g)).val.val 1) (groupArchDomain F)) ∧
    ∀ (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      f.val (g * j.val) = f.val g}
  zero_mem' := by
    constructor
    · intro g; exact contDiffOn_const
    · intros; rfl
  add_mem' := by
    intro f k hf hk
    constructor
    · intro g; exact (hf.1 g).add (hk.1 g)
    · intro g j; change f.val (g * j.val) + k.val (g * j.val) = _
      rw [hf.2 g j, hk.2 g j]
      rfl
  smul_mem' := by
    intro c f hf
    constructor
    · intro g; exact contDiffOn_const.smul (hf.1 g)
    · intro g j; change c • f.val (g * j.val) = _
      rw [hf.2 g j]
      rfl

def Induced (P : Polarization F ζ hζ)  :=
  ⨆ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, InducedLevel F ζ hζ P J

local instance inducedFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

local instance inducedAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

section
variable (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
include P J g n K
def inducedJetBound  
    (f : InducedLevel F ζ hζ P J)  :=
  sSup ((fun z => ‖iteratedFDerivWithin ℝ n
    (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
    (groupArchDomain F) z‖) '' K.set)

theorem jet_image_bdd  
    (f : InducedLevel F ζ hζ P J) :
    BddAbove ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
  apply K.compact.bddAbove_image
  apply ContinuousOn.mono _ K.inside
  exact ((f.property.1 g).continuousOn_iteratedFDerivWithin (by simp)
    (groupArchDomain_open F).uniqueDiffOn).norm

theorem inducedJetBound_add_le  
    (f h : InducedLevel F ζ hζ P J) :
    inducedJetBound F ζ hζ P J g n K (f + h) ≤
      inducedJetBound F ζ hζ P J g n K f + inducedJetBound F ζ hζ P J g n K h := by
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro r ⟨z, hz, rfl⟩
    have hzU := K.inside hz
    change ‖iteratedFDerivWithin ℝ n
      ((fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1) +
       (fun y => (h.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ ≤ _
    rw [iteratedFDerivWithin_add_apply
      ((f.property.1 g z hzU).of_le (by simp))
      ((h.property.1 g z hzU).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn hzU]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup (jet_image_bdd F ζ hζ P J g n K f) (Set.mem_image_of_mem _ hz))
      (le_csSup (jet_image_bdd F ζ hζ P J g n K h) (Set.mem_image_of_mem _ hz)))
  · have hE  := Set.not_nonempty_iff_eq_empty.mp hK
    simp [inducedJetBound, hE, Real.sSup_empty]
end


private theorem norm_jet_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} {v : V} {n : ℕ} {f : V → ℂ} (c : ℂ)
    (hf : ContDiffWithinAt ℝ n f s v) (hs : UniqueDiffOn ℝ s) (hv : v ∈ s) :
    ‖iteratedFDerivWithin ℝ n (c • f) s v‖ =
      ‖c‖ * ‖iteratedFDerivWithin ℝ n f s v‖ := by
  rw [iteratedFDerivWithin_const_smul_apply (R := ℂ) hf hs hv, norm_smul]

section
variable (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
include P J g n K
theorem inducedJetBound_smul  
    (c : ℂ) (f : InducedLevel F ζ hζ P J) :
    inducedJetBound F ζ hζ P J g n K (c • f) = ‖c‖ * inducedJetBound F ζ hζ P J g n K f := by
  unfold inducedJetBound
  have hEq : (fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => ((c • f).val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set =
      ‖c‖ • ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
    change _ = (fun r : ℝ => ‖c‖ • r) '' ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set)
    rw [Set.image_image]
    apply Set.image_congr
    intro z hz
    change ‖iteratedFDerivWithin ℝ n
      (c • (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ = ‖c‖ * ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖
    exact norm_jet_smul c
      ((f.property.1 g z (K.inside hz)).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn (K.inside hz)
  rw [hEq]
  exact Real.sSup_smul_of_nonneg (α := ℝ) (norm_nonneg c) _

def inducedJet   :
    Seminorm ℂ (InducedLevel F ζ hζ P J) :=
  Seminorm.of (inducedJetBound F ζ hζ P J g n K)
    (inducedJetBound_add_le F ζ hζ P J g n K) (inducedJetBound_smul F ζ hζ P J g n K)
end


section
variable (P : Polarization F ζ hζ)
include P
def inducedLevelTopology  
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)  :=
  (SeminormFamily.moduleFilterBasis
    (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2)).topology

def inducedStageInclusion  
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] Induced F ζ hζ P :=
  Submodule.inclusion (le_iSup (fun J => InducedLevel F ζ hζ P J) J)

def inducedFinalSeminorms   :=
  {q : Seminorm ℂ (Induced F ζ hζ P) // ∀ J,
    @Continuous (InducedLevel F ζ hζ P J) ℝ
      (inducedLevelTopology F ζ hζ P J) inferInstance
      (q ∘ inducedStageInclusion F ζ hζ P J)}

def inducedTopology   : TopologicalSpace (Induced F ζ hζ P) :=
  (SeminormFamily.moduleFilterBasis
    (fun q : inducedFinalSeminorms F ζ hζ P => q.val)).topology
end


local instance inducedTop (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

alias finitePart_normal := _root_.DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse.finitePart_normal

def scalarSection (P : Polarization F ζ hζ) :
    Induced F ζ hζ P →ₗ[ℂ] KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P := by
  refine { toFun := fun f => ⟨fun g => (f.val.val g).val.val 1, ?_⟩
           map_add' := ?_
           map_smul' := ?_ }
  · rename_i f
    intro h x g
    have hf := f.val.property h.val x g
    have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hf
    change (f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val.val 1 = _ at he
    change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
      (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P h.val (f.val.val g)).val.val 1 at he
    rw [KPGlobalTorusPeriodizationInverse.rightAction_formula, one_mul] at he
    change (f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val.val 1 =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val * (P.character h : ℂ) *
        (f.val.val g).val.val 1
    rw [he]
    have hc := (f.val.val g).val.property h 1
    simp only [mul_one] at hc
    change _ * (f.val.val g).val.val h.val = _
    rw [hc]
    exact (mul_assoc _ _ _).symm
  · intros; rfl
  · intros; rfl

section
variable (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ)
include P f g
theorem scalarSection_formula   :
    (scalarSection F ζ hζ P f).val g = (f.val.val g).val.val 1 := by
  unfold scalarSection
  rfl

 theorem scalar_transitivity   (t : E F ζ hζ) :
    (f.val.val g).val.val t = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
      (scalarSection F ζ hζ P f).val (t.val * g) := by
  have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hf := f.val.property t 0 g
  simp only [hN, mul_one] at hf
  have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hf
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
    (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f.val.val g)).val.val 1 at he
  rw [KPGlobalTorusPeriodizationInverse.rightAction_formula, one_mul] at he
  rw [scalarSection_formula, he]
  change _ = _⁻¹ * (_ * _)
  have hp : (0 : ℝ) < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
    exact_mod_cast (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)) |> pos_iff_ne_zero.mpr
  have hn : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
end


section
variable (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ))
include P J K
def levelRestriction   :
    InducedLevel F ζ hζ P J →ₗ[ℂ] (K → Smooth F ζ hζ P) where
  toFun f k := f.val.val k.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def CompactLevel    := (levelRestriction F ζ hζ P J K).range

def restrictLevel   :
    InducedLevel F ζ hζ P J →ₗ[ℂ] CompactLevel F ζ hζ P J K :=
  (levelRestriction F ζ hζ P J K).rangeRestrict

def compactLevelTopology    :=
  TopologicalSpace.coinduced (restrictLevel F ζ hζ P J K) (inducedLevelTopology F ζ hζ P J)
end


local instance compactTop (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    TopologicalSpace (CompactLevel F ζ hζ P J K) := compactLevelTopology F ζ hζ P J K

local instance inducedLevelTop (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    TopologicalSpace (InducedLevel F ζ hζ P J) := inducedLevelTopology F ζ hζ P J

def upperRoot (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
  Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
private theorem upperRoot_entries (x : KPGlobalTorusFunctionData.Adeles F) (i j : Fin 2) :
    upperRoot F x i j = (!![1, x; 0, 1]) i j := by
  fin_cases i <;> fin_cases j <;> simp [upperRoot, Matrix.transvection]
private theorem adele_ext (a b : KPGlobalTorusFunctionData.Adeles F)
    (h : ∀ v, KPAdelicCoverRestrictedProduct.adeleEval F v a = KPAdelicCoverRestrictedProduct.adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply Subtype.ext
    funext q
    exact h (Sum.inr q)
 theorem projected_root (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (upperRoot F x) := by
  change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) = _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply adele_ext F
  intro v
  have h := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x) v
  have he := congrArg (fun A : KPLocalCover.LocalGL2 F v => A i j) h
  change KPAdelicCoverRestrictedProduct.adeleEval F v
    ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) i j) = _ at he
  rw [he]
  fin_cases i <;> fin_cases j <;>
    simp [KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N,
      KPLocalCover.projection_apply, KPLocalCover.sectionMap, KubotaRankTwo.n,
      upperRoot_entries]
section
variable {R : Type*} [CommRing R] (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0)
include R A h10
private theorem upper_unit   :
    IsUnit (A 0 0) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) R)) :=
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := R) A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) R) = A 0 0 * A 1 1 := by
    simp only [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  exact isUnit_of_mul_isUnit_left (hd ▸ h)
private theorem upper_diagonal  
    (x : R) (hx : A 0 0 * x = A 0 1) :
    ((A * Matrix.GeneralLinearGroup.transvection (R := R) 0 1 (by decide) (-x) : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
    ((A * Matrix.GeneralLinearGroup.transvection (R := R) 0 1 (by decide) (-x) : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
  constructor <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10, hx]
end


 theorem actual_borel_factorization (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    ∃ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
      b.val = t.val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  obtain ⟨A, hA, h10⟩ := b.property
  let u := (upper_unit A h10).unit
  let x : KPGlobalTorusFunctionData.Adeles F := ↑u⁻¹ * A 0 1
  have hx : A 0 0 * x = A 0 1 := by
    change A 0 0 * (↑u⁻¹ * A 0 1) = _
    have hu : (u : KPGlobalTorusFunctionData.Adeles F) = A 0 0 := (upper_unit A h10).unit_spec
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have ht : b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x) ∈ E F ζ hζ := by
    change ∃ D : KPAdelicCoverRestrictedProduct.AdelicGL2 F,
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) D =
        KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x)) ∧ D 1 0 = 0 ∧ D 0 1 = 0
    refine ⟨A * upperRoot F (-x), ?_, upper_diagonal A h10 x hx⟩
    simp only [map_mul, projected_root, hA]
  refine ⟨⟨b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x), ht⟩, x, ?_⟩
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (-x) * KPGlobalTorusFunctionData.N F ζ hζ x = 1 := by
    rw [← KPGlobalTorusFunctionData.N_add, neg_add_cancel]
    exact (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  change b.val = (b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x)) * KPGlobalTorusFunctionData.N F ζ hζ x
  rw [mul_assoc, hn, mul_one]

 alias upper_units := _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.upper_units
 def ratio {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0)  :=
  (upper_units A h10).1.unit * ((upper_units A h10).2.unit)⁻¹
section
variable {R : Type*} [CommRing R]
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) (hA : A 1 0 = 0) (hB : B 1 0 = 0)
include R A B hA hB
private theorem upper_product   :
    ((A * B : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
private theorem ratio_mul   :
    ratio (A * B) (upper_product A B hA hB) = ratio A hA * ratio B hB := by
  have h0 : (upper_units (A * B) (upper_product A B hA hB)).1.unit =
      (upper_units A hA).1.unit * (upper_units B hB).1.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB]
  have h1 : (upper_units (A * B) (upper_product A B hA hB)).2.unit =
      (upper_units A hA).2.unit * (upper_units B hB).2.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  simp only [ratio, h0, h1]
  simp only [mul_inv_rev]; ac_rfl
end

private theorem ratio_eq (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (h : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) :
    ratio A hA = ratio B hB := by
  have hm := QuotientGroup.eq.mp h
  obtain ⟨z, hz⟩ := hm
  have he : B = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = A⁻¹ * B at hz
    rw [hz]
    group
  have h0 : (upper_units B hB).1.unit = (upper_units A hA).1.unit * z := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    rw [he]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar]
  have h1 : (upper_units B hB).2.unit = (upper_units A hA).2.unit * z := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    rw [he]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar]
  simp only [ratio, h0, h1]
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

private theorem root_upper (x : KPGlobalTorusFunctionData.Adeles F) :
    upperRoot F x 1 0 = 0 := by rw [upperRoot_entries]; rfl

 def borelRatio (b : KPGlobalTorusFunctionData.borel F ζ hζ) : KPGlobalTorusFunctionData.Ideles F :=
  ratio (Classical.choose b.property) (Classical.choose_spec b.property).2

private theorem borelRatio_formula (b : KPGlobalTorusFunctionData.borel F ζ hζ)
    (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ b.val) (h10 : A 1 0 = 0) :
    borelRatio F ζ hζ b = ratio A h10 := by
  apply ratio_eq F
  exact (Classical.choose_spec b.property).1.trans hA.symm

 theorem borelRatio_mul (b c : KPGlobalTorusFunctionData.borel F ζ hζ) :
    borelRatio F ζ hζ (b * c) = borelRatio F ζ hζ b * borelRatio F ζ hζ c := by
  let A := Classical.choose b.property
  let B := Classical.choose c.property
  have hA := Classical.choose_spec b.property
  have hB := Classical.choose_spec c.property
  rw [borelRatio_formula F ζ hζ (b * c) (A * B) (by
    change _ = KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (b.val * c.val)
    exact (map_mul _ A B).trans ((congrArg₂ (fun a b => a * b) hA.1 hB.1).trans (map_mul _ b.val c.val).symm)) (upper_product A B hA.2 hB.2)]
  exact ratio_mul A B hA.2 hB.2

 theorem borel_torus (t : E F ζ hζ) : t.val ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  exact ⟨A, hA, h10⟩

 alias borel_root := _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.borel_root

 def borelElement (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.borel F ζ hζ :=
  ⟨t.val * KPGlobalTorusFunctionData.N F ζ hζ x,
    Subgroup.mul_mem _ (borel_torus F ζ hζ t) (borel_root F ζ hζ x)⟩

 theorem borelRatio_torus (t : E F ζ hζ) :
    borelRatio F ζ hζ ⟨t.val, borel_torus F ζ hζ t⟩ = KPGlobalTorusFunctionData.p F ζ hζ t := by
  let A := Classical.choose t.property
  have hA := Classical.choose_spec t.property
  rw [borelRatio_formula F ζ hζ _ A hA.1 hA.2.1]
  apply Units.ext
  have hh := KPGlobalTorusFunctionData.ratio_formula F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ A hA.1 hA.2.1 hA.2.2
  change (ratio A hA.2.1 : KPGlobalTorusFunctionData.Adeles F) =
    ((KPGlobalTorusFunctionData.torusRatio F)
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ : KPGlobalTorusFunctionData.Adeles F)
  rw [hh]
  unfold ratio
  simp only [Units.val_mul]

private theorem borelRatio_root (x : KPGlobalTorusFunctionData.Adeles F) :
    borelRatio F ζ hζ ⟨KPGlobalTorusFunctionData.N F ζ hζ x, borel_root F ζ hζ x⟩ = 1 := by
  rw [borelRatio_formula F ζ hζ _ (upperRoot F x) (projected_root F ζ hζ x).symm (root_upper F x)]
  have h0 : (upper_units (upperRoot F x) (root_upper F x)).1.unit = 1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec, upperRoot_entries, Units.val_one]
    rfl
  have h1 : (upper_units (upperRoot F x) (root_upper F x)).2.unit = 1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec, upperRoot_entries, Units.val_one]
    rfl
  simp only [ratio, h0, h1, inv_one, mul_one]

private theorem borelRatio_element (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    borelRatio F ζ hζ (borelElement F ζ hζ t x) = KPGlobalTorusFunctionData.p F ζ hζ t := by
  change borelRatio F ζ hζ (⟨t.val, borel_torus F ζ hζ t⟩ *
    ⟨KPGlobalTorusFunctionData.N F ζ hζ x, borel_root F ζ hζ x⟩) = _
  rw [borelRatio_mul, borelRatio_torus, borelRatio_root, mul_one]

 def borelRatioHom : KPGlobalTorusFunctionData.borel F ζ hζ →* KPGlobalTorusFunctionData.Ideles F where
  toFun := borelRatio F ζ hζ
  map_one' := by
    have h := borelRatio_torus F ζ hζ 1
    have he : (⟨(1 : E F ζ hζ).val, borel_torus F ζ hζ 1⟩ : KPGlobalTorusFunctionData.borel F ζ hζ) = 1 := Subtype.ext rfl
    rw [he, map_one] at h
    exact h
  map_mul' := borelRatio_mul F ζ hζ

 def borelDelta : KPGlobalTorusFunctionData.borel F ζ hζ →* (ℝ≥0)ˣ :=
  (KPGlobalTorusFunctionData.ideleAbs F).comp (borelRatioHom F ζ hζ)

private theorem borelDelta_element (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    borelDelta F ζ hζ (borelElement F ζ hζ t x) = KPGlobalTorusFunctionData.delta F ζ hζ t := by
  change KPGlobalTorusFunctionData.ideleAbs F (borelRatio F ζ hζ (borelElement F ζ hζ t x)) = _
  rw [borelRatio_element]
  rfl

structure IwasawaData where
  K : Subgroup (G F ζ hζ)
  compact : IsCompact (K : Set (G F ζ hζ))
  decomposition : ∀ g : G F ζ hζ,
    ∃ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (k : K),
      g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val
  overlap : ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
    t.val * KPGlobalTorusFunctionData.N F ζ hζ x ∈ K →
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1

section
variable (D : IwasawaData F ζ hζ)
include D
def iwasawaNorm   (g : G F ζ hζ) : (ℝ≥0)ˣ :=
  KPGlobalTorusFunctionData.delta F ζ hζ (Classical.choose (D.decomposition g))

 theorem iwasawaNorm_formula  
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (k : D.K) :
    iwasawaNorm F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) =
      KPGlobalTorusFunctionData.delta F ζ hζ t := by
  let g := (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val
  let u := Classical.choose (D.decomposition g)
  let y := Classical.choose (Classical.choose_spec (D.decomposition g))
  let l := Classical.choose (Classical.choose_spec (Classical.choose_spec (D.decomposition g)))
  have hl : g = (u.val * KPGlobalTorusFunctionData.N F ζ hζ y) * l.val :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (D.decomposition g)))
  let b := borelElement F ζ hζ u y
  let c := borelElement F ζ hζ t x
  have he : (b⁻¹ * c).val = l.val * k.val⁻¹ := by
    have h : c.val * k.val = b.val * l.val := hl
    change b.val⁻¹ * c.val = _
    calc
      b.val⁻¹ * c.val = b.val⁻¹ * ((c.val * k.val) * k.val⁻¹) := by group
      _ = b.val⁻¹ * ((b.val * l.val) * k.val⁻¹) := by rw [h]
      _ = l.val * k.val⁻¹ := by group
  obtain ⟨v, z, hv⟩ := actual_borel_factorization F ζ hζ (b⁻¹ * c)
  have hK : v.val * KPGlobalTorusFunctionData.N F ζ hζ z ∈ D.K := by
    rw [← hv, he]
    exact D.K.mul_mem l.property (D.K.inv_mem k.property)
  have hd : borelDelta F ζ hζ (b⁻¹ * c) = 1 := by
    have hb : b⁻¹ * c = borelElement F ζ hζ v z := Subtype.ext hv
    rw [hb, borelDelta_element]
    exact D.overlap v z hK
  rw [map_mul, map_inv] at hd
  have hb := borelDelta_element F ζ hζ u y
  have hc := borelDelta_element F ζ hζ t x
  change (borelDelta F ζ hζ b)⁻¹ * borelDelta F ζ hζ c = 1 at hd
  rw [hb, hc] at hd
  change KPGlobalTorusFunctionData.delta F ζ hζ u = KPGlobalTorusFunctionData.delta F ζ hζ t
  exact inv_mul_eq_one.mp hd

theorem iwasawaNorm_right_compact  
    (g : G F ζ hζ) (k : D.K) :
    iwasawaNorm F ζ hζ D (g * k.val) = iwasawaNorm F ζ hζ D g := by
  obtain ⟨t, x, l, rfl⟩ := D.decomposition g
  have he : ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * l.val) * k.val =
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * (l * k).val := by
    simp [mul_assoc]
  rw [he, iwasawaNorm_formula, iwasawaNorm_formula]

theorem iwasawaNorm_borel_mul  
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    iwasawaNorm F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.delta F ζ hζ t * iwasawaNorm F ζ hζ D g := by
  obtain ⟨u, y, k, rfl⟩ := D.decomposition g
  let b := borelElement F ζ hζ t x * borelElement F ζ hζ u y
  obtain ⟨v, z, hv⟩ := actual_borel_factorization F ζ hζ b
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ v =
      KPGlobalTorusFunctionData.delta F ζ hζ t * KPGlobalTorusFunctionData.delta F ζ hζ u := by
    have hb : b = borelElement F ζ hζ v z := Subtype.ext hv
    have hm := (borelDelta F ζ hζ).map_mul (borelElement F ζ hζ t x) (borelElement F ζ hζ u y)
    change borelDelta F ζ hζ b = _ at hm
    rw [hb, borelDelta_element, borelDelta_element, borelDelta_element] at hm
    exact hm
  have he : (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) *
      ((u.val * KPGlobalTorusFunctionData.N F ζ hζ y) * k.val) =
      (v.val * KPGlobalTorusFunctionData.N F ζ hζ z) * k.val := by
    rw [← hv]
    change _ = ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) *
      (u.val * KPGlobalTorusFunctionData.N F ζ hζ y)) * k.val
    exact (mul_assoc _ _ _).symm
  rw [he, iwasawaNorm_formula, iwasawaNorm_formula, hd]

theorem iwasawaNorm_compact   (k : D.K) :
    iwasawaNorm F ζ hζ D k.val = 1 := by
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have h := iwasawaNorm_formula F ζ hζ D 1 0 k
  simpa [hn] using h
end


end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility

section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] smoothTopology inducedFunctionsAddGroup inducedLevelAddGroup
  inducedAddGroup inducedTop compactTop inducedLevelTop

section
variable (P : Polarization F ζ hζ) (s : ℂ)
include P s
def normTwist   :
    Smooth F ζ hζ P ≃L[ℂ] Smooth F ζ hζ (twist F ζ hζ P s) := by
  exact KPGlobalTorusBorelNormTwistTransport.normTwist F ζ hζ P s

 theorem normTwist_formula  
    (f : Smooth F ζ hζ P) (t : E F ζ hζ) :
    (normTwist F ζ hζ P s f).val.val t = normPower F ζ hζ s t * f.val.val t := by
  exact KPGlobalTorusBorelNormTwistTransport.normTwist_formula F ζ hζ P s f t

 theorem normTwist_inverse_formula  
    (f : Smooth F ζ hζ (twist F ζ hζ P s)) (t : E F ζ hζ) :
    ((normTwist F ζ hζ P s).symm f).val.val t =
      normPower F ζ hζ (-s) t * f.val.val t := by
  have hf := normTwist_formula F ζ hζ P s ((normTwist F ζ hζ P s).symm f) t
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  rw [normPower_neg, hf]
  have hn : normPower F ζ hζ s t ≠ 0 := Complex.exp_ne_zero _
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
end


abbrev productModel (C : ModelData F ζ hζ) :=
  KPGlobalTorusPeriodizationInverse.productModel F ζ hζ C
abbrev Rational (s : ℂ) := Smooth F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)
section
variable (C : ModelData F ζ hζ) (s : ℂ)
include C s
abbrev Product   :=
  Smooth F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)

def twistedP   :
    Product F ζ hζ C s →L[ℂ] Rational F ζ hζ s :=
  (normTwist F ζ hζ (rationalModel F ζ hζ) s).toContinuousLinearMap.comp
    ((KPGlobalTorusPeriodizationInverse.periodization F ζ hζ C).comp
      (normTwist F ζ hζ (productModel F ζ hζ C) s).symm.toContinuousLinearMap)

def twistedQ   :
    Rational F ζ hζ s →L[ℂ] Product F ζ hζ C s :=
  (normTwist F ζ hζ (productModel F ζ hζ C) s).toContinuousLinearMap.comp
    ((KPGlobalTorusPeriodizationInverse.averaging F ζ hζ C).comp
      (normTwist F ζ hζ (rationalModel F ζ hζ) s).symm.toContinuousLinearMap)

 theorem twistedP_twistedQ   (f : Rational F ζ hζ s) :
    twistedP F ζ hζ C s (twistedQ F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [KPGlobalTorusPeriodizationInverse.periodization_averaging F ζ hζ C]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

 theorem twistedQ_twistedP   (f : Product F ζ hζ C s) :
    twistedQ F ζ hζ C s (twistedP F ζ hζ C s f) = f := by
  simp only [twistedP, twistedQ, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [KPGlobalTorusPeriodizationInverse.averaging_periodization F ζ hζ C]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

def borelP   :
    Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelP F ζ hζ C s

def borelQ   :
    Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelQ F ζ hζ C s

 theorem borelP_fiberwise  
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) (g : G F ζ hζ) :
    (borelP F ζ hζ C s f).val.val g = twistedP F ζ hζ C s (f.val.val g) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelP_fiberwise F ζ hζ C s f g

 theorem borelQ_fiberwise  
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) (g : G F ζ hζ) :
    (borelQ F ζ hζ C s f).val.val g = twistedQ F ζ hζ C s (f.val.val g) := by
  exact KPGlobalTorusBorelNormTwistTransport.borelQ_fiberwise F ζ hζ C s f g

 theorem borelP_borelQ  
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelP F ζ hζ C s (borelQ F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelP_fiberwise, borelQ_fiberwise, twistedP_twistedQ]

 theorem borelQ_borelP  
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelQ F ζ hζ C s (borelP F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelQ_fiberwise, borelP_fiberwise, twistedQ_twistedP]
end


private def finiteConj (a : G F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨(MulAut.conjNormal a).toEquiv, ?_, ?_⟩
  · apply Continuous.subtype_mk
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => a * x.val * a⁻¹)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · apply Continuous.subtype_mk
    have he : (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a).symm = MulAut.conjNormal a⁻¹ := by
      change (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a)⁻¹ = _
      rw [map_inv]
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => ((MulAut.conjNormal a).symm x).val)
    rw [he]
    simp only [MulAut.conjNormal_apply, inv_inv]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private def conjLevel (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  exact ⟨J.toOpenSubgroup.comap (MulAut.conjNormal a⁻¹).toMonoidHom (by
      change Continuous (finiteConj F ζ hζ a⁻¹)
      exact (finiteConj F ζ hζ a⁻¹).continuous),
    (finiteConj F ζ hζ a⁻¹).isCompact_preimage.mpr J.isCompact⟩

 section
variable (P : Polarization F ζ hζ)
include P
def inducedFunctionsTranslation   :
    Representation ℂ (G F ζ hζ) (InducedFunctions F ζ hζ P) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro t x g
        simpa only [mul_assoc] using f.property t x (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

private theorem induced_translate_level  
    (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ InducedLevel F ζ hζ P J) :
    inducedFunctionsTranslation F ζ hζ P a f ∈
      InducedLevel F ζ hζ P (conjLevel F ζ hζ a J) := by
  constructor
  · intro g
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val ((groupArchChart F ζ hζ z * g) * a)).val.val 1) _
    simpa only [mul_assoc] using hf.1 (g * a)
  · intro g j
    have hj : a⁻¹ * j.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
      obtain ⟨k, hk, he⟩ := j.property
      have hk' : a⁻¹ * k.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
        letI := finitePart_normal F ζ hζ
        apply Subgroup.mem_map.mpr
        exact ⟨MulAut.conjNormal a⁻¹ k, hk, by simp only [Subgroup.subtype_apply, MulAut.conjNormal_apply, inv_inv]⟩
      change k.val = j.val at he
      rw [← he]
      exact hk'
    have hh := hf.2 (g * a) ⟨a⁻¹ * j.val * a, hj⟩
    change f.val ((g * j.val) * a) = f.val (g * a)
    have he : (g * a) * (a⁻¹ * j.val * a) = (g * j.val) * a := by group
    change f.val ((g * a) * (a⁻¹ * j.val * a)) = f.val (g * a) at hh
    rwa [he] at hh

 theorem induced_translate_union   (a : G F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ Induced F ζ hζ P) :
    inducedFunctionsTranslation F ζ hζ P a f ∈ Induced F ζ hζ P := by
  have hle : Induced F ζ hζ P ≤ (Induced F ζ hζ P).comap
      (inducedFunctionsTranslation F ζ hζ P a) := by
    apply iSup_le
    intro J x hx
    exact Submodule.mem_iSup_of_mem (conjLevel F ζ hζ a J)
      (induced_translate_level F ζ hζ P a J x hx)
  exact hle hf

def inducedRightAction   :
    Representation ℂ (G F ζ hζ) (Induced F ζ hζ P) where
  toFun a := (inducedFunctionsTranslation F ζ hζ P a).restrict
    (induced_translate_union F ζ hζ P a)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * 1) = f.val.val g
    exact congrArg f.val.val (mul_one g)
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * (a * b)) = f.val.val ((g * a) * b)
    exact congrArg f.val.val (mul_assoc g a b).symm

 theorem inducedRightAction_formula  
    (a g : G F ζ hζ) (f : Induced F ζ hζ P) :
    (inducedRightAction F ζ hζ P a f).val.val g = f.val.val (g * a) := by rfl
end


 theorem borelP_intertwines (C : ModelData F ζ hζ) (s : ℂ) (a : G F ζ hζ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelP F ζ hζ C s
        (inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a f) =
      inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a
        (borelP F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  simp only [borelP_fiberwise, inducedRightAction_formula]

 theorem induced_smooth (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val.val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F) := by
  have hf := f.property
  change f.val ∈ ⨆ J, InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction (motive := fun x : InducedFunctions F ζ hζ P =>
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (x.val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F)) (fun J => InducedLevel F ζ hζ P J) hf
      (fun J x hx => hx.1 g) contDiffOn_const (fun x y hx hy => hx.add hy)

theorem iwasawaUpperUnits (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) : IsUnit (A 0 0) ∧ IsUnit (A 1 1) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F))) := (Matrix.GeneralLinearGroup.det A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F)) = A 0 0 * A 1 1 := by simp [Matrix.det_fin_two, h10]
  exact ⟨isUnit_of_mul_isUnit_left (hd ▸ h), isUnit_of_mul_isUnit_right (hd ▸ h)⟩
def iwasawaUpperRatio (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) : KPGlobalTorusFunctionData.Ideles F :=
  (iwasawaUpperUnits F A h10).1.unit * (iwasawaUpperUnits F A h10).2.unit⁻¹
section
variable (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0)
include A B hA hB
theorem iwasawaUpperRatio_scalar  
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) : iwasawaUpperRatio F A hA = iwasawaUpperRatio F B hB := by
  obtain ⟨C, hC, he⟩ := (QuotientGroup.mk'_eq_mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).mp he
  obtain ⟨c, rfl⟩ := hC
  have he00 := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F => M 0 0) he
  have he11 := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F => M 1 1) he
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at he00 he11
  have hu00 : (iwasawaUpperUnits F A hA).1.unit * c = (iwasawaUpperUnits F B hB).1.unit := by
    apply Units.ext
    simpa only [Units.val_mul, IsUnit.unit_spec] using he00
  have hu11 : (iwasawaUpperUnits F A hA).2.unit * c = (iwasawaUpperUnits F B hB).2.unit := by
    apply Units.ext
    simpa only [Units.val_mul, IsUnit.unit_spec] using he11
  unfold iwasawaUpperRatio
  rw [← hu00, ← hu11]
  group
theorem iwasawaUpperMul_zero   : (A * B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
theorem iwasawaUpperRatio_mul   : iwasawaUpperRatio F (A * B) (iwasawaUpperMul_zero F A B hA hB) = iwasawaUpperRatio F A hA * iwasawaUpperRatio F B hB := by
  have hu00 : (iwasawaUpperUnits F (A * B) (iwasawaUpperMul_zero F A B hA hB)).1.unit = (iwasawaUpperUnits F A hA).1.unit * (iwasawaUpperUnits F B hB).1.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB]
  have hu11 : (iwasawaUpperUnits F (A * B) (iwasawaUpperMul_zero F A B hA hB)).2.unit = (iwasawaUpperUnits F A hA).2.unit * (iwasawaUpperUnits F B hB).2.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  unfold iwasawaUpperRatio
  rw [hu00, hu11]
  simp only [mul_inv_rev]
  ac_rfl
end


private theorem upperRoot_zero (x : KPGlobalTorusFunctionData.Adeles F) :
    upperRoot F x 1 0 = 0 := by simp [upperRoot_entries]

private theorem upperRoot_ratio (x : KPGlobalTorusFunctionData.Adeles F) :
    iwasawaUpperRatio F (upperRoot F x) (upperRoot_zero F x) = 1 := by
  have h00 : (iwasawaUpperUnits F (upperRoot F x) (upperRoot_zero F x)).1.unit = 1 := by
    apply Units.ext
    simp [IsUnit.unit_spec, upperRoot_entries]
  have h11 : (iwasawaUpperUnits F (upperRoot F x) (upperRoot_zero F x)).2.unit = 1 := by
    apply Units.ext
    simp [IsUnit.unit_spec, upperRoot_entries]
  simp [iwasawaUpperRatio, h00, h11]

theorem iwasawaUpperRatio_torus (t : E F ζ hζ)
    (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val) :
    iwasawaUpperRatio F A h10 = KPGlobalTorusFunctionData.p F ζ hζ t := by
  apply Units.ext
  change _ = (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ : KPGlobalTorusFunctionData.Adeles F)
  rw [KPGlobalTorusFunctionData.ratio_formula F _ A hA h10 h01]
  rfl

theorem iwasawaUpperRatio_torus_root (t : E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hB : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x)) :
    iwasawaUpperRatio F B hB = KPGlobalTorusFunctionData.p F ζ hζ t := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  have hrep : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (A * upperRoot F x) = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B := by
    rw [map_mul, hA, ← projected_root F ζ hζ x, ← map_mul, ← he]
  rw [← iwasawaUpperRatio_scalar F (A * upperRoot F x) B
    (iwasawaUpperMul_zero F A (upperRoot F x) h10 (upperRoot_zero F x)) hB hrep,
    iwasawaUpperRatio_mul F A (upperRoot F x) h10 (upperRoot_zero F x),
    upperRoot_ratio, mul_one]
  exact iwasawaUpperRatio_torus F ζ hζ t A h10 h01 hA

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility

end
