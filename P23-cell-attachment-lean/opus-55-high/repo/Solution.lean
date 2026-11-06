module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Constructions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Analysis.Complex.CoveringMap
@[expose] public section
noncomputable section
open unitInterval CategoryTheory
namespace CellAttachment
universe u v
abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
def boundaryInclusion : C(Circle, Disk) where
  toFun z := ⟨z, le_of_eq (Circle.norm_coe z)⟩
  continuous_toFun := by fun_prop
abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
inductive AttachingRel (f : ι → C(Circle, X)) : Raw X ι → Raw X ι → Prop
  | boundary (i : ι) (z : Circle) :
      AttachingRel f (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
def Space (f : ι → C(Circle, X)) := Quot (AttachingRel f)
instance (f : ι → C(Circle, X)) : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))
def quotientMap (f : ι → C(Circle, X)) : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩
def inclusion (f : ι → C(Circle, X)) : C(X, Space f) where
  toFun x := quotientMap f (.inl x)
  continuous_toFun := (quotientMap f).continuous.comp continuous_inl
def characteristic (f : ι → C(Circle, X)) (i : ι) : C(Disk, Space f) where
  toFun z := quotientMap f (.inr ⟨i, z⟩)
  continuous_toFun := (quotientMap f).continuous.comp
    (continuous_inr.comp (continuous_sigmaMk (i := i)))
@[simp] theorem characteristic_boundary (f : ι → C(Circle, X)) (i : ι) (z : Circle) :
    characteristic f i (boundaryInclusion z) = inclusion f (f i z) :=
  Quot.sound (.boundary i z)
def inclusionPi1 (f : ι → C(Circle, X)) (x₀ : X) :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop
def circleGeneratorClass : FundamentalGroup Circle (1 : Circle) :=
  .mk circleGenerator
def attachingLoop (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) : Path x₀ x₀ :=
  (γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)
def attachingLoopClass (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : ι → FundamentalGroup X x₀ :=
  fun i => .mk (attachingLoop f x₀ γ i)
def attachingNormalClosure (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : Subgroup (FundamentalGroup X x₀) :=
  Subgroup.normalClosure (Set.range (attachingLoopClass f x₀ γ))
instance attachingNormalClosure_normal (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : (attachingNormalClosure f x₀ γ).Normal := by
  unfold attachingNormalClosure
  infer_instance

def hf (a : I) : C(I, I) :=
  ⟨fun s => ⟨(a + s) / 2, by cases a.2
                             cases s.2
                             constructor <;> linarith⟩, by fun_prop⟩

lemma hfv : hf 0 0 = 0 ∧ hf 0 1 = hf 1 0 ∧ hf 1 1 = 1 := by norm_num [hf, Subtype.ext_iff]
lemma hf_dist a x y : 2 * dist (hf a x) (hf a y) ≤ dist x y := by
  simp [Subtype.dist_eq, Real.dist_eq, hf, ← sub_div, abs_div, mul_div_cancel₀]

variable [TopologicalSpace Y] [Group G] (W : J → Set Y) [PseudoMetricSpace M] [PseudoMetricSpace N]

notation "◁" ρ:max c:max => ρ (ContinuousMap.comp c $ hf 1) * ρ (ContinuousMap.comp c $ hf 0)
set_option hygiene false
notation "□" => C(I × I, Y)
notation "Ψ" => C(I, Y)
notation c " ⊑ " S:51 => ∀ s, c s ∈ S

def value (ρ : Ψ → G) : ℕ → Ψ → G
  | 0, c => ρ c
  | k + 1, c => ◁ (value ρ k) c

def Fine k (g : M → Y) :=
  ∀ x, ∃ j, ∀ y, dist y x ≤ 2⁻¹ ^ k → g y ∈ W j

variable {W}

lemma fine_comp
    (h : Fine W (k + 1) g) (φ : N → M) (hφ : ∀ x y, 2 * dist (φ x) (φ y) ≤ dist x y) :
    Fine W k (g ∘ φ) := fun x => (h $ φ x).imp fun j hj y hy => hj _ $ by
  rw [pow_succ]
  linarith [hφ y x]




variable {ρ : Ψ → G}

lemma value_small {S : Set Y} (H : ∀ c, c ⊑ S → ρ c = ◁ ρ c) :
    ∀ k c, c ⊑ S → value ρ k c = ρ c
  | 0, c, _ => rfl
  | k + 1, c, h => by
    rw [H c h, value]
    congr <;> exact value_small H k _ fun s => h _

lemma value_mem {H : Subgroup G} (hm : ∀ c, ρ c = ◁ ρ c)
    (hH : ∀ c : Ψ, (∃ j, c ⊑ W j) → ρ c ∈ H) : ∀ k (c : Ψ), Fine W k c → ρ c ∈ H
  | 0, c, h => hH c $ (h 0).imp fun j hj s => hj s $ Real.dist_le_of_mem_Icc_01 s.2 zero_mem
  | k + 1, c, h => by
    rw [hm]
    apply H.mul_mem <;> exact value_mem hm hH k _ $ fine_comp h _ $ hf_dist _

variable (h : □)
def eS := h.curry
def tr := (h.comp .prodSwap).curry
def quad a b := h.comp $ (hf a).prodMap $ hf b
notation "⊞" ρ:max h:max => ρ (tr h 1) * ρ (eS h 0) = ρ (eS h 1) * ρ (tr h 0)
lemma eS_quad : eS (quad h a b) t = (eS h $ hf a t).comp (hf b) := rfl
lemma tr_quad : tr (quad h a b) s = (tr h $ hf b s).comp (hf a) := rfl

lemma square (H2 : ∀ h : □, (∃ j, h ⊑ W j) →
      ⊞ ρ h) :
    ∀ k (h : □), Fine W k h →
      ⊞ (value ρ k) h
  | 0, h, hh => H2 h $ (hh 0).imp fun j hj x => hj x $ max_le (Real.dist_le_of_mem_Icc_01 x.1.2 zero_mem) $ Real.dist_le_of_mem_Icc_01 x.2.2 zero_mem
  | k + 1, h, hh => by
    have q a b := square H2 k (quad h a b) (fine_comp hh _ fun x y =>
      (mul_max_of_nonneg _ _ $ by norm_num).trans_le $ max_le_max (hf_dist ..) $ hf_dist ..)
    have := q 0 0
    have := q 0 1
    have := q 1 0
    have := q 1 1
    simp_all [value, eS_quad, tr_quad, hfv, eq_mul_inv_iff_mul_eq.symm]
    group

section
variable [TopologicalSpace Z] [TopologicalSpace V] [TopologicalSpace W'] (g : C(Z, V))
  (t : ∀ z, Path b $ g z)

variable {x y z : V}
def qm (q : Path x y) : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦q⟧
lemma qm_trans (p : Path x y) : qm (p.trans q) = qm p ≫ qm q := rfl
lemma qm_symm (q : Path x y) : qm q.symm = inv (qm q) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

lemma conj_mem {N : Subgroup (FundamentalGroup V b)} {x m : FundamentalGroup V b}
    (h : x ≫ m ≫ inv x ∈ N) (hx : N.Normal ∨ x ∈ N) : m ∈ N := by
  rw [← Groupoid.inv_eq_inv] at h
  change x⁻¹ * m * x ∈ N at h
  rcases hx with hx | hx
  convert hx.conj_mem _ h x
  group
  convert N.mul_mem (N.mul_mem hx h) $ N.inv_mem hx
  group

variable {y z : Z} (p : Path y z)
def kap' : FundamentalGroup V b := qm (t y) ≫ qm (p.map g.2) ≫ inv (qm $ t z)

notation "✦" => kap' g t
def kap c := ✦ (⟨c, rfl, rfl⟩ : Path _ _)

notation "✧" => kap g t
lemma kap_eq : ✧ p.toContinuousMap = ✦ p := by
  obtain ⟨c, rfl, rfl⟩ := p
  rfl

lemma kap'_trans :
    ✦ (.trans p q) = ✦ q * ✦ p := by
  simp [kap', qm_trans]



lemma kap'_refl : ✦ (.refl y) = 1 := by
  change qm _ ≫ 𝟙 _ ≫ inv _ = _
  simp

lemma kap1 c : ✧ c = ◁ ✧ c := by
  let p₁ : Path _ _ := ⟨c.comp _, congrArg c hfv.1, rfl⟩
  let p₂ : Path _ _ := ⟨c.comp _, congrArg c hfv.2.1.symm, congrArg c hfv.2.2⟩
  have : (p₁.trans p₂).toContinuousMap = c := by
    ext s
    erw [Path.trans_apply]
    split_ifs <;> exact congrArg c $ Subtype.ext $ by simp [hf]
  nth_rw 1 [← this]
  rw [kap_eq, kap'_trans, ← kap_eq _ _ p₁, ← kap_eq _ _ p₂]

lemma kap2 h :
    ⊞ ✧ h := by
  have : ✦ _ = ✦ _ := congrArg (qm _ ≫ · ≫ inv _) (Path.Homotopic.Quotient.eq.2 ((Path.Homotopic.map_trans_evalAt
    (⟨h, fun _ => rfl, fun _ => rfl⟩ : ContinuousMap.Homotopy (eS h 0) $ eS h 1) Path.id).map g))
  rwa [kap'_trans, kap'_trans] at this
lemma kap'_pre :
    kap' g (.trans T $ s ·) p =
      ((Groupoid.isoEquivHom ..).symm $ qm T).symm.conj (kap' g s p) := by
  simp [kap', Iso.conj_apply, qm_trans]
lemma kap'_map (h : C(V, W'))
    s :
    kap' (h.comp g) (fun z => (s z).map h.2) p = FundamentalGroup.map h a (kap' g s p) := by
  change _ = (FundamentalGroupoid.map h).map _
  simp only [kap', Functor.map_comp, Functor.map_inv]
  rfl
lemma kap'_htpy (H : φ₀.Homotopy φ₁) (s : ∀ z, Path b _) : kap' φ₀ (fun z => (s z).trans (H.evalAt z).symm) p = kap' φ₁ s p := by
  have key : qm _ ≫ qm _ = qm _ ≫ qm _ :=
    Path.Homotopic.Quotient.eq.2 $ Path.Homotopic.map_trans_evalAt H p
  simp [kap', qm_trans, qm_symm, reassoc_of% key]

lemma kap_comp (φ : C(W', Z)) c :
    ✧ (φ.comp c) = kap (g.comp φ) (t $ φ ·) c := rfl

lemma kap'_congr (hy : qm (t y) = qm (t' y))
    (hz : qm (t z) = qm (t' z)) : ✦ p = kap' g t' p := by simp [kap', hy, hz]

variable [SimplyConnectedSpace Z]
notation "⊙" => Path.Homotopic.Quotient.eq.2 $ (SimplyConnectedSpace.paths_homotopic ..).map g
lemma kap'_flat (T : Path b c)
    (r : ∀ z, Path a z) :
    kap' g (fun z => T.trans $ ((r z).map g.2).cast hc rfl) p = 1 := by
  subst hc
  have : qm ((r y).map g.2) ≫ qm (p.map g.2) = qm ((r z).map g.2) := by
    rw [← qm_trans, ← Path.map_trans]
    exact ⊙
  simp [kap', qm_trans, reassoc_of% this]

lemma hom_lift {p q : Path x w} (p' q' : Path a c)
    (hp : ∀ s, p s = g (p' s)) (hq : ∀ s, q s = g (q' s)) : qm p = qm q := by
  obtain rfl : x = g a := by simpa using hp 0
  obtain rfl : w = g c := by simpa using hp 1
  obtain rfl : p = p'.map g.2 := Path.ext $ funext hp
  obtain rfl : q = q'.map g.2 := Path.ext $ funext hq
  exact ⊙
end


theorem circleGenerator_generates g : ∃ n : ℤ, circleGeneratorClass ^ n = g := by
  let Φ := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv ⟨0, Circle.exp_zero⟩
  have h1 : Φ circleGeneratorClass = .op (.ofAdd ⟨2 * Real.pi, AddSubgroup.mem_zmultiples _⟩) := by
    refine Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_apply_eq_Iff.2 $ Eq.trans ?_ $ DFunLike.congr_fun ((Circle.isAddQuotientCoveringMap_exp.isCoveringMap.eq_liftPath_iff' (Γ := ⟨(· * _), by fun_prop⟩) _).2 ⟨rfl, by simp⟩) 1
    simp
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (Φ g).unop.toAdd.2
  use n
  apply Φ.injective
  apply MulOpposite.unop_injective
  ext
  simp [h1, hn]

def pol (z : ℂ) : Circle :=
  ⟨if z = 0 then 1 else z / ‖z‖, by split_ifs with h <;> simp [Submonoid.unitSphere, h]⟩

lemma ne0 {z : ℂ} (h : 0.5 < ‖z‖) : z ≠ 0 := norm_pos_iff.1 $ by linarith

lemma pol_cont : ContinuousOn pol {0}ᶜ :=
  Topology.IsInducing.subtypeVal.continuousOn_iff.2 $ ContinuousOn.congr (f := fun z : ℂ => z / ‖z‖) (by fun_prop (disch := simp_all))
    fun z hz => if_neg hz

instance : SimplyConnectedSpace Disk :=
  @SimplyConnectedSpace.ofContractible _ _ (Convex.contractibleSpace (s := {z : ℂ | ‖z‖ ≤ 1})
    (by simpa [Metric.closedBall] using convex_closedBall (0:ℂ) 1) ⟨0, by simp⟩)

def clamp (w : ℂ) : Disk := ⟨w / max 1 ‖w‖, by
  simp [abs_of_pos, div_le_one_of_le₀]⟩
notation "♮" t:max z:max => clamp ((1 + t : ℝ) * z)

lemma clamp_cont : Continuous clamp :=
  (continuous_id.div (by fun_prop) fun w => Complex.ofReal_ne_zero.2 $ by positivity).subtype_mk _

open Classical
variable {f : ι → C(Circle, X)} {z : Disk}
lemma clamp0 : ♮ (0:I) z = z := by
                                                     simp [clamp, z.2]
notation "χ" => characteristic f
notation "⊚" => χ i
notation "⋆" => ‖z.1‖ < 1
notation "Ω" => Space f
notation "◇" => inclusion f

lemma qcont [TopologicalSpace T] {F : Ω → T} (hS : IsOpen S)
    (h1 : ∀ x, ◇ x ∈ S → ContinuousAt (F ∘ ◇) x)
    (h2 : ∀ i z, ⊚ z ∈ S → ContinuousAt (F ∘ ⊚) z) :
    ContinuousOn F S := by
  refine (isQuotientMap_quot_mk.continuousOn_isOpen_iff hS).2 ?_
  rintro (x | ⟨i, z⟩) h
  exact (Topology.IsOpenEmbedding.inl.continuousAt_iff.1 $ h1 x h).continuousWithinAt
  exact ((Topology.IsOpenEmbedding.inr.comp .sigmaMk).continuousAt_iff.1 $ h2 i z h).continuousWithinAt

notation "Λ" a:max b:max => Quot.lift (Sum.elim a fun p => b) (by rintro _ _ ⟨⟩
                                                                  simp [boundaryInclusion, pol]
                                                                  try rfl)
def U : Set Ω := Λ 1 ‖p.2.1‖ ⁻¹' Set.Ioi 0.5
notation "𝒰" => U (f := f)
lemma incl_U x : ◇ x ∈ 𝒰 := show _ < 1 by norm_num

def V (i : ι) : Set Ω :=
  Λ 1 (if p.1 = i then ‖p.2.1‖ else 1) ⁻¹' Set.Iio 1

def cov (o : Option ι) := o.elim 𝒰 V

lemma cov_open : ∀ o, IsOpen (cov o : Set Ω) := by
  rintro (_ | i) <;> refine (continuous_quot_lift _ (continuous_const.sumElim (continuous_sigma fun _ => by first | fun_prop | dsimp; split_ifs <;> fun_prop))).isOpen_preimage _ ?_
  exacts [isOpen_Ioi, isOpen_Iio]

def E : Ω → Option (Σ _ : ι, Disk) :=
  Λ (fun _ => none) (if ‖p.2.1‖ < 1 then some p else none)

variable (hz : ⋆)
include hz in
lemma E_char : E (⊚ z) = some ⟨i, z⟩ := if_pos hz

lemma E_some (h : E y = some p) : y = χ p.1 p.2 := by
  rcases y with ⟨x | q⟩ <;> simp [E] at h
  obtain ⟨-, rfl⟩ := h
  rfl

def Z (y : Ω) := (E y).elim (boundaryInclusion 1) Sigma.snd

include hz in
lemma Z_char : Z (⊚ z) = z := by
  simp [Z, E_char hz]

lemma V_char (h : χ j z ∈ V i) : j = i ∧ ⋆ := by
  change (if j = i then _ else _) < 1 at h
  split_ifs at h <;> simp_all

lemma Z_spec (h : y ∈ V i) : ‖(Z y).1‖ < 1 ∧ ⊚ (Z y) = y := by
  rcases y with ⟨x | ⟨j, z⟩⟩
  cases lt_irrefl _ h
  obtain ⟨rfl, hz⟩ := V_char h
  erw [Z_char hz]
  exact ⟨hz, rfl⟩

lemma Z_cont : ContinuousOn Z (V i : Set Ω) := by
  refine qcont (cov_open $ some i) (fun x h => absurd h $ lt_irrefl _) fun j z h => ?_
  obtain ⟨rfl, hz⟩ := V_char h
  exact continuousAt_id.congr ((continuous_subtype_val.norm.continuousAt.eventually_lt
    continuousAt_const hz).mono fun w hw => (Z_char hw).symm)

def R' : Ω → X := Λ id (f p.1 $ pol p.2)

def R : C(𝒰, X) := ⟨_, (qcont (F := R') (cov_open none) (fun x _ => continuousAt_id) fun i z h => (f i).2.continuousAt.comp $ (pol_cont.continuousAt
    (isOpen_compl_singleton.mem_nhds $ ne0 h)).comp continuous_subtype_val.continuousAt).restrict⟩

def D : C(Ω × I, Ω) :=
  ⟨fun q => Quot.lift (Quot.mk _ ∘ Sum.map id fun p : Σ _, Disk => ⟨p.1, ♮ q.2 p.2.1⟩) (fun _ _ ⟨i, w⟩ => (congrArg ⊚ (by
      have := q.2.2.1
      simp [clamp, boundaryInclusion, abs_of_nonneg, add_nonneg, this, -Complex.ofReal_add]
      exact mul_div_cancel_left₀ _ $ by norm_cast
                                        linarith)).trans
    (characteristic_boundary ..)) q.1,
    isQuotientMap_quot_mk.continuous_lift_prod_left $ (Homeomorph.sumProdDistrib.symm.comp_continuous_iff').1 (continuous_sum_dom.2
      ⟨◇.2.comp continuous_fst, (Homeomorph.sigmaProdDistrib.symm.comp_continuous_iff').1
        (continuous_sigma fun i => ⊚.2.comp $ clamp_cont.comp (by fun_prop : Continuous fun p : Disk × I => ((1 + p.2 : ℝ) : ℂ) * p.1))⟩)⟩

lemma clamp_two (hz : 0.5 < ‖z.1‖) :
    ♮ (1:I) z.1 = boundaryInclusion (pol z) := by
  simp [clamp, pol, ne0 hz, boundaryInclusion, one_add_one_eq_two, max_eq_right (by linarith : 1 ≤ 2 * ‖z.1‖)]
  ring

def F : ContinuousMap.Homotopy (.subtypeVal 𝒰)
    (◇.comp R) where
  toFun q := D (q.2.1, q.1)
  map_zero_left := by
    rintro ⟨⟨x | ⟨i, z⟩⟩, -⟩
    rfl
    exact congrArg ⊚ clamp0
  map_one_left := by
    rintro ⟨⟨x | ⟨i, z⟩⟩, hy⟩
    rfl
    exact (congrArg ⊚ $ clamp_two hy).trans $ characteristic_boundary ..


lemma cov_cover : ∀ y : Ω, ∃ o, y ∈ cov o := by
  rintro ⟨x | ⟨i, z⟩⟩
  exact ⟨none, incl_U x⟩
  by_cases h : 0.5 < ‖z.1‖
  exact ⟨none, h⟩
  exact ⟨some i, (if_pos rfl).trans_lt $ by linarith⟩

lemma exists_fine [CompactSpace M] (g : C(M, Ω)) :
    ∃ k, Fine cov k g := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric isCompact_univ (fun j => (cov_open j).preimage g.2)
    (fun x _ => Set.mem_iUnion.2 $ cov_cover _)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ two_inv_lt_one
  exact ⟨k, fun x => (h x trivial).imp fun j hj y hy => hj $ Metric.mem_ball.2 $ by linarith⟩

variable {x₀} (γ : ∀ i, Path x₀ $ f i 1) [PathConnectedSpace X]

def P (y : Ω) : Path x₀ (R' y) :=
  match h : E y with
  | some p => ((γ p.1).trans $ (PathConnectedSpace.somePath 1 $ pol p.2).map (f p.1).2).cast rfl
      (E_some h ▸ rfl)
  | none => PathConnectedSpace.somePath ..

include hz in
lemma P_char : P γ (⊚ z) =
    (γ i).trans ((PathConnectedSpace.somePath 1 _).map (f i).2) := by
  unfold P
  split <;> cases (E_char hz).symm.trans ‹_›
  rfl

notation:max "⊡" a:max b:max => ((PathConnectedSpace.somePath _ b).map (χ a).2).cast (characteristic_boundary ..).symm rfl
def t y :=
  if hy : y ∈ 𝒰 then ((P γ y).map ◇.2).trans (F.evalAt ⟨y, hy⟩).symm
  else match h : E y with
  | some p => (((γ p.1).map ◇.2).trans ⊡ p.1 p.2).cast rfl $ E_some h
  | none => absurd (by rcases y with ⟨x | q⟩ <;> simp [E] at h
                       exact incl_U x
                       exact h.trans_lt' $ by norm_num) hy

include hz in
lemma t_char : qm (t γ _) =
    qm ((γ i).map ◇.2) ≫ qm ⊡ i z := by
  unfold t
  split_ifs with hy
  erw [P_char hz γ, Path.map_trans, qm_trans, qm_trans, Category.assoc]
  congr
  refine hom_lift ⊚ (((PathConnectedSpace.somePath 1 _).map
    boundaryInclusion.2).trans $ (Path.symm ⟨⟨fun τ => ♮ τ z, clamp_cont.comp $ by fun_prop⟩, rfl, rfl⟩).cast (clamp_two hy).symm clamp0.symm)
    _ ?_ fun _ => rfl
  intro
  erw [Path.trans_apply, Path.trans_apply]
  split_ifs
  simp
  rfl
  rfl
  split <;> cases (E_char hz).symm.trans ‹_›
  rfl

notation "◰" => ⟨_, c.2.codRestrict h⟩
def rho (c : C(I, Ω)) : _ ⧸ attachingNormalClosure f x₀ γ :=
  if h : c ⊑ 𝒰 then kap R (P γ ·) ◰ else 1

lemma kill c (hV : c ⊑ V i) : rho γ c = 1 := by
  refine dite_eq_right_iff.2 fun h => (QuotientGroup.eq_one_iff _).2 ?_
  have hz s := Z_spec $ hV s
  let pA : C(⊚ ⁻¹' 𝒰, Circle) := ⟨_,
    pol_cont.comp_continuous (continuous_subtype_val.comp continuous_subtype_val) fun a => ne0 a.2⟩
  let c' : C(I, ⊚ ⁻¹' 𝒰) := ⟨_, (Z_cont.comp_continuous c.2 hV).codRestrict
    fun s => ((hz s).2.symm ▸ h s :)⟩
  obtain ⟨n, hn⟩ := circleGenerator_generates
    (kap pA (PathConnectedSpace.somePath 1 $ pA ·) c')
  rw [← (ContinuousMap.ext fun s => Subtype.ext (hz s).2 :
    (⊚.restrictPreimage 𝒰).comp c' = ◰)]
  refine Eq.mpr (congrArg _ ((kap_comp _ _ _ c').trans ((kap'_congr ((f i).comp pA) _ _
    (congrArg qm $ P_char (hz 0).1 γ) $ congrArg qm $ P_char (hz 1).1 γ).trans
    ((kap'_pre ..).trans $ congrArg _ $ (kap'_map ..).trans $ congrArg _ hn.symm)))) ?_
  simp [map_zpow]
  exact zpow_mem (Subgroup.subset_normalClosure $ Set.mem_range_self i) n

def completeStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {ι : Type v}
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)),
    Function.Surjective (inclusionPi1 f x₀) ∧
    (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ ∧
    ∃ e : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀

notation "⊠" => inclusionPi1 f x₀
notation "◫" => q.map $ ◇.2.codRestrict incl_U
theorem two_cell_attachment : completeStatement.{u,v} := fun f x₀ γ =>
  have hs := by
    rintro ⟨ℓ⟩
    have h1 := value_mem (H := ⊠.range) (kap1 (.id _) $ t γ) ?_ _ _ (exists_fine ℓ.toContinuousMap).choose_spec
    erw [kap_eq] at h1
    exact conj_mem h1 $ .inr ⟨qm $ P γ $ ◇ x₀, by simp [t, incl_U]
                                                  exact (Category.comp_id _).symm⟩
    rintro c ⟨_ | i, h⟩
    refine ⟨kap R (P γ ·.1) ◰, Eq.symm ?_⟩
    show kap (.subtypeVal 𝒰) (t γ ·) ◰ = _
    simp [t]
    exact (kap'_htpy _ F _).trans $ kap'_map ..
    have hz s := Z_spec $ h s
    rw [← (ContinuousMap.ext fun s => (hz s).2 : ⊚.comp
      ⟨_, Z_cont.comp_continuous c.2 h⟩ = c)]
    convert one_mem ⊠.range
    exact (kap_comp ..).trans $ (kap'_congr _ _ _ (t_char (hz 0).1 γ)
      (t_char (hz 1).1 γ)).trans $ kap'_flat ..
  have hker : ⊠.ker = attachingNormalClosure f x₀ γ := le_antisymm (by
    rintro ⟨ℓ⟩ hg
    obtain ⟨H⟩ := Quotient.exact hg
    obtain ⟨k, hk⟩ := exists_fine H.toContinuousMap
    have hsq := square (ρ := rho γ) (fun c => by
      rintro ⟨_ | i, h⟩
      simp [rho, show c ⊑ 𝒰 from h, tr, eS]
      exact congrArg _ $ kap2 _ _ ◰
      simp [kill γ (tr c _) fun s => h _, kill γ (eS c _) fun s => h _]) k _ hk
    have e c (q : Path x₀ x₀ := .refl _) (hc : ∀ s, c s = ◇ (q s) := by simp [tr, eS]) :
        value (rho γ) k c = kap' R (P γ ·) ◫ := by
      obtain rfl : c = q.map ◇.2 := ContinuousMap.ext hc
      rw [value_small (fun c h => by
        simp [rho, h]
        exact congrArg _ $ kap1 ..)
        k _ (incl_U $ q ·)]
      exact (dif_pos fun s => incl_U _).trans $ congrArg _ $ kap_eq _ _ ◫
    erw [e _, e $ tr _ 0, e $ eS _ 1, e _ ℓ, mul_right_inj, kap'_refl] at hsq
    have := (QuotientGroup.eq_one_iff _).1 hsq
    exact conj_mem this $ .inl inferInstance)
  $ Subgroup.normalClosure_le_normal $ by
    rintro _ ⟨i, rfl⟩
    have : qm ((circleGenerator.map (f i).2).map ◇.2) = 𝟙 _ :=
      hom_lift ⊚ (circleGenerator.map boundaryInclusion.2) (.refl _)
        (fun _ => by simp) fun _ => by simp
    show qm _ = 𝟙 _
    simp [attachingLoop, qm_trans, this, ← Path.map_symm, qm_symm, -Path.map_map]
  ⟨hs, hker, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs), rfl⟩

end CellAttachment
