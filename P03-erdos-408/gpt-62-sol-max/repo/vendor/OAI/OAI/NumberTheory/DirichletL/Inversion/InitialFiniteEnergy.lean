module

public import OAI.NumberTheory.DirichletL.Inversion.InitialRetainedPhysical
public import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalDomains
public import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateWindow
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerFixedWindows
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerEmpty
public import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyRetained
public import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailBound
public import OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds

public import OAI.NumberTheory.DirichletL.Inversion.InitialAssignments

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialFiniteEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerSourceMask InverseInitialCanonicalState FirstPassCubeLabels
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds InverseSecondChildWindows Filter
local notation "O"=>ActualEisensteinCubic.O

theorem finite_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=poolPrimary_maximal F hF;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ForInitialAssignments (fun P : primePool F => (P.val.absNorm : ℝ)) K Z fun σ _ all assigned lists Hslot coeff qelem z al bl primeW =>
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ForInitialSourceScales all assigned Hslot z bl Z cap η gap fun D m r =>
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ
        (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0<max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  let lo : Fin 4 → ℝ := fun _ => 1/4
  let hi : Fin 4 → ℝ := fun _ => 1
  have hlo₀ : ∀ i, 0 < lo i := by intros; norm_num [lo]
  have hhi₀ : ∀ i, lo i ≤ hi i := by intros; norm_num [lo,hi]
  obtain ⟨fresh,Vlog,Mlog,af,bf,haf,hab,hfc,hfs,hM,hVc,hVs,hwindow⟩:=
    InverseInitialEnergyCallerFixedWindows.exists_actual_initial_windows
      W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ lo hi hlo₀ hhi₀
  have hfs':Function.support (fresh:ℝ→ℂ)⊆Set.Icc af (max 1 bf):=by
    intro x hx
    have h:=hfs (subset_closure hx)
    exact ⟨h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨J,Btree,hBtree,hbound⟩:=InverseInitialRetainedPhysical.retained_physical_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ (fun i=>Vlog i) Mlog
    (fun i=>(Vlog i).smooth ⊤) hVc hM (fun i y hy=>abs_le.mpr (hVs i hy))
    fresh fresh af (max 1 bf) haf (le_max_left _ _) hfs' hfs' (fresh.smooth ⊤) (fresh.smooth ⊤)
    cap gap eps (cap+3) π hcap hgap heps (by linarith) hπ K
  let Tclip := Real.log (max 1 bf)
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 (by norm_num)
  obtain ⟨ss,Ct,hCt,htail⟩:=InverseInitialDyadicTailBound.actual_high_mass_tail (2*cap+2) 1 τ hτ
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC:0≤tailC:=by dsimp [tailC];positivity
  have htailEvent:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩ := eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and (hevent.and htailEvent))))
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Zq,hC,hZq,hwnd⟩ := hbound q hq
  let Cr := A*C
  have hCr : 0 < Cr := mul_pos hA hC
  refine ⟨Cr+tailC,max Zq Zaux,by linarith,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=poolPrimary_maximal F hFa
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZq':=(le_max_left _ _).trans hZ
  have hZp:1<Z:=hZq.trans_le hZq'
  obtain ⟨hcZ,hpow,hlog,hexp,hbZ,h64⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z^D≤Z^(2*cap+2):=by
    calc
      _≤Z*Z^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z^(D+1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  have hs₁':Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₁ a₀ b₀ c₁ θ₁ ha₀ hc₁ hs₁ hx) (le_max_right 1 b₀)
  have hs₂':Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₂ a₀ b₀ c₂ θ₂ ha₀ hc₂ hs₂ hx) (le_max_right 1 b₀)
  obtain ⟨T,hT,hfreqcap⟩:=exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hret :
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          Sc w Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        Cr*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
    have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
    have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
    have hloZ:Z^(-η)≤lo 1:=by
      rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
      simpa only [one_div,lo] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
    have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
        (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
        ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
          (primeMark (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
          (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
          C*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
      have hsize:0<max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
      have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
      have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
      let B := exponent Z (k 0).val
      let v := exponent Z (k 2).val
      let θ := exponent Z (k 1).val
      let H := exponent Z (k 3).val
      let ψ := cutoff
      let w' := fun x => w x*outerCutoff ψ (sourceRelative p x Z D B v θ H)
      have hψ (i : Fin 4) : Function.support (ψ i) ⊆ Set.Icc (lo i) (hi i) :=
        fun _ hx => Set.Ioo_subset_Icc_self (cutoff_support i hx)
      have hhiZ : ∀ i, hi i ≤ Z^η := fun _ => by dsimp [hi]; linarith
      have hupper : B-θ+2*η ≤ cap+3 := by dsimp [B,θ]; linarith [h0.2,h1.1]
      have hrad := (Finset.mem_filter.mp hk).2
      have hw' : ∀ x ∈ Sc, ‖w' x‖ ≤ 1 := by
        intro x hx
        dsimp [w']; rw [norm_mul]
        have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
          (mul_le_of_le_one_left hb₀ ha).trans hb
        apply hmul (hw x (Finset.mem_filter.mp hx).1) (by positivity)
        unfold outerCutoff
        simp only [norm_mul]
        exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
          (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
      have hprimary:=InverseInitialRayAttachment.poolPrimary_primary F hFa
      let Swin:=windowSource p Sc ψ Z D B v θ H
      let Swcop:=coprimeSource p Swin
      have hdivw:∀x∈Swin,x.divisor⊆x.common:=fun x hx=>hdivc x (Finset.mem_filter.mp hx).1
      have hfw:∀x∈Swin,x.frequency≠0:=fun x hx=>hfc x (Finset.mem_filter.mp hx).1
      have hdivwc:∀x∈Swcop,x.divisor⊆x.common:=fun x hx=>hdivw x (Finset.mem_filter.mp hx).1
      have hfc':∀x∈Swcop,x.frequency≠0:=fun x hx=>hfw x (Finset.mem_filter.mp hx).1
      have hswhole:=hwindow p hp Finset.univ Sc hdivc hfc ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂
        (zero_lt_one.trans hZp) hc₁ hbc₁ hc₂ hbc₂
      have hpoint:pointSource Finset.univ Swcop⊆pointSource Finset.univ Swin:=by
        intro x hx
        obtain ⟨y,hy,hm⟩:=Finset.mem_biUnion.mp hx
        exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hm⟩
      have hsupport:BlockSupport p (pointSource Finset.univ Swcop) W₁ W₂ fresh fresh
          (fun i=>Vlog i) Z D B v θ H c₁ c₂ θ₁ θ₂:=
        ⟨fun x hx=>hswhole.1 x (hpoint hx),fun x hx=>hswhole.2.1 x (hpoint hx),
          fun x hx=>hswhole.2.2 x (hpoint hx)⟩
      unfold windowBlock
      rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
      by_cases hempty:physicalBlock p hp hcop hg (pointSource Finset.univ Swcop) (w'∘erasePoint) Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
      · rw [hempty,norm_zero];positivity
      have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
        hprimary Finset.univ Swcop hdivwc hfc' (w'∘erasePoint) Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
        Z D B v θ H m c₁ c₂ θ₁ θ₂ af (max 1 bf) η hZp (le_max_left _ _) hfs' hsupport hlog hempty).2
      have hqt:quotientSet p Swcop⊆quotientSet p Swin:=
        Finset.image_subset_image (Finset.filter_subset _ _)
      have hn:∀t∈quotientSet p Swcop,(t.absNorm:ℝ)≤Z^(B-θ+2*η):=by
        intro t ht
        exact retained_quotient_bound p hp Sc (fun _=>1) (ψ 0) (ψ 1)
          (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZp)
          (hψ 0) (hψ 1) (hhiZ 0) hloZ hdivc t
          (window_quotient_subset_retained p Sc ψ Z D B v θ H (hqt ht))
      have hstates:∀t∈quotientSet p Swcop,
          assignedElement assigned qelem*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
          0≤fullPunctureWidth Z t (assignedElement assigned qelem) ∧
          ‖eisEmbedding (assignedElement assigned qelem*primaryGenerator t)‖^2=
            Z^(fullPunctureWidth Z t (assignedElement assigned qelem)) ∧
          θ+H+2*η≤cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤cap ∧
          CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η)) (θ+H+2*η)
            (fullPunctureWidth Z t (assignedElement assigned qelem))
            (assignedCenter (all\assigned) z+η) gap:=by
        intro t ht
        have hs:=actual_window_state p hp hprimary Sc ψ lo hi hψ Z D B v θ H η hZp hη.le hhiZ hloZ
          hdivc hfc all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj (hqt ht)
          m r τ (2*gap) (2*gap) hDeq hmargin₁ hmargin₂ (by simp;positivity)
          (by simp only [min_self];linarith) (by simp only [min_self];linarith) hrad hclip
        simp only [min_self] at hs
        obtain ⟨hm,hN,hV,hM,hQ,he,hmargin,hF,hMr,hshift⟩:=hs
        refine ⟨hm,hV,hM,hQ,he,hMr.trans hparent,hF.trans hparent,?_⟩
        convert hmargin using 1 <;> simp [columnCenter]
      apply hwnd Z hZq' Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
        lists Hslot coeff (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hHs hPs hac
        (assignedCenter (all\assigned) z+η) (by apply add_nonneg _ hη.le;exact Finset.sum_nonneg (fun i hi=>hz i (Finset.mem_sdiff.mp hi).1))
        hprod Ψ hΨ hperiod Swcop hdivwc hfc' (assignedElement assigned qelem) D B v θ H (B-θ+2*η) m η
        hupper hη.le c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w'
        (fun x hx=>hw' x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
        (idealRange (Z^(θ+v+2*η))) (nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)))
        (fun f hfc=>mem_idealRange.mp hfc) (Finset.Subset.refl _) ?_ ?_ hclip rfl hstates
      · intro k hk
        exact (child_ball_neg _ k).mpr hk
      · intro x hx
        exact InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg (poolPrimary_odd F hFa)
          hprimary Sc hdivc hfc ψ lo hi hψ Z D B v θ H η (zero_lt_one.trans hZp) hhiZ x hx _

    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum hnorm).trans
    rw [Finset.sum_const, nsmul_eq_mul]
    calc
      _≤(A*Z^loss)*(C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
        mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
      _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];dsimp [Cr]; ring

  have hheight:1≤((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂]))
  apply (add_le_add hret ht).trans
  change Cr*Z^(m+15*η+π+eps+loss)*_+(Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-1:ℝ))≤_
  have hh:tailC*Z^(-1:ℝ)≤tailC*Z^(m+15*η+π+eps+loss)*
      ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤tailC*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)) htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert add_le_add_left hh (Cr*Z^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

end SevenEighths.InverseInitialFiniteEnergy

end

end OAI
