module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveStepScalars
public import OAI.NumberTheory.DirichletL.Descent.FirstSecondHeightCost

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks InverseMomentFirstChildWindows InverseAmbientProfileTower
open JointLogSeparation FourierBridge InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell
open CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_first_height
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∀eps:ℝ,0<eps → ∃C:ℝ,0<C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[OAI.PrincipalFamily.Maximal p]
      (hcop:OAI.PrincipalFamily.Coprime p)
      (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta Kphysical loss:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A → 0≤epschild → -saving≤r+3*ell+V+48*eta+tau+pi+epschild+eps →
      48*eta+tau+pi+epschild+eps≤loss →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree → ∀z:Frequency×(Fin 9 → ℝ),
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) (InverseMomentFirstSecondHeightCost.firstHeight negative z) (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      (C*(1+A)*Z^(r+3*ell+V+loss))*
        (tripleHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.1*
          coordinateHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.2) :=by
  let cap:=3*F+16
  have hbig:0≤16*cap+20:=by positivity
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_label_cell_step om lo hi hlo hs negative
    window (16*cap+20) (16*cap+20) tau saving (hhib.trans hwindow) hbig hbig htau b hb ed hed (fun _=>0) (by norm_num) K em hem
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree eps heps
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  obtain ⟨Ctotal,hCtotal,hlossBound⟩:=InverseMomentFirstSecondHeightCost.first_source_requested_loss degree C Cbin Cz Ct eps hC hCz hCt heps
  refine ⟨Ctotal,hCtotal,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta Kphysical loss hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA hechild hsave hloss cutoff W mark S k hk hchild z
  let t := InverseMomentFirstSecondHeightCost.firstHeight negative z
  have hZ1:1<Z:=by linarith
  obtain ⟨hY1,hX1,hcol,hYcap,hYi,hgeom,hphysical,hPcap,hbudget,hcost,hellcap,hactivecap,hcommoncap,hquotcap⟩:=
    original_live_step_scalars p hp hcop hg pool Q labels β Ψ m mark old Φ Kphysical Z M r ell V F eta tau theta oldb b window em ed pi
      hZ1 hbin hF hM hMF hr hrF hell hellF hV hVF heta heta1 htau.le htau1 hwin hold hwindow hem.le hed.le hpi hetapi
      hsmall hsmall' hQ hn hsold k hk negative
  apply le_trans _ (hlossBound A Z (r+3*ell+V) eta tau pi epschild saving loss hA hZ heta hechild hsave hloss negative z)
  apply hstep p hp hcop hg hpr hinj hc pool Q k.1 k.2.1 k.2.2 Ψ m slots lists weights
    Z M r ell V eta pi b (cap+1) (4*cap+2) epschild A t (fun _=>0)
    hZ heta hbin (by linarith) hQ hslots hcard hw hΨ (by simp) hhib le_rfl hb
  all_goals try assumption
  · exact (hwindow.trans hwin).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hYi.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hcol.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  all_goals assumption

end SevenEighths.InverseMoment

end

end OAI
