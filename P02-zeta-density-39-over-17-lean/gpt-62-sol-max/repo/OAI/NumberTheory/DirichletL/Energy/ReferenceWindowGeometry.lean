module
public import OAI.NumberTheory.DirichletL.Energy.DeletedRobustGeometry
public import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionGeometry

@[expose] public section
namespace OAI.SevenEighths.CenteredMomentEnergyReferenceWindowGeometry
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
  CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyLiveClippingDefect
local notation "O" => HeckeFamily.O

/-- Use either the two actual lengths or the balanced comparison pair. -/
inductive ReferenceWindow where
  | actual | balanced

abbrev ReferenceWindow.left (m : ReferenceWindow) (Z w X : ℝ) : ℝ :=
  match m with | .actual => X | .balanced => comparisonFirst Z w

abbrev ReferenceWindow.right (m : ReferenceWindow) (Z w X Y : ℝ) : ℝ :=
  match m with | .actual => Y | .balanced => comparisonSecond Z w X Y

abbrev ReferenceWindow.reserve (m : ReferenceWindow) (w xi defect : ℝ) : Prop :=
  match m with | .actual => xi ≤ w/14 | .balanced => xi+11*defect/7 ≤ w/14

abbrev ReferenceWindow.admitted (m : ReferenceWindow) (Z w X Y ell κ defect : ℝ) : Prop :=
  match m with
  | .actual => length Z X≤w/4 ∧ 5*w/6≤length Z X+length Z Y+ell ∧
      length Z X+length Z Y+6*κ*ell≤w
  | .balanced => 5*w/6-defect≤Real.logb Z (X*Y)+ell ∧
      Real.logb Z (X*Y)+ell+(6*κ-1)*ell≤w

abbrev ReferenceWindow.defect (m : ReferenceWindow) (rho : ℝ) : ℝ :=
  match m with | .actual => 0 | .balanced => rho/100

theorem ReferenceWindow.positive (m : ReferenceWindow) {Z w X Y : ℝ}
    (hZ : 0<Z) (hX : 0<X) (hY : 0<Y) : 0<m.left Z w X ∧ 0<m.right Z w X Y := by
  cases m
  · exact ⟨hX,hY⟩
  · exact comparison_positive Z w X Y hZ hX hY

theorem ReferenceWindow.reserve_of_le (m : ReferenceWindow) {w xi rho : ℝ}
    (hxi : 0<xi) (hxr : xi≤rho/100) (hrw : rho≤w) : m.reserve w xi (m.defect rho) := by
  cases m <;> dsimp [ReferenceWindow.reserve, ReferenceWindow.defect] <;> linarith

theorem ReferenceWindow.slots_le_width (m : ReferenceWindow) {Z w X Y ell κ xi defect : ℝ}
    (hZ : 1<Z) (hκ : 3/4≤κ) (hell : 0≤ell) (hxi : 0<xi)
    (hr : m.reserve w xi defect) (h : m.admitted Z w X Y ell κ defect) : ell≤w := by
  cases m
  · have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hell
    linarith [length_nonneg Z X hZ,length_nonneg Z Y hZ,h.2.2]
  · have hg := robust_slot_budgets w (Real.logb Z (X*Y)) ell κ defect hell hκ h.1 h.2
    change xi+11*defect/7≤w/14 at hr
    linarith [hg.1]

theorem ReferenceWindow.deleted_gates (m : ReferenceWindow) {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0<xi)(he:0≤e)(hxiM:m.reserve s.width xi e)
    (h:m.admitted Z s.width X₁ X₂ ell κ e)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let Y₁ := m.left Z s.width X₁
    let Y₂ := m.right Z s.width X₁ X₂
    let short:=Real.logb Z (Y₁/((∏P∈D₁,P).absNorm:ℝ))
    let along:=Real.logb Z (Y₂/((∏P∈D₂,P).absNorm:ℝ))
    Z^short=Y₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=Y₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)) := by
  cases m
  · have hw : 0<s.width := by change xi≤s.width/14 at hxiM; linarith
    exact CenteredMomentEnergyOriginalHighReflectionGeometry.actual_deleted_gates s hZ hw hB
      Mcap L X₁ X₂ ell z κ xi hwidth hL hX₁ hX₂ hell hz hze hκ hxi.le hxiM h.1 h.2.1 h.2.2 D₁ D₂ hD₁ hD₂
  · dsimp [ReferenceWindow.left,ReferenceWindow.right]
    have hZp := zero_lt_one.trans hZ
    have hp := comparison_positive Z s.width X₁ X₂ hZp hX₁ hX₂
    have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 := Real.logb_rpow hZp hZ.ne'
    have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
      rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hZp hZ.ne']
    rw [Real.logb_div (b:=Z) hp.1.ne' (zero_lt_one.trans_le (divisor_norm s D₁ hD₁).1).ne',
      Real.logb_div (b:=Z) hp.2.ne' (zero_lt_one.trans_le (divisor_norm s D₂ hD₂).1).ne', hf, hl]
    exact CenteredMomentEnergyDeletedRobustGeometry.actual_deleted_gates s hZ hB
      Mcap L X₁ X₂ ell z κ xi e hwidth hL hX₁ hX₂ hell hz hze hκ hxi.le he hxiM h.1 h.2 D₁ D₂ hD₁ hD₂

end
end OAI.SevenEighths.CenteredMomentEnergyReferenceWindowGeometry
