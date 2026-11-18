module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicAddress
public import HypoellipticAleksandrov.Measure.ParabolicDyadicInkSpotsBridge
public import HypoellipticAleksandrov.Measure.InkSpotsWind
public import HypoellipticAleksandrov.Measure.InkSpotsHotWind

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped ENNReal Function Topology




/-- The non-root addressed cells that first become wholly contained in `U`. -/
def parabolicDyadicFirstEntry {d : Nat} (U : Set (TimeVelocity d)) :
    Set (ParabolicDyadicAddress d) :=
  fun a => match a with
    | ⟨0, _⟩ => False
    | ⟨_ + 1, index⟩ =>
        parabolicDyadicOpenCell index ⊆ U ∧
          ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ U


/-- The open cell of a child is contained in the open cell of its parent. -/
theorem parabolicDyadicOpenCell_child_subset {d n : Nat}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicOpenCell (parabolicDyadicChildIndex index child) ⊆
      parabolicDyadicOpenCell index := by
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz ⊢
  rw [parabolicDyadicTimeCode_childIndex] at hz
  constructor
  · have hpow : 0 < 4 ^ n := pow_pos (by norm_num) _
    have hchild : 0 ≤ (child.1.val : ℝ) := by positivity
    have htime := hz.1
    norm_num [pow_succ] at htime ⊢
    field_simp [ne_of_gt hpow] at htime ⊢
    nlinarith
  constructor
  · have hpow : 0 < 4 ^ n := pow_pos (by norm_num) _
    have hchild : (child.1.val : ℝ) < 4 := by exact_mod_cast child.1.isLt
    have hchild_le : (child.1.val + 1 : ℝ) ≤ 4 := by
      exact_mod_cast (Nat.succ_le_iff.mpr child.1.isLt)
    have htime := hz.2.1
    norm_num [pow_succ] at htime ⊢
    field_simp [ne_of_gt hpow] at htime ⊢
    nlinarith
  · intro coordinate
    have hpow : 0 < 2 ^ n := pow_pos (by norm_num) _
    have hchild : 0 ≤ ((child.2 coordinate).val : ℝ) := by positivity
    have hvelocity := hz.2.2 coordinate
    rw [parabolicDyadicVelocityCode_childIndex] at hvelocity
    constructor
    · norm_num [pow_succ] at hvelocity ⊢
      field_simp [ne_of_gt hpow] at hvelocity ⊢
      nlinarith [hvelocity.1]
    · have hchild' : ((child.2 coordinate).val : ℝ) < 2 := by
        exact_mod_cast (child.2 coordinate).isLt
      have hchild_le : ((child.2 coordinate).val + 1 : ℝ) ≤ 2 := by
        exact_mod_cast (Nat.succ_le_iff.mpr (child.2 coordinate).isLt)
      norm_num [pow_succ] at hvelocity ⊢
      field_simp [ne_of_gt hpow] at hvelocity ⊢
      nlinarith [hvelocity.2]

private theorem parabolicDyadicOpenCell_subset_truncate {d m n : Nat}
    (hmn : m ≤ n) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index ⊆
      parabolicDyadicOpenCell (parabolicDyadicTruncate hmn index) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n hmn ih =>
      calc
        parabolicDyadicOpenCell index ⊆
            parabolicDyadicOpenCell (parabolicDyadicParent index) := by
          simpa using
            (parabolicDyadicOpenCell_child_subset
              (parabolicDyadicParent index) (index (Fin.last n)))
        _ ⊆ parabolicDyadicOpenCell
            (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) :=
          ih (parabolicDyadicParent index)
        _ = parabolicDyadicOpenCell
            (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
          congr 1

/-- An open addressed cell is contained in the open cell of every ancestor. -/
theorem parabolicDyadicOpenCell_subset_of_addressPrefix {d : Nat}
    {a b : ParabolicDyadicAddress d} (hab : parabolicDyadicAddressPrefix a b) :
    parabolicDyadicOpenCell b.2 ⊆ parabolicDyadicOpenCell a.2 := by
  rcases hab with ⟨hmn, htruncate⟩
  rw [← htruncate]
  exact parabolicDyadicOpenCell_subset_truncate hmn b.2


/-- Open cells indexed by distinct first entries are pairwise disjoint. -/
theorem pairwiseDisjoint_parabolicDyadicFirstEntry_openCell {d : Nat}
    (U : Set (TimeVelocity d)) :
    (parabolicDyadicFirstEntry U).Pairwise
      (Disjoint on (fun a : ParabolicDyadicAddress d => parabolicDyadicOpenCell a.2))  := by
  have isAntichain_parabolicDyadicFirstEntry :
      IsAntichain (parabolicDyadicAddressPrefix)
      (parabolicDyadicFirstEntry U) := by
    rintro ⟨m, a⟩ ha ⟨n, b⟩ hb hne hab
    cases m with
    | zero =>
        change False at ha
        exact ha
    | succ m =>
        cases n with
        | zero =>
            change False at hb
            exact hb
        | succ n =>
            rcases hab with ⟨hmn, htruncate⟩
            change m + 1 ≤ n + 1 at hmn
            change parabolicDyadicTruncate hmn b = a at htruncate
            by_cases hmnEq : m + 1 = n + 1
            · have hmnEq' : m = n := by omega
              subst m
              have hba : b = a := by
                calc
                  b = parabolicDyadicTruncate (le_refl (n + 1)) b :=
                    (parabolicDyadicTruncate_self b).symm
                  _ = a := by simpa only using htruncate
              subst a
              exact hne rfl
            · have hlt : m + 1 < n + 1 := lt_of_le_of_ne hmn hmnEq
              have hmn' := Nat.lt_succ_iff.mp hlt
              have hprefix : parabolicDyadicAddressPrefix ⟨m + 1, a⟩
                  ⟨n, parabolicDyadicParent b⟩ := by
                refine ⟨hmn', ?_⟩
                calc
                  parabolicDyadicTruncate hmn' (parabolicDyadicParent b) =
                      parabolicDyadicTruncate (Nat.le_succ_of_le hmn') b := by
                    funext j
                    simp
                    apply congrArg b
                    exact Fin.ext (by rfl)
                  _ = a := by simpa only using htruncate
              exact hb.2 ((parabolicDyadicOpenCell_subset_of_addressPrefix hprefix).trans ha.1)
  rintro a ha b hb hab
  apply disjoint_parabolicDyadicOpenCell_of_incomparable
  · intro habPrefix
    exact isAntichain_parabolicDyadicFirstEntry ha hb hab habPrefix
  · intro hbaPrefix
    exact isAntichain_parabolicDyadicFirstEntry hb ha hab.symm hbaPrefix







/-- The non-root dyadic cells which first enter the actual source D1 union. -/
def parabolicDyadicD1Entry {d : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real) :
    Set (ParabolicDyadicAddress d) :=
  parabolicDyadicFirstEntry (inkSpotsD1 Gamma xi)




private theorem parabolicDyadicD1Entry_openCell_subset
    {d : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real)
    (a : {a : ParabolicDyadicAddress d // a ∈ parabolicDyadicD1Entry Gamma xi}) :
    parabolicDyadicOpenCell a.1.2 ⊆ inkSpotsD1 Gamma xi := by
  rcases a with ⟨⟨n, index⟩, ha⟩
  cases n with
  | zero => exact False.elim ha
  | succ n => exact ha.1

private theorem parabolicDyadicD1_entry_density_le
    {d : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real)
    (a : {a : ParabolicDyadicAddress d // a ∈ parabolicDyadicD1Entry Gamma xi}) :
    (volume (Gamma ∩ parabolicDyadicOpenCell a.1.2)).toReal ≤
      xi * (volume (parabolicDyadicOpenCell a.1.2)).toReal := by
  rcases a with ⟨⟨n, index⟩, ha⟩
  cases n with
  | zero => exact False.elim ha
  | succ n =>
      by_contra hle
      exact ha.2
        (parabolicDyadicOpenCell_parent_subset_inkSpotsD1_of_density_gt Gamma xi index (lt_of_not_ge hle))





/-- Krylov--Safonov, Lemma 2.5: the initial measurable set is controlled by its third
ink-spots enlargement. -/
theorem volume_Gamma_le_inkSpotsD3
    (d : Nat) (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (hGamma : MeasurableSet Gamma)
    (hGammaUnit : Gamma ⊆ inkSpotsUnitBox d)
    (hxi : xi ∈ Set.Ioo (0 : Real) 1)
    (heta : eta ∈ Set.Ioo (0 : Real) 1)
    (hzeta : zeta ∈ Set.Ioo (0 : Real) 1)
    (hsubcritical : (volume Gamma).toReal <
      xi * (volume (inkSpotsUnitBox d)).toReal) :
    (volume Gamma).toReal ≤
      xi * (1 + eta) * zeta ^ (-((d : Int) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal   := by
  let parabolicDyadicAddressBoundary {d : Nat} (a : ParabolicDyadicAddress d) :=
    parabolicDyadicHalfOpenCell a.2 \ parabolicDyadicOpenCell a.2
  have volume_Gamma_le_xi_volume_inkSpotsD1 :
      Gamma ≤ᵐ[volume] inkSpotsD1 Gamma xi ∧
      (volume Gamma).toReal ≤ xi * (volume (inkSpotsD1 Gamma xi)).toReal := by
    let parabolicDyadicAllBoundary (d : Nat) :=
      ⋃ a : ParabolicDyadicAddress d, parabolicDyadicAddressBoundary a
    have volume_inkSpotsUnitBox_ne_top :
        volume (inkSpotsUnitBox d) ≠ ∞ := by
      intro htop
      have hformula : (volume (inkSpotsUnitBox d)).toReal =
          (1 * 1 ^ 2) * (2 * 1) ^ d := by
        simpa only [inkSpotsUnitBox] using
          (volume_parabolicBox_toReal
            (t₀ := 0) (v₀ := 0) (by norm_num) (by norm_num))
      rw [htop] at hformula
      norm_num at hformula
      exact (ne_of_gt (pow_pos (by norm_num : (0 : Real) < 2) d)) hformula.symm
    have parabolicDyadicRoot_openCell_eq_inkSpotsUnitBox :
        parabolicDyadicOpenCell (fun i => Fin.elim0 i : ParabolicDyadicIndex d 0) =
        inkSpotsUnitBox d := by
      ext z
      rcases z with ⟨time, velocity⟩
      rw [mem_parabolicDyadicOpenCell_iff, inkSpotsUnitBox, mem_parabolicBox_iff,
        mem_velocityCube_iff]
      simp [parabolicDyadicTimeCode, parabolicDyadicVelocityCode, abs_lt]
      intro _ _
      constructor <;> intro hvelocity <;> intro coordinate
      · exact ⟨(hvelocity coordinate).1, by linarith [(hvelocity coordinate).2]⟩
      · exact ⟨(hvelocity coordinate).1, by linarith [(hvelocity coordinate).2]⟩
    have parabolicDyadicD1_subset_unit :
        inkSpotsD1 Gamma xi ⊆ inkSpotsUnitBox d := by
      intro z hz
      simp [inkSpotsD1] at hz
      obtain ⟨q, hqDense, hzq⟩ := hz
      exact hzq.2
    have ae_eq_iUnion_parabolicDyadicFirstEntry_openCell (U : Set (TimeVelocity d)) (hU : IsOpen U) (hURef : U ⊆ parabolicDyadicOpenCell (fun i => Fin.elim0 i)) (hRoot : ¬ parabolicDyadicOpenCell (fun i => Fin.elim0 i) ⊆ U) :
        U =ᵐ[volume] ⋃ a ∈ parabolicDyadicFirstEntry U, parabolicDyadicOpenCell a.2 := by
      have exists_parabolicDyadicFirstEntry_of_mem_isOpen_off_boundary (z : TimeVelocity d) (hzU : z ∈ U) (hzBoundary : z ∉ parabolicDyadicAllBoundary d) :
          ∃ a : ParabolicDyadicAddress d,
          a ∈ parabolicDyadicFirstEntry U ∧ z ∈ parabolicDyadicOpenCell a.2 := by
        have exists_parabolicDyadicOpenCell_subset_of_mem_isOpen_off_boundary (hzRef : z ∈ parabolicDyadicReferenceCell d) :
            ∃ a : ParabolicDyadicAddress d,
            z ∈ parabolicDyadicOpenCell a.2 ∧ parabolicDyadicOpenCell a.2 ⊆ U := by
          obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
          obtain ⟨n, htime, hvelocity⟩ :=
            ((tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hε).and
              (tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hε)).exists
          rw [← iUnion_parabolicDyadicHalfOpenCell_eq_reference d n] at hzRef
          obtain ⟨index, hzHalf⟩ := Set.mem_iUnion.mp hzRef
          have hzOpen : z ∈ parabolicDyadicOpenCell index := by
            by_contra hzNotOpen
            apply hzBoundary
            exact Set.mem_iUnion.mpr ⟨⟨n, index⟩, ⟨hzHalf, hzNotOpen⟩⟩
          refine ⟨⟨n, index⟩, hzOpen, ?_⟩
          rintro ⟨time', velocity'⟩ hy
          apply hball
          have hyHalf :=
            parabolicDyadicOpenCell_subset_halfOpenCell index hy
          rcases z with ⟨time, velocity⟩
          rw [Metric.mem_ball, Prod.dist_eq]
          apply max_lt
          · simpa only [Real.dist_eq, abs_sub_comm] using
              (abs_sub_le_parabolicDyadicTimeWidth index hyHalf hzHalf).trans_lt htime
          · rw [dist_pi_lt_iff hε]
            intro coordinate
            simpa only [Real.dist_eq, abs_sub_comm] using
              (abs_sub_le_parabolicDyadicVelocityWidth index coordinate hyHalf hzHalf).trans_lt hvelocity
        classical
        let root : ParabolicDyadicIndex d 0 := fun i => Fin.elim0 i
        have hzReference : z ∈ parabolicDyadicReferenceCell d := by
          rw [← parabolicDyadicHalfOpenCell_zero_eq_reference d root]
          exact parabolicDyadicOpenCell_subset_halfOpenCell root (hURef hzU)
        obtain ⟨address, hzAddress, hAddressU⟩ :=
          exists_parabolicDyadicOpenCell_subset_of_mem_isOpen_off_boundary hzReference
        let P : Nat → Prop := fun n => ∃ index : ParabolicDyadicIndex d n,
          z ∈ parabolicDyadicOpenCell index ∧ parabolicDyadicOpenCell index ⊆ U
        have hP : ∃ n, P n := ⟨address.1, address.2, hzAddress, hAddressU⟩
        have hnZero : Nat.find hP ≠ 0 := by
          intro hn
          have hZero : P 0 := by simpa only [hn] using Nat.find_spec hP
          obtain ⟨index, hzIndex, hIndexU⟩ := hZero
          apply hRoot
          simpa only [Subsingleton.elim index root] using hIndexU
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnZero
        have hSucc : P (m + 1) := by simpa only [hm] using Nat.find_spec hP
        obtain ⟨index, hzIndex, hIndexU⟩ := hSucc
        refine ⟨⟨m + 1, index⟩, ?_, hzIndex⟩
        refine ⟨hIndexU, ?_⟩
        intro hParentU
        have hzChild : z ∈ parabolicDyadicOpenCell
            (parabolicDyadicChildIndex (parabolicDyadicParent index) (index (Fin.last m))) := by
          simpa using hzIndex
        have hMin := Nat.find_min' hP (show P m from ⟨parabolicDyadicParent index,
          parabolicDyadicOpenCell_child_subset (parabolicDyadicParent index) (index (Fin.last m))
            hzChild, hParentU⟩)
        rw [hm] at hMin
        omega
      have parabolicDyadicOpenCell_subset_of_firstEntry {U : Set (TimeVelocity d)} {a : ParabolicDyadicAddress d} (ha : a ∈ parabolicDyadicFirstEntry U) :
          parabolicDyadicOpenCell a.2 ⊆ U := by
        rcases a with ⟨n, index⟩
        cases n with
        | zero => exact False.elim ha
        | succ n => exact ha.1
      let V :=
        ⋃ a ∈ parabolicDyadicFirstEntry U, parabolicDyadicOpenCell a.2
      have hVsub : V ⊆ U := by
        intro z hz
        obtain ⟨address, hzAddress⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hEntry, hzAddress⟩ := Set.mem_iUnion.mp hzAddress
        exact parabolicDyadicOpenCell_subset_of_firstEntry hEntry hzAddress
      have hBoundaryZero : volume (parabolicDyadicAllBoundary d) = 0 := by
        unfold parabolicDyadicAllBoundary
        exact measure_iUnion_null fun a =>
          (ae_eq_set.mp (parabolicDyadicOpenCell_ae_eq_halfOpenCell a.2)).2
      apply ae_eq_set.mpr
      constructor
      · apply measure_mono_null ?_ hBoundaryZero
        intro z hz
        by_contra hzBoundary
        obtain ⟨address, hEntry, hzAddress⟩ :=
          exists_parabolicDyadicFirstEntry_of_mem_isOpen_off_boundary z hz.1 hzBoundary
        exact hz.2 (Set.mem_iUnion.mpr ⟨address,
          Set.mem_iUnion.mpr ⟨hEntry, hzAddress⟩⟩)
      · rw [diff_eq_empty.mpr hVsub]
        exact measure_empty
    let U := inkSpotsD1 Gamma xi
    let root : ParabolicDyadicIndex d 0 := fun i => Fin.elim0 i
    have hGammaAE : Gamma ≤ᵐ[volume] U := by
      simpa using
        (ae_le_inkSpotsD1_of_parabolicDyadicDensity d Gamma xi hGamma hGammaUnit hxi)
    have hUUnit : U ⊆ inkSpotsUnitBox d := by
      simpa using parabolicDyadicD1_subset_unit
    have hrootEq : parabolicDyadicOpenCell root = inkSpotsUnitBox d := by
      simpa only [root] using parabolicDyadicRoot_openCell_eq_inkSpotsUnitBox
    have hURoot : U ⊆ parabolicDyadicOpenCell root := by
      rw [hrootEq]
      exact hUUnit
    refine ⟨by simpa only [U] using hGammaAE, ?_⟩
    by_cases hroot : parabolicDyadicOpenCell root ⊆ U
    · have hUeq : U = inkSpotsUnitBox d := by
        apply Set.Subset.antisymm hUUnit
        rw [← hrootEq]
        exact hroot
      simpa only [U, hUeq] using hsubcritical.le
    · let E := {a : ParabolicDyadicAddress d | a ∈ parabolicDyadicD1Entry Gamma xi}
      let C : E → Set (TimeVelocity d) := fun a => parabolicDyadicOpenCell a.1.2
      let V := ⋃ a : E, C a
      have hV : V = ⋃ a ∈ parabolicDyadicD1Entry Gamma xi,
          parabolicDyadicOpenCell a.2 := by
        change (⋃ a : {a : ParabolicDyadicAddress d //
          a ∈ parabolicDyadicD1Entry Gamma xi}, parabolicDyadicOpenCell a.1.2) = _
        rw [Set.iUnion_subtype]
      have hcover : U =ᵐ[volume] V := by
        rw [hV]
        simpa only [U, parabolicDyadicD1Entry] using
          (ae_eq_iUnion_parabolicDyadicFirstEntry_openCell U
            (isOpen_inkSpotsD1 Gamma xi) hURoot hroot)
      have hdisjointC : Pairwise (Function.onFun Disjoint C) := by
        intro a b hab
        simp only [C]
        apply pairwiseDisjoint_parabolicDyadicFirstEntry_openCell U
        · exact a.2
        · exact b.2
        · exact Subtype.coe_ne_coe.mpr hab
      have hmeasC : ∀ a : E, MeasurableSet (C a) := by
        intro a
        exact measurableSet_parabolicDyadicOpenCell a.1.2
      have hdisjointGammaC : Pairwise (Function.onFun Disjoint fun a => Gamma ∩ C a) := by
        intro a b hab
        exact (hdisjointC hab).mono inter_subset_right inter_subset_right
      have hmeasGammaC : ∀ a : E, MeasurableSet (Gamma ∩ C a) := by
        intro a
        exact hGamma.inter (hmeasC a)
      have hunit_ne_top :=
        volume_inkSpotsUnitBox_ne_top
      have hC_ne_top : ∀ a : E, volume (C a) ≠ ∞ := by
        intro a
        apply measure_ne_top_of_subset
        exact (parabolicDyadicD1Entry_openCell_subset Gamma xi a).trans hUUnit
        exact hunit_ne_top
      have hGammaC_ne_top : ∀ a : E, volume (Gamma ∩ C a) ≠ ∞ := by
        intro a
        exact measure_ne_top_of_subset inter_subset_right (hC_ne_top a)
      let xie := ENNReal.ofReal xi
      have hlocal : ∀ a : E, volume (Gamma ∩ C a) ≤ xie * volume (C a) := by
        intro a
        apply (ENNReal.toReal_le_toReal (hGammaC_ne_top a)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hC_ne_top a))).mp
        simpa only [xie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hxi.1.le] using
          (parabolicDyadicD1_entry_density_le Gamma xi a)
      have hGammaAEInter : Gamma =ᵐ[volume] (Gamma ∩ U : Set (TimeVelocity d)) := by
        filter_upwards [hGammaAE] with z hz
        apply propext
        constructor
        · intro hzGamma
          exact ⟨hzGamma, hz hzGamma⟩
        · exact fun hzGamma => hzGamma.1
      have hGammaInterCover : (Gamma ∩ U : Set (TimeVelocity d)) =ᵐ[volume]
          (Gamma ∩ V : Set (TimeVelocity d)) :=
        ae_eq_set_inter (EventuallyEq.rfl) hcover
      have hGammaV : Gamma ∩ V = ⋃ a : E, Gamma ∩ C a := by
        simp only [V, inter_iUnion]
      have hmeasure : volume Gamma ≤ xie * volume U := by
        calc
          volume Gamma = volume (Gamma ∩ U) := measure_congr hGammaAEInter
          _ = volume (Gamma ∩ V) := measure_congr hGammaInterCover
          _ = volume (⋃ a : E, Gamma ∩ C a) := by rw [hGammaV]
          _ = ∑' a : E, volume (Gamma ∩ C a) :=
            measure_iUnion hdisjointGammaC hmeasGammaC
          _ ≤ ∑' a : E, xie * volume (C a) := ENNReal.tsum_le_tsum hlocal
          _ = xie * ∑' a : E, volume (C a) := ENNReal.tsum_mul_left
          _ = xie * volume V := by rw [← measure_iUnion hdisjointC hmeasC]
          _ = xie * volume U := by rw [measure_congr hcover]
      have hxieU_ne_top : xie * volume U ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top_of_subset hUUnit hunit_ne_top)
      simpa only [U, xie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hxi.1.le] using (ENNReal.toReal_mono hxieU_ne_top hmeasure)
  have hxi_nonneg := hxi.1.le
  calc
    (volume Gamma).toReal ≤ xi * (volume (inkSpotsD1 Gamma xi)).toReal := ((volume_Gamma_le_xi_volume_inkSpotsD1).2)
    _ ≤ xi * ((1 + eta) * (volume (inkSpotsD2 Gamma xi eta)).toReal) :=
      mul_le_mul_of_nonneg_left (volume_inkSpotsD1_toReal_le_one_add_eta_mul_D2 Gamma xi eta heta.1 heta.2) hxi_nonneg
    _ ≤ xi * ((1 + eta) * (zeta ^ (-((d : Int) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (volume_inkSpotsD2_toReal_le_zeta_zpow_mul_D3 Gamma xi eta zeta heta.1 hzeta.1 hzeta.2) ((add_pos_of_pos_of_nonneg zero_lt_one heta.1.le).le)) hxi_nonneg
    _ = xi * (1 + eta) * zeta ^ (-((d : Int) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal := by
      simp only [mul_assoc]


end HypoellipticAleksandrov.Parabolic

