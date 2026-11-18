module

public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.Duality.WholePlaneDualConfiguration
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace PottsDiscontinuity.Duality
open SimpleGraph FK FK.Medial
noncomputable section

private lemma zmod2_two (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

private def eVal (X : LatticeVertex → ZMod 2) (z w : LatticeVertex) : ZMod 2 :=
  if w = (z.1, z.2 + 1) then X (z.1, z.2 + 1) + X (z.1 + 1, z.2 + 1)
  else if w = (z.1, z.2 - 1) then X (z.1, z.2) + X (z.1 + 1, z.2)
  else if w = (z.1 + 1, z.2) then X (z.1 + 1, z.2) + X (z.1 + 1, z.2 + 1)
  else if w = (z.1 - 1, z.2) then X (z.1, z.2) + X (z.1, z.2 + 1)
  else 0

private lemma eVal_self (X : LatticeVertex → ZMod 2) (z : LatticeVertex) : eVal X z z = 0 := by
  unfold eVal
  rw [ite_eq_right (by simp [Prod.ext_iff]), ite_eq_right (by simp [Prod.ext_iff]; omega),
    ite_eq_right (by simp [Prod.ext_iff]), ite_eq_right (by simp [Prod.ext_iff]; omega)]

private lemma eVal_symm (X : LatticeVertex → ZMod 2) (z w : LatticeVertex) :
    eVal X z w = eVal X w z := by
  rcases z with ⟨zx, zy⟩; rcases w with ⟨wx, wy⟩
  unfold eVal; simp only [Prod.mk.injEq]
  by_cases h1 : wx = zx ∧ wy = zy + 1
  · rcases h1 with ⟨rfl, rfl⟩; simp; omega
  · by_cases h2 : wx = zx ∧ wy = zy - 1
    · rcases h2 with ⟨rfl, rfl⟩; simp; omega
    · by_cases h3 : wx = zx + 1 ∧ wy = zy
      · rcases h3 with ⟨rfl, rfl⟩; simp; omega
      · by_cases h4 : wx = zx - 1 ∧ wy = zy
        · rcases h4 with ⟨rfl, rfl⟩; simp; split_ifs <;> first | rfl | omega
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

private lemma sum_symm_zero {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α → ZMod 2)
    (hsym : ∀ a b, f a b = f b a) (hdiag : ∀ a, f a a = 0) :
    ∑ a ∈ S, ∑ b ∈ S, f a b = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x T hx ih =>
    rw [Finset.sum_insert hx]
    conv_lhs => rhs; arg 2; ext a; rw [Finset.sum_insert hx]
    rw [Finset.sum_insert hx, Finset.sum_add_distrib, ih, add_zero, hdiag x, zero_add,
      Finset.sum_congr rfl fun a _ => hsym a x, zmod2_two]

private lemma eVal_sum_four (X : LatticeVertex → ZMod 2) (z : LatticeVertex) :
    eVal X z (z.1, z.2 + 1) + eVal X z (z.1, z.2 - 1) + eVal X z (z.1 + 1, z.2) + eVal X z (z.1 - 1, z.2) = 0 := by
  have h1 : eVal X z (z.1, z.2 + 1) = X (z.1, z.2 + 1) + X (z.1 + 1, z.2 + 1) := ite_eq_left rfl
  have h2 : eVal X z (z.1, z.2 - 1) = X (z.1, z.2) + X (z.1 + 1, z.2) := by
    unfold eVal; rw [ite_eq_right (by simp only [Prod.ext_iff]; omega), ite_eq_left rfl]
  have h3 : eVal X z (z.1 + 1, z.2) = X (z.1 + 1, z.2) + X (z.1 + 1, z.2 + 1) := by
    unfold eVal; rw [ite_eq_right (by simp [Prod.ext_iff]), ite_eq_right (by simp [Prod.ext_iff]), ite_eq_left rfl]
  have h4 : eVal X z (z.1 - 1, z.2) = X (z.1, z.2) + X (z.1, z.2 + 1) := by
    unfold eVal; rw [ite_eq_right (by simp only [Prod.ext_iff]; omega), ite_eq_right (by simp only [Prod.ext_iff]; omega),
      ite_eq_right (by simp only [Prod.ext_iff]; omega), ite_eq_left rfl]
  rw [h1, h2, h3, h4]
  generalize X (z.1, z.2) = a; generalize X (z.1 + 1, z.2) = b
  generalize X (z.1 + 1, z.2 + 1) = c; generalize X (z.1, z.2 + 1) = d
  revert a b c d; decide

theorem no_infinite_cluster_implies_opposite_connections (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) (R : ℕ) :
    ∃ k : ℕ, ∃ j : Fin 2, ∃ w : LatticeVertex, R ≤ k ∧ w.1 < 0 ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ connectionEvent ((k : ℤ), -(j.val : ℤ)) w := by
  classical
  let K : Set LatticeVertex := ⋃ i ∈ Finset.range (R + 1), cluster ω ((i : ℤ), 0)
  have hK_fin : K.Finite := Set.Finite.biUnion (Finset.finite_toSet _) fun i _ =>
    Set.not_infinite.mp fun hinf => hno ⟨((i : ℤ), 0), hinf⟩
  have hK_adj {x y : LatticeVertex} (hadj : (rcInfiniteOpenGraph ω).Adj x y) : x ∈ K ↔ y ∈ K := by
    simp only [K, Set.mem_iUnion, cluster, Set.mem_ofPred_eq]
    exact exists_congr fun _ => exists_congr fun _ => ⟨(·.trans hadj.reachable), (·.trans hadj.symm.reachable)⟩
  let KF := hK_fin.toFinset
  have hseg_KF (i : ℕ) (hi : i ≤ R) : ((i : ℤ), 0) ∈ KF :=
    hK_fin.mem_toFinset.mpr (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr (by omega), .refl _⟩)
  let B_nat : ℕ := KF.sup fun v => max v.1.natAbs v.2.natAbs
  let M : ℤ := max (R : ℤ) (B_nat : ℤ) + 2
  have hKF_bounds (v) (hv : v ∈ KF) : -M + 2 ≤ v.1 ∧ v.1 ≤ M - 2 ∧ -M + 2 ≤ v.2 ∧ v.2 ≤ M - 2 := by
    have hle := Finset.le_sup (f := fun u : LatticeVertex => max u.1.natAbs u.2.natAbs) hv
    have : v.1.natAbs ≤ B_nat ∧ v.2.natAbs ≤ B_nat ∧ (B_nat : ℤ) + 2 ≤ M :=
      ⟨(le_max_left _ _).trans hle, (le_max_right _ _).trans hle, by dsimp [M]; omega⟩
    omega
  let X (v : LatticeVertex) : ZMod 2 := if v ∈ KF then 1 else 0
  let G_star := rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω)
  have heVal_adj_and_box {z w : LatticeVertex} (hne : eVal X z w ≠ 0) :
      G_star.Adj z w ∧ (-M + 1 ≤ w.1 ∧ w.1 ≤ M - 1 ∧ -M + 1 ≤ w.2 ∧ w.2 ≤ M - 1) := by
    have hclosed_bond (b : LatticeBond) (hXne : X b.source + X b.target ≠ 0) :
        G_star.Adj (dualBondOfPrimal b).source (dualBondOfPrimal b).target ∧
        (-M + 2 ≤ b.source.1 ∧ b.source.1 ≤ M - 2 ∧ -M + 2 ≤ b.source.2 ∧ b.source.2 ≤ M - 2 ∨
         -M + 2 ≤ b.target.1 ∧ b.target.1 ≤ M - 2 ∧ -M + 2 ≤ b.target.2 ∧ b.target.2 ≤ M - 2) := by
      have hdiff : ¬ (b.source ∈ KF ↔ b.target ∈ KF) := fun hiff => hXne <| by
        dsimp [X]; by_cases hs : b.source ∈ KF
        · rw [ite_eq_left hs, ite_eq_left (hiff.mp hs), zmod2_two]
        · rw [ite_eq_right hs, ite_eq_right (mt hiff.mpr hs), add_zero]
      have hstate_false : latticeConfigurationBondState ω b = false := by
        cases hs : latticeConfigurationBondState ω b; rfl
        exfalso; refine hdiff (hK_fin.mem_toFinset.trans ((hK_adj ?_).trans hK_fin.mem_toFinset.symm))
        rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]; exact ⟨b.adjacent, hs⟩
      have hadj_dual : (wholePlaneClosedDualGraph ω).Adj (dualBondOfPrimal b).source (dualBondOfPrimal b).target :=
        (wholePlaneClosedDualGraph_adj_iff ω _ _).mpr ⟨b, hstate_false, .inl ⟨dualBondOfPrimal_source b, dualBondOfPrimal_target b⟩⟩
      rw [← wholePlaneOpenPrimalGraph_dualConfiguration_eq, wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph] at hadj_dual
      have hbox : b.source ∈ KF ∨ b.target ∈ KF := by by_contra hn; rw [not_or] at hn; exact hdiff ⟨fun h => absurd h hn.1, fun h => absurd h hn.2⟩
      exact ⟨hadj_dual, hbox.imp (hKF_bounds _) (hKF_bounds _)⟩
    unfold eVal at hne
    by_cases h1 : w = (z.1, z.2 + 1)
    · subst h1; rw [ite_eq_left rfl] at hne
      obtain ⟨hadj, hb⟩ := hclosed_bond ⟨(z.1, z.2 + 1), .horizontal⟩ hne
      dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target] at hadj hb
      rw [add_sub_cancel_right] at hadj; exact ⟨hadj, by rcases hb with hb | hb <;> omega⟩
    · rw [ite_eq_right h1] at hne; by_cases h2 : w = (z.1, z.2 - 1)
      · subst h2; rw [ite_eq_left rfl] at hne
        obtain ⟨hadj, hb⟩ := hclosed_bond ⟨(z.1, z.2), .horizontal⟩ hne
        dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target] at hadj hb
        rw [sub_add_cancel] at hadj; exact ⟨hadj.symm, by rcases hb with hb | hb <;> omega⟩
      · rw [ite_eq_right h2] at hne; by_cases h3 : w = (z.1 + 1, z.2)
        · subst h3; rw [ite_eq_left rfl] at hne
          obtain ⟨hadj, hb⟩ := hclosed_bond ⟨(z.1 + 1, z.2), .vertical⟩ hne
          dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target] at hadj hb
          rw [add_sub_cancel_right] at hadj; exact ⟨hadj, by rcases hb with hb | hb <;> omega⟩
        · rw [ite_eq_right h3] at hne; by_cases h4 : w = (z.1 - 1, z.2)
          · subst h4; rw [ite_eq_left rfl] at hne
            obtain ⟨hadj, hb⟩ := hclosed_bond ⟨(z.1, z.2), .vertical⟩ hne
            dsimp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target] at hadj hb
            rw [sub_add_cancel] at hadj; exact ⟨hadj.symm, by rcases hb with hb | hb <;> omega⟩
          · rw [ite_eq_right h4] at hne; exact absurd rfl hne
  by_contra hgoal
  let D_box : Finset LatticeVertex := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M
  let isSeed (u : LatticeVertex) : Prop := (R : ℤ) ≤ u.1 ∧ u.1 ≤ M - 1 ∧ (u.2 = 0 ∨ u.2 = -1)
  let C_right : Finset LatticeVertex := D_box.filter fun z => ∃ u, isSeed u ∧ G_star.Reachable u z
  let C_up : Finset LatticeVertex := C_right.filter fun z => 0 ≤ z.2
  have hC_right_nonneg (z) (hz : z ∈ C_right) : 0 ≤ z.1 := by
    obtain ⟨_, u, ⟨huR, _, huy⟩, hruz⟩ := Finset.mem_filter.mp hz
    by_contra hlt
    have hk : (u.1.toNat : ℤ) = u.1 := Int.toNat_of_nonneg (by omega)
    rcases huy with hy | hy
    · have hu_eq : u = ((u.1.toNat : ℤ), -(((0 : Fin 2).val : ℕ) : ℤ)) := by ext <;> simp [hk, hy]
      exact hgoal ⟨u.1.toNat, 0, z, by omega, not_le.mp hlt, hu_eq ▸ hruz⟩
    · have hu_eq : u = ((u.1.toNat : ℤ), -(((1 : Fin 2).val : ℕ) : ℤ)) := by ext <;> simp [hk, hy]
      exact hgoal ⟨u.1.toNat, 1, z, by omega, not_le.mp hlt, hu_eq ▸ hruz⟩
  have hdouble0 : ∑ z ∈ C_up, ∑ w ∈ D_box, eVal X z w = 0 := Finset.sum_eq_zero fun z hz => by
    have hz_box := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hz_box
    by_cases hz_int : z.1 ≤ -M ∨ M ≤ z.1 ∨ z.2 ≤ -M ∨ M ≤ z.2
    · refine Finset.sum_eq_zero fun w _ => ?_
      by_contra hne; have ⟨_, hwb⟩ := heVal_adj_and_box (eVal_symm X w z ▸ hne); omega
    · let four : Finset LatticeVertex := {(z.1, z.2 + 1), (z.1, z.2 - 1), (z.1 + 1, z.2), (z.1 - 1, z.2)}
      rw [← Finset.sum_subset (s₁ := four)
        (fun w hw => by simp only [four, Finset.mem_insert, Finset.mem_singleton] at hw
                        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; rcases hw with rfl | rfl | rfl | rfl <;> omega)
        (fun w _ hnw => by unfold eVal; simp only [four, Finset.mem_insert, Finset.mem_singleton, not_or] at hnw
                           simp [hnw.1, hnw.2.1, hnw.2.2.1, hnw.2.2.2])]
      dsimp [four]
      rw [Finset.sum_insert (by simp [Prod.ext_iff]; omega), Finset.sum_insert (by simp [Prod.ext_iff]),
        Finset.sum_insert (by simp [Prod.ext_iff]; omega), Finset.sum_singleton]
      linear_combination eVal_sum_four X z
  have hclosed_up (z) (hz : z ∈ C_up) : ∑ w ∈ D_box, eVal X z w = ∑ w ∈ C_right, eVal X z w :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun w hwD hwnC => by
      by_contra hne
      obtain ⟨_, u, huS, hruz⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hz).1
      exact hwnC (Finset.mem_filter.mpr ⟨hwD, u, huS, hruz.trans (heVal_adj_and_box hne).1.reachable⟩)).symm
  have hup_sub : C_up ⊆ C_right := Finset.filter_subset _ _
  rw [Finset.sum_congr rfl hclosed_up,
    show (∑ z ∈ C_up, ∑ w ∈ C_right, eVal X z w) =
      (∑ z ∈ C_up, ∑ w ∈ C_up, eVal X z w) + ∑ z ∈ C_up, ∑ w ∈ C_right \ C_up, eVal X z w by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => (Finset.sum_sdiff hup_sub).symm.trans (add_comm _ _),
    sum_symm_zero C_up (eVal X) (eVal_symm X) (eVal_self X), zero_add] at hdouble0
  have hcross_term (z) (hz : z ∈ C_up) : ∑ w ∈ C_right \ C_up, eVal X z w =
      if (R : ℤ) ≤ z.1 ∧ z.1 ≤ M - 1 ∧ z.2 = 0 then X (z.1, 0) + X (z.1 + 1, 0) else 0 := by
    have hzy : 0 ≤ z.2 := (Finset.mem_filter.mp hz).2
    have hzx : 0 ≤ z.1 := hC_right_nonneg z (hup_sub hz)
    have honly_down (w) (hw : w ∈ C_right \ C_up) (hne : w ≠ (z.1, -1)) : eVal X z w = 0 := by
      have hwy : w.2 < 0 := by
        obtain ⟨hwC, hwnU⟩ := Finset.mem_sdiff.mp hw
        by_contra h; exact hwnU (Finset.mem_filter.mpr ⟨hwC, by omega⟩)
      unfold eVal
      rw [ite_eq_right (by simp [Prod.ext_iff]; omega),
        ite_eq_right (fun h => hne (by ext <;> [exact (Prod.ext_iff.mp h).1; (have := (Prod.ext_iff.mp h).2; omega)])),
        ite_eq_right (by simp [Prod.ext_iff]; omega), ite_eq_right (by simp [Prod.ext_iff]; omega)]
    by_cases hcond : (R : ℤ) ≤ z.1 ∧ z.1 ≤ M - 1 ∧ z.2 = 0
    · rw [ite_eq_left hcond, Finset.sum_eq_single (z.1, -1) honly_down fun h => absurd (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨by rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; dsimp only; omega,
          (z.1, -1), ⟨hcond.1, hcond.2.1, .inr rfl⟩, .refl _⟩, fun hm => by have := (Finset.mem_filter.mp hm).2; dsimp at this; omega⟩) h]
      simp [eVal, hcond.2.2]
    · rw [ite_eq_right hcond]
      refine Finset.sum_eq_zero fun w hw => ?_
      by_cases hweq : w = (z.1, -1)
      · subst hweq
        by_cases hz0 : z.2 = 0
        · by_cases hxM : z.1 ≤ M - 1
          · have hxR : z.1 < R := by omega
            simp only [eVal, hz0]; simp
            have h1 := hseg_KF z.1.toNat (by omega); rw [Int.toNat_of_nonneg hzx] at h1
            have h2 := hseg_KF (z.1 + 1).toNat (by omega); rw [Int.toNat_of_nonneg (by omega)] at h2
            dsimp [X]; rw [ite_eq_left h1, ite_eq_left h2, zmod2_two]
          · by_contra hne; have ⟨_, hwb⟩ := heVal_adj_and_box (eVal_symm X (z.1, -1) z ▸ hne); omega
        · unfold eVal
          rw [ite_eq_right (by simp [Prod.ext_iff]; omega), ite_eq_right (by simp [Prod.ext_iff]; omega),
            ite_eq_right (by simp [Prod.ext_iff]), ite_eq_right (by simp [Prod.ext_iff]; omega)]
      · exact honly_down w hw hweq
  let segR := (Finset.Icc (R : ℤ) (M - 1)).image fun x => (x, (0 : ℤ))
  have hseg_sub : segR ⊆ C_up := fun z hz => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz; rw [Finset.mem_Icc] at hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, (x, 0), ⟨hx.1, hx.2, .inl rfl⟩, .refl _⟩, le_rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; dsimp only [M] at *; omega
  rw [Finset.sum_congr rfl hcross_term, ← Finset.sum_subset hseg_sub (fun z _ hnz => ite_eq_right fun ⟨h1, h2, h3⟩ =>
      hnz (Finset.mem_image.mpr ⟨z.1, Finset.mem_Icc.mpr ⟨h1, h2⟩, Prod.ext rfl h3.symm⟩)),
    Finset.sum_image (fun _ _ _ _ h => (Prod.ext_iff.mp h).1),
    Finset.sum_congr rfl fun x hx => ite_eq_left ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hx).2, rfl⟩] at hdouble0
  have htel (n : ℕ) : ∑ x ∈ Finset.Icc (R : ℤ) ((R : ℤ) + n), (X (x, 0) + X (x + 1, 0)) =
      X ((R : ℤ), 0) + X ((R : ℤ) + n + 1, 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show Finset.Icc (R : ℤ) ((R : ℤ) + ↑(n + 1)) = insert ((R : ℤ) + ↑(n + 1)) (Finset.Icc (R : ℤ) ((R : ℤ) + ↑n)) by
          ext; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega), ih,
        show (R : ℤ) + ↑n + 1 = (R : ℤ) + ↑(n + 1) by push_cast; ring]
      generalize X ((R : ℤ), 0) = a; generalize X ((R : ℤ) + ↑(n + 1), 0) = b; generalize X ((R : ℤ) + ↑(n + 1) + 1, 0) = c
      revert a b c; decide
  have htelM := htel (M - 1 - R).toNat
  rw [show (R : ℤ) + ↑(M - 1 - (R : ℤ)).toNat = M - 1 by dsimp [M]; omega, show M - 1 + 1 = M by ring] at htelM
  rw [htelM, show X ((R : ℤ), 0) = 1 from ite_eq_left (hseg_KF R le_rfl),
    show X (M, 0) = 0 from ite_eq_right fun hv => by have := hKF_bounds _ hv; dsimp [M] at *; omega, add_zero] at hdouble0
  exact absurd hdouble0 (by decide)

end
end PottsDiscontinuity.Duality
