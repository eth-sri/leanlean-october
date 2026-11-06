module

public import Chazelle.Core.RestoreFComplete

/-!
# WP-E, the search: the leaf's step count

An arc of a region of a `γ'`-granular normal form of a chain model visits at most `γ' + 8` walk
vertices (`lcnt_le`), so a leaf takes at most `5 (γ' + 9)` steps (`lmuB_le`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)
open DownHost ArcT

/-- **The vertex count of an arc** (with distinct end keys) is at most its weight plus `8`. -/
theorem arcCnt_le_wt {M : Model} {Q : Polygon} {n0 : ℕ}
    (hunc : {p | p < M.W.n ∧ ¬ M.counted p}.ncard ≤ 7) {s e : WPos}
    (hs : ProperPos M Q n0 s) (he : ProperPos M Q n0 e) (hse : s.edge < M.W.n)
    (hee : e.edge < M.W.n) (hne : M.key Q s ≠ M.key Q e) :
    arcCnt M.W.n s.edge e.edge
      (if s.edge = e.edge ∧ M.key Q s < M.key Q e then 1 else 0) ≤
        M.arcWt (M.key Q s) (M.key Q e) + 8 := by
  set n := M.W.n
  have hn : 0 < n := by omega
  set a := M.key Q s
  set b := M.key Q e
  have hka : a = s.edge + M.param Q s := rfl
  have hkb : b = e.edge + M.param Q e := rfl
  have hsR : (s.edge : ℝ) + 1 ≤ n := by exact_mod_cast hse
  have heR : (e.edge : ℝ) + 1 ≤ n := by exact_mod_cast hee
  have ha : 0 ≤ a ∧ a < n := by constructor <;> linarith [hs.1, hs.2.1, (Nat.cast_nonneg s.edge : (0:ℝ) ≤ _)]
  have hb : 0 ≤ b ∧ b < n := by constructor <;> linarith [he.1, he.2.1, (Nat.cast_nonneg e.edge : (0:ℝ) ≤ _)]
  have hpe : 0 ≤ (e.edge : ℝ) ∧ (e.edge : ℝ) < n := ⟨Nat.cast_nonneg _, by linarith⟩
  by_cases h1 : s.edge = e.edge ∧ a < b
  · rw [ite_eq_left h1]
    unfold arcCnt
    rw [ite_eq_right (by omega), h1.1, show e.edge + n - e.edge = n by omega, Nat.mod_self]
    omega
  rw [ite_eq_right h1]
  -- the end vertex is on the closed arc
  have hcl : ClosedArc a b (e.edge : ℝ) := by
    rcases lt_trichotomy s.edge e.edge with hlt | heq | hgt
    · have hle : (s.edge : ℝ) + 1 ≤ e.edge := by exact_mod_cast hlt
      have hu1 : unwrapK n a (e.edge : ℝ) = e.edge := by unfold unwrapK; rw [ite_eq_left (by linarith [hs.2.1])]
      have hu2 : unwrapK n a b = b := by unfold unwrapK; rw [ite_eq_left (by linarith [hs.2.1, he.1])]
      exact (closedArc_unwrap ha hb hpe hne).2 ⟨by rw [hu1]; linarith [hs.2.1], by
        rw [hu1, hu2]; linarith [he.1]⟩
    · have hba : b < a := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact absurd ⟨heq, h⟩ h1
        · exact h
      have hu1 : unwrapK n a (e.edge : ℝ) = e.edge + n := by
        unfold unwrapK; rw [ite_eq_right (by linarith [he.1])]
      have hu2 : unwrapK n a b = b + n := by unfold unwrapK; rw [ite_eq_right (by linarith)]
      exact (closedArc_unwrap ha hb hpe hne).2 ⟨by rw [hu1]; linarith, by
        rw [hu1, hu2]; linarith [he.1]⟩
    · have hle : (e.edge : ℝ) + 1 ≤ s.edge := by exact_mod_cast hgt
      have hu1 : unwrapK n a (e.edge : ℝ) = e.edge + n := by
        unfold unwrapK; rw [ite_eq_right (by linarith [hs.1])]
      have hu2 : unwrapK n a b = b + n := by
        unfold unwrapK; rw [ite_eq_right (by linarith [hs.1, he.2.1])]
      exact (closedArc_unwrap ha hb hpe hne).2 ⟨by rw [hu1]; linarith [hs.2.1], by
        rw [hu1, hu2]; linarith [he.1]⟩
  obtain ⟨t, ht, htu⟩ := steps_le (w := M.arcWt a b) hunc hs hse hb hne le_rfl hee hcl
  -- the vertex count is `t + 1`
  have hcnt : arcCnt n s.edge e.edge 0 = t + 1 := by
    unfold arcCnt
    rcases lt_trichotomy s.edge e.edge with hlt | heq | hgt
    · have hu1 : unwrapK n a (e.edge : ℝ) = e.edge := by
        have hle : (s.edge : ℝ) + 1 ≤ e.edge := by exact_mod_cast hlt
        unfold unwrapK; rw [ite_eq_left (by linarith [hs.2.1])]
      rw [hu1] at htu
      have h2 : s.edge + t = e.edge := by exact_mod_cast htu
      have h3 : e.edge + n - s.edge = t + n := by omega
      rw [ite_eq_right (by omega), h3, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hba : b < a := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact absurd ⟨heq, h⟩ h1
        · exact h
      have hu1 : unwrapK n a (e.edge : ℝ) = e.edge + n := by
        unfold unwrapK; rw [ite_eq_right (by linarith [he.1])]
      rw [hu1] at htu
      have : s.edge + t = e.edge + n := by exact_mod_cast htu
      rw [ite_eq_left ⟨heq, rfl⟩, heq, show e.edge + n - e.edge = n by omega, Nat.mod_self]; omega
    · have hu1 : unwrapK n a (e.edge : ℝ) = e.edge + n := by
        have hle : (e.edge : ℝ) + 1 ≤ s.edge := by exact_mod_cast hgt
        unfold unwrapK; rw [ite_eq_right (by linarith [hs.1])]
      rw [hu1] at htu
      have h2 : s.edge + t = e.edge + n := by exact_mod_cast htu
      have h3 : e.edge + n - s.edge = t := by omega
      rw [ite_eq_right (by omega), h3, Nat.mod_eq_of_lt (by omega)]
  rw [hcnt]; omega


/-- At most seven walk edges of a chain model are uncounted. -/
theorem chain_uncounted_le (C : Chain) :
    {p | p < (chainModel C).W.n ∧ ¬ (chainModel C).counted p}.ncard ≤ 7 := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hsub : {p | p < (chainModel C).W.n ∧ ¬ (chainModel C).counted p} ⊆
      (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ) := by
    rintro p ⟨hp, hc⟩
    simp only [chainModel, not_and, not_lt] at hc
    simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
    by_cases h6 : 6 ≤ p
    · have := hc h6; omega
    · omega
  calc _ ≤ (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 7 := by rw [Set.ncard_coe_finset]; exact List.toFinset_card_le _

/-- The weight of the whole walk of a chain model (the arc of the empty family). -/
theorem arcWt_zero_zero (C : Chain) : (chainModel C).arcWt 0 0 = 2 * C.m := by
  rw [← MergeAsm.chainModel_size C]
  unfold Model.arcWt Model.size
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, 1 / 2, by norm_num, by norm_num, ?_⟩
    unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]
    left; have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith

/-- **The vertex count of an arc of a granular normal form of a chain model.** -/
theorem lcnt_le {Cα : Chain} {Q : Polygon} {N : NF} {γ' : ℕ}
    (hcan : IsCanonicalNF (chainModel Cα) Q N γ' 4) {r : ℕ} (hr : r < N.nRegions) {t : ℕ}
    (ht : t < (N.region r).arcs.length) : lcnt Cα Q N r (2 * Cα.m + 7) t ≤ γ' + 8 := by
  obtain ⟨hnf, -, hgr, -⟩ := hcan
  have hnf' := hnf
  obtain ⟨hFam, -, -, reg, hRC, -, hArcs, hRg, -, -, hpp⟩ := hnf'
  have hn : (chainModel Cα).W.n = 2 * Cα.m + 7 := chainModel_n Cα
  set j := lj N r t with hjdef
  have hjm : j ∈ (N.region r).arcs := by
    rw [hjdef, lj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  obtain ⟨hj, hjr⟩ := (hArcs.2.2.2 r hr j).1 hjm
  have harc := (hArcs.1 j hj).2
  rw [hjr] at harc
  have hU := hRC.1 r hr
  have hwt : (chainModel Cα).arcWt ((chainModel Cα).key Q (N.arc j).s)
      ((chainModel Cα).key Q (N.arc j).e) ≤ γ' :=
    (WalkEmbed.arcWt_le_weight _ harc).trans (hgr.1 _ hU)
  obtain ⟨ha0, ha1, hb0, hb1, hc, -, -⟩ := harc
  have hps := (hpp j hj).1
  have hpe := (hpp j hj).2
  have hse : (N.arc j).s.edge < (chainModel Cα).W.n := by
    have hk : (chainModel Cα).key Q (N.arc j).s = (N.arc j).s.edge + (chainModel Cα).param Q (N.arc j).s := rfl
    have : ((N.arc j).s.edge : ℝ) < (chainModel Cα).W.n := by linarith [hps.1]
    exact_mod_cast this
  have hee : (N.arc j).e.edge < (chainModel Cα).W.n := by
    have hk : (chainModel Cα).key Q (N.arc j).e = (N.arc j).e.edge + (chainModel Cα).param Q (N.arc j).e := rfl
    have : ((N.arc j).e.edge : ℝ) < (chainModel Cα).W.n := by linarith [hpe.1]
    exact_mod_cast this
  unfold lcnt
  rw [← hjdef, ← hn]
  rcases hc with ⟨hca, -, hne⟩ | ⟨hF, ha, hb⟩
  · -- a family with chords
    have hnc : 0 < N.nChords := by
      rcases Nat.eq_zero_or_pos N.nChords with h0 | h0
      · exfalso
        obtain ⟨c, hcF, -⟩ := hca
        have h1 := Gran.ncard_F hnf
        rw [h0, Set.ncard_eq_zero (hs := hFam.1)] at h1
        rwa [h1] at hcF
      · exact h0
    have hw : wBit Cα Q N.nChords (N.arc j).s.edge (N.arc j).s.hgt (N.arc j).e.edge (N.arc j).e.hgt =
        if (N.arc j).s.edge = (N.arc j).e.edge ∧
          (chainModel Cα).key Q (N.arc j).s < (chainModel Cα).key Q (N.arc j).e then 1 else 0 := by
      unfold wBit
      by_cases h : (N.arc j).s.edge = (N.arc j).e.edge ∧
          (chainModel Cα).key Q (N.arc j).s < (chainModel Cα).key Q (N.arc j).e
      · rw [ite_eq_left ⟨hnc, h⟩, ite_eq_left h]
      · rw [ite_eq_right (fun h' => h ⟨h'.2.1, h'.2.2⟩), ite_eq_right h]
    rw [hw]
    have := arcCnt_le_wt (chain_uncounted_le Cα) hps hpe hse hee hne
    omega
  · -- the empty family: the whole walk
    have hs0 : (N.arc j).s.edge = 0 := by
      have hk : (chainModel Cα).key Q (N.arc j).s =
          (N.arc j).s.edge + (chainModel Cα).param Q (N.arc j).s := rfl
      have : ((N.arc j).s.edge : ℝ) ≤ 0 := by linarith [hps.1]
      have : ((N.arc j).s.edge : ℝ) = 0 := le_antisymm this (Nat.cast_nonneg _)
      exact_mod_cast this
    have he0 : (N.arc j).e.edge = 0 := by
      have hk : (chainModel Cα).key Q (N.arc j).e =
          (N.arc j).e.edge + (chainModel Cα).param Q (N.arc j).e := rfl
      have : ((N.arc j).e.edge : ℝ) ≤ 0 := by linarith [hpe.1]
      have : ((N.arc j).e.edge : ℝ) = 0 := le_antisymm this (Nat.cast_nonneg _)
      exact_mod_cast this
    have hw : wBit Cα Q N.nChords (N.arc j).s.edge (N.arc j).s.hgt (N.arc j).e.edge
        (N.arc j).e.hgt = 0 := by
      unfold wBit
      rw [ite_eq_right]; rintro ⟨h0, -⟩
      have h1 := Gran.ncard_F hnf
      rw [hF, Set.ncard_empty] at h1; omega
    rw [hw, hs0, he0]
    rw [ha, hb, arcWt_zero_zero] at hwt
    unfold arcCnt
    rw [ite_eq_left ⟨rfl, rfl⟩, hn, show 0 + (2 * Cα.m + 7) - 0 = 2 * Cα.m + 7 by omega, Nat.mod_self]
    omega

/-- **The steps of a leaf.** -/
theorem lmuB_le {Cα : Chain} {Q : Polygon} {N : NF} {γ' : ℕ} (hP : Cα.P.Simple)
    (hcan : IsCanonicalNF (chainModel Cα) Q N γ' 4) : lmuB Cα Q N ≤ 5 * (γ' + 9) := by
  have hGα : GoodModel (chainModel Cα) := Or.inl ⟨Cα, hP, rfl⟩
  have hM := walkAx_of_goodModel hGα
  unfold lmuB
  refine Finset.sup_le fun r hr => ?_
  rw [Finset.mem_range] at hr
  unfold lmu
  have hlen := region_arcs_le hM hcan.1 hcan.2.1 hr
  calc ∑ t ∈ Finset.range (N.region r).arcs.length, (lcnt Cα Q N r (2 * Cα.m + 7) t + 1)
      ≤ ∑ t ∈ Finset.range (N.region r).arcs.length, (γ' + 9) :=
        Finset.sum_le_sum fun t ht => by
          have := lcnt_le hcan hr (Finset.mem_range.1 ht); omega
    _ = (N.region r).arcs.length * (γ' + 9) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ 5 * (γ' + 9) := Nat.mul_le_mul_right _ (by omega)


/-! ## The piece bound -/

/-- Lemma 2.3 with its explicit constant. -/
theorem l23_explicit (M : Model) (Q : Polygon) (F : Set (Set Point)) (γ D : ℕ) (hM : GoodModel M)
    (hF : M.ChordFamily Q F) (hdeg : M.DegLe F D) (hgran : M.Granular F γ) :
    F.ncard * (γ + 1) ≤ (fun D => 140 * (D + 2)) D * (M.size + 1) := by
  have hW := walkAx_of_goodModel hM
  obtain ⟨hfin, hAdm, -⟩ := hF
  obtain ⟨hn, p₀, hp₀, hc₀⟩ := goodModel_walk M hM
  show F.ncard * (γ + 1) ≤ 140 * (D + 2) * (M.size + 1)
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · rcases F.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact absurd hgran.1 (hW.not_semigranular_zero hAdm hfin hne hp₀ hc₀)
  · have h := hW.lemma23_walk hAdm hfin hdeg hgran
    calc F.ncard * (γ + 1) ≤ 2 * (F.ncard * γ) := by nlinarith
      _ ≤ 2 * (2 * (D + 2) * (5 * M.W.n)) := Nat.mul_le_mul_left _ h
      _ ≤ 2 * (2 * (D + 2) * (5 * (7 * (M.size + 1)))) := by gcongr
      _ = 140 * (D + 2) * (M.size + 1) := by ring

theorem halfK_le {n x : ℕ} (hn : 3 ≤ n) (hx : x ≤ 6720 * n + 20163) : halfK n x ≤ 120011 := by
  unfold halfK
  have : x / (2 * (n / 2)) ≤ 30000 := Nat.div_le_of_le_mul (by omega)
  omega

/-- The bound of a piece's run. -/
def pK (E : FEnv) : ℕ := 10 ^ 9 * (tK E * (E.H E.γ + Nat.clog 2 E.γ + 1))

variable {E : FEnv} {c₀ : Config}

theorem k0K_le : k0K E ≤ pK E := by
  have hT : 20 ≤ tK E := by unfold tK; omega
  have hP : tK E ≤ tK E * (E.H E.γ + Nat.clog 2 E.γ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold pK k0K tvK hvK
  omega

/-- **The bound of a kind-1 piece.** -/
theorem k1K_le (hE : FGood E c₀) {Cα : Chain} {N : NF} {γ' : ℕ} (hQ : Cα.P = Qof E.P)
    (hcan : IsCanonicalNF (chainModel Cα) (Qof E.P) N γ' 4) (hγ' : γ' ≤ E.H E.γ)
    (hm : Cα.m ≤ E.γ) : k1K E Cα N ≤ pK E := by
  have hP : Cα.P.Simple := by rw [hQ]; exact qof_simple hE
  have hGα : GoodModel (chainModel Cα) := Or.inl ⟨Cα, hP, rfl⟩
  have hMα := walkAx_of_goodModel hGα
  set T := tK E with hTdef
  set a := Nat.clog 2 E.γ with hadef
  set h := E.H E.γ with hhdef
  have hT : 20 ≤ T := by rw [hTdef]; unfold tK; omega
  have hm1 := Cα.one_le
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  have hmP : Cα.m < E.P.n := by have := Cα.m_lt; rwa [hQ, hQn] at this
  have hn3 : 3 ≤ E.P.n := hE.hG.1.1
  -- the chords
  have hnc : N.nChords ≤ 140 * (4 + 2) * (2 * Cα.m + 8) :=
    MergeAsm.nChords_le_canonical (c := fun D => 140 * (D + 2)) l23_explicit hP hcan
  have hreg : N.nRegions = N.nChords + 1 := Gran.nRegions_eq hcan.1 hMα
  -- the halving cost
  have hX : halfK E.P.n (maxCode N) ≤ 120011 := halfK_le hn3 (by unfold maxCode; omega)
  -- the depth
  have hdd : decDepth 4 N.nChords + 1 ≤ 58 * (a + 1) := by
    unfold decDepth
    have h1 : N.nChords + 1 ≤ 2 ^ 14 * E.γ := by omega
    have h2 : Nat.clog 2 (N.nChords + 1) ≤ 14 + a := by
      calc Nat.clog 2 (N.nChords + 1) ≤ Nat.clog 2 (2 ^ 14 * E.γ) := MergeAsm.clog_mono h1
        _ ≤ Nat.clog 2 (2 ^ 14) + Nat.clog 2 E.γ := MergeAsm.clog_mul_le _ _
        _ = 14 + a := by rw [Nat.clog_pow 2 14 (by norm_num)]
    omega
  -- the leaf
  have hlm : lmuB Cα (Qof E.P) N ≤ 5 * (h + 9) := by
    have := lmuB_le hP hcan; omega
  -- the step costs
  have hdb : dbK E N + 2 ≤ 30000 * T := by
    unfold dbK ndK clK paK efK etK erK ehK wsK wcK scK
    rw [← hTdef]; omega
  have hlb : lbK E + 2 ≤ 2000 * T := by
    unfold lbK vsK tvK hvK csK
    rw [← hTdef]; omega
  have hC : (dbK E N + 2) * (decDepth 4 N.nChords + 1) ≤ 30000 * 58 * (T * (a + 1)) := by
    calc (dbK E N + 2) * (decDepth 4 N.nChords + 1) ≤ (30000 * T) * (58 * (a + 1)) :=
          Nat.mul_le_mul hdb hdd
      _ = 30000 * 58 * (T * (a + 1)) := by ring
  have hD : (lbK E + 2) * lmuB Cα (Qof E.P) N ≤ 2000 * 5 * (T * (h + 9)) := by
    calc (lbK E + 2) * lmuB Cα (Qof E.P) N ≤ (2000 * T) * (5 * (h + 9)) := Nat.mul_le_mul hlb hlm
      _ = 2000 * 5 * (T * (h + 9)) := by ring
  have hR1 : T * (a + 1) ≤ T * (h + a + 1) := Nat.mul_le_mul_left _ (by omega)
  have hR2 : T * (h + 9) ≤ 9 * (T * (h + a + 1)) := by
    calc T * (h + 9) ≤ T * (9 * (h + a + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 9 * (T * (h + a + 1)) := by ring
  have hR3 : T ≤ T * (h + a + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hdesc : descK E Cα N (decDepth 4 N.nChords) ≤ 10 ^ 8 * (T * (h + a + 1)) := by
    unfold descK
    have hpa : paK E (maxCode N) ≤ 120013 := by unfold paK; omega
    omega
  unfold k1K pK voK tvK hvK
  rw [← hTdef, ← hadef, ← hhdef]
  omega

end

end Restore

end Chazelle.Core
