/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFiniteCapRequests

/-! # The relative datum on a calibrated actual context

Construct the cleaned native source, shorter donor encoding, literal root
restoration and relative datum on the same private scheme. The admitted state
is the stable private vector paired with the chosen donor, not the native
encoded template. There is no physical-receiving assertion here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthStableTemplate
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor CellScheme.restrictFace

universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

theorem exists_input (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    {k : ℕ} {s : Fin k ↪ M} {p₀ : S α.1 k} (hs : W.eval s = some p₀)
    (a₀ : Cell p₀.scheme.scheme) (hatop : p₀.label a₀ = ⊤) {i : ℕ}
    (ha₀ : W.stableValue s p₀ a₀ = ofOrd (α.1 + i))
    {n : ℕ} (hn : 0 < n) {t : Fin n ↪ M} {p : S α.1 n} (hp : W.eval t = some p)
    (q : S α.nextBlock.1 (n + 1)) (hq : IsCoface (stableLiftType hM t p hp) q)
    (γ : Ordinal.{0}) (hγ : γ < α.nextBlock.1) :
    ∃ (J : ℕ) (u : Fin J ↪ M) (C : S α.1 J), W.eval u = some C ∧
      ∃ (f : Fin n ↪ Fin J), f.trans u = t ∧ typeMap f C = some p ∧
        ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
          (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
          (hvC : Finset.univ.image f ∈ C.scheme.scheme.plan)
          (hF : C.scheme.restrictFace f hvC = p.scheme)
          (X : RelativeData C.scheme.scheme C.scheme.rows q.scheme.scheme q.scheme.rows),
          X.top = (Finset.univ, n + 1) ∧ n + 1 < X.req.N ∧
          C.scheme.scheme.scope X.req.C = Finset.univ ∧ C.label X.req.C = ⊤ ∧
          Nonempty (Growth.RootAttachment p.scheme Fin.castSuccEmb hvP hP f hvC hF X) ∧
          X.ZA = {d | C.label d.1 = ⊥} ∧
          (∀ j, Growth.Admitted X j (GrowthStableSelectedInput.state
            (W := W) (u := u) (C := C) (q := q))) ∧
          (∀ v : Cell q.scheme.scheme → ExtOrd,
            X.req.Correct (X.req.sec (W.stableValue u C)) v →
              (∀ d, q.label d ≠ ⊤ → v d = q.label d) ∧
              (∀ d, q.label d = ⊤ → ofOrd γ < v d)) := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : ℕ, γ < α.1 + b := by
    rcases lt_or_ge γ α.1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨b, rfl⟩ := exists_nat_of_lt_add_omega h hγ
      exact ⟨b + 1, add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self b)) _⟩
  obtain ⟨L, hbL, hnL, hfp, hproper⟩ := GrowthFiniteCapRequests.exists_cut q b
  have hγL : ofOrd γ < ofOrd (α.1 + L) :=
    ofOrd_lt_ofOrd.mpr (hb.trans (add_lt_add_right (Nat.cast_lt.mpr hbL) _))
  obtain ⟨J, u, C, hC, f, _, hfu, -, hf, hg₀, c, hsc, hc, hLN, hi,
    hab, ha, hcut, hai, ref, off, href, -, -⟩ :=
    GrowthStableCalibration.exists_calibration hM hg hs a₀ hatop ha₀ t p hp (blocks q)
      (GrowthFiniteCapRequests.blocks_limit q) (GrowthFiniteCapRequests.blocks_le q) L
  let a : C.scheme.scheme.below (C.scheme.scheme.cell c) := ⟨mapCell hg₀ a₀, hab⟩
  obtain ⟨hvP, hvC, hP, hF⟩ := GrowthStableSelectedInput.common_faces hM hp hf hq
  let root : Finset (Fin (n + 1)) × ℕ := (Finset.univ.image Fin.castSuccEmb, n)
  let top : Finset (Fin (n + 1)) × ℕ := (Finset.univ, n + 1)
  have hbelow : GradedLe (Finset.univ.image f, n) (C.scheme.scheme.cell c) :=
    ⟨by change Finset.univ.image f ⊆ C.scheme.scheme.scope c; rw [hsc]; exact Finset.subset_univ _,
      (Nat.le_succ n).trans (hnL.le.trans hLN.le)⟩
  let κ := Growth.literalKappa p.scheme Fin.castSuccEmb hvP hP f hvC hF c hbelow
  have hlit (d : q.scheme.scheme.below root) : q.label d.1 = W.stableValue u C (κ d).1 := by
    have hP' := restrictFace_eq_of_typeMap_eq_some hq
    have hC' := restrictFace_eq_of_typeMap_eq_some
      (GrowthStableSelectedInput.stable_face hM hp hC hfu)
    change q.label d.1 = W.stableValue u C (commonFace Fin.castSuccEmb hvP hP f hvC hF n d).1
    rw [commonFace_val]
    exact ((StageType.label_castCell hC'.symm _).trans
      ((StageType.label_castCell hP' _).trans
        (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ d)))).symm
  have hroot : ∀ s, RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) s →
      RespectsSemanticsBelow q.scheme.rows root (fun d => s (κ d)) :=
    fun _ hs => Growth.literalKappa_lawful _ _ _ _ _ _ _ _ _ hs
  have hrmem : root ∈ Plan.gradedPlan q.scheme.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨hvP, hn, by
      change n ≤ (Finset.univ.image Fin.castSuccEmb).card
      rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective]; simp⟩
  have htmem : top ∈ Plan.gradedPlan q.scheme.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨q.scheme.scheme.isPlan.domain_mem, Nat.succ_pos n, by simp [top]⟩
  have hrt : GradedLe root top := ⟨Finset.subset_univ _, Nat.le_succ _⟩
  have hrne : root ≠ top := fun h => Nat.succ_ne_self n (congrArg Prod.snd h).symm
  have htop (d) : GradedLe (q.scheme.scheme.cell d) top :=
    ⟨Finset.subset_univ _, (q.scheme.scheme.grade_le_card_scope d).trans
      (by simpa using Finset.card_le_univ (q.scheme.scheme.scope d))⟩
  let req := GrowthFiniteCapRequests.requests c L hLN a ref q.label
  obtain ⟨e, he, hebot, heeq, τ, hτ, -, hchart⟩ :=
    GrowthStableSelectedInput.exists_cleaned_source_chart hM hC c hc
  have heproper (d) : e d ≠ ⊤ := by
    by_cases hb : C.label d.1 = ⊥
    · rw [(hebot d).mpr hb]; exact bot_ne_top
    · rw [heeq d hb]
      rcases C.scheme.rows_coded c d with h | ⟨i, j, _, h⟩
      · rw [h]; exact bot_ne_top
      · rw [h]; exact ofOrd_ne_top _
  have hebot' (d) : e d = ⊥ ↔ W.stableValue u C d.1 = ⊥ :=
    (hebot d).trans (GrowthStableSelectedInput.private_bottom hM hC d.1).symm
  have hblocks (d β) (hd : q.label d = ofOrd β) :
      limitPart β ∈ blocks q ∧ finitePart β < L :=
    ⟨mem_blocks.mpr ⟨_, mem_donorRequests.mpr ⟨d, β, hd, rfl⟩, rfl⟩, hfp d β hd⟩
  have hfields (d) (hd : d ∈ req.F) : ∃ β, q.label d = ofOrd β ∧
      req.ρ d = ref (limitPart β) ∧ req.off d = finitePart β := by
    rcases ExtOrd.cases (q.label d) with hb | ht | ⟨β, hβ⟩
    · exact (hd.1 hb).elim
    · exact (hd.2 ht).elim
    refine ⟨β, hβ, ?_, ?_⟩ <;>
      simp only [req, GrowthFiniteCapRequests.requests, hβ, ordOf_ofOrd]
  obtain ⟨V, hV, hVr, hVc, hframe, -, -, -⟩ :=
    GrowthFiniteCapTemplate.exists_template req e he heproper (W.stableValue u C) hebot' hτ
      hchart (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)) hi ha hai hcut
      (blocks q) (GrowthFiniteCapRequests.blocks_limit q) (GrowthFiniteCapRequests.blocks_le q)
      ref off (fun μ hμ => (href μ hμ).1)
      (fun μ hμ => by rw [hchart, (href μ hμ).2.1, min_eq_left (href μ hμ).2.2.le])
      q.respects hblocks hproper hrmem htmem hrt hrne htop hnL κ hroot q.scheme.bountiful hlit
      (fun _ h => h) (fun _ h => h) hfields
  have href' (d β) (hd : q.label d = ofOrd β) :
      off (limitPart β) < C.scheme.scheme.grade c ∧
        W.stableValue u C (ref (limitPart β)).1 = ofOrd (limitPart β + off (limitPart β)) :=
    ⟨(href _ (hblocks d β hd).1).1, (href _ (hblocks d β hd).1).2.1⟩
  let X : RelativeData C.scheme.scheme C.scheme.rows q.scheme.scheme q.scheme.rows := {
    req := req
    grade_C := rfl
    ZA := {d | C.label d.1 = ⊥}
    C_notin := by change C.label c ≠ ⊥; rw [hc]; exact top_ne_bot
    a_notin := fun hb => ofOrd_ne_bot _ (ha ▸ (GrowthStableSelectedInput.private_bottom hM hC a.1).mpr hb)
    ρ_notin := fun d hd hb => by
      obtain ⟨β, hβ, hρ, -⟩ := hfields d hd
      have h := (GrowthStableSelectedInput.private_bottom hM hC (req.ρ d).1).mpr hb
      rw [hρ, (href' d β hβ).2] at h
      exact ofOrd_ne_bot _ h
    off_lt := fun d hd => by
      obtain ⟨β, hβ, -, ho⟩ := hfields d hd
      rw [ho]; exact (hfp d β hβ).le.trans hLN.le
    e := e
    e_bot := hebot
    e_eq := heeq
    root := root
    top := top
    root_mem := hrmem
    top_mem := htmem
    root_le := hrt
    root_ne := hrne
    below_top := htop
    top_le_N := hnL.le.trans hLN.le
    κ := κ
    hroot := hroot
    bountiful := q.scheme.bountiful
    cover := fun d => by
      by_cases hb : q.label d = ⊥
      · exact Or.inl hb
      by_cases ht : q.label d = ⊤
      · exact Or.inr (Or.inr (Or.inl ht))
      exact Or.inr (Or.inl ⟨hb, ht⟩)
    V := V
    V_respects := hV
    V_root := hVr
    V_correct := hVc
    frame := hframe }
  refine ⟨J, u, C, hC, f, hfu, hf, hvP, hP, hvC, hF, X, rfl, hnL.trans hLN, hsc, hc,
    ⟨⟨rfl, fun _ => rfl⟩⟩, rfl, fun j => ?_, fun v hv => ⟨fun d hnt => ?_, fun d hd => ?_⟩⟩
  · refine ⟨(stableLiftRespects hM hC).toBelow _, q.respects.toBelow _, ?_, hlit, fun _ _ =>
      GrowthFiniteCapRequests.correct c L hLN a ref q.label (W.stableValue u C) off href'⟩
    rintro (d | d)
    · exact SelfVis.mono ((stableLiftRespects hM hC).orderly d).symm (C.scheme.scheme.grade_pos d)
    · exact SelfVis.mono (q.respects.orderly d).symm (q.scheme.scheme.grade_pos d)
  · by_cases hb : q.label d = ⊥
    · have he : min (v d) (W.stableValue u C c) = ⊥ := hv.1 d hb
      exact ((min_eq_bot.mp he).resolve_right (ne_of_gt ((bot_lt_ofOrd _).trans hcut))).trans hb.symm
    · exact GrowthFiniteCapRequests.proper_readback c L hLN a ref q.label
        (W.stableValue u C) hcut off href' hproper hv ⟨hb, hnt⟩
  · exact hγL.trans_le (GrowthFiniteCapRequests.high_readback c L hLN a ref q.label
      (W.stableValue u C) (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2))
      hi ha hcut hv hd)
