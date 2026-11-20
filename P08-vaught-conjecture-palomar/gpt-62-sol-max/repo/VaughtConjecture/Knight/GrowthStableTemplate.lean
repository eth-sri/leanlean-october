/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFiniteCapRequests

@[expose] public section

namespace VaughtConjecture.Knight.GrowthStableTemplate

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor

open CellScheme.restrictFace

noncomputable section

universe w

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

theorem exists_input_at (hM : W.IsModel) {n J : ℕ} (hn : 0 < n)
    {t : Fin n ↪ M} {p : S α.1 n} (hp : W.eval t = some p)
    {u : Fin J ↪ M} {C : S α.1 J} (hC : W.eval u = some C)
    {f : Fin n ↪ Fin J} (hfu : f.trans u = t) (hf : typeMap f C = some p)
    (q : S α.nextBlock.1 (n + 1)) (hq : IsCoface (stableLiftType hM t p hp) q)
    (c : Cell C.scheme.scheme) (hsc : C.scheme.scheme.scope c = Finset.univ)
    (hc : C.label c = ⊤) (L : ℕ) (hnL : n + 1 < L) (hLN : L < C.scheme.scheme.grade c)
    (a : C.scheme.scheme.below (C.scheme.scheme.cell c)) {i : ℕ}
    (hi : i < C.scheme.scheme.grade c) (ha : W.stableValue u C a.1 = ofOrd (α.1 + i))
    (hai : ofOrd (α.1 + i) < W.stableValue u C c)
    (hcut : ofOrd (α.1 + L) < W.stableValue u C c)
    (ref : Ordinal.{0} → C.scheme.scheme.below (C.scheme.scheme.cell c))
    (off : Ordinal.{0} → ℕ)
    (href : ∀ μ ∈ blocks q, off μ < C.scheme.scheme.grade c ∧
      W.stableValue u C (ref μ).1 = ofOrd (μ + off μ) ∧
      ofOrd (μ + off μ) < W.stableValue u C c)
    (hfp : ∀ d β, q.label d = ofOrd β → finitePart β < L)
    (hproper : ∀ d, q.label d ≠ ⊤ → q.label d < ofOrd (α.1 + L)) :
    ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
      (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
      (hvC : Finset.univ.image f ∈ C.scheme.scheme.plan)
      (hF : C.scheme.restrictFace f hvC = p.scheme)
      (X : RelativeData C.scheme.scheme C.scheme.rows q.scheme.scheme q.scheme.rows),
      X.req = GrowthFiniteCapRequests.requests c L hLN a ref q.label ∧
      X.top = (Finset.univ, n + 1) ∧
      Nonempty (Growth.RootAttachment p.scheme Fin.castSuccEmb hvP hP f hvC hF X) ∧
      (∀ j, Growth.Admitted X j (GrowthStableSelectedInput.state
        (W := W) (u := u) (C := C) (q := q))) ∧
      HEq X.ZA {d : C.scheme.scheme.below (C.scheme.scheme.cell c) | C.label d.1 = ⊥} := by
  classical
  obtain ⟨hvP, hvC, hP, hF⟩ := GrowthStableSelectedInput.common_faces hM hp hf hq
  have hbelow := Growth.root_below_cap f hsc ((Nat.le_succ n).trans (hnL.le.trans hLN.le))
  let κ := Growth.literalKappa p.scheme Fin.castSuccEmb hvP hP f hvC hF c hbelow
  have hlit (d : q.scheme.scheme.below (Growth.rootIndex n)) :
      q.label d.1 = W.stableValue u C (κ d).1 :=
    Growth.literalKappa_label (restrictFace_eq_of_typeMap_eq_some hq)
      (restrictFace_eq_of_typeMap_eq_some (GrowthStableSelectedInput.stable_face hM hp hC hfu)) d
  obtain ⟨hrmem, htmem, hrt, hrne, htop⟩ := Growth.successor_bounds hn hvP
  let req := GrowthFiniteCapRequests.requests c L hLN a ref q.label
  obtain ⟨e, he, hebot, heeq, τ, hτ, -, hchart⟩ :=
    GrowthStableSelectedInput.exists_cleaned_source_chart hM hC c hc
  have hebot' (d) : e d = ⊥ ↔ W.stableValue u C d.1 = ⊥ :=
    (hebot d).trans (GrowthStableSelectedInput.private_bottom hM hC d.1).symm
  have hblocks (d β) (hd : q.label d = ofOrd β) :
      limitPart β ∈ blocks q ∧ finitePart β < L :=
    ⟨block_of_label hd, hfp d β hd⟩
  have hread (μ) (hμ : μ ∈ blocks q) : τ (e (ref μ)) = ofOrd (μ + off μ) := by
    grind
  have hfields (d) (hd : d ∈ req.F) : ∃ β, q.label d = ofOrd β ∧
      req.ρ d = ref (limitPart β) ∧ req.off d = finitePart β := Requests.ofLabels_field hd
  have hroot : ∀ s, RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) s →
      RespectsSemanticsBelow q.scheme.rows (Growth.rootIndex n) (fun d => s (κ d)) :=
    fun _ => Growth.literalKappa_lawful _ _ _ _ _ _ _ _ _
  obtain ⟨V, hV, hVr, hVc, hframe⟩ :=
    GrowthFiniteCapTemplate.exists_template req e he (W.stableValue u C) hebot' hτ
      hchart (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)) hi ha hai hcut
      (blocks q) (blocks_limit q) (GrowthFiniteCapRequests.blocks_le q)
      ref off (fun μ hμ => (href μ hμ).1) hread q.respects hblocks hproper
      hrmem htmem hrt hrne htop hnL κ hroot q.scheme.bountiful hlit
      (fun _ h => h) (fun _ h => h) hfields
  have href' (d β) (hd : q.label d = ofOrd β) :
      off (limitPart β) < C.scheme.scheme.grade c ∧
        W.stableValue u C (ref (limitPart β)).1 = ofOrd (limitPart β + off (limitPart β)) :=
    ⟨(href _ (hblocks d β hd).1).1, (href _ (hblocks d β hd).1).2.1⟩
  have ha_ne : C.label a.1 ≠ ⊥ := by
    intro hb
    have h := (GrowthStableSelectedInput.private_bottom hM hC a.1).mpr hb
    rw [ha] at h; exact ofOrd_ne_bot _ h
  have hρ_ne (d) (hd : d ∈ req.F) : C.label (req.ρ d).1 ≠ ⊥ := by
    intro hb
    obtain ⟨β, hβ, hρ, -⟩ := hfields d hd
    have h := (GrowthStableSelectedInput.private_bottom hM hC (req.ρ d).1).mpr hb
    rw [hρ, (href' d β hβ).2] at h
    exact ofOrd_ne_bot _ h
  have hOff (d) (hd : d ∈ req.F) : req.off d ≤ req.N := by
    obtain ⟨β, hβ, -, ho⟩ := hfields d hd
    rw [ho]; exact (hfp d β hβ).le.trans hLN.le
  let X := mkRelativeData req rfl (hc.trans_ne top_ne_bot) ha_ne hρ_ne hOff e hebot heeq
    hrmem htmem hrt hrne htop (hnL.le.trans hLN.le) κ hroot q.scheme.bountiful
    (fun d => Requests.ofLabels_cover d) V hV hVr hVc hframe
  refine ⟨hvP, hP, hvC, hF, X, rfl, rfl, by solve_by_elim, ?_, HEq.rfl⟩
  intro j
  refine ⟨(stableLiftRespects hM hC).toBelow _, q.respects.toBelow _, ?_, hlit, ?_⟩
  · intro d
    cases d with
    | inl d =>
      have hv : SelfVis (C.scheme.scheme.grade d) (W.stableValue u C d) :=
        ((stableLiftRespects hM hC).orderly d).symm
      exact hv.mono (C.scheme.scheme.grade_pos d)
    | inr d =>
      have hv : SelfVis (q.scheme.scheme.grade d) (q.label d) := (q.respects.orderly d).symm
      exact hv.mono (q.scheme.scheme.grade_pos d)
  · intro _ _
    exact GrowthFiniteCapRequests.correct c L hLN a ref q.label (W.stableValue u C) off href'

/-- End-to-end scalar input acquisition. The marker is an attained proper
stable value at an actual top, and growth supplies the later cap. No calibrated
context, source alignment, encoded template or activated admission is supplied.

The final two receipts deliberately differ: non-top donor labels are recovered
exactly, whereas donor tops are only forced strictly above the requested cut.
The positive-root restriction belongs to the existing `RelativeData` geometry.
-/
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
  have hfloor : ∃ b : ℕ, γ < α.1 + b := by
    rcases lt_or_ge γ α.1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨b, rfl⟩ := exists_nat_of_lt_add_omega h hγ
      exact ⟨b + 1, add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self b)) _⟩
  obtain ⟨b, hb⟩ := hfloor
  obtain ⟨L, hbL, hnL, hfp, hproper⟩ := GrowthFiniteCapRequests.exists_cut q b
  have hγL : ofOrd γ < ofOrd (α.1 + L) :=
    ofOrd_lt_ofOrd.mpr (hb.trans (add_lt_add_right (Nat.cast_lt.mpr hbL) _))
  obtain ⟨J, u, C, hC, f, g, hfu, -, hf, hg₀, c, hsc, hc, hLN, hi,
    hab, ha, hcut, hai, ref, off, href, -, -⟩ :=
    GrowthStableCalibration.exists_calibration hM hg hs a₀ hatop ha₀ t p hp (blocks q)
      (blocks_limit q) (GrowthFiniteCapRequests.blocks_le q) L
  let a : C.scheme.scheme.below (C.scheme.scheme.cell c) := ⟨mapCell hg₀ a₀, hab⟩
  obtain ⟨hvP, hP, hvC, hF, X, hreq, htop, hattach, hadmit, hclass⟩ :=
    exists_input_at hM hn hp hC hfu hf q hq c hsc hc L hnL hLN a hi ha hai hcut
      ref off href hfp hproper
  have hcap : X.req.C = c := congrArg Requests.C hreq
  have hN : X.req.N = C.scheme.scheme.grade c := congrArg Requests.N hreq
  refine ⟨J, u, C, hC, f, hfu, hf, hvP, hP, hvC, hF, X, htop,
    by rw [hN]; exact hnL.trans hLN, hcap.symm ▸ hsc, hcap.symm ▸ hc, hattach,
    ?_, hadmit, ?_⟩
  · cases hcap
    exact eq_of_heq hclass
  · intro v hv
    rw [hreq] at hv
    have href' (d β) (hd : q.label d = ofOrd β) :
        off (limitPart β) < C.scheme.scheme.grade c ∧
          W.stableValue u C (ref (limitPart β)).1 = ofOrd (limitPart β + off (limitPart β)) := by
      have hm := mem_blocks.mpr ⟨_, mem_donorRequests.mpr ⟨d, β, hd, rfl⟩, rfl⟩
      aesop
    constructor
    · intro d hnt
      by_cases hb : q.label d = ⊥
      · have he := hv.1 d hb
        change min (v d) (W.stableValue u C c) = ⊥ at he
        grind
      · exact GrowthFiniteCapRequests.proper_readback c L hLN a ref q.label
          (W.stableValue u C) hcut off href' hproper hv ⟨hb, hnt⟩
    · intro d hd
      exact hγL.trans_le (GrowthFiniteCapRequests.high_readback c L hLN a ref q.label
        (W.stableValue u C) (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2))
        hi ha hcut hv hd)

end

end VaughtConjecture.Knight.GrowthStableTemplate
