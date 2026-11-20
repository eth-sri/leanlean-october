module
public import Chazelle.Core.ModelAccess
public import Chazelle.Cost.Invariant
public import Chazelle.Programs.Address
public import Chazelle.Programs.Evidence
public import Chazelle.Programs.ReadWords
public import Chazelle.Programs.Verification

public import Chazelle.Core.SweepEvStepL1

/-!
# The sweep (WP-D), stage 3: the chords found at a key (Task L1)

* `stp_pre_frame`: the window and the reset keep the registers of the loop state and the memory below
  the allocator;
* `stp_stop_at`: a stop chord attached on the `C₁` part is a stop record;
* `stp_stop_near`: a stop record at the first cut beyond the key is the stop `sP` or `sP + 1`;
* `stp_query_tried`: the chord of `S₂` of a non-stop chord at the first cut beyond the key (given by
  `nonstop_found`) is tried in the iteration (both endpoint queries are in `iterO`);
* **`stp_accepted_of_found`**: a non-stop chord attached at the first cut beyond the key, not beyond
  the window end, is accepted by the batch of origins.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config}

/-- **The window and the reset** keep the loop registers and the memory below the allocator. -/
theorem stp_pre_frame (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs) :
    (∀ k, (600 ≤ k ∧ k < 700) ∨ (2400 ≤ k ∧ k ≤ 2406) ∨ (2430 ≤ k ∧ k ≤ 2459) ∨
      (2600 ≤ k ∧ k ≤ 2699) → cs.nreg (sw k) = c.nreg (sw k)) ∧
    (∀ x, x < c.nreg ALLOC → cs.nmem x = c.nmem x) ∧
    cs.nreg wGB = cw.nreg wGB ∧ cs.nreg wGK = cw.nreg wGK := by
  obtain ⟨rs₁, -, -, -, -, -, -, -, -, -, hmW, hregW⟩ := hW
  refine ⟨fun k hk => ?_, fun x hx => by grind [hR.1], ?_, ?_⟩
  all_goals try (solve | (invariant_facts; block_post))
  · rw [at_index hR.2.2.2 _]
    exact stp_win_keep hregW hk

/-- **A stop chord attached on the `C₁` part is a stop record.** -/
theorem stp_stop_at (L : LoopInv P J N₁ N₂ c₀ c) {s : Set Point}
    (hs : s ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)))
    (hss : StopChord2 J (N₂.F (chainModel J.right) (Qof P)) s) {p : ℕ} {t : ℝ}
    (hsA : SideAttach (chainModel J.whole).W s p t) (hL : (Lst J : ℝ) ≤ oW J (p + t)) :
    ∃ rs ax, StopData P J N₂ c rs ax ∧ ∃ i, ∃ hi : i < rs.length, rs[i].1 = p ∧
      (chainModel J.whole).param (Qof P) ⟨rs[i].1, rs[i].2.1⟩ = t ∧
      stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = s ∧
      i < c.nreg sC ∧ stopOff P J c i = oW J (p + t) := by
  obtain ⟨rs, ax, hD⟩ := L.stops
  obtain ⟨hlen, -, hrec, -, hok, -⟩ := id hD
  obtain ⟨r, hr, hreq⟩ := List.mem_map.1 (hok.2.1 s hs hss p t hsA hL)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  simp at hreq
  obtain ⟨h1, h2, h3⟩ := hreq
  obtain ⟨e0, e1, -⟩ := hrec i hi
  rw [List.getD_eq_getElem _ _ hi] at e0 e1
  have hoff : stopOff P J c i = oW J (p + t) := by
    show offK P J (c.nmem (c.nreg sB + 5 * i)) (c.nmem (c.nreg sB + 5 * i + 1)) = _
    rw [e0, e1]
    show oW J ((rs[i].1 : ℝ) + J.whole.chainModel.param (P.Qof) ⟨rs[i].1, rs[i].2.1⟩) = _
    simp_all
  grind

/-- **Every stop record is a cut** of `F₂⁺` on the `C₁` part. -/
theorem stp_stop_cut (L : LoopInv P J N₁ N₂ c₀ c) {i : ℕ} (hi : i < c.nreg sC) :
    ∃ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)), ∃ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W e p t ∧ stopOff P J c i = oW J (p + t) ∧
      StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e := by
  obtain ⟨rs, ax, hD⟩ := L.stops
  obtain ⟨hlen, -, hrec, -, hok, -⟩ := hD
  have hi' := hlen ▸ hi
  have hmem : (stopsOf J P.Qof N₂ rs)[i]'(by simpa [stopsOf] using hi') ∈
      stopsOf J P.Qof N₂ rs := List.getElem_mem _
  obtain ⟨h1, h2, h3, -⟩ := hok.1 _ hmem
  obtain ⟨e0, e1, -⟩ := hrec i hi'
  rw [List.getD_eq_getElem _ _ hi'] at e0 e1
  refine ⟨_, h1, _, _, h3, ?_, h2⟩
  show offK P J (c.nmem (c.nreg sB + 5 * i)) (c.nmem (c.nreg sB + 5 * i + 1)) = _
  simp [e0, e1, stopsOf]
  rfl

/-- **The stops at the first cut beyond the key** are the stops `sP` and `sP + 1`. -/
theorem stp_stop_near (L : LoopInv P J N₁ N₂ c₀ c) {o : ℝ} (ho : keyOff P J c < o)
    (hgap : ∀ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)), ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e q s → ¬ (keyOff P J c < oW J (q + s) ∧ oW J (q + s) < o))
    {i : ℕ} (hi : i < c.nreg sC) (hio : stopOff P J c i = o) :
    i = c.nreg sP ∨ i = c.nreg sP + 1 := by
  have hpi : c.nreg sP ≤ i := by
    by_contra h
    have := guarded (L.ptrL i hi).1
    linarith
  -- every stop from `sP` to `i` is at `o`
  have hat : ∀ i' ≥ c.nreg sP, i' ≤ i → stopOff P J c i' = o := by
    intro i' h1 h2
    have hi' : i' < c.nreg sC := by omega
    have hgt : keyOff P J c < stopOff P J c i' := by
      by_contra h
      have := (L.ptrL i' hi').2 (not_lt.1 h)
      omega
    have hle : stopOff P J c i' ≤ o := hio ▸ L.sorted i' i h2 hi
    obtain ⟨e, he, q, s, hA, hq, -⟩ := stp_stop_cut L hi'
    rcases hle.lt_or_eq with h | h
    · grind
    · exact h
  by_contra hne
  have := at_index L.two (c.nreg sP); grind

/-- **The chord of `S₂` of a non-stop chord at the first cut beyond the key is tried** in the
iteration: it touches a region of the label set or a gap region (`regO`), or contains a stop chord
at the cut, the stop `sP` or `sP + 1` (`parO`). -/
theorem stp_query_tried (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs) {o : ℝ} (ho : keyOff P J c < o)
    (hgap : ∀ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)), ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e q s → ¬ (keyOff P J c < oW J (q + s) ∧ oW J (q + s) < o))
    {pK : ℕ} {tK : ℝ} (hoK : oW J (pK + tK) = o) {ch : Set Point}
    (hch : ch ∈ N₂.F (chainModel J.right) (Qof P))
    (hsrc : (∃ V ∈ (chainModel J.right).regions (N₂.F (chainModel J.right) (Qof P)),
        (V ∈ curLab P J N₂ c ∨ GapLab J (N₂.F (chainModel J.right) (Qof P)) V) ∧
          Chazelle.Chain.TouchesIn (chainModel J.right).D ch V) ∨
      (∃ s ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)),
        SideAttach (chainModel J.whole).W s pK tK ∧
          StopChord2 J (N₂.F (chainModel J.right) (Qof P)) s ∧ s ⊆ ch)) :
    ∃ k, k < N₂.nChords ∧ (N₂.chord k).toSet (chainModel J.right) (Qof P) = ch ∧
      ∀ s, s ≤ 1 → 2 * k + s ∈ iterO N₂ cs := by
  obtain ⟨hkp, hmem, -, -⟩ := stp_pre_frame hW hR
  have ekN : cs.nreg kN = c.nreg kN := at_index hkp 2402
  have ekL : ∀ u < 4, cs.nreg (kL + u) = c.nreg (kL + u) := fun u hu => by
    have := at_index hkp (2403 + u)
    grind [kL, sw]
  have egN : cs.nreg gN = c.nreg gN := at_index hkp 2440
  have egR : ∀ u < 2, cs.nreg (gR + u) = c.nreg (gR + u) := fun u hu => by
    have := at_index hkp (2441 + u)
    grind [gR, sw]
  rcases hsrc with ⟨V, -, hVΛ, hT⟩ | ⟨s₀, hs₀, hsA, hss, hsub⟩
  · obtain ⟨k, hk, hci⟩ := Restore.mem_F_iff hch
    refine ⟨k, hk, hci.symm, fun s hs => ?_⟩
    have hreg : ∀ l < N₂.nRegions, regOf J.right.chainModel P.Qof N₂ l = V →
        2 * k + s ∈ regO N₂ l := by
      intro l hl hlV
      refine ⟨k, ((((regOf_spec E.hNF₂).2.2.2.1) l hl).1 k).2 ⟨hk, ?_⟩, s, hs, rfl⟩
      rwa [← hci, hlV]
    rcases hVΛ with ⟨l, hl, hlV⟩ | hg
    · obtain ⟨u, hu, hu4, rfl⟩ : ∃ u < c.nreg kN, u < 4 ∧ l = c.nreg (kL + u) := by
        rcases hl with h | h | h | h
        · exact ⟨0, h.1, by norm_num, h.2⟩
        · exact ⟨1, h.1, by norm_num, h.2⟩
        · exact ⟨2, h.1, by norm_num, h.2⟩
        · exact ⟨3, h.1, by norm_num, h.2⟩
      refine Or.inl (Or.inl ⟨u, by rw [ekN]; omega, ?_⟩)
      rw_facts [ekL]
      exact from_facts hreg
    · obtain ⟨u, hu, hlV⟩ := L.gap V hg
      refine Or.inl (Or.inr ⟨u, by grind [L.gapN], ?_⟩)
      rw [egR u (by have := L.gapN; omega)]
      exact from_facts hreg
  · -- the parent of a stop at the cut
    obtain ⟨rs, ax, hD, i, hi, -, -, hset, hic, hio⟩ := stp_stop_at L hs₀ hss hsA (by rw [hoK]; linarith [L.keyL])
    obtain ⟨-, hax, -, hrecA, -, -, hauxOK, -⟩ := hD
    have hiA : i < ax.length := hax ▸ hi
    have hok := hauxOK i hi
    rw [List.getD_eq_getElem _ _ hi, hset, List.getD_eq_getElem _ _ hiA] at hok
    obtain ⟨-, -, -, -, -, -, hparle, hpar, -⟩ := hok
    obtain ⟨hpar0, hpch⟩ := hpar ch hch hsub
    obtain ⟨-, -, -, -, e4⟩ := hrecA i hiA
    rw [List.getD_eq_getElem _ _ hiA] at e4
    have esP : cs.nreg sP = c.nreg sP := at_index hkp 2450
    have esC : cs.nreg sC = c.nreg sC := at_index hkp 2601
    have eaB : cs.nreg aB = c.nreg aB := at_index hkp 2602
    have hlay5 := L.lay5
    have hpo : parOf cs i = ax[i].2.2.2.2 := by
      unfold parOf
      read_words
    refine ⟨ax[i].2.2.2.2 - 1, by omega, hpch, fun s hs => Or.inr ⟨i, by rw [esP]; exact (stp_stop_near L ho hgap hic (hio.trans hoK)),
      by rw [esC]; exact hic, by rwa [hpo], s, hs, by rw [hpo]⟩⟩

/-- **A non-stop chord at the first cut beyond the key, not beyond the window end, is accepted**
by the batch of origins (at its far end, from a valid origin). -/
theorem stp_accepted_of_found (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs) {A : Set (ℕ × ℕ × ℕ)}
    (hBA : BatchA P J N₂ cs
      (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) (cs.nreg wGK) [])
      (iterO N₂ cs) co A)
    {e : Set Point} (he : e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P))) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hlt : keyOff P J c < oW J (p + t))
    (hgap : ∀ e' ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)), ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e' q s →
        ¬ (keyOff P J c < oW J (q + s) ∧ oW J (q + s) < oW J (p + t)))
    (hst : ¬ StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e)
    (hwin : cw.nreg wX = 0 → oW J (p + t) ≤ offK P J (cw.nreg wE) (cw.nreg wH)) :
    ∃ k, k < N₂.nChords ∧ ∃ (a : Point) (σ : ℝ),
      ((σ = 1 ∧ a = Merge.lend ((N₂.chord k).toSet (chainModel J.right) (Qof P))) ∨
        (σ = -1 ∧ a = Merge.rend ((N₂.chord k).toSet (chainModel J.right) (Qof P)))) ∧
      a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧
      e = Merge.shoot J.whole a σ ∧ J.whole.hitParam a σ < J.right.hitParam a σ ∧
      ∃ j, j < 2 * N₂.nChords ∧ j / 2 = k ∧ endOrigin J (Qof P) N₂ j = a ∧ endDir j = σ ∧
        ∃ h, (chainModel J.whole).param (Qof P) ⟨p, h⟩ = t ∧ (j, p, h) ∈ A := by
  classical
  set S₂ := N₂.F J.right.chainModel P.Qof with hS₂d
  have hP := E.hP
  have hS₂ := E.hNF₂.1
  have hS₂a := hS₂.2.1
  have hLst := lt_of_le_of_lt L.keyL hlt
  obtain ⟨ch, hch, a, σ, ha, haR, hav, hat, hfree, rfl, hsrc⟩ :=
    nonstop_found hP hS₂ (F₂plus_chordFamily E) L.keyL L.inv hA.1 hA.2.1 hA.2.2.1 hlt hgap he hA hst
  obtain ⟨k, hk, hkch, htried⟩ := from_facts stp_query_tried
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hlt' := by apply whole_lt_right <;> assumption
  have hpt := attach_far hP hσ haR hav hfree hA hLst.le
  have hnv : sidePt J.whole.chainModel.W p t ≠ J.shared := by
    intro h
    have hvD := fun hd =>
      J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset J.shared_mem_left)
    obtain ⟨σ', hσ', hfr, he'⟩ := chord_eq_shoot_of_end J.whole (F₂plus_subset J hS₂a he) (h ▸ hA.2.2.2.1) hvD
    exact hst (Or.inl (Or.inl ⟨σ', hσ', hfr, he'⟩))
  have ha₁ : a.2 ≤ J.left.top.2 := by
    rcases SweepStop.hit_cases (right_hit_end (hS₂a hch) ha).2.1 hσ with h | h
    · exact absurd h hlt'.ne
    · exact h.1
  obtain ⟨-, -, d, hMV, hmE, hArr⟩ := guarded (cand_prep hP hS₂a hch ha haR hav ha₁)
  rw [← hkch] at ha
  -- the endpoint query
  obtain ⟨j, hj, hjk, hji, hjO, hjD⟩ : ∃ j < 2 * N₂.nChords, j / 2 = k ∧
      (∃ s ≤ 1, j = 2 * k + s) ∧ endOrigin J P.Qof N₂ j = a ∧ endDir j = σ := by
    unfold endOrigin endDir
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨2 * k, by omega, by omega, ⟨0, by omega, by omega⟩, ?_, ?_⟩ <;> simp
    · refine ⟨2 * k + 1, by omega, by omega, ⟨1, le_rfl, rfl⟩, ?_, ?_⟩
      · rw [guarded ite_eq_right, show (2 * k + 1) / 2 = k by omega]
      · simp
  have hjO' : j ∈ iterO N₂ cs := by
    obtain ⟨s, hs, rfl⟩ := hji
    exact htried s hs
  -- the hit is on the gathered arcs
  obtain ⟨-, -, eGB, eGK⟩ := stp_pre_frame hW hR
  obtain ⟨rs₁, -, -, hgk, -, -, -, -, -, hcov, -, -⟩ := hW
  have hoffd : (Lst J : ℝ) + ψ J d + t = oW J (p + t) := by
    rw [oW_def, off_key' stp_gW_lt hA.1 hA.2.1 hA.2.2.1, ← hmE]
    unfold mEdge
    rw [dOf_add_mod stp_gW_lt (Lst_ψ_lt hP hMV.1)]
    push_cast; ring
  have hlo : rayPt a σ (J.whole.hitParam a σ) ∈
      ShotList.loSet J.left.chainModel P.Qof cs.nmem (cs.nreg wGB) (cs.nreg wGK) [] := by
    have hin := hcov d t hMV hA.2.1 hA.2.2.1 (by rwa [hoffd]) (fun h0 => by
      grind)
    rw [hArr.2.2.2.1, ← hgk] at hin
    rwa [hR.1, eGB, eGK]
  obtain ⟨h, hh, hmA⟩ := hBA.comp j hjO' hj ⟨by rwa [hjO], by rwa [hjO],
    by rwa [hjO]⟩ p t (by rwa [hjO, hjD]) (by rwa [hjO, hjD]) hLst
    hnv (by rwa [hjO, hjD]) (by rwa [hjO, hjD])
  exact ⟨k, hk, a, σ, ha, haR, hav, hat, hfree, rfl, hlt', j, hj, hjk, hjO, hjD, h, hh, hmA⟩

end

end SweepEv

end Chazelle.Core
