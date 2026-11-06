module

public import Chazelle.Core.RestoreFCover
public import Chazelle.Core.MergeAsmMath

/-!
# WP-E, the search: the obligations of the pieces

From the cutter's contract: the pieces tile the arc (`tile_of_cut`), a piece weighs at most the arc
(`piece_wt_le`), and every kind-1 piece meets `K1Hyp` (`k1hyp_of`), so every piece is `PieceGood`
for any piece bound `Kp` dominating the costs of its handlers (`pgood_of`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sideInArc)
open DownHost ArcT

/-! ## The arcs of a region of a normal form -/

/-- **A region of a normal form has at most `D + 1` arcs** if its degree is at most `D`. -/
theorem region_arcs_le {M : Model} {Q : Polygon} {N : NF} (hM : WalkAx M) (hNF : IsNF M Q N)
    {D : ℕ} (hD : M.DegLe (N.F M Q) D) {r : ℕ} (hr : r < N.nRegions) :
    (N.region r).arcs.length ≤ D + 1 := by
  classical
  obtain ⟨hFam, -, -, reg, hRC, -, hArcs, hRg, -, -, -⟩ := hNF
  have hU := hRC.1 r hr
  set l := (N.region r).arcs
  have hnd : l.Nodup := (hRg r hr).2.2.1
  set f : ℕ → ℝ × ℝ := fun j => (M.key Q (N.arc j).s, M.key Q (N.arc j).e)
  have hinj : Set.InjOn f (↑l.toFinset : Set ℕ) := by
    intro j hj j' hj' he
    have hj := List.mem_toFinset.1 hj
    have hj' := List.mem_toFinset.1 hj'
    obtain ⟨hjl, hjr⟩ := (hArcs.2.2.2 r hr j).1 hj
    obtain ⟨hjl', hjr'⟩ := (hArcs.2.2.2 r hr j').1 hj'
    exact hArcs.2.1 j j' hjl hjl' (by rw [hjr, hjr']) (congrArg Prod.fst he)
  have hsub : f '' (↑l.toFinset : Set ℕ) ⊆ {ab : ℝ × ℝ | M.IsArc (N.F M Q) (reg r) ab.1 ab.2} := by
    rintro _ ⟨j, hj, rfl⟩
    have hj := List.mem_toFinset.1 hj
    obtain ⟨hjl, hjr⟩ := (hArcs.2.2.2 r hr j).1 hj
    have := (hArcs.1 j hjl).2
    rwa [hjr] at this
  obtain ⟨hfin, hcard⟩ := hM.arcs_bound hFam.2.1 hFam.1 hU
  have hl : l.length = (↑l.toFinset : Set ℕ).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  calc l.length = (f '' (↑l.toFinset : Set ℕ)).ncard := by rw [hinj.ncard_image, hl]
    _ ≤ {ab : ℝ × ℝ | M.IsArc (N.F M Q) (reg r) ab.1 ab.2}.ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ M.deg (N.F M Q) (reg r) + 1 := hcard
    _ ≤ D + 1 := by have := hD _ hU; omega


/-! ## The tiling of an arc by its pieces -/

variable {E : FEnv} {c₀ : Config}

/-- The key of the start of piece `i` of the list at `L` in memory `m`. -/
noncomputable def psK (E : FEnv) (m : ℕ → ℕ) (L i : ℕ) : ℝ :=
  E.M.key (Qof E.P) ⟨m (L + 1 + 7 * i + 0), m (L + 1 + 7 * i + 1)⟩

/-- The key of the end of piece `i`. -/
noncomputable def peK (E : FEnv) (m : ℕ → ℕ) (L i : ℕ) : ℝ :=
  E.M.key (Qof E.P) ⟨m (L + 1 + 7 * i + 2), m (L + 1 + 7 * i + 3)⟩

theorem key_bounds {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x)
    (he : x.edge < M.W.n) : 0 ≤ M.key Q x ∧ M.key Q x < M.W.n := by
  have hk : M.key Q x = x.edge + M.param Q x := rfl
  have : (x.edge : ℝ) + 1 ≤ M.W.n := by exact_mod_cast he
  rw [hk]; constructor <;> linarith [hx.1, hx.2.1, (Nat.cast_nonneg x.edge : (0 : ℝ) ≤ x.edge)]

/-- The arc `t` of the region is an arc of every region map of the normal form. -/
theorem arc_isArc (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) {t : ℕ} (ht : t < (E.N.region E.r).arcs.length) :
    E.M.IsArc (E.N.F E.M (Qof E.P)) (reg E.r) (E.M.key (Qof E.P) (arcOf E.N E.r t).s)
      (E.M.key (Qof E.P) (arcOf E.N E.r t).e) := by
  obtain ⟨-, -, hArcs, -⟩ := hregs
  have hr : E.r < E.N.nRegions := hE.hr
  set j := (E.N.region E.r).arcs.getD t 0 with hjdef
  have hjm : j ∈ (E.N.region E.r).arcs := by
    rw [hjdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  obtain ⟨hj, hjr⟩ := (hArcs.2.2.2 E.r hr j).1 hjm
  have := (hArcs.1 j hj).2
  rwa [hjr] at this

/-- The ends of an arc of a region with an exit chord differ. -/
theorem arc_ne (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) :
    E.M.key (Qof E.P) (arcOf E.N E.r t).s ≠ E.M.key (Qof E.P) (arcOf E.N E.r t).e := by
  obtain ⟨reg, hregs⟩ := nfregs_of hE
  obtain ⟨-, -, -, -, hc, -⟩ := arc_isArc hE hregs ht
  rcases hc with ⟨-, -, h⟩ | ⟨hF, -, -⟩
  · exact h
  · exfalso
    have hr : E.r < E.N.nRegions := hE.hr
    obtain ⟨-, -, -, hRg⟩ := hregs
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hch
    obtain ⟨hi', -⟩ := ((hRg E.r hr).1 i).1 hi
    have hmem : E.N.chord i ∈ E.N.chords := by
      unfold NF.chord
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      exact List.getElem_mem hi'
    have : (E.N.chord i).toSet E.M (Qof E.P) ∈ E.N.F E.M (Qof E.P) := ⟨E.N.chord i, hmem, rfl⟩
    rwa [hF] at this

/-- **The pieces of the cut of arc `t` tile it.** -/
theorem tile_of_cut (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) {m : ℕ → ℕ} {A L : ℕ}
    (hcp : CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r t).s)
      (normOf E.M (Qof E.P) (arcOf E.N E.r t).e) m A L) :
    Tile E.M.W.n (E.M.key (Qof E.P) (arcOf E.N E.r t).s) (E.M.key (Qof E.P) (arcOf E.N E.r t).e)
      (m L) (psK E m L) (peK E m L) := by
  obtain ⟨reg, hregs⟩ := nfregs_of hE
  obtain ⟨ha0, ha1, hb0, hb1, -, -⟩ := arc_isArc hE hregs ht
  have hAi := hE.arcOK hch ht
  obtain ⟨-, -, hq1, hk0, hkq, hcons, hin, -, -, hpos, -⟩ := hcp
  have ku := (normOf_facts hAi.sp).2.2.2.1
  have kv := (normOf_facts hAi.ep).2.2.2.1
  refine ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, arc_ne hE hch ht, hq1, fun i hi => ?_, fun i hi => ?_,
    ?_, ?_, fun i hi => hcons i hi, fun i hi => ?_⟩
  · obtain ⟨h1, -, h3, -⟩ := hpos i hi
    exact key_bounds h1 h3
  · obtain ⟨-, h2, -, h4⟩ := hpos i hi
    exact key_bounds h2 h4
  · exact hk0.trans ku
  · exact hkq.trans kv
  · have e1 : E.M.key (Qof E.P) ⟨(normOf E.M (Qof E.P) (arcOf E.N E.r t).e).edge,
        (normOf E.M (Qof E.P) (arcOf E.N E.r t).e).hgt⟩ = E.M.key (Qof E.P) (arcOf E.N E.r t).e := kv
    have := hin i hi
    dsimp only at this
    rwa [e1] at this

/-- **A piece weighs at most its arc.** -/
theorem piece_wt_le {n a b : ℝ} {q : ℕ} {s e : ℕ → ℝ} {M : Model} (hn : n = M.W.n)
    (h : Tile n a b q s e) {i : ℕ} (hi : i < q) : M.arcWt (s i) (e i) ≤ M.arcWt a b := by
  refine Set.ncard_le_ncard (fun p hp => ?_) ((Set.finite_Iio M.W.n).subset fun x hx => hx.1)
  obtain ⟨hp, hc, τ, h0, h1, hin⟩ := hp
  have hpn : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp
  exact ⟨hp, hc, τ, h0, h1, tile_inner h hi ⟨by positivity, by rw [hn]; linarith⟩ hin⟩


/-! ## A kind-1 piece -/

theorem arcWt_le_size (M : Model) (a b : ℝ) : M.arcWt a b ≤ M.size :=
  Set.ncard_le_ncard (fun _ hp => ⟨hp.1, hp.2.1⟩) ((Set.finite_Iio M.W.n).subset fun _ hx => hx.1)

theorem qof_simple (hE : FGood E c₀) : (Qof E.P).Simple :=
  (shearInvariance (epsOf E.P) E.P).1 hE.hG.1

/-- **The facts of a kind-1 piece**, from the cutter's contract. -/
theorem k1hyp_of (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) {c' : Config} (hI' : FInv E.W c₀ c') {L : ℕ}
    (hcp : CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r t).s)
      (normOf E.M (Qof E.P) (arcOf E.N E.r t).e) c'.nmem (c'.nreg ALLOC) L)
    {i : ℕ} (hi : i < c'.nmem L) (hk : c'.nmem (prOf L i + 4) = 1) :
    ∃ Hs Cα N γ', K1Hyp (E.re c') c' (prOf L i) Hs Cα N γ' ∧ γ' ≤ E.H E.γ ∧ Cα.m ≤ E.γ := by
  have hT := tile_of_cut hE hch ht hcp
  have hAi := hE.arcOK hch ht
  have hcp' := hcp
  obtain ⟨hLq, -, -, -, -, -, -, -, hk1w, hpos, -⟩ := hcp'
  obtain ⟨hwf, Hs, Cα, N, hCD, hNW, ⟨γ', hγ', hcan⟩, -, hwt, hPW, hQ, hdir⟩ := hk1w i hi hk
  obtain ⟨-, -, hs, -⟩ := hpos i hi
  obtain ⟨h0, h3, -, he, -⟩ := hPW
  have hWh := hE.hWh
  unfold hostWords at hWh
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  have hmP : Cα.m < E.P.n := by have := Cα.m_lt; rwa [hQ, hQn] at this
  set n := E.M.W.n
  set s := c'.nmem (L + 1 + 7 * i + 0)
  -- the weight of the piece
  have hwt' : E.M.arcWt (s : ℝ) (((s + Cα.m) % n : ℕ) : ℝ) = Cα.m := by
    have e1 : E.M.key (Qof E.P) ⟨c'.nmem (L + 1 + 7 * i + 0), c'.nmem (L + 1 + 7 * i + 1)⟩ = s := by
      simp only at h0; rw [h0]; exact key_vtx' _ _ _
    have e2 : E.M.key (Qof E.P) ⟨c'.nmem (L + 1 + 7 * i + 2), c'.nmem (L + 1 + 7 * i + 3)⟩ =
        (((s + Cα.m) % n : ℕ) : ℝ) := by
      simp only at h3 he; rw [h3, he]; exact key_vtx' _ _ _
    have := hwt
    simp only at this
    rwa [e1, e2] at this
  have hmn : Cα.m < n := by
    rcases hE.kind with ⟨C, -, hM⟩ | hM
    · have h1 := arcWt_le_size E.M (s : ℝ) (((s + Cα.m) % n : ℕ) : ℝ)
      rw [hwt'] at h1
      have h2 : E.M.size = 2 * C.m := by rw [hM]; exact MergeAsm.chainModel_size C
      have h3 : n = 2 * C.m + 7 := by show E.M.W.n = _; rw [hM]; exact chainModel_n C
      omega
    · have : n = E.P.n := by
        show E.M.W.n = _; rw [hM]; show (interiorWalk (Qof E.P)).n = _; rw [interiorWalk_n', hQn]
      omega
  have hm1 := Cα.one_le
  -- the piece's chain lies on the model's chain
  have hsub : ∀ C : Chain, E.M = chainModel C → Cα.set ⊆ C.set := fun C hM => by
    have hc := counted_of_wt (M := E.M) hs (by omega) hmn hwt'
    have hdir' := hdir
    have hn' : n = (chainModel C).W.n := by rw [← hM]
    rw [hn'] at hdir'
    rw [hM] at hc hdir'
    exact piece_set_sub hdir' hc
  -- the weight bound
  have hwγ : Cα.m ≤ E.γ := by
    have h1 := piece_wt_le rfl hT hi
    have h2 : E.M.arcWt (psK E c'.nmem L i) (peK E c'.nmem L i) = Cα.m := hwt
    have h3 := hAi.wt
    omega
  -- the walk model of the piece's chain
  have hGα : GoodModel (chainModel Cα) := Or.inl ⟨Cα, by rw [hQ]; exact qof_simple hE, rfl⟩
  have hMα := walkAx_of_goodModel hGα
  obtain ⟨hB7, hcb, -, -, -, -⟩ := nf_bounds hNW
  have hAW : c'.nreg ALLOC ≤ E.W := hI'.hw.1 ALLOC
  refine ⟨Hs, Cα, N, γ', ⟨?_, hCD, hwf, hNW, hcan, hQ, hdir, hs, hmn, fun C hM => ?_, ?_, ?_, ?_⟩,
    hγ', hwγ⟩
  · show L + 1 + 7 * i + 6 < _
    omega
  · have hv : E.M.pos (Qof E.P) ⟨s, 0⟩ = E.M.W.vtx s := by
      rw [pos_eq_sidePt, param_vtx, Chazelle.Chain.sidePt_zero]
    show E.M.pos (Qof E.P) ⟨s, 0⟩ ∈ C.set
    rw [hv]
    have hs0 : (s + 0) % n = s := by rw [Nat.add_zero, Nat.mod_eq_of_lt hs]
    rcases hdir with hu | hd
    · rw [← hs0, hu 0 (Nat.zero_le _)]; exact hsub C hM (Cα.vertex_mem_set (Nat.zero_le _))
    · rw [← hs0, hd 0 (Nat.zero_le _)]; exact hsub C hM (Cα.vertex_mem_set (Nat.sub_le _ _))
  · show 2 * (2 * Cα.m + 7) ≤ E.W
    omega
  · intro r hr
    have := region_arcs_le hMα hcan.1 hcan.2.1 hr
    show 2 * (2 * Cα.m + 7) + _ ≤ E.W
    omega
  · show 4 * Nat.clog 2 (N.nChords + 1) + 1 + 1 ≤ E.W
    have hcl : Nat.clog 2 (N.nChords + 1) ≤ N.nChords :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self
    rcases Nat.lt_or_ge N.nChords 2 with h | h
    · omega
    · have := hcb (N.nChords - 1) (by omega)
      omega


/-- **Every piece of the cut of an arc is good** for a piece bound `Kp` dominating the handlers. -/
theorem pgood_of (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) {Kp : ℕ} (hk0 : k0K E ≤ Kp)
    (hk1 : ∀ (Cα : Chain) (N : NF) (γ' : ℕ), Cα.P = Qof E.P →
      IsCanonicalNF (chainModel Cα) (Qof E.P) N γ' 4 → γ' ≤ E.H E.γ → Cα.m ≤ E.γ →
      k1K E Cα N ≤ Kp) :
    PGood E c₀ Kp t := by
  intro c' hI' hcp i hi
  have hcp' := hcp
  obtain ⟨hLq, -, -, -, -, -, -, -, -, hpos, -⟩ := hcp'
  refine ⟨by show c'.nreg 81076 + 1 + 7 * i + 6 < _; omega, (hpos i hi).2.2.1, hk0, fun hk => ?_⟩
  obtain ⟨Hs, Cα, N, γ', hK, hγ', hm⟩ := k1hyp_of hE hch ht hI' hcp hi hk
  exact ⟨Hs, Cα, N, γ', hK, hk1 Cα N γ' hK.hQ hK.hcan hγ' hm⟩

end

end Restore

end Chazelle.Core
