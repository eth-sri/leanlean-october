module

public import Chazelle.Core.Lemma41Ram4
public import Chazelle.Core.Facts2Chain
public import Chazelle.Core.ShearInv

/-!
# WP-J, part 13: the nodes of the merge tree and the precondition of a merge

* `NodeOK P m A d f C γ`: a node, i.e. the descriptor at `d` (whole host) of a chain `C` of `Q` and
  a `γ`-canonical normal form at `f`, all readable below `A`; `NodeOK.agree` (stable under writes
  at `≥ A`) and `NodeOK.mono`;
* `sharedGeneric_q`: junctions of consecutive chains of `Q` are generic (distinct heights);
* `mergePre_of`: two consecutive nodes, the descriptor of their union, the context and the
  targets give `MergePre`.
-/

namespace Chazelle.Core.L41

open Machine Chazelle Chazelle.Merge

@[expose] public section

/-- **A node** of the merge tree. -/
def NodeOK (P : Polygon) (m : ℕ → ℕ) (A hp d f : ℕ) (C : Chain) (γ : ℕ) : Prop :=
  ChainDescAt m d (Qof P) (Host.whole P.n) C ∧ C.P = Qof P ∧ m d = hp ∧ d + 5 ≤ A ∧
    hp + 7 ≤ A ∧ C.s + C.m + 1 ≤ P.n ∧
    ∃ N, NFWithin m f A N ∧ IsCanonicalNF (chainModel C) (Qof P) N γ 4

theorem hostAt_agree {m m' : ℕ → ℕ} {hp A : ℕ} {H : Host} (h : HostAt m hp H) (hl : H.length = 1)
    (hA : hp + 4 ≤ A) (he : MemEqBelow A m' m) : HostAt m' hp H :=
  h.copy fun j hj => he _ (by omega)

theorem chainDescAt_agree {m m' : ℕ → ℕ} {d hp A : ℕ} {Q : Polygon} {n : ℕ} {C : Chain}
    (h : ChainDescAt m d Q (Host.whole n) C) (hd : d + 5 ≤ A) (hh : m d = hp) (hA : hp + 7 ≤ A)
    (he : MemEqBelow A m' m) : ChainDescAt m' d Q (Host.whole n) C := by
  apply h.agree hd _ he
  rw [hh]
  exact hA

/-- Nodes survive writes at or above `A`. -/
theorem NodeOK.agree {P : Polygon} {m m' : ℕ → ℕ} {A hp d f : ℕ} {C : Chain} {γ : ℕ}
    (h : NodeOK P m A hp d f C γ) (he : MemEqBelow A m' m) : NodeOK P m' A hp d f C γ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, N, hN, hc⟩ := h
  refine ⟨chainDescAt_agree h1 h4 h3 h5 he, h2, by ram_simp [he] <;> omega, h4, h5, h6,
    N, ?_, hc⟩
  intro m'' hm''
  exact hN m'' (fun a ha => (hm'' a ha).trans (he a ha))

/-- Nodes stay nodes for a larger bound. -/
theorem NodeOK.mono {P : Polygon} {m : ℕ → ℕ} {A A' hp d f : ℕ} {C : Chain} {γ : ℕ}
    (h : NodeOK P m A hp d f C γ) (hA : A ≤ A') : NodeOK P m A' hp d f C γ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, N, hN, hc⟩ := h
  exact ⟨h1, h2, h3, by omega, by omega, h6, N, fun m' hm' => hN m' (fun a ha => hm' a (by omega)),
    hc⟩

/-- **Junctions of consecutive chains of `Q` are generic.** -/
theorem sharedGeneric_q {P : Polygon} (hG : GoodEnv P) {J : Junction} (hJ : J.P = Qof P)
    (hn : J.s + J.m₁ + J.m₂ + 1 ≤ P.n) : SharedGeneric J := by
  have hDH : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  have hQn : (Qof P).n = P.n := shear_n _ _
  have h1 := J.one_le_m₁; have h2 := J.one_le_m₂
  have ev : ∀ k, J.s + k < P.n → J.whole.vertex k = (Qof P).vtx (J.s + k) := fun k hk => by
    unfold Chain.vertex Chain.edgeIdx
    show J.P.vtx ((J.s + k) % J.P.n) = _
    rw [hJ, hQn, Nat.mod_eq_of_lt hk]
  unfold SharedGeneric sharedU sharedV sharedW
  ram_rw [ev, ev, ev]
  refine ⟨hDH _ _ (by omega) (by omega) (by omega), hDH _ _ (by omega) (by omega) (by omega),
    hDH _ _ (by omega) (by omega) (by omega)⟩

/-- A host description in memory is determined by the memory. -/
abbrev hostAt_unique := @Chazelle.Core.NFLoc.hostAt_unique

/-- **The precondition of a merge** from two consecutive nodes and the union's descriptor. -/
theorem mergePre_of {P : Polygon} {W : ℕ} {c : Config} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hX : X.holds P c.nmem (rd c bMerge 9) (c.nreg ALLOC))
    (hcap : rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem (rd c bMerge 9))
    (h7 : rd c bMerge 7 = 4) (h56 : rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6)
    {hp d1 f1 d2 f2 TD : ℕ} {C1 C2 : Chain} {γ1 γ2 : ℕ}
    (hn1 : NodeOK P c.nmem (c.nreg ALLOC) hp d1 f1 C1 γ1)
    (hn2 : NodeOK P c.nmem (c.nreg ALLOC) hp d2 f2 C2 γ2)
    (hγ1 : γ1 ≤ rd c bMerge 5) (hγ2 : γ2 ≤ rd c bMerge 5)
    (hcons : C2.s = C1.s + C1.m) (hlen : C1.m + C2.m + 1 ≤ C1.P.n)
    (r0 : rd c bMerge 0 = d1) (r1 : rd c bMerge 1 = d2) (r2 : rd c bMerge 2 = TD)
    (r3 : rd c bMerge 3 = f1) (r4 : rd c bMerge 4 = f2)
    (hTD : ChainDescAt c.nmem TD (Qof P) (Host.whole P.n) (jOf C1 C2 hlen).whole)
    (hTDm : c.nmem TD = hp) (hTDA : TD + 5 ≤ c.nreg ALLOC)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P (chainModel C)) : MergePre X Ok P W c := by
  obtain ⟨d1a, d1P, d1h, d1A, hpA, d1n, N1, hN1, hc1⟩ := hn1
  obtain ⟨d2a, d2P, d2h, d2A, -, d2n, N2, hN2, hc2⟩ := hn2
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn1 : 1 ≤ P.n := by have := C1.one_le; omega
  have hQ := (shearInvariance (epsOf P) P).1 hG.1
  
  set J := jOf C1 C2 hlen with hJ
  have hl : J.left = C1 := jOf_left C1 C2 hlen
  have hr : J.right = C2 := jOf_right hlen (by rw [d2P, d1P]) hcons
  have hwP : J.whole.P = Qof P := by assumption
  have hpoly : (Host.whole P.n).poly (Qof P) = Qof P := by
    have := poly_whole (Qof P) (by omega); rwa [hQn] at this
  have hHA : HostAt c.nmem hp (Host.whole P.n) := by have := d1a.1; simp_all
  -- well-formed descriptors
  have wf : ∀ d, d + 5 ≤ c.nreg ALLOC → c.nmem d = hp → c.nmem (d + 1) < P.n →
      ChainWF P (c.nreg ALLOC) c.nmem d := by
    intro d hd hdh hds
    refine ⟨hd, fun H C hC => ?_⟩
    have hH := hostAt_unique hC.1 (by rw [hdh]; exact hHA)
    subst hH
    refine ⟨by simp [Host.whole], hostWF_whole hn1, ?_, ?_⟩
    · rw [hdh]; reg_omega
    · rwa [hC.2.1, hpoly, hQn, ← hC.2.2.1]
  have s1 : c.nmem (d1 + 1) < P.n := by rw [d1a.2.2.1]; omega
  have s2 : c.nmem (d2 + 1) < P.n := by rw [d2a.2.2.1]; omega
  have sT : c.nmem (TD + 1) < P.n := by rw [hTD.2.2.1, jOf_whole_s]; omega
  refine ⟨hG, hWh, hX, hcap, by rw [h7], h56, ⟨?_, ?_, ?_, fun H hH => ?_⟩,
    Host.whole P.n, J, N1, N2, ⟨?_, ?_, ?_⟩, by rw [show J.P = Qof P from hwP]; exact hQ,
    sharedGeneric_q hG hwP (by show C1.s + C1.m + C2.m + 1 ≤ P.n; omega),
    by simpa only [Merge.Junction.leftModel, hl] using hOk C1 d1P,
    by simpa only [Merge.Junction.rightModel, hr] using hOk C2 d2P, hOk _ hwP,
    by rw [h7]; exact (fullDegSpec P hG.1 hG.2).1 _ hwP, by rwa [r3],
    by rwa [r4], ⟨γ1, hγ1, by simpa only [Merge.Junction.leftModel, hl, h7] using hc1⟩,
    ⟨γ2, hγ2, by simpa only [Merge.Junction.rightModel, hr, h7] using hc2⟩⟩
  · rw [r0]; exact wf d1 d1A d1h s1
  · rw [r1]; exact wf d2 d2A d2h s2
  · rw [r2]; exact wf TD hTDA hTDm sT
  · rw [r2, hTDm] at hH
    rw [hostAt_unique hH hHA]; exact hostRegular_whole hn1
  · rwa [r0, hl]
  · rwa [r1, hr]
  · rwa [r2]

end

end Chazelle.Core.L41
