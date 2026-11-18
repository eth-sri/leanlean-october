module

public import Chazelle.Core.DownPhaseDrvPDrop
public import Chazelle.Core.DownPhaseMathLevel
public import Chazelle.Core.GranArcs

/-!
# Down-phase pieces (D4), part 7: the mathematics of the normal form of a piece

* `twin_leaf`: a leaf of the host (its points are the vertices `v_a … v_{a+m}` of `Q`) is a box
  twin (`BoxT.Twin`) of the chain `⟨Q, a, m⟩`;
* `leaf_list`: the wall-filtered chord triples of a canonical normal form of `⟨Q, a, m⟩` are a
  valid chord list of the leaf, of degree `≤ 4` and `2γ'`-semigranular (`BoxT.boxTransport_nf`);
* `conn_list`: the empty list for a connector (`2m ≤ γ`: the weight of the only region);
* `canonical_cap`: a canonical normal form of cap `4` is canonical of any cap `D ≥ 4`;
* `chain_eq`: a chain is determined by its polygon, start and length.
-/

namespace Chazelle.Core

namespace DrvP

@[expose] public section

open Set
open BuildRegions (famOf)

theorem chain_eq {C C' : Chain} (hP : C.P = C'.P) (hs : C.s = C'.s) (hm : C.m = C'.m) :
    C = C' := by
  cases C; cases C'; simp only at hP hs hm; subst hP hs hm; rfl

/-- **A leaf is a box twin** of the chain of `Q` over the same vertices. -/
theorem twin_leaf {P : Polygon} {H : Host} {CQ CH : Chain} {a : ℕ} (hQ : CQ.P = Qof P)
    (hsQ : CQ.s = a) (hm : CQ.m = CH.m) (hCH : CH.P = H.poly (Qof P))
    (hsm : CH.s + CH.m < (H.pts P.n).length) (han : a + CH.m < P.n)
    (hpt : ∀ k, k ≤ CH.m → pt H P.n (CH.s + k) = .vtx (a + k)) : BoxT.Twin CQ CH := by
  refine ⟨hm, fun k hk => ?_⟩
  rw [hchain_vertex_lt hCH (by omega), hpt k (by omega)]
  show CQ.P.vtx ((CQ.s + k) % CQ.P.n) = _
  rw [hQ, hsQ, qof_n, Nat.mod_eq_of_lt (by omega)]
  rfl

/-- **The transported list of a leaf.** -/
theorem leaf_list {P : Polygon} {CQ CH : Chain} {N₀ : NF} {γ' : ℕ} (hG : GoodEnv P)
    (hQ : CQ.P = Qof P) (hT : BoxT.Twin CQ CH) (hP' : CH.P.Simple)
    (hN₀ : IsCanonicalNF (chainModel CQ) (Qof P) N₀ γ' 4) :
    ChordTriplesOK (chainModel CH) (Qof P) (BoxT.dropWalls (DrvT.triplesOf N₀)) ∧
      (chainModel CH).DegLe
        (famOf (chainModel CH) (Qof P) (BoxT.dropWalls (DrvT.triplesOf N₀))) 4 ∧
      (chainModel CH).Semigranular
        (famOf (chainModel CH) (Qof P) (BoxT.dropWalls (DrvT.triplesOf N₀))) (2 * γ') := by
  have hP : CQ.P.Simple := by rw [hQ]; exact (shearInvariance (epsOf P) P).1 hG.1
  obtain ⟨hNF, hdeg, hgran, -⟩ := hN₀
  exact BoxT.boxTransport_nf hT hP hP' hNF hdeg hgran.semigranular

/-- **The empty list of a connector.** -/
theorem conn_list {P : Polygon} {CH : Chain} {γ : ℕ} (hP' : CH.P.Simple) (h2m : 2 * CH.m ≤ γ) :
    ChordTriplesOK (chainModel CH) (Qof P) [] ∧
      (chainModel CH).DegLe (famOf (chainModel CH) (Qof P) []) 4 ∧
      (chainModel CH).Semigranular (famOf (chainModel CH) (Qof P) []) γ := by
  have he : famOf (chainModel CH) (Qof P) [] = ∅ := by
    ext c; simp [famOf]
  have hM := walkAx_chainModel hP'
  refine ⟨⟨⟨?_, ?_, ?_⟩, by simp, by simp, by simp⟩, ?_, ?_⟩
  · have : {c | ∃ x ∈ ([] : List (ℕ × ℕ × ℕ)), c = (recOf x).toSet (chainModel CH) (Qof P)} =
        (∅ : Set (Set Point)) := by ext c; simp
    rw [this]; exact finite_empty
  · intro c hc; simp at hc
  · intro c hc; simp at hc
  · rw [he]; intro U _
    unfold Model.deg
    simp
  · rw [he]; intro U hU
    rw [Gran.weight_empty hM hU, DownMath.chainModel_size]
    exact h2m

theorem isDecomp_mono {N : NF} {d d' : ℕ} (h : IsDecomp N d) (hd : d ≤ d') : IsDecomp N d' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun x hx => ?_, h8, h9, h10⟩
  obtain ⟨j, hj, e⟩ := h7 x hx
  exact ⟨j, hj.trans hd, e⟩

/-- **A canonical normal form of cap `4` has every cap `D ≥ 4`.** -/
theorem canonical_cap {M : Model} {Q : Polygon} {N : NF} {γ D : ℕ}
    (h : IsCanonicalNF M Q N γ 4) (hD : 4 ≤ D) : IsCanonicalNF M Q N γ D := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, Model.DegLe.mono M h2 hD, h3, isDecomp_mono h4 ?_⟩
  unfold decDepth
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hD) 1

theorem semigranular_mono {M : Model} {F : Set (Set Point)} {γ γ' : ℕ} (h : M.Semigranular F γ)
    (hγ : γ ≤ γ') : M.Semigranular F γ' := fun U hU => (h U hU).trans hγ

end

end DrvP

end Chazelle.Core
