module

public import Chazelle.Core.OraclePrepPhB
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# Lemma 3.6 (WP-H), preprocessing part 30: descriptors and tables in memory

Memory facts of the preprocessing that survive changes above a bound: chain descriptors and their
copies (the model descriptor), the well-formedness of a copied descriptor, the locator facts of the
zipper (`zloc`), the region table of the star chords (`rgMem_of`), and addresses of robust layouts.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- A word reached through a robustly determined address lies below the bound. -/
theorem robust_addrF {E : ℕ} {m : ℕ → ℕ} {f : (ℕ → ℕ) → ℕ} {v : ℕ}
    (hf : ∀ m', (∀ a, a < E → m' a = m a) → f m' = f m)
    (h : Robust E m fun m' => m' (f m') = v) : f m < E := by
  by_contra hge
  have hm' : ∀ a, a < E → Function.update m (f m) (v + 1) a = m a := fun a ha => by
    rw [Function.update_of_ne (by omega)]
  have := h _ hm'
  dsimp at this
  rw [hf _ hm', Function.update_self] at this
  omega

/-- A host layout depends only on the memory below its end. -/
theorem hostAt_agree {m m' : ℕ → ℕ} {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  refine ⟨by rw [hm _ (by omega)]; exact h.1, fun i hi => ?_⟩
  have hh := h.2 i hi
  have e1 := hm (B + 1 + 3 * i) (by omega)
  have e2 := hm (B + 2 + 3 * i) (by omega)
  have e3 := hm (B + 3 + 3 * i) (by omega)
  generalize H.getD i (.run 0 0) = it at hh ⊢
  cases it with
  | run a l => obtain ⟨h1, h2, h3⟩ := hh; exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
  | pt x =>
    cases x with
    | vtx j => obtain ⟨h1, h2⟩ := hh; exact ⟨e1.trans h1, e2.trans h2⟩
    | onEdge e hh' => obtain ⟨h1, h2, h3⟩ := hh; exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩

/-- A chain descriptor depends only on the memory below its end. -/
theorem chainDescAt_agree {m m' : ℕ → ℕ} {D X : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (h : ChainDescAt m D Q H C) (hD : D + 5 ≤ X) (hH : m D + 3 * H.length + 4 ≤ X)
    (hm : ∀ a, a < X → m' a = m a) : ChainDescAt m' D Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h1, by rwx [hm _ (by omega)], by rwx [hm _ (by omega)],
    by rwx [hm _ (by omega)], by rwx [hm _ (by omega)]⟩
  rw [hm _ (by omega)]
  exact hostAt_agree h0 hH hm

/-- A copy of a chain descriptor describes the same chain. -/
theorem chainDescAt_copy {m : ℕ → ℕ} {D D' : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (h : ChainDescAt m D Q H C) (hc : ∀ i, i < 5 → m (D' + i) = m (D + i)) :
    ChainDescAt m D' Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have e0 := hc 0 (by omega); have e1 := hc 1 (by omega); have e2 := hc 2 (by omega)
  have e3 := hc 3 (by omega); have e4 := hc 4 (by omega)
  simp [Nat.add_zero] at e0
  exact ⟨by rwx [e0], h1, by rwx [e1], by rwx [e2], by rwx [e3],
    by rwx [e4]⟩

/-- A well-formed chain descriptor stays well formed under a change above the bound. -/
theorem chainWF_agree {P : Polygon} {m m' : ℕ → ℕ} {D X : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P X m D) (hD : ChainDescAt m D (Qof P) H C)
    (hm : ∀ a, a < X → m' a = m a) : ChainWF P X m' D := by
  obtain ⟨hDX, hall⟩ := hwf
  obtain ⟨h1, h2, h3, h4⟩ := hall H C hD
  refine ⟨hDX, fun H' C' hC' => ?_⟩
  have hD' := chainDescAt_agree hD hDX h3 hm
  have hH  := NFLoc.hostAt_unique hC'.1 hD'.1
  have hC  := NFLoc.chain_eq_of_desc hC' hD'
  subst hH hC
  rw [hm _ (by omega)]
  exact ⟨h1, h2, h3, h4⟩

/-- **The model descriptor** made of `0` and a copy of a well-formed chain descriptor. -/
theorem modelDesc_of {P : Polygon} {m : ℕ → ℕ} {D MD X : ℕ} {H : Host} {C : Chain}
    (hD : ChainDescAt m D (Qof P) H C) (hwf : ChainWF P X m D) (h0 : m MD = 0)
    (hc : ∀ i, i < 5 → m (MD + 1 + i) = m (D + i)) (hMX : MD + 6 ≤ X) :
    ModelDescAt m MD (Qof P) (chainModel C) ∧ ModelDescWF P X m MD := by
  have hD'  := chainDescAt_copy hD hc
  refine ⟨Or.inl ⟨h0, H, C, hD', rfl⟩, hMX, fun _ => ⟨by omega, fun H' C' hC' => ?_⟩⟩
  have hH  := NFLoc.hostAt_unique hC'.1 hD'.1
  have hC  := NFLoc.chain_eq_of_desc hC' hD'
  subst hH hC
  have e0 : m (MD + 1) = m D := by have := hc 0 (by omega); simpa using this
  obtain ⟨h1, h2, h3, h4⟩ := hwf.2 H' C' hD
  exact ⟨h1, h2, by rwx [e0], h4⟩

/-- The region table of the star chords from the normal form. -/
theorem rgMem_of {m : ℕ → ℕ} {B : ℕ} {M : Model} {Q : Polygon} {N : NF} (hNF : NFAt m B N)
    (hN : IsNF M Q N) :
    RgMem m (m (B + 4)) (m (B + 6)) N.arcs.length (fun p => N.seq.getD p 0)
      (fun j => (N.arc j).reg) :=
  ⟨fun p hp => hNF.2.2.2.2.2.2.2.2.1 p (by rwx [NFLoc.seq_length hN]),
    fun p hp => NFLoc.seq_lt hN hp, fun j hj => (hNF.2.2.2.2.2.2.1 j hj).1⟩

/-- **The locator facts of the zipper** from the descriptors and tables of phase A. -/
theorem zloc_of {P : Polygon} {W : ℕ} {m₀ m : ℕ → ℕ} {D NB MD TB L A₀ X : ℕ} {H : Host}
    {C : Chain} {N : NF} {V : QV} (hHW : hostWords P.n ≤ W) (hsimp : C.P.Simple)
    (hD : ChainDescAt m₀ D (Qof P) H C) (hwf : ChainWF P A₀ m₀ D)
    (hNFw : NFWithin m₀ NB A₀ N) (hN : IsNF (chainModel C) (Qof P) N)
    (hagree : ∀ a, a < A₀ → m a = m₀ a) (hmd0 : m MD = 0)
    (hmdc : ∀ i, i < 5 → m (MD + 1 + i) = m₀ (D + i)) (hA₀MD : A₀ ≤ MD) (hMD6 : MD + 6 ≤ TB)
    (htab : ∀ j, j < L → m (TB + j) = 2 ^ j) (hAlt : N.arcs.length < 2 ^ L)
    (hTBX : TB + L ≤ X) (hXW : X ≤ W)
    (hVMD : V.MD = MD) (hVNB : V.NB = NB) (hVTB : V.TB = TB) (hVL : V.L = L)
    (hVA : V.A = N.arcs.length) (hVAB : V.AB = m₀ (NB + 4)) (hVSB : V.SB = m₀ (NB + 6))
    (hVμ : N.arcs.length ≤ V.μ) :
    Robust X m fun m' => LocMemOK P V m' W (chainModel C) N ∧ m' (V.NB + 4) = V.AB ∧
      m' (V.NB + 6) = V.SB := by
  intro m' hm'
  have hQn : (Qof P).n = P.n := shear_n _ _
  have agree0 : ∀ a, a < A₀ → m' a = m₀ a := fun a ha => by
    rw [hm' a (by omega), hagree a ha]
  have hA0 := OracleR.arcs_pos hsimp hN
  obtain ⟨hNB7, hABb, hSBb⟩ := NFLoc.nfWithin_bounds hNFw hN hA0
  have hNF'  := hNFw m' agree0
  obtain ⟨hDA, hall⟩ := hwf
  obtain ⟨h1, h2, h3, h4⟩ := hall H C hD
  have hD'  := chainDescAt_agree hD hDA h3 agree0
  have hwf' : ChainWF P X m' D :=
    ChainWF.mono (chainWF_agree ⟨hDA, hall⟩ hD agree0) (by omega)
  obtain ⟨hmd, hmdwf⟩ := modelDesc_of (m := m') (MD := MD) hD' hwf'
    (by rw [hm' _ (by omega), hmd0])
    (fun i hi => by rw [hm' _ (by omega), hmdc i hi, agree0 _ (by omega)]) (by omega)
  obtain ⟨hMDW, hlwf⟩ := NFLoc.locChainWF_of hmdwf hXW hHW
  have e4 : m' (NB + 4) = m₀ (NB + 4) := agree0 _ (by omega)
  have e6 : m' (NB + 6) = m₀ (NB + 6) := agree0 _ (by omega)
  refine ⟨⟨by rwx [hVMD], Or.inl ⟨C, hsimp, rfl⟩, by rwx [hVMD],
    by rwx [hVMD], by rwx [hVNB], hN, hVA, fun j hj => ?_,
    fun j hj => by rw [hVTB, hm' _ (by omega)]; rw [hVL] at hj; exact htab j hj,
    by rwx [hVA, hVL], by rwo [hVNB, hVTB],
    by rwo [hVNB, hVTB, hVA, e4], by rwo [hVNB, hVTB, hVA, e6],
    by rwo [hVTB, hVL], by rw [hVA]; exact hVμ⟩, by rw [hVNB, hVAB, e4],
    by rw [hVNB, hVSB, e6]⟩
  obtain ⟨-, -, -, reg, -, -, -, -, -, -, hpp⟩ := hN
  have := (hpp j hj).1
  rwa [hQn] at this

end

end OracleR

end Chazelle.Core
