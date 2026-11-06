module

public import Chazelle.Core.RestoreTRead
public import Chazelle.Core.RestoreTValidMath

/-!
# WP-E, the candidate test on the RAM, part 8: the model operations

The candidate test runs in a chain model (`OkModel`) or in the interior model of `Q` (finding
E7-B).  The few operations that depend on the model are specified here by contracts under the run
invariant, so that the test itself is written once:

* `KeyOK kc K`: `kc a b d e` compares the keys of the positions `(a, b)` and `(d, e)` of band
  `bRestore` (bits in `50210`, `50211`);
* `LeftOK ls K`: `ls` decides whether the direction points into the left sector of the walk at
  the candidate (bit in `50210`);
* `TurnOK tn tp K`: `tn`, `tp` decide the signs of the turns from the next walk edge and to the
  previous one at the candidate vertex (`50210 = 1` iff positive; `tp` at a vertex candidate).

The positions compared (`PosG`) are on the walk proper and are not box vertices of a chain model
(`offCmp` excludes those).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- **A position the tests compare**: on the walk proper, not a box vertex of a chain model. -/
def PosG (M : Model) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  x.edge < M.W.n ∧ ProperPos M Q n x ∧ ∀ C : Chain, M = chainModel C → x.hgt = 0 → 6 ≤ x.edge

/-- The candidate position of a run started in `c₀`. -/
def xOf (c₀ : Config) : WPos := ⟨c₀.nreg 83005, c₀.nreg 83006⟩

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ : Config}

/-- The chain of a chain model of the run is simple. -/
theorem TGood.chain_simple (hE : TGood P W M N c₀) {C : Chain} (hM : M = chainModel C) :
    ∃ C' : Chain, C'.P.Simple ∧ M = chainModel C' := by
  rcases hE.hkind with ⟨H, C', -, -, -, hs, hM'⟩ | hI
  · exact ⟨C', hs, hM'⟩
  · exact absurd (hM.symm.trans hI) (chainModel_ne_interior C (Qof P))

/-- **The candidate is a position the tests compare.** -/
theorem TGood.xPosG (hE : TGood P W M N c₀) : PosG M (Qof P) P.n (xOf c₀) := by
  refine ⟨hE.hxe, hE.hxp, fun C hM => ?_⟩
  have hy : |(M.pos (Qof P) (xOf c₀)).2| < C.radius :=
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set (hE.hxC C hM)).2 C.coordBound_lt_radius
  subst hM
  exact (posOK_of hE.hxe hE.hxp hy).2.2

/-- **The ends of the chord records** are positions the tests compare. -/
theorem TGood.chordPosG (hE : TGood P W M N c₀) {i : ℕ} (hi : i < N.nChords) :
    PosG M (Qof P) P.n (N.chord i).lpos ∧ PosG M (Qof P) P.n (N.chord i).rpos := by
  have hp := chord_proper hE.hNF hi
  have hat := hE.hNF.2.2.1 i hi
  refine ⟨⟨hat.1.1, hp.1, fun C hM => ?_⟩, ⟨hat.2.1, hp.2, fun C hM => ?_⟩⟩ <;>
  · obtain ⟨C', hs, hM'⟩ := hE.chain_simple hM
    have hNF := hE.hNF
    rw [hM'] at hNF
    have := chord_posOK hs hNF hi
    first | exact this.1.2.2 | exact this.2.2.2

/-- **The ends of the arc records** of a nonempty family are positions the tests compare. -/
theorem TGood.arcPosG (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) {j : ℕ}
    (hj : j < N.arcs.length) :
    PosG M (Qof P) P.n (N.arc j).s ∧ PosG M (Qof P) P.n (N.arc j).e := by
  have hQ : (Qof P).n = P.n := shear_n _ _
  obtain ⟨hFam, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hE.hNF
  obtain ⟨hs, he⟩ := hpp j hj
  have harc := (harcs.1 j hj).2
  have hn := harc.2.1
  have hn' := harc.2.2.2.1
  have e1 : (N.arc j).s.edge < M.W.n := by
    have : ((N.arc j).s.edge : ℝ) < M.W.n := by
      have := hs.1; unfold Model.key at hn; linarith
    exact_mod_cast this
  have e2 : (N.arc j).e.edge < M.W.n := by
    have : ((N.arc j).e.edge : ℝ) < M.W.n := by
      have := he.1; unfold Model.key at hn'; linarith
    exact_mod_cast this
  refine ⟨⟨e1, by rwa [← hQ], fun C hM => ?_⟩, ⟨e2, by rwa [← hQ], fun C hM => ?_⟩⟩
  all_goals
    obtain ⟨C', hsC, hM'⟩ := hE.chain_simple hM
    have hNF := hE.hNF
    rw [hM'] at hNF hne
    have := arc_posOK hsC hNF hne hj
    first | exact this.1.2.2 | exact this.2.2.2

/-- **Contract of a key comparison.** -/
def KeyOK (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (K : ℕ) : Prop :=
  ∀ a b d e, InR a → InR b → InR d → InR e →
  ∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → PosG M (Qof P) P.n ⟨c.nreg a, c.nreg b⟩ →
    PosG M (Qof P) P.n ⟨c.nreg d, c.nreg e⟩ → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W (kc a b d e) c c' k ∧ k ≤ K ∧
      BitIs c' 50210 (M.key (Qof P) ⟨c.nreg a, c.nreg b⟩ < M.key (Qof P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' 50211 (M.key (Qof P) ⟨c.nreg d, c.nreg e⟩ < M.key (Qof P) ⟨c.nreg a, c.nreg b⟩) ∧
      TStep W c₀ c c' k

/-- **Contract of the sector test** at the candidate. -/
def LeftOK (ls : Stmt) (K : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W ls c c' k ∧ k ≤ K ∧
      BitIs c' 50210 (LeftB M P (xOf c₀) (c₀.nreg 83008)) ∧ TStep W c₀ c c' k

/-- **Contract of the turning tests** at the candidate vertex. -/
def TurnOK (tn tp : Stmt) (K : ℕ) : Prop :=
  (∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W tn c c' k ∧ k ≤ K ∧
      (c'.nreg 50210 = 1 ↔ TurnNB M (xOf c₀) (c₀.nreg 83008)) ∧ TStep W c₀ c c' k) ∧
  (∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → c₀.nreg 83006 = 0 → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W tp c c' k ∧ k ≤ K ∧
      (c'.nreg 50210 = 1 ↔ TurnPB M (xOf c₀) (c₀.nreg 83008)) ∧ TStep W c₀ c c' k)

end

end Restore

end Chazelle.Core
