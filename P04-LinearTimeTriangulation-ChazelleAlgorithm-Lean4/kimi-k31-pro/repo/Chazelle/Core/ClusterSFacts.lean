module

public import Chazelle.Core.ClusterStageD5
public import Chazelle.Core.ClusterStageC4
public import Chazelle.Core.ClusterStageB2S
public import Chazelle.Rwx
set_option maxHeartbeats 4000000

/-!
# WP-I, part 60: the static facts of the split driver

* `ssOf g`: the static layout of the split step in the slots of `g`;
* `ssOf_lay`: the layout is valid;
* `sfacts_of`: the facts of stages A, B, C give the `SFacts` of the driver, with the slab width
  `k'` and the shift `cs` of the level tables.
-/

namespace Chazelle.Core.Cluster

open Machine Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The layout of the split step. -/
def ssOf (g : GV) : SS where
  bACT := g.base 43
  bFIRST := g.base 0
  bFPRE := g.base 29
  bPOW := g.base 40
  bFSZ := g.base 28
  bUP := g.A0 + 54 * g.U + g.L * g.U
  L := g.L
  N := g.N
  bLEV := g.base 3
  bUPT := g.A0 + 54 * g.U
  bPV := g.base 6
  bPOS := g.base 44
  bDF := g.base 48
  μ := g.μ
  bSO := g.base 11
  bSF := g.base 17
  bFPAR := g.base 26
  bTMP := g.base 45
  bHALF := g.base 39
  bLBOT := g.base 37
  bLTOP := g.base 38
  bVERT := g.bV
  bOPP := g.bO
  bATT := g.base 9
  bFP := g.base 7
  s := g.s
  bSTK := g.base 46

theorem ssOf_lay {g : GV} {W : ℕ} (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) : (ssOf g).Lay g.A0 g.U W := by
  have hU := g.U_ge; have hLU := g.L_le_U
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, by show g.μ + 3 ≤ g.U; omega, by show g.N + 1 ≤ g.U; omega, hLU,
    by show g.μ ≤ g.N + 1; omega, hV, hO, hW⟩

/-- The first dart of each vertex, read from slot 0. -/
def firstOf (g : GV) (m : ℕ → ℕ) (h : ∀ u, u < g.μ → m (g.base 0 + u) < g.N) :
    Fin g.μ → Fin g.N := fun v => ⟨m (g.base 0 + v), h v v.2⟩

/-- The window of a slab from the level tables. -/
theorem lv_win {k cs l l' : ℕ} (hk : 0 < k) (h : (l' + cs) / k = (l + cs) / k) :
    l - (l + cs) % k ≤ l' ∧ l' ≤ l + (k - 1) - (l + cs) % k := by
  have h1 := Nat.div_add_mod (l + cs) k; have h2 := Nat.mod_lt (l + cs) hk
  have h3 := Nat.div_add_mod (l' + cs) k; have h4 := Nat.mod_lt (l' + cs) hk
  rw [h] at h3
  generalize k * ((l + cs) / k) = q at h1 h3
  omega

variable {W : ℕ}

/-- **The static facts.** -/
theorem sfacts_of {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face (a f) = f} {C : CoTree (starTree T a ha)} {R : BTree} {preE slot : ℕ → ℕ}
    {m : ℕ → ℕ} (hA : AF g M T m) (hB1 : B1F g M T a ha m) (hB2 : B2F g C R preE slot m)
    (hpl : M.Planar) (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0)
    (hW : g.END ≤ W) (hL : 0 < g.L)
    (hhalf : ∀ w, w ≤ g.μ → m (g.base 39 + w) = w / 2)
    (hpow : ∀ j, j < g.L → m (g.base 40 + j) = 2 ^ j)
    (hk : 0 < g.k') {cs : ℕ} (hlv : ∀ l, l < g.μ → LvOK g m cs l) :
    SFacts M T a ha C R (firstOf g m hA.first_lt) preE slot (upTf T) g.k' cs (ssOf g) g.A0 g.U W
      m := by
  have hU := g.U_ge
  have hP := g.two_pow_L; have hPU := g.P_le_U
  refine ⟨ssOf_lay hμN hO hV hW, rfl, rfl, hpl, fun v => ?_, fun d => (hA.map d).2.2,
    fun d => (hA.map d).1, fun v => rfl, hA.lev, hA.lev_lt, hB1.att, hB1.fp, fun x => ?_,
    fun x => ?_, hB2.fpar, hB2.fpar_lt, hB2.r0, hB2.pre, hB2.sz, hB2.R_ok, hB2.R_n, hB2.R_up,
    hB2.R_root, hB2.R_pre, hB2.up_tab, fun v => ?_, fun x hx => upTf_lt T hx, fun x hx => ?_,
    hA.upt, hpow, by show g.N + g.μ < 2 ^ g.L; omega, hPU, hL, hhalf, fun v x hvx => ?_,
    fun v => ?_⟩
  · apply Fin.ext
    have h1 := (hA.map (firstOf g m hA.first_lt v)).2.2
    have h2 := hA.first_v v v.2
    simp [firstOf] at h1 ⊢
    rwx [← h1]
  · rcases x with d | d | d
    · show m (g.base 11 + d) = (M.opp d : ℕ)
      exact (hB1.so d).1
    · show m (g.base 11 + (g.N + d)) = 2 * g.N + d
      rw [← Nat.add_assoc]; exact (hB1.so d).2.1
    · show m (g.base 11 + (2 * g.N + d)) = g.N + d
      rw [← Nat.add_assoc]; exact (hB1.so d).2.2
  · rcases x with d | d | d
    · show m (g.base 17 + d) = (d : ℕ)
      exact (hB1.sf d).1
    · show m (g.base 17 + (g.N + d)) = (d : ℕ)
      rw [← Nat.add_assoc]; exact (hB1.sf d).2.1
    · show m (g.base 17 + (2 * g.N + d)) = ((M.fperm⁻¹ d : Fin g.N) : ℕ)
      rw [← Nat.add_assoc]; exact (hB1.sf d).2.2
  · unfold upTf; rw [dite_eq_left v.2]
  · have := hA.pv ⟨x, hx⟩; simp at this
    show m (g.base 6 + x) = upTf T x
    unfold upTf; rwx [dite_eq_left hx]
  · have hlvv := hlv _ (hA.lev_lt v)
    obtain ⟨hb, ht, -, -⟩ := hlvv
    simp [slabN, dite_eq_left v.2, dite_eq_left x.2] at hvx
    show m (g.base 37 + T.level v) ≤ T.level x ∧ T.level x ≤ m (g.base 38 + T.level v)
    rw [hb, ht]; exact lv_win hk hvx
  · have hlvv := hlv _ (hA.lev_lt v)
    obtain ⟨hb, ht, -, -⟩ := hlvv
    show m (g.base 38 + T.level v) + 1 - m (g.base 37 + T.level v) ≤ g.k'
    rw [hb, ht]
    have := Nat.mod_lt (T.level v + cs) hk
    omega

end

end Chazelle.Core.Cluster
