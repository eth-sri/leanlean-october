module

public import Chazelle.Core.SweepEvStep
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.DownPhaseMathJunc
public import Chazelle.Core.NFLocateHost
public import Chazelle.Core.GranPz
public import Chazelle.RewriteTactics

/-!
# The sweep (WP-D), stage 3: `F₂⁺` is a chord family of `Q`

`F₂plus_chordFamily'`: if the chords of `S₂` are at vertex heights of `Q` and every vertex of `C`
is at a vertex height of `Q`, then `F₂⁺` is a chord family of `Q` in the model of `C` (finite,
admissible, every chord at a vertex height: each chord of `F₂⁺` passes through an end of a chord
of `S₂`, the shared vertex or the top of `C₂`, `f2_cases`).

`whole_vertex_height`: the vertices of a chain with a well-formed descriptor are host points,
at vertex heights of `Qof P`.

**`F₂plus_chordFamily`**: in the environment of the event loop, `F₂⁺` (of the normal form `N₂`)
is a chord family of `Qof P` in the model of `C`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine WalkEmbed Sweep

@[expose] public section

/-- **`F₂⁺` is a chord family** when the vertices of `C` are at vertex heights of `Q`. -/
theorem F₂plus_chordFamily' {J : Merge.Junction} {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hvtx : ∀ k, ∃ h, h < Q.n ∧ (J.whole.vertex k).2 = (Q.vtx h).2) :
    (chainModel J.whole).ChordFamily Q (F₂plus J S₂) := by
  have hS₂a  := hS₂.2.1
  refine ⟨F₂plus_finite J hS₂.1, F₂plus_subset J hS₂a, fun e he => ?_⟩
  -- a point of `e` at a vertex height of `Q`
  obtain ⟨z, hz, h, hh, hzh⟩ : ∃ z ∈ e, ∃ h, h < Q.n ∧ z.2 = (Q.vtx h).2 := by
    rcases f2_cases hS₂a he with ⟨c, hc, a, σ, ha, -, rfl⟩ | ⟨σ, -, -, rfl⟩ | ⟨σ, -, -, rfl⟩
    · refine ⟨a, origin_mem J, ?_⟩
      obtain ⟨h, hh, a', b', hceq⟩ := hS₂.2.2 c hc
      obtain ⟨y, l, r, hH, -, hcy, hl, hr⟩ := Merge.augChords_spec (hS₂a hc)
      have hlr := hH.lt
      have hmem : a ∈ c := by
        rcases ha with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · rw [hl, hcy]; exact ⟨rfl, le_rfl, hlr.le⟩
        · rw [hr, hcy]; exact ⟨rfl, hlr.le, le_rfl⟩
      rw [hceq] at hmem
      exact ⟨h, hh, hmem.1⟩
    · obtain ⟨h, hh, e⟩ := hvtx J.m₁
      exact ⟨J.shared, origin_mem J, h, hh, e⟩
    · obtain ⟨h, hh, e⟩ := hvtx (J.m₁ + J.right.topIdx)
      refine ⟨J.right.top, origin_mem J, h, hh, ?_⟩
      rwr [← e, Merge.Junction.whole_vertex_add]
  obtain ⟨y, l, r, -, -, rfl, -, -⟩ := Merge.augChords_spec (F₂plus_subset J hS₂a he)
  refine ⟨h, hh, l, r, ?_⟩
  rw [show y = (Q.vtx h).2 from hz.1.symm.trans hzh]

/-- **The vertices of a described chain are at vertex heights of `Qof P`.** -/
theorem whole_vertex_height {P : Polygon} (hn3 : 3 ≤ P.n) {E : ℕ} {m : ℕ → ℕ} {B : ℕ} {H : Host}
    {C : Chain} (hwf : ChainWF P E m B) (hC : ChainDescAt m B (Qof P) H C) (k : ℕ) :
    ∃ h, h < (Qof P).n ∧ (C.vertex k).2 = ((Qof P).vtx h).2 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hHwf : HostWF (Qof P).n H := by rw [hQn]; exact (hwf.2 H C hC).2.1
  have hn : 0 < (Qof P).n := by omega
  rw [DownMath.chain_vertex_host hC.2.1 k, Gran.eval_snd]
  refine ⟨_, Gran.hv_lt ?_, rfl⟩
  set L := H.pts (Qof P).n
  by_cases hi : (C.s + k) % L.length < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact NFLoc.hostWF_pts hHwf hn _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hn

/-- **`F₂⁺` is a chord family of `Qof P`** in the environment of the event loop. -/
theorem F₂plus_chordFamily {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction}
    {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) :
    (chainModel J.whole).ChordFamily (Qof P) (F₂plus J (N₂.F (chainModel J.right) (Qof P))) := by
  obtain ⟨-, -, hwf, ⟨H, hC, -⟩, -, -⟩ := E.ctxW
  exact F₂plus_chordFamily' E.hNF₂.1 (whole_vertex_height E.hG.1.1 hwf hC)

end

end SweepEv

end Chazelle.Core
