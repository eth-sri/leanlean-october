module

public import Chazelle.Core.SweepChain

/-!
# The sweep (WP-D), part 9: chain brackets (events in unlabelled regions)

A region `G` of `F₂⁺` without a label (`∀ V, ¬ RLabel J S₂ G V`) that lies on the side `ρ` of a
fused chord `e ⊆ c ∈ S₂` attached in the right stretch is the middle region of a *chain*: the
collinear chords of `F₂⁺` through ties at `C₂` vertices, all with `G` on their side `ρ` and all
contained in chords of `S₂` with the same region `V` of `S₂` on their side `ρ` (`local_step`).
The chain leaves the right stretch at its two ends `Z₂`, `Z₁`, and it acts as a *bracket*: the
positions of the `C₁` part faced by `G` lie between `Z₂` and `Z₁`, and no chord of `F₂⁺` with an
attachment in `[0, L]` (offsets from the base of the right stretch) is attached strictly between
them, except at the shared vertex.  So the first such cut after a position faced by `G` is the
end `Z₁` of the chain, made by a chord whose chord of `S₂` has `V` on the side of `G`: the sweep
finds it among the pieces of the exit chords of its label `V`.

* `side_arc`: walk order in offsets (`sideInArc_rev_iff_off`, `no_cross_off` are in
  `SweepLabelGap`).
* `chain_gen`: the walk along a chain with an invariant propagated across ties.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace Sweep

section
variable {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
include hM hF
/-- **The side of a chord confines the positions facing it** (the core of `chord_bound`): if `G`
is on the side `ρ` of `f`, attached at `N` and `Fr`, with orientation `θ`, then no position
facing `G` lies in the cyclic interval from `Fr` to `N` (`θ = 1`) or from `N` to `Fr`
(`θ = -1`). -/
theorem side_arc
    {f : Set Point} (hf : f ∈ F) {pn pf : ℕ} {tn tf : ℝ} (hN : SideAttach M.W f pn tn)
    (hFr : SideAttach M.W f pf tf) (hNF : sidePt M.W pn tn ≠ sidePt M.W pf tf) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ M.regions F) (hS : SideOf M ρ f G)
    {θ : ℝ} (hori : 0 < θ * ρ * ((sidePt M.W pn tn).1 - (sidePt M.W pf tf).1)) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hfG : M.Faces p t G) :
    (θ = 1 → ¬ sideInArc (pf + tf) (pn + tn) (p + t)) ∧
      (θ = -1 → ¬ sideInArc (pn + tn) (pf + tf) (p + t)) := by
  obtain ⟨hfseg, hy, hopen, -, -⟩ := hM.attach_seg (hF hf) hN hFr hNF
  have hmid : lerp (sidePt M.W pn tn) (sidePt M.W pf tf) (1 / 2) ∈ f := by
    rw [hfseg]; exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)
  have hmidD := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  have hsym : lerp (sidePt M.W pf tf) (sidePt M.W pn tn) (1 / 2) =
      lerp (sidePt M.W pn tn) (sidePt M.W pf tf) (1 / 2) := by
    grind [Geometry.lerp]
  constructor
  · intro hθ1
    subst hθ1
    have hleft := left_of_side hρ hS (a := sidePt M.W pf tf) (b := sidePt M.W pn tn) hy.symm
      (by grind) (by grind) (by linarith)
    exact fun hin => hM.not_left_of_after hF hf hFr hN (Ne.symm hNF) hG hp ht hin hfG hleft
  · intro hθ1
    subst hθ1
    have hleft := left_of_side hρ hS (a := sidePt M.W pn tn) (b := sidePt M.W pf tf) hy hmid
      hmidD (by linarith)
    exact fun hin => hM.not_left_of_after hF hf hN hFr hNF hG hp ht hin hfG hleft

/-- **A third chord at a tie** is one of the two chords of the tie. -/
theorem tie_third
    {c c' e : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) (he : e ∈ F) (hne : c ≠ c') {p : ℕ}
    {t : ℝ} (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p t)
    (hE : SideAttach M.W e p t) : e = c ∨ e = c' := by
  rcases hM.tie_pair hF hc hc' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨-, -, h⟩ := hM.tie_shape hF hc hc' hA hA' h1 h2
    simp_all
  · obtain ⟨-, -, h⟩ := hM.tie_shape hF hc' hc hA' hA h2 h1
    grind


end

/-- A key of a chord is one of two given keys of it with distinct points. -/
theorem key_of_two {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {pa pb p : ℕ} {ta tb t : ℝ} (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (hP : SideAttach M.W c p t) :
    (p = pa ∧ t = ta) ∨ (p = pb ∧ t = tb) := by
  obtain ⟨hseg, -, hopen, -, -⟩ := hM.attach_seg hc hA hB hAB
  rw [hseg] at hP
  have hP' := hP
  rw [← hseg] at hP'
  rcases hM.attach_endpoint hopen hP with h | h
  · exact Or.inl (hM.attach_unique hc hP' hA h)
  · exact Or.inr (hM.attach_unique hc hP' hB h)

/-! ## Walking along a chain with an invariant -/

section ChainWalk

variable (J : Merge.Junction)

section
variable (S₂ : Set (Set Point))
include S₂
/-- **An invariant propagated across ties** of the right stretch: if `Φ` holds for a chord `f`
at its near attachment, and `f'` is the other chord of the tie at the far attachment of `f`
(both in the right stretch), then `Φ` holds for `f'` at that attachment. -/
def Propag (Φ : Set Point → ℝ → Prop) : Prop :=
  ∀ (f f' : Set Point) (pn : ℕ) (tn : ℝ) (pf pb : ℕ) (tb : ℝ), f ∈ F₂plus J S₂ →
    f' ∈ F₂plus J S₂ → f' ≠ f → SideAttach (chainModel J.whole).W f pn tn →
    SideAttach (chainModel J.whole).W f pf 0 →
    sidePt (chainModel J.whole).W pn tn ≠ sidePt (chainModel J.whole).W pf 0 →
    SideAttach (chainModel J.whole).W f' pf 0 → SideAttach (chainModel J.whole).W f' pb tb →
    sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W pf 0 →
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn) <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + 0) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + 0) <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    Φ f (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pn + tn)) →
    Φ f' (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pf + 0))

/-! ## The two invariants -/

/-- **The forward invariant**: chords of `F₂⁺` (other than `f`) with an attachment beyond `lo`
and one inside the right stretch have the latter before `o`. -/
def PhiI (lo : ℝ) (f : Set Point) (o : ℝ) : Prop :=
  ∀ e ∈ F₂plus J S₂, e ≠ f → ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
    SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
    sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
    lo < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) < o

/-- **The backward invariant**: chords of `F₂⁺` (other than `f`) with an attachment in the `C₁`
part and one inside the right stretch before `o` have the latter before `oA` (weakly). -/
def PhiK (oA : ℝ) (f : Set Point) (o : ℝ) : Prop :=
  ∀ e ∈ F₂plus J S₂, e ≠ f → ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
    SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
    sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
    ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pw + tw) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ≤ o →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pb + tb) ≤ oA

/-! ## The ends of a chain -/


end

section
variable (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) {h : Set Point} (hh : h ∈ F₂plus J S₂) {ph pz : ℕ} {th tz : ℝ} (hPa : SideAttach (chainModel J.whole).W h ph th) (hZa : SideAttach (chainModel J.whole).W h pz tz) (hne : sidePt (chainModel J.whole).W ph th ≠ sidePt (chainModel J.whole).W pz tz) (hS : SideOf (chainModel J.whole) ρ h G)
include hP Q hS₂ hρ hG h hh hPa hZa hne hS
/-- **The backward end** of a chain (orientation `-1`) lies in the `C₁` part before every
non-cut position facing `G` there. -/
theorem back_end
    (hori : 0 < -1 * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1))
    (hPL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hZout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    ((rL1 J + rL2 J : ℕ) : ℝ) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  have hsa := (side_arc hC.hM hC.hF hh hPa hZa hne hρ hG hS hori hp₀ ht₀ hfG₀).2 rfl
  obtain ⟨kP0, kP1⟩ := Corr.key_mem hPa.1 hPa.2.1 hPa.2.2.1
  obtain ⟨kZ0, kZ1⟩ := Corr.key_mem hZa.1 hZa.2.1 hZa.2.2.1
  obtain ⟨kx0, kx1⟩ := Corr.key_mem hp₀ ht₀.1.le ht₀.2
  have hZ0 := off_nonneg kZ0 hgn
  have hP0 := off_nonneg kP0 hgn
  have hLZ : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) := by
    by_contra hlt
    push Not at hlt
    rcases hZ0.lt_or_eq with hpos | hzero
    · grind
    · apply hsa
      rcases hP0.lt_or_eq with hP0' | hP0'
      · exact (sideInArc_rev_iff_off hg0 hgn kZ0 kZ1 kP0 kP1 kx0 kx1 (by linarith)).2
          (Or.inr (by linarith))
      · exfalso
        have hk := off_inj hg0 hgn kP0 kP1 kZ0 kZ1 (by linarith)
        exact hne (by obtain ⟨rfl, rfl⟩ := sideKey_inj hPa.2.1 hPa.2.2.1 hZa.2.1 hZa.2.2.1 hk; rfl)
  refine ⟨hLZ, ?_⟩
  have hPZ : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) := by linarith
  have hle : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) := by
    by_contra hc
    push Not at hc
    exact hsa ((sideInArc_iff_off hg0 hgn kP0 kP1 kZ0 kZ1 kx0 kx1 hPZ).2 ⟨by linarith, hc⟩)
  rcases hle.lt_or_eq with hq | hq
  · exact hq
  · exact absurd ⟨h, hh, pz, tz, hZa, (off_inj hg0 hgn kZ0 kZ1 kx0 kx1 hq).symm⟩ hnc₀

/-- **The forward end** of a chain (orientation `1`) is the shared vertex copy at offset `0`, or
lies in the `C₁` part after every non-cut position facing `G` there. -/
theorem fwd_end
    (hori : 0 < 1 * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1))
    (hPL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th) <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hZout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p₀ + t₀))
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (_ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀)) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz)) := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  have hsa := (side_arc hC.hM hC.hF hh hPa hZa hne hρ hG hS hori hp₀ ht₀ hfG₀).1 rfl
  obtain ⟨kP0, kP1⟩ := Corr.key_mem hPa.1 hPa.2.1 hPa.2.2.1
  obtain ⟨kZ0, kZ1⟩ := Corr.key_mem hZa.1 hZa.2.1 hZa.2.2.1
  obtain ⟨kx0, kx1⟩ := Corr.key_mem hp₀ ht₀.1.le ht₀.2
  have hZ0 := off_nonneg kZ0 hgn
  rcases hZ0.lt_or_eq with hpos | hzero
  · right
    have hLZ : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) := by
      grind
    refine ⟨hLZ, ?_⟩
    have hPZ : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (ph + th) <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) := by linarith
    have hle : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p₀ + t₀) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (pz + tz) := by
      by_contra hc
      push Not at hc
      exact hsa ((sideInArc_rev_iff_off hg0 hgn kP0 kP1 kZ0 kZ1 kx0 kx1 hPZ).2 (Or.inr hc))
    rcases hle.lt_or_eq with hq | hq
    · exact hq
    · exact absurd ⟨h, hh, pz, tz, hZa, off_inj hg0 hgn kx0 kx1 kZ0 kZ1 hq⟩ hnc₀
  grind


end

end ChainWalk

end Sweep

end

end Chazelle.Core
