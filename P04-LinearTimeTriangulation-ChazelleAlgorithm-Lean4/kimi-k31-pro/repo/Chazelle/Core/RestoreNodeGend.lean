module

public import Chazelle.Core.RestoreNodeEndMath
public import Chazelle.Core.RestoreWitness

/-!
# WP-E, the search: a failed end test in offsets

`end_gend`: the test at the host position `E_M` of a node chord end strictly inside the stretch
(offset `d + t`), in the direction of the other end `O`, arrived at `F` and failed `CountOK`.
With `α = off n g kF`: `α ≥ 0`, an `α` in the open stretch is the offset of `O` (arrival), the
good vertex (offset `x`) satisfies `sideInArc (d + t) α x ↔ sE` (prune), and for every integer
offset `u < L` the host-key test `κ(u) ∈ (kE, kF)` is `sideInArc (d + t) α u` (rotation).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (lerp)
open WalkEmbed (off off_nonneg off_lt off_key off_key')

variable {M : Model} {Cα : Chain} {g g' L : ℕ}

/-- Rotation of a host-key interval test at an integer offset of the stretch. -/
theorem rot_u (hS : Stretch M Cα g g' L) {a b : ℝ} (ha0 : 0 ≤ a) (han : a < M.W.n) (hb0 : 0 ≤ b)
    (hbn : b < M.W.n) {u : ℕ} (hu : u < L) :
    sideInArc a b (((g + u) % M.W.n : ℕ) : ℝ) ↔
      sideInArc (off M.W.n g a) (off M.W.n g b) (u : ℝ) := by
  have hn : 0 < M.W.n := by have := hS.hg; omega
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hgn : (g : ℝ) < M.W.n := by exact_mod_cast hS.hg
  have hx0 : (0 : ℝ) ≤ (((g + u) % M.W.n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxn : (((g + u) % M.W.n : ℕ) : ℝ) < M.W.n := by exact_mod_cast Nat.mod_lt _ hn
  rw [sideInArc_rot hg0 hgn ha0 han hb0 hbn hx0 hxn]
  have h := off_key (n := M.W.n) (g := g) (d := u) hS.hg (by have := hS.hLn; omega)
    (t := 0) le_rfl zero_lt_one
  rw [add_zero, add_zero] at h
  rw [h]

theorem ray_ne' {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) : z ≠ rayPt z σ T := by
  intro h
  have := congrArg Prod.fst h
  rw [Chazelle.Visibility.rayPt_fst] at this
  rcases hσ with rfl | rfl <;> linarith

/-- **A failed end test, in offsets.** -/
theorem end_gend (hS : Stretch M Cα g g' L) (hGα : WalkAx (chainModel Cα)) (hM : WalkAx M)
    {S : Set (Set Point)} (hSA : S ⊆ M.Adm) (hfin : S.Finite) (hne : S.Nonempty)
    {R : Set Point} {ai bi aj bj : ℝ} (hAi : M.IsArc S R ai bi) (hAj : M.IsArc S R aj bj)
    (hij : ai ≠ aj)
    -- the node chord and its other end in the piece chain's walk
    {c : Set Point} (hc : c ∈ (chainModel Cα).Adm) {pO : ℕ} {tO : ℝ}
    (hO : SideAttach (chainModel Cα).W c pO tO)
    -- the end, at offset `d + t` of the stretch
    {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (_hdt : 0 < (d : ℝ) + t)
    {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment (sidePt M.W ((g + d) % M.W.n) t)
      (rayPt (sidePt M.W ((g + d) % M.W.n) t) σ L₀))
    (hoO : rayPt (sidePt M.W ((g + d) % M.W.n) t) σ L₀ = sidePt (chainModel Cα).W pO tO)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W ((g + d) % M.W.n) t)
      (rayPt (sidePt M.W ((g + d) % M.W.n) t) σ L₀) s ∈ Cα.dom)
    (hsetD : ∀ x ∈ Cα.set, x ∉ M.D)
    -- the test
    {T : ℝ} (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt (sidePt M.W ((g + d) % M.W.n) t) σ s ∈ M.D)
    {pF : ℕ} {tF : ℝ}
    (hfar : sidePt M.W pF tF = rayPt (sidePt M.W ((g + d) % M.W.n) t) σ T)
    (hea : chordOf (sidePt M.W ((g + d) % M.W.n) t) σ T ∈ M.Adm)
    (hEA : SideAttach M.W (chordOf (sidePt M.W ((g + d) % M.W.n) t) σ T) ((g + d) % M.W.n) t)
    (hFA : SideAttach M.W (chordOf (sidePt M.W ((g + d) % M.W.n) t) σ T) pF tF)
    (hka : sideInArc ai bi (((g + d) % M.W.n : ℕ) + t))
    (hbad : ¬ CountOK M S R (((g + d) % M.W.n : ℕ) + t) (pF + tF))
    -- the good vertex at offset `x`
    {ex : Set Point} (hex : ex ∈ M.Adm) {x : ℕ} (hx : x < L) {px' : ℕ} {tx' : ℝ}
    (hX : SideAttach M.W ex ((g + x) % M.W.n) 0) (hX' : SideAttach M.W ex px' tx')
    (hXX' : sidePt M.W ((g + x) % M.W.n) 0 ≠ sidePt M.W px' tx')
    (hkx : ClosedArc ai bi (((g + x) % M.W.n : ℕ) + 0)) (hkx' : ClosedArc aj bj (px' + tx'))
    (hgood : CountOK M S R (((g + x) % M.W.n : ℕ) + 0) (px' + tx'))
    (hxa : (((g + x) % M.W.n : ℕ) : ℝ) + 0 ≠ ((g + d) % M.W.n : ℕ) + t)
    (hxa' : (((g + x) % M.W.n : ℕ) : ℝ) + 0 ≠ pF + tF) :
    0 ≤ off M.W.n g (pF + tF) ∧
      (0 < off M.W.n g (pF + tF) → off M.W.n g (pF + tF) < L →
        off M.W.n g (pF + tF) = off (chainModel Cα).W.n g' (pO + tO)) ∧
      (sideInArc ((d : ℝ) + t) (off M.W.n g (pF + tF)) (x : ℝ) ↔
        (aj = ((g + d) % M.W.n : ℕ) + t ∨
          sideInArc ((((g + d) % M.W.n : ℕ) : ℝ) + t) (pF + tF) aj)) ∧
      ∀ u : ℕ, u < L →
        (sideInArc ((((g + d) % M.W.n : ℕ) : ℝ) + t) (pF + tF) (((g + u) % M.W.n : ℕ) : ℝ) ↔
          sideInArc ((d : ℝ) + t) (off M.W.n g (pF + tF)) (u : ℝ)) := by
  have haC  := hS.memM hd ht0 ht1
  obtain ⟨h0, harr⟩ := arrival_off hS hGα hc hO haC hσ hL₀ hceq hoO hkopen hsetD hT hdom hfar hFA
  have hpr := prune_side hM hSA hfin hne hAi hAj hij hea hEA hFA
    (by rw [hfar]; exact ray_ne' hσ hT) hka hex hX hX' hXX' hkx hkx' hgood hbad hxa hxa'
  obtain ⟨hkE0, hkEn⟩ := key_range hEA
  obtain ⟨hkF0, hkFn⟩ := key_range hFA
  have hoE  := endM_off hS hd ht0 ht1
  refine ⟨h0, harr, ?_, fun u hu => ?_⟩
  · have hr := rot_u hS hkE0 hkEn hkF0 hkFn hx
    rw [hoE] at hr
    rw [← hr]
    rw [add_zero] at hpr
    exact hpr
  · have hr := rot_u hS hkE0 hkEn hkF0 hkFn hu
    rw [hoE] at hr
    exact hr

end

end Restore

end Chazelle.Core
