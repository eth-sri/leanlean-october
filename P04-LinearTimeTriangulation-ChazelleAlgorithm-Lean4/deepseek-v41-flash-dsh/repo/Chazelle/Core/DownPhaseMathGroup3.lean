module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathGroup2

/-!
# Down phase, math (H-R1): the points the driver writes for one arc

`group_rep`: for an arc `(key xs, key xe)` of `R` (record positions `xs`, `xe`) with host-key data
`ArcData … i₁ d₁` and junction flag `J₁` (`DownMath.arcs_cycle`), the points
`[start] ++ run ++ [end] ++ [junction?]` (the junction is written iff `DrvR.partner` at the end is
not the start `xn` of the next arc) represent the host keys `i₁, …, i₁ + d₁ + J₁` and are
`d₁ + 1 + J₁` many.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)

variable {Q : Polygon} {N : NF} {R : Set Point} {r : ℕ}

/-- `(y + n - x) mod n = c` for `y = (x + c) mod n`. -/
theorem runCnt_arith2 {n x c y : ℕ} (hx : x < n) (hcn : c < n) (hy : y = (x + c) % n) :
    (y + n - x) % n = c := by
  subst hy
  by_cases h : x + c < n
  · rw [Nat.mod_eq_of_lt h, show x + c + n - x = c + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hcn]
  · have e : (x + c) % n = x + c - n := by
      Ξ Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)
    Ξ e, show x + c - n + n - x = c by omega, Nat.mod_eq_of_lt hcn

/-- The points of an arc group. -/
def grpPts (li : Bool) (n : ℕ) (N : NF) (r : ℕ) (xs xe xn : WPos) : List SymPt :=
  [ptSym li n xs false] ++ (runItems li n xs xe).flatMap (wpts li n) ++ [ptSym li n xe true] ++
    (if partner N r xe = xn then [] else [ptSym li n (partner N r xe) false])

variable (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF (interiorModel Q) Q N)
  (hne : (N.F (interiorModel Q) Q).Nonempty)
  (hR : R ∈ (interiorModel Q).regions (N.F (interiorModel Q) Q))
  (hRC : ∀ i, i ∈ (N.region r).chords ↔
    i < N.nChords ∧ TouchesIn (interiorModel Q).D ((N.chord i).toSet (interiorModel Q) Q) R)

include hQ hdh hN hne hR hRC in
/-- **The points of one arc group represent its host keys.** -/
theorem group_rep {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {xs xe xn : WPos}
    (hxs : ChordPos N xs) (hxe : ChordPos N xe) (hxn : ChordPos N xn)
    (harc : (interiorModel Q).IsArc (N.F (interiorModel Q) Q) R ((interiorModel Q).key Q xs)
      ((interiorModel Q).key Q xe))
    {i₁ d₁ J₁ : ℕ}
    (hD : ArcData (interiorModel Q) (N.F (interiorModel Q) Q) R ((interiorModel Q).key Q xs)
      ((interiorModel Q).key Q xe) i₁ d₁)
    (_hJ : J₁ = 0 ↔ ArcGap (interiorModel Q) (N.F (interiorModel Q) Q) R
      ((i₁ + d₁ + 1) % nk (interiorModel Q) (N.F (interiorModel Q) Q) R))
    (hJ1 : J₁ ≤ 1)
    (hnext : (interiorModel Q).key Q xn = hk (interiorModel Q) (N.F (interiorModel Q) Q) R
      ((i₁ + d₁ + 1 + J₁) % nk (interiorModel Q) (N.F (interiorModel Q) Q) R)) :
    RepFrom li Q (N.F (interiorModel Q) Q) R (grpPts li Q.n N r xs xe xn) i₁ ∧
      (grpPts li Q.n N r xs xe xn).length = d₁ + 1 + J₁ ∧
      ((runItems li Q.n xs xe).flatMap (wpts li Q.n)).length = d₁ - 1 ∧
      ChordGap (interiorModel Q) (N.F (interiorModel Q) Q) R
        ((i₁ + d₁) % nk (interiorModel Q) (N.F (interiorModel Q) Q) R) ∧
      ChordPos N (partner N r xe) := by
  set I := interiorModel Q with hI
  set S := N.F I Q with hS
  set K := nk I S R with hK
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hFam : I.ChordFamily Q S := hN.1
  have h3 : 3 ≤ K := three_le_nk hQ hFam hne hR
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  have hil := hD.hil
  have hd0 := hD.hd0
  have hdN := hD.hdN
  obtain ⟨hinner, hend, hdn⟩ := arc_run hQ hFam hne hR hdh harc hD
  -- floors of the record positions
  have hfl : ∀ {x : WPos}, ChordPos N x → ⌊I.key Q x⌋₊ = x.edge ∧ x.edge < Q.n := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨-, hA, ek, -, -, -⟩ := chordPos_attach hN hc hxc
    exact ⟨by rw [ek, floor_add hA.2.1 hA.2.2.1], walk_n Q ▸ hA.1⟩
  obtain ⟨hfls, hes⟩ := hfl hxs
  obtain ⟨hfle, hee⟩ := hfl hxe
  -- the start
  have hstart : RepPt li Q S R i₁ (ptSym li Q.n xs false) := by
    apply ptSym_rep hN hdh hli hxs hD.hl
    · obtain ⟨c, ⟨hc, ht⟩, p, t, hA, he⟩ := hM.exists_exit_at_start hFam.2.1 hFam.1 hne hR harc
      exact ⟨c, hc, ht, p, t, hA, by rw [hD.hl]; exact he⟩
    · intro _
      constructor
      · intro h; exact absurd h (by decide)
      · intro hB
        exfalso
        have hA := arcGap_of_start hQ hFam hne hR hil (by rw [hD.hl]; exact harc)
        obtain ⟨c, ⟨hc, ht⟩, p, t, hA', he⟩ := hM.exists_exit_at_start hFam.2.1 hFam.1 hne hR harc
        exact not_arcGap_both hQ hFam hne hR hil ⟨c, hc, ht, p, t, hA', by rw [hD.hl]; exact he⟩
          hA hB
  -- the end
  set m := (i₁ + d₁) % K with hm
  have hmK : m < K := Nat.mod_lt _ (by omega)
  have hkm : hk I S R m = I.key Q xe := hD.hr
  have harc' : I.IsArc S R (I.key Q xs) (hk I S R m) := by rw [hkm]; exact harc
  have hAprev := arcGap_prev_of_end hQ hFam hne hR hmK harc'
  have hexe : hk I S R m ∈ exitKeys I S R := by
    obtain ⟨c, ⟨hc, ht⟩, p, t, hA, he⟩ := hM.exists_exit_at_end hFam.2.1 hFam.1 hne hR harc
    exact ⟨c, hc, ht, p, t, hA, by rw [hkm]; exact he⟩
  have hendR : RepPt li Q S R m (ptSym li Q.n xe true) :=
    ptSym_rep hN hdh hli hxe hkm hexe fun _ => ⟨fun _ => hAprev, fun _ => rfl⟩
  -- the run
  have hcnt : runCnt li Q.n xs xe = d₁ - 1 := by
    unfold runCnt
    rcases hend with ⟨hint, hfr⟩ | ⟨hni, hfr⟩
    · have hat : atVtx li Q.n xe = true := (atVtx_iff hN hdh hli hxe).2 hint
      rw [ite_eq_left hat, add_zero, ← hfls, ← hfle]
      exact runCnt_arith (by rw [hfls]; exact hes) (by omega) hdn hfr
    · have hat : atVtx li Q.n xe = false := by
        by_contra h
        exact hni ((atVtx_iff hN hdh hli hxe).1 (by simpa using h))
      rw [ite_eq_right (by rw [hat]; decide), ← hfls, ← hfle,
        show ⌊I.key Q xe⌋₊ + 1 + Q.n - 1 = ⌊I.key Q xe⌋₊ + Q.n by omega]
      exact runCnt_arith2 (by rw [hfls]; exact hes) (by omega) hfr
  have hrun : RepFrom li Q S R ((runItems li Q.n xs xe).flatMap (wpts li Q.n)) (i₁ + 1) ∧
      ((runItems li Q.n xs xe).flatMap (wpts li Q.n)).length = d₁ - 1 := by
    unfold runItems
    rw [hcnt]
    by_cases hd1 : d₁ - 1 = 0
    · rw [ite_eq_left hd1]
      exact ⟨repFrom_nil li _, by simp [hd1]⟩
    · rw [ite_eq_right hd1]
      obtain ⟨hlen, hget⟩ := run_wpts (li := li) (by omega) hes (show d₁ - 1 < Q.n by omega)
        (by omega)
      refine ⟨fun j hj => ?_, hlen⟩
      rw [hlen] at hj
      have hgj := hget j hj
      rw [hgj]
      have hidx : (i₁ + 1 + j) % K = (i₁ + (j + 1)) % K := by ring_nf
      rw [hidx]
      have hv := hinner (j + 1) (by omega) (by omega)
      left
      refine ⟨?_, ?_⟩
      · obtain ⟨⟨k, hk'⟩, hin⟩ := hD.inner (j + 1) (by omega) (by omega)
        refine ⟨k, ?_, hk', I.key Q xs, I.key Q xe, harc, ?_⟩
        · have := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 (Nat.mod_lt (i₁ + (j + 1))
            (show 0 < K by omega)))
          rw [hk'] at this
          exact_mod_cast this.2
        · rw [← hk']; exact hin
      · rw [hv, Nat.floor_natCast, hfls]
  -- the junction
  have hq₁m : (i₁ + d₁ + 1) % K = (m + 1) % K := by rw [hm, Nat.mod_add_mod]
  obtain ⟨hpos, hpkey, hpex⟩ := partner_key hQ hdh hN hne hR hRC hxe hmK hkm harc
  obtain ⟨hCm, -⟩ := end_chord hQ hFam hne hR hmK hexe hAprev
  have hjunc : RepFrom li Q S R
      (if partner N r xe = xn then [] else [ptSym li Q.n (partner N r xe) false]) (i₁ + d₁ + 1) ∧
      (if partner N r xe = xn then [] else [ptSym li Q.n (partner N r xe) false]).length = J₁ := by
    by_cases hJ0 : J₁ = 0
    · have hpx : partner N r xe = xn := by
        apply chordPos_eq hN hdh hpos hxn
        rw [hpkey, hnext, hJ0, add_zero, hq₁m]
      rw [ite_eq_left hpx]
      exact ⟨repFrom_nil _ _, by simp [hJ0]⟩
    · have hJ1' : J₁ = 1 := by omega
      have hpx : partner N r xe ≠ xn := by
        intro h
        have e1 : I.key Q xn = hk I S R (((m + 1) % K + 1) % K) := by
          rw [hnext, hJ1', ← hq₁m, Nat.mod_add_mod]
        have e2 : I.key Q (partner N r xe) = hk I S R ((m + 1) % K) := hpkey
        rw [h] at e2
        exact hk_succ_ne hM hFam.2.1 hFam.1 (by omega) (Nat.mod_lt _ (by omega)) (e2.symm.trans e1)
      rw [ite_eq_right hpx]
      refine ⟨repFrom_single ?_, by simp [hJ1']⟩
      rw [hq₁m]
      apply ptSym_rep hN hdh hli hpos hpkey.symm hpex
      intro _
      constructor
      · intro h; exact absurd h (by decide)
      · intro hB
        rw [prevIdx_succ hmK] at hB
        exact absurd hCm fun hC => not_arc_and_chord hM hFam.2.1 hFam.1 (by omega) hmK hB hC
  -- assembly
  obtain ⟨hrunR, hrunL⟩ := hrun
  obtain ⟨hjR, hjL⟩ := hjunc
  have hA1 : RepFrom li Q S R [ptSym li Q.n xs false] i₁ :=
    repFrom_single (by rw [Nat.mod_eq_of_lt hil]; exact hstart)
  have hA2 := repFrom_append hA1 (by simpa using hrunR)
  have hA3 := repFrom_append hA2 (L' := [ptSym li Q.n xe true]) (repFrom_single (by
    rw [List.length_append, hrunL, List.length_singleton,
      show i₁ + (1 + (d₁ - 1)) = i₁ + d₁ by omega]
    exact hendR))
  have hA4 := repFrom_append hA3 (by
    simp only [List.length_append, hrunL, List.length_singleton]
    rw [show i₁ + (1 + (d₁ - 1) + 1) = i₁ + d₁ + 1 by omega]
    exact hjR)
  refine ⟨hA4, ?_, hrunL, hCm, hpos⟩
  unfold grpPts
  rw [List.length_append, List.length_append, List.length_append, hrunL, hjL]
  simp only [List.length_singleton]
  omega

end

end DownMath

end Chazelle.Core
