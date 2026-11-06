module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathGroup3

/-!
# Down phase, math (H-R1): the whole walk-order point list of the driver's host

`walk_rep`: for region `r` of `N = buildNF I Q L E` (`RegCtx`), the walk-order points of
`DrvR.walkItems li n N r` represent the host keys of `reg r` cyclically from some index `i0`, they
are exactly `nk` many, and the host key before `i0` is a chord gap (the edge the chain leaves out).

* `flatMap_rot`: rotating a cyclic concatenation of groups `A t ++ B t` by `|A 0|`;
* `exists_arc`: every region has an arc;
* `walkItems_wpts`: the walk-order points of the walk items, arc by arc.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF)
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)

/-- **Rotating a cyclic concatenation.** -/
theorem flatMap_rot {α : Type*} (A B : ℕ → List α) {k : ℕ} (hk : 0 < k) :
    (List.range k).flatMap (fun t => B t ++ A ((t + 1) % k)) =
      ((List.range k).flatMap (fun t => A t ++ B t)).rotate (A 0).length := by
  set f : ℕ → List α := fun t => A (t % k) with hf
  have key : ∀ m, (List.range m).flatMap (fun t => f t ++ B t) ++ f m =
      f 0 ++ (List.range m).flatMap (fun t => B t ++ f (t + 1)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
        List.flatMap_singleton, List.append_assoc, List.append_assoc, ← List.append_assoc (f m),
        ← List.append_assoc _ (f m ++ B m)]
      Ξ ← List.append_assoc, ih
      ϴ List.append_assoc
  have h1 : (List.range k).flatMap (fun t => f t ++ B t) =
      (List.range k).flatMap (fun t => A t ++ B t) := by
    apply List.flatMap_congr
    intro t ht
    rw [List.mem_range] at ht
    ϴ hf, Nat.mod_eq_of_lt ht
  have h2 : (List.range k).flatMap (fun t => B t ++ f (t + 1)) =
      (List.range k).flatMap (fun t => B t ++ A ((t + 1) % k)) := rfl
  have hk0 : f k = A 0 := ⊚ hf
  have hf0 : f 0 = A 0 := ⊚ hf, Nat.zero_mod
  have e := key k
  rw [h1, h2, hk0, hf0] at e
  -- the concatenation starts with `A 0`
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, ⋄⟩
  obtain ⟨W', hW'⟩ : ∃ W', (List.range (k' + 1)).flatMap (fun t => A t ++ B t) = A 0 ++ W' := by
    Ξ List.range_succ_eq_map, List.flatMap_cons
    exact ⟨B 0 ++ List.flatMap (fun t => A t ++ B t) (List.map Nat.succ (List.range k')),
      ⍟ List.append_assoc⟩
  rw [hW'] at e ⊢
  rw [List.append_assoc] at e
  have := List.append_cancel_left e
  Ξ ← this, List.rotate_append_length_eq

/-- **Every region has an arc.** -/
theorem exists_arc {Q : Polygon} {S : Set (Set Point)} {R : Set Point} (hQ : Q.Simple)
    (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
    (hR : R ∈ (interiorModel Q).regions S) : ∃ a b, (interiorModel Q).IsArc S R a b := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  obtain ⟨p, t, hp, ht0, ht1, hnc, hfac⟩ := DownHost.exists_faces_nc hM hFam.2.1 hFam.1 hR
  obtain ⟨X, hX, l, r', harc, hin⟩ := hM.arc_around hFam.2.1 hFam.1 hne hnc
  have hfacX := harc.2.2.2.2.2.2 p t hp ht0 ht1 hin
  have hXR : X = R := by
    obtain ⟨δ, h1, h2⟩ := (hfacX.and hfac).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hR with h | h
    · exact h
    · exact absurd h2 (Set.disjoint_left.1 h h1)
  exact ⟨l, r', hXR ▸ harc⟩

/-- The walk-order points of one arc's items. -/
theorem arcItems_wpts (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).flatMap (wpts li n) =
      (if partner N r (N.arc jp).e = (N.arc j).s then []
        else [ptSym li n (partner N r (N.arc jp).e) false]) ++
      ([ptSym li n (N.arc j).s false] ++
        (runItems li n (N.arc j).s (N.arc j).e).flatMap (wpts li n) ++
        [ptSym li n (N.arc j).e true]) := by
  unfold arcItems
  ϴ List.flatMap_append, ptI_eq, List.flatMap_singleton, wpts_pt, List.append_assoc
  congr 1
  split_ifs <;> simp [wpts_pt]

/-- **The walk-order points of the driver's host** represent the host keys of the region
cyclically, `nk` of them, starting right after a chord gap; and the host is well formed. -/
theorem walk_rep {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
    {r : ℕ} (X : RegCtx Q L E reg r) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) :
    ∃ i0 g : ℕ,
      RepFrom li Q ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r)
        ((walkItems li Q.n (buildNF (interiorModel Q) Q L E) r).flatMap (wpts li Q.n)) i0 ∧
      ((walkItems li Q.n (buildNF (interiorModel Q) Q L E) r).flatMap (wpts li Q.n)).length =
        nk (interiorModel Q) ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) ∧
      g < nk (interiorModel Q) ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) ∧
      ChordGap (interiorModel Q) ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r) g ∧
      (g + 1) % nk (interiorModel Q) ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r)
        = i0 % nk (interiorModel Q) ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r)
      ∧ HostWF Q.n (walkItems li Q.n (buildNF (interiorModel Q) Q L E) r) := by
  set N := buildNF (interiorModel Q) Q L E with hNdef
  set I := interiorModel Q with hI
  set S := N.F I Q with hS
  set R := reg r with hRdef
  set K := nk I S R with hK
  have hQ := X.hQ
  have hdh := X.hdh
  have hN : IsNF I Q N := isNF_build X.hQ X.hL X.hperm X.hsort
  have hFam := hN.1
  have hnc : N.nChords = L.length := nChords_build X.hQ X.hL X.hperm X.hsort
  have hne : S.Nonempty :=
    ⟨_, (chordPos_attach hN (show 0 < N.nChords by rw [hnc]; exact X.hK) (Or.inl rfl)).1⟩
  have hR : R ∈ I.regions S := X.hregs.1.1 r X.hr
  have hRC := (X.hregs.2.2.2 r X.hr).1
  have hM : WalkAx I := walkAx_interiorModel hQ
  have h3 : 3 ≤ K := three_le_nk hQ hFam hne hR
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  obtain ⟨hAarc, hAsort, hAcomp⟩ := regArcs_facts (E := E) X.hQ X.hL X.hperm X.hsort X.hK
    X.hregs X.hr
  set as := (N.region r).arcs with has
  set k := as.length with hkdef
  set xs : ℕ → WPos := fun t => (N.arc (as.getD t 0)).s with hxs
  set xe : ℕ → WPos := fun t => (N.arc (as.getD t 0)).e with hxe
  have hk1 : 0 < k := by
    obtain ⟨a, b, hab⟩ := exists_arc hQ hFam hne hR
    obtain ⟨t, ht, -⟩ := hAcomp a b hab
    omega
  obtain ⟨i, d, J, hD, hJ0, hJ1, hoff, htot⟩ := arcs_cycle hQ hFam hne hR hdh hk1
    (fun t => I.key Q (xs t)) (fun t => I.key Q (xe t)) (fun t ht => (hAarc t ht).2) hAsort
    (fun a b h => by
      obtain ⟨t, ht, h1, h2⟩ := hAcomp a b h
      exact ⟨t, ht, h1, h2⟩)
  have hpos : ∀ t, t < k → ChordPos N (xs t) ∧ ChordPos N (xe t) := fun t ht =>
    arc_pos X.hQ X.hL X.hperm X.hsort X.hK (hAarc t ht).1
  have hil : ∀ t, t < k → i t < K := fun t ht => (hD t ht).hil
  -- the next start
  have hnext : ∀ t, t < k → I.key Q (xs ((t + 1) % k)) = hk I S R ((i t + d t + 1 + J t) % K) := by
    intro t ht
    have hst : i t + d t + 1 + J t = i 0 + grpOff d J (t + 1) := by
      rw [grpOff_succ, hoff t ht]; unfold grpLen; ring
    by_cases ht1 : t + 1 < k
    · Ξ Nat.mod_eq_of_lt ht1, hst, ← hoff (t + 1) ht1, Nat.mod_eq_of_lt (hil (t + 1) ht1)
      exact (hD (t + 1) ht1).hl.symm
    · have hkt : t + 1 = k := ⋄
      Ξ hkt, Nat.mod_self, hst, hkt, htot, Nat.add_mod_right, Nat.mod_eq_of_lt (hil 0 hk1)
      exact (hD 0 hk1).hl.symm
  -- the groups
  have hgrp : ∀ t, t < k →
      RepFrom li Q S R (grpPts li Q.n N r (xs t) (xe t) (xs ((t + 1) % k))) (i t) ∧
      (grpPts li Q.n N r (xs t) (xe t) (xs ((t + 1) % k))).length = d t + 1 + J t ∧
      ((runItems li Q.n (xs t) (xe t)).flatMap (wpts li Q.n)).length = d t - 1 ∧
      ChordGap I S R ((i t + d t) % K) ∧ ChordPos N (partner N r (xe t)) := fun t ht =>
    group_rep hQ hdh hN hne hR hRC hli (hpos t ht).1 (hpos t ht).2
      (hpos _ (Nat.mod_lt _ hk1)).1 (hAarc t ht).2 (hD t ht) (hJ0 t ht) (hJ1 t ht) (hnext t ht)
  -- the cyclic list from the first arc
  set A : ℕ → List SymPt := fun t => [ptSym li Q.n (xs t) false] ++
    (runItems li Q.n (xs t) (xe t)).flatMap (wpts li Q.n) ++ [ptSym li Q.n (xe t) true] with hA
  set B : ℕ → List SymPt := fun t => if partner N r (xe t) = xs ((t + 1) % k) then []
    else [ptSym li Q.n (partner N r (xe t)) false] with hB
  have hGAB : ∀ t, grpPts li Q.n N r (xs t) (xe t) (xs ((t + 1) % k)) = A t ++ B t :=
    fun t => rfl
  obtain ⟨hWrep, hWlen⟩ := repFrom_flatMap (li := li) (Q := Q) (S := S) (R := R)
    (fun t => A t ++ B t) d J (i 0) k fun t ht => by
      obtain ⟨h1, h2, -⟩ := hgrp t ht
      Ξ ← hGAB, ← hoff t ht
      exact ⟨h1, h2⟩
  rw [htot] at hWlen
  -- the driver's list is a rotation
  have hWP : (walkItems li Q.n N r).flatMap (wpts li Q.n) =
      ((List.range k).flatMap fun t => A t ++ B t).rotate (A 0).length := by
    Ξ ← flatMap_rot A B hk1
    unfold walkItems
    Ξ List.flatMap_assoc
    apply List.flatMap_congr
    intro t ht
    Ξ arcItems_wpts
  have hA0 : (A 0).length = d 0 + 1 := by
    obtain ⟨-, -, h3', -⟩ := hgrp 0 hk1
    ϴ hA, List.length_append, List.length_singleton, h3'
    have := (hD 0 hk1).hd0
    omega
  refine ⟨i 0 + (A 0).length, (i 0 + d 0) % K, ?_, ?_, Nat.mod_lt _ (⋄),
    (hgrp 0 hk1).2.2.2.1, ?_, ?_⟩
  · rw [hWP]; exact repFrom_rotate hWlen hWrep _
  · Ξ hWP, List.length_rotate, hWlen
  · Ξ Nat.mod_add_mod, hA0, Nat.add_assoc
  · -- well formed
    intro it hit
    unfold walkItems at hit
    rw [← has, ← hkdef] at hit
    obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 hit
    rw [List.mem_range] at ht
    have hp0 := hpos t ht
    have hp1 := hpos _ (Nat.mod_lt (t + 1) hk1)
    have hpp := (hgrp t ht).2.2.2.2
    have hptI : ∀ (x : WPos) (b : Bool), ChordPos N x →
        (match ptI li Q.n x b with
          | .run a ℓ => a < Q.n ∧ ℓ < Q.n
          | .pt x => x.Lt Q.n) := by
      intro x b hx
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨-, hAx, -, eh, hh, -⟩ := chordPos_attach hN hc hxc
      have hxn : x.edge < Q.n := walk_n Q ▸ hAx.1
      show qE li Q.n _ < Q.n ∧ x.hgt - 1 < Q.n
      refine ⟨qE_lt li ?_, by rw [eh]; simpa using hh⟩
      split_ifs
      · exact Nat.mod_lt _ (⋄)
      · exact hxn
    unfold arcItems at hit
    simp only [List.mem_append, List.mem_singleton] at hit
    rcases hit with ((hj | rfl) | hrun) | rfl
    · split_ifs at hj with hpe
      · simp at hj
      · rw [List.mem_singleton] at hj
        subst hj
        exact hptI _ _ hpp
    · exact hptI _ _ (hpos _ (Nat.mod_lt (t + 1) hk1)).1
    · unfold runItems at hrun
      have hxn : (N.arc (as.getD ((t + 1) % k) 0)).s.edge < Q.n := by
        obtain ⟨c, hc, hxc⟩ := hp1.1
        obtain ⟨-, hAx, -, -, -, -⟩ := chordPos_attach hN hc hxc
        exact walk_n Q ▸ hAx.1
      have hcn : runCnt li Q.n (N.arc (as.getD ((t + 1) % k) 0)).s
          (N.arc (as.getD ((t + 1) % k) 0)).e < Q.n := Nat.mod_lt _ (⋄)
      split_ifs at hrun with h0 h1
      · simp at hrun
      · rw [List.mem_singleton] at hrun; subst hrun
        exact ⟨Nat.mod_lt _ (⋄), ⋄⟩
      · rw [List.mem_singleton] at hrun; subst hrun
        exact ⟨⋄, ⋄⟩
    · exact hptI _ _ (hpos _ (Nat.mod_lt (t + 1) hk1)).2

end

end DownMath

end Chazelle.Core
