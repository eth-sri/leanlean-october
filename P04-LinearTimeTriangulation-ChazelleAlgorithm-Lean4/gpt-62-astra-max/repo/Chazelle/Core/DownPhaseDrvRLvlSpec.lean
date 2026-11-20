module

public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.DownPhaseDrvRRegSpec
public import Chazelle.Core.DownPhaseDrvRBktM

/-!
# Down-phase driver: the math of one level (D7)

One level (`LevelSpec`, from `Inv(λ)` to `Inv(μ)`, `μ = nextLvl λ`) runs, for every region `r`
of the current interior normal form `N = buildNF I Q L E`:
the host RAM (`HostRamSpec`: `H_r = regHost li n N r`), the region procedure (`RegionSpec`:
a `γ_r`-canonical map `NR_r` of cap `regCap` of the chain `C_r = ⟨H_r.poly Q, 0, #pts - 1⟩`,
`γ₀ ≤ γ_r ≤ γ₀ + 128`) and the extraction (`ExtractRamSpec`: the kept chords `Lx_r` of `NR_r`
in region `r`, with the buckets `keyBkt Q N` of their ends); it gathers
`L₂ = Lx_0 ++ … ++ Lx_K`, splices it into `(L, E)` (`splice_meets`, `SplPre`) and runs the
restoration rounds (`RoundsSpec`).

**`LevelMathSpec`** is the math the level needs between these RAM pieces:

1. *the hosts* (input of `RegionSpec`): at most `20` items, runs of at most `2 · 2^μ` edges, at
   least `3` and at most `10 · 2^μ + 8` points (degree `≤ 4`: at most `5` arcs of at most `4`
   items each, `DrvB.arcs_length_le`; weight `≤ 2^(μ+1)`: `DrvB.arcCnt_le`,
   `DrvB.regPts_length_le`);
2. *the splice precondition* (`SplPre`, as `DrvD.round_ok` for a round): `L ++ L₂` is valid, the
   buckets are bounded by `2 · #arcs + 1`, ordered like `codeLe`, and a bucket holds at most
   `4 M` ends when every `Lx_r` has at most `M` triples (a bucket meets at most two arcs);
3. *the size of `Lx_r`* (cost; Lemma 2.3, `DownMath.lemma23_chain`, and the host size of 1.);
4. *the family after the splice* (as `DrvD.round_family`; `DownDrv.downStepG`,
   `DownMath.level_count`): it contains `S`, has degree `≤ regCap + 4`, is
   `2^(⌈βμ⌉+12)`-semigranular, and `K₁ (γ₀ + 1) ≤ K (γ₀ + 1) + 1120 (regCap + 2) (n + 4 K)` (`level_count` gives `560`).
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine
open BuildNF (codeLe)

/-- **The math of one level (D7).** -/
noncomputable def LevelMathSpec : Prop :=
  open Classical in
  ∀ (P : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point) (lam : ℕ),
    GoodEnv P → L ≠ [] →
    ChordTriplesOK (interiorModel (Qof P)) (Qof P) L → E.Perm (List.range (2 * L.length)) →
    E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L) →
    (interiorModel (Qof P)).DegLe
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4 →
    (interiorModel (Qof P)).Semigranular
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P))
      (2 ^ (Cost.ceilBeta lam + 12)) →
    Restore.NFRegs (interiorModel (Qof P)) (Qof P)
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) reg →
    -- 1. the hosts
    (∀ r, r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
      (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r).length ≤ 20 ∧
      (∀ a ℓ, HostItem.run a ℓ ∈ regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r → ℓ ≤ 2 * 2 ^ nextLvl lam) ∧
      3 ≤ ((regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r).pts (Qof P).n).length ∧
      ((regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r).pts (Qof P).n).length ≤
        10 * 2 ^ nextLvl lam + 8) ∧
    -- the region data
    ∀ (γ₀ M : ℕ) (C : ℕ → Chain) (NR : ℕ → NF) (γR : ℕ → ℕ) (Lx : ℕ → List (ℕ × ℕ × ℕ)),
      γ₀ + 128 ≤ 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) →
      (∀ r, r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
        (C r).P = (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r).poly (Qof P) ∧
        (C r).s = 0 ∧ (C r).m + 1 = (C r).P.n ∧
        IsCanonicalNF (chainModel (C r)) (Qof P) (NR r) (γR r) regCap ∧
        γ₀ ≤ γR r ∧ γR r ≤ γ₀ + 128 ∧
        {x | ∃ y ∈ Lx r, x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} =
          Extract.kept (reg r) ((NR r).F (chainModel (C r)) (Qof P)) ∧
        ((Lx r).map fun y => (recOf y).toSet (interiorModel (Qof P)) (Qof P)).Nodup ∧
        (∀ y ∈ Lx r, (recOf y).Attached (interiorModel (Qof P)) (Qof P) ∧ y.1 < (Qof P).n) ∧
        (∀ q, q < 2 * (Lx r).length →
          ∃ j ∈ ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
            OnArcKey (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j
              (endPos (Lx r) q)) ∧
        (Lx r).length ≤ M) →
      -- 3. the size of the kept lists
      (∀ r, r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
        (Lx r).length * (γ₀ + 1) ≤ 140 * (regCap + 2) * (20 * 2 ^ nextLvl lam + 17)) ∧
      -- 2. the splice precondition
      ChordTriplesOK (interiorModel (Qof P)) (Qof P)
        (L ++ (List.range (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap
          Lx) ∧
      (∀ q, q < 2 * ((List.range
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx).length →
        keyBkt (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
            (endPos ((List.range
              (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) q) ≤
          2 * (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length + 1) ∧
      (∀ q q', q < 2 * ((List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx).length →
          q' < 2 * ((List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx).length →
          keyBkt (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
              (endPos ((List.range
                (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) q) <
            keyBkt (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
              (endPos ((List.range
                (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) q') →
          codeLe (interiorModel (Qof P)) (Qof P)
            (L ++ (List.range
              (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx)
            (2 * L.length + q) (2 * L.length + q')) ∧
      (∀ b, bcnt (fun q => keyBkt (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
            (endPos ((List.range
              (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) q))
          (2 * ((List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx).length)
          b ≤ 4 * M) ∧
      -- 4. the family after the splice
      ∀ E' : List ℕ,
        E'.Perm (List.range (2 * (L ++ (List.range
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx).length)) →
        E'.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) (L ++ (List.range
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx)) →
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P) ⊆
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) (L ++ (List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) E').F
            (interiorModel (Qof P)) (Qof P) ∧
        (interiorModel (Qof P)).DegLe
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) (L ++ (List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) E').F
            (interiorModel (Qof P)) (Qof P)) (regCap + 4) ∧
        (interiorModel (Qof P)).Semigranular
          ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) (L ++ (List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx) E').F
            (interiorModel (Qof P)) (Qof P)) (2 ^ (Cost.ceilBeta (nextLvl lam) + 12)) ∧
        (L ++ (List.range
            (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap Lx).length *
            (γ₀ + 1) ≤
          L.length * (γ₀ + 1) + 1120 * (regCap + 2) * ((Qof P).n + 4 * L.length)

end

end DrvR

end Chazelle.Core
