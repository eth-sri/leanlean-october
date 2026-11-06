module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLHit4

/-!
# The sweep RAM (WP-D), answers: the local hit

**The local hit** at a walk position `x = (lE, lH)` of a chain model in the direction of code
`lD`: the spine position and the three regions around `x` (part 1), the normalised arcs of these
regions (gather), the holes at `x`, the shot along the ray against the arcs with the offer of its
hit, and the far ends of the matching exit chords of the three regions.  Every offered candidate
is a point of the chain or of the box on the ray at a positive parameter, and (below the top, for a
ray in the left sector at a height-coded position) the exit point of the chain is offered
(`Sweep.local_hit_mem`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The local hit.** -/
def localHit (sh : Stmt) : Stmt :=
  .seq lh1 (.seq lhGather (.seq lhHoles (.seq (lhShotOffer sh) lhScan)))

/-- The registers the local hit writes (besides the allocator and the oracle bands):
`sw 1000 … sw 2199` (the accumulator `accA = sw 2000 … sw 2012` included) and `sw 3000 … sw 3199`. -/
def LHW (r : ℕ) : Prop := (sw 1000 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 3200)

/-- **The geometric conditions of completeness**: a positive height code naming the height of the
point, the ray in the left sector, the point not above the top. -/
def LHGeo (P : Polygon) (C : Chain) (x : WPos) (d : ℕ) : Prop :=
  ∃ h, x.hgt = h + 1 ∧ h < P.n ∧ ((Qof P).vtx h).2 = ((chainModel C).pos (Qof P) x).2 ∧
    sideLeft (chainModel C).W x.edge ((chainModel C).param (Qof P) x)
      (rayPt ((chainModel C).pos (Qof P) x) (dirOf d) 1) ∧
    ((chainModel C).pos (Qof P) x).2 ≤ C.top.2

/-- The cost of the local hit: `T` the length of the table of powers, `Fg` the shooter's cost,
`Da` and `Dc` bounds on the numbers of arcs and exit chords of a region. -/
def localK (T Fg Da Dc : ℕ) : ℕ :=
  lh1K T + ((3 + (11 + 3 * (regK Da + 2))) +
    (11200 + (shotOfferK Fg (3 * Da) + lhScanK Dc Dc Dc)))

/-! ## Cost bounds -/

section
variable {N : NF} {rs : List ℕ} {Da : ℕ} (h : ∀ r ∈ rs, (N.region r).arcs.length ≤ Da)
include h
theorem gatherK_le :
    gatherK N rs ≤ 11 + rs.length * (regK Da + 2) := by
  unfold gatherK
  have := List.sum_le_length_nsmul (rs.map fun r => regK (N.region r).arcs.length + 2)
    (regK Da + 2) (by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
      simp_all [regK] )
  simp_all

theorem regArcs_length_le :
    (regArcs N rs).length ≤ rs.length * Da := by
  unfold regArcs
  rw [List.length_flatMap]
  have := List.sum_le_length_nsmul (rs.map fun r => (N.region r).arcs.length) Da (by
    simp_all)
  simp_all


end

theorem shotOfferK_mono {Fg K K' : ℕ} (h : K ≤ K') : shotOfferK Fg K ≤ shotOfferK Fg K' := by
  omega_nf


theorem lhScanK_mono {a b d a' b' d' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hd : d ≤ d') :
    lhScanK a b d ≤ lhScanK a' b' d' := by
  omega_nf

/-! ## The regions around the spine position -/

section
variable {C : Chain} {N : NF} (hNF : IsNF (chainModel C) (Qof P) N)
include C hNF
theorem nbrRegs_lt {j : ℕ}
    (hj : j < N.arcs.length) : ∀ r ∈ Sweep.nbrRegs N j, r < N.nRegions := by
  have hNF' := hNF
  obtain ⟨-, -, -, reg, -, -, hArcs, -⟩ := hNF'
  have hreg : ∀ p, p < N.arcs.length → (N.arc (sj N p)).reg < N.nRegions := fun p hp =>
    (hArcs.1 _ (NFLoc.seq_lt hNF hp)).1
  intro r hr
  simp only [Sweep.nbrRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hreg _ (OracleQ.predP_lt hj)
  · simp_all
  · exact hreg _ (OracleQ.succP_lt hj)

section
variable {rs : List ℕ} (hrs : ∀ r ∈ rs, r < N.nRegions)
include rs hrs
theorem regArcs_lt : ∀ a ∈ regArcs N rs, a < N.arcs.length := by
  intro a ha
  obtain ⟨-, -, -, reg, -, -, hArcs, -⟩ := hNF
  obtain ⟨r, hr, har⟩ := List.mem_flatMap.1 ha
  exact ((hArcs.2.2.2 r (hrs r hr) a).1 har).1

/-- The gathered arcs list the arcs of the regions, up to the keys. -/
theorem gathered_keys {m : ℕ → ℕ} {AB : ℕ}
    (harcs : ∀ k, k < (regArcs N rs).length → ShotList.arcAt m AB k =
      nArc (chainModel C) (Qof P) N ((regArcs N rs).getD k 0)) :
    ∀ r ∈ rs, ∀ a ∈ (N.region r).arcs, ∃ i < (regArcs N rs).length,
      (chainModel C).key (Qof P) (ShotList.arcAt m AB i).1 =
        (chainModel C).key (Qof P) (N.arc a).s ∧
      (chainModel C).key (Qof P) (ShotList.arcAt m AB i).2 =
        (chainModel C).key (Qof P) (N.arc a).e := by
  intro r hr a ha
  have hNF' := hNF
  obtain ⟨-, -, -, reg, -, -, hArcs, -, -, -, hpp⟩ := hNF'
  have hal : a < N.arcs.length := ((hArcs.2.2.2 r (hrs r hr) a).1 ha).1
  have hmem : a ∈ regArcs N rs := List.mem_flatMap.2 ⟨r, hr, ha⟩
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.1 hmem
  refine ⟨i, hi, ?_⟩
  have hg : (regArcs N rs).getD i 0 = a := by simp_all
  rw [harcs i hi, hg]
  unfold nArc
  exact ⟨(Restore.normOf_facts (hpp a hal).1).2.2.2.1, (Restore.normOf_facts (hpp a hal).2).2.2.2.1⟩

/-! ## The local hit -/



end

end

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- **The local hit.** -/
theorem localHit_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ}
    {Da Dc : ℕ} {x : WPos} {d : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hL : LCtx P W C N E c)
    (hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC))
    (hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10)))
    (hOk : Ok P (chainModel C))
    (hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 5)))
    (hAr : ∀ r, r < N.nRegions → (N.region r).arcs.length ≤ Da)
    (hCh : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ Dc)
    (hxE : c.nreg lE = x.edge) (hxH : c.nreg lH = x.hgt) (hxD : c.nreg lD = d)
    (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n x)
    (hy : |((chainModel C).pos (Qof P) x).2| < C.radius)
    (hloc : (x.edge = 1 ∨ x.edge = 3) ∨
      (6 ≤ x.edge ∧ (chainModel C).pos (Qof P) x ∈ C.set))
    (hacc : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod (c.nreg lT) = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (hroom : c.nreg ALLOC + localK (c.nreg TLR) (F (c₀.nreg (sw 5))) Da Dc ≤ W) :
    IRS P W c₀ (localHit sh) c (localK (c.nreg TLR) (F (c₀.nreg (sw 5))) Da Dc) (fun c' =>
      (∃ L', AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L' c' ∧ L ⊆ L' ∧
        (∀ τ ∈ L', τ ∈ L ∨
          (0 < τ ∧ OnCB C (rayPt ((chainModel C).pos (Qof P) x) (dirOf d) τ))) ∧
        (LHGeo P C x d → Merge.FreeAt C ((chainModel C).pos (Qof P) x) (dirOf d) ∧
          C.hitParam ((chainModel C).pos (Qof P) x) (dirOf d) ∈ L')) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  obtain ⟨xe, xh⟩ := x
  simp only at hxE hxH he hloc
  subst hxE hxH hxD
  have hσ' : dirOf (c.nreg lD) = 1 ∨ dirOf (c.nreg lD) = -1 := dirOf_cases _
  have hQn : (Qof P).n = P.n := shear_n _ _
  -- the input registers
  let LIn : ℕ → Prop := fun r => r = lMD ∨ r = lCD ∨ r = lNF ∨ r = lE ∨ r = lH ∨ r = lD ∨
    r = lN ∨ r = lT
  have lin : ∀ r, LIn r → 241100 ≤ r ∧ r ≤ 241107 := by
    grind [lMD, lCD, lNF, lE, lH, lD, lN, lT, sw]
  have linO : ∀ r, LIn r → bandOf r ∉ oracleBands := fun r hr =>
    not_oracle_sw (by have := lin r hr; omega) (by have := lin r hr; omega)
  -- 1. the spine position and the regions
  refine IRS.seq (K₂ := (3 + (11 + 3 * (regK Da + 2))) +
      (11200 + (shotOfferK (F (c₀.nreg (sw 5))) (3 * Da) + lhScanK Dc Dc Dc)))
    (lh1_irs hI hK hL he hpp (by grind [localK])) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hj1, hl1, hl2, hLL, hA1, hlist1, hm1, fr1, hR0, hR1, hR2⟩
  have k1 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1 r h1 (fun h => h2 (by grind [LSet, sw, LHW])) h3
  have i1 : ∀ r, LIn r → c₁.nreg r = c.nreg r := fun r hr =>
    fr1 r (linO r hr) (fun h => by have := lin r hr; grind [LSet, sw])
      (by have := lin r hr; omega_nf)
  have hL₁ : LCtx P W C N E c₁ := hL.transport (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · grind
      · grind
      · grind
      · exact hI₁.hin _ (by omega_nf) |>.trans (hI.hin _ (by omega_nf)).symm
      · exact hI₁.hin _ (by omega_nf) |>.trans (hI.hin _ (by omega_nf)).symm)
    hm1 hA₁
  set j := c₁.nreg lJ with hjd
  have hrsl : ∀ r ∈ Sweep.nbrRegs N j, r < N.nRegions := nbrRegs_lt hL.hNF hj1
  have hrs3 : (Sweep.nbrRegs N j).length = 3 := by simp [Sweep.nbrRegs]
  have hGl : gatherK N (Sweep.nbrRegs N j) ≤ 11 + 3 * (regK Da + 2) := by
    have := gatherK_le (N := N) (rs := Sweep.nbrRegs N j) (Da := Da)
      (fun r hr => hAr r (hrsl r hr))
    grind
  have hKl : (regArcs N (Sweep.nbrRegs N j)).length ≤ 3 * Da := by
    have := regArcs_length_le (N := N) (rs := Sweep.nbrRegs N j) (Da := Da)
      (fun r hr => hAr r (hrsl r hr))
    grind
  -- 2. the gather
  refine IRS.seq (K₂ := 11200 + (shotOfferK (F (c₀.nreg (sw 5))) (3 * Da) + lhScanK Dc Dc Dc))
    ((lhGather_irs (rs := Sweep.nbrRegs N j) hI₁ hK hL₁ hrs3 hrsl
      (fun i hi => by grind) (by omega)
      (by grind [localK])).mono (K' := 3 + (11 + 3 * (regK Da + 2)))
      (by omega) (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨g1, g2, g3, g4, hm2, fr2⟩
  have k2 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => fr2 r h1 (fun h => h2 (by unfold GCall sw at h; omega_nf)) h3
  have i2 : ∀ r, LIn r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [← i1 r hr]
    exact fr2 r (linO r hr) (fun h => by have := lin r hr; unfold GCall sw at h; omega)
      (by grind)
  have hL₂ : LCtx P W C N E c₂ := hL₁.transport (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [i2 _ (Or.inl rfl), i1 _ (Or.inl rfl)]
      · rw [i2 _ (Or.inr (Or.inl rfl)), i1 _ (Or.inr (Or.inl rfl))]
      · rw [i2 _ (Or.inr (Or.inr (Or.inl rfl))), i1 _ (Or.inr (Or.inr (Or.inl rfl)))]
      · exact hI₂.hin _ (by omega_nf) |>.trans (hI₁.hin _ (by omega_nf)).symm
      · exact hI₂.hin _ (by unfold TLR IFix sw; omega) |>.trans (hI₁.hin _ (by unfold TLR IFix sw; omega)).symm)
    hm2 hA₂
  have e2 : c₂.nreg lE = c.nreg lE := i2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : c₂.nreg lH = c.nreg lH := i2 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  -- 3. the holes
  refine IRS.seq (K₂ := shotOfferK (F (c₀.nreg (sw 5))) (3 * Da) + lhScanK Dc Dc Dc)
    (lhHoles_irs hI₂ hK hL₂.hctx (by rw [e2]; exact he) (by rw [e2, h2]; exact hpp)
      (by rw [e2, h2]; exact hy) (by rw [e2, h2]; exact hloc)
      (by unfold localK at hroom; omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨hho, fr3, hA3, hm3⟩
  rw [e2, h2] at hho
  have k3 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => fr3 r h1 (fun h => h2 (by
      unfold HSet lO sw at h; unfold LHW sw; omega)) h3
  have i3 : ∀ r, LIn r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [← i2 r hr]
    exact fr3 r (linO r hr) (fun h => by have := lin r hr; unfold HSet lO sw at h; omega)
      (by have := lin r hr; unfold ALLOC; omega)
  have kG : ∀ r, GCall r → c₃.nreg r = c₂.nreg r := fun r hr =>
    fr3 r (not_oracle_sw (by unfold GCall sw at hr; omega) (by unfold GCall sw at hr; omega))
      (fun h => by unfold GCall sw at hr; unfold HSet lO sw at h; omega)
      (by unfold GCall sw at hr; unfold ALLOC; omega)
  have hL₃ : LCtx P W C N E c₃ := hL₂.transport (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [i3 _ (Or.inl rfl), i2 _ (Or.inl rfl)]
      · rw [i3 _ (Or.inr (Or.inl rfl)), i2 _ (Or.inr (Or.inl rfl))]
      · rw [i3 _ (Or.inr (Or.inr (Or.inl rfl))), i2 _ (Or.inr (Or.inr (Or.inl rfl)))]
      · exact hI₃.hin _ (by unfold TBR IFix sw; omega) |>.trans (hI₂.hin _ (by unfold TBR IFix sw; omega)).symm
      · exact hI₃.hin _ (by unfold TLR IFix sw; omega) |>.trans (hI₂.hin _ (by unfold TLR IFix sw; omega)).symm)
    (fun a _ => by rw [hm3]) hA3.ge
  have e3 : c₃.nreg lE = c.nreg lE := i3 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : c₃.nreg lH = c.nreg lH := i3 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have d3 : c₃.nreg lD = c.nreg lD := i3 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have n3 : c₃.nreg lN = c.nreg lN :=
    i3 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have t3 : c₃.nreg lT = c.nreg lT :=
    i3 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  have gB3 : c₃.nreg gBase = c₁.nreg ALLOC := by rw [kG _ (by unfold GCall gBase sw; omega), g1]
  have gK3 : c₃.nreg gK = (regArcs N (Sweep.nbrRegs N j)).length := by rw [kG _ (by unfold GCall gK sw; omega), g2]
  -- the accumulator is untouched so far
  have hacc₃ : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩)
      (dirOf (c.nreg lD)) L c₃ := hacc.transport (fun i hi => by
    have o : bandOf (accA + i) ∉ oracleBands :=
      not_oracle_sw (by unfold accA sw; omega) (by unfold accA sw; omega)
    rw [fr3 _ o (by unfold HSet lO accA sw; omega) (by unfold accA ALLOC sw; omega),
      fr2 _ o (by unfold GCall accA sw; omega) (by unfold accA ALLOC sw; omega)]
    exact fr1 _ o (by unfold LSet accA sw; omega) (by unfold accA ALLOC sw; omega))
  have hW3 : P.n + 3 ≤ W := by have := hL.hWh; unfold hostWords at this; omega
  have hD : DistinctHeights (Qof P) := (goodShear_epsOf hL.hG.2).2.1
  -- 4. the shot and its offer
  refine IRS.seq (K₂ := lhScanK Dc Dc Dc)
    ((lhShotOffer_irs hsh hBs hXl (rs := Sweep.nbrRegs N j) (L := L) hI₃ hK hL₃ hX hcap hOk hsg
      (by rw [e3]; exact he) (by rw [e3, h3]; exact hpp) (by rw [e3, h3]; exact hy)
      (regArcs_lt hL.hNF hrsl) gK3 (by rw [gB3, hA3, g3]) (by rw [gB3, hm3]; exact g4)
      (by rw [e3, h3]; exact hho) (by rw [e3, h3, d3]; exact hacc₃) (by rw [t3]; exact htag)
      (by rw [t3]; exact hMod) hR (by rw [n3]; exact hn)
      (by
        have := shotOfferK_mono (Fg := F (c₀.nreg (sw 5))) hKl
        unfold localK at hroom; omega)).mono
      (K' := shotOfferK (F (c₀.nreg (sw 5))) (3 * Da)) (shotOfferK_mono hKl) (fun _ h => h)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨L₁, a₁, hL₁, comp₁, fr4, hA4, hm4⟩
  rw [e3, h3, d3] at a₁ hL₁ comp₁
  have k4 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₄.nreg r = c₃.nreg r :=
    fun r h1 h2 h3 => fr4 r h1 (fun h => h2 (by unfold RS at h; unfold LHW sw; omega))
      (by unfold LHW sw at h2; unfold accA sw; omega) (fun h => h2 (by subst h; unfold lO LHW sw; omega))
      (fun h => h2 (by subst h; unfold lO LHW sw; omega)) h3
  have keep4 : ∀ r, 241100 ≤ r → r ≤ 241111 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    fr4 r (not_oracle_sw (by omega) (by omega)) (by unfold RS; omega) (by unfold accA sw; omega)
      (by unfold lO sw; omega) (by unfold lO sw; omega) (by unfold ALLOC; omega)
  have i4 : ∀ r, LIn r → c₄.nreg r = c.nreg r := fun r hr => by
    have := lin r hr
    rw [keep4 r (by omega) (by omega), i3 r hr]
  have hL₄ : LCtx P W C N E c₄ := hL₃.transport (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [i4 _ (Or.inl rfl), i3 _ (Or.inl rfl)]
      · rw [i4 _ (Or.inr (Or.inl rfl)), i3 _ (Or.inr (Or.inl rfl))]
      · rw [i4 _ (Or.inr (Or.inr (Or.inl rfl))), i3 _ (Or.inr (Or.inr (Or.inl rfl)))]
      · exact hI₄.hin _ (by unfold TBR IFix sw; omega) |>.trans (hI₃.hin _ (by unfold TBR IFix sw; omega)).symm
      · exact hI₄.hin _ (by unfold TLR IFix sw; omega) |>.trans (hI₃.hin _ (by unfold TLR IFix sw; omega)).symm)
    hm4 hA4
  have e4 : c₄.nreg lE = c.nreg lE := i4 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : c₄.nreg lH = c.nreg lH := i4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have d4 : c₄.nreg lD = c.nreg lD := i4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have n4 : c₄.nreg lN = c.nreg lN :=
    i4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have t4 : c₄.nreg lT = c.nreg lT :=
    i4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  -- the region registers
  have kR : ∀ r, 241109 ≤ r → r ≤ 241111 → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [keep4 r (by omega) (by omega),
      fr3 r (not_oracle_sw (by omega) (by omega)) (by unfold HSet lO sw; omega) (by unfold ALLOC; omega),
      fr2 r (not_oracle_sw (by omega) (by omega)) (by unfold GCall sw; omega) (by unfold ALLOC; omega)]
  have r0 : c₄.nreg lR0 = (N.arc (sj N (predP N.arcs.length j))).reg := by
    rw [kR lR0 (by unfold lR0 sw; omega) (by unfold lR0 sw; omega), hR0]
  have r1 : c₄.nreg lR1 = (N.arc (sj N j)).reg := by
    rw [kR lR1 (by unfold lR1 sw; omega) (by unfold lR1 sw; omega), hR1]
  have r2 : c₄.nreg lR2 = (N.arc (sj N (succP N.arcs.length j))).reg := by
    rw [kR lR2 (by unfold lR2 sw; omega) (by unfold lR2 sw; omega), hR2]
  have hr0 : (N.arc (sj N (predP N.arcs.length j))).reg < N.nRegions :=
    hrsl _ (by simp [Sweep.nbrRegs])
  have hr1 : (N.arc (sj N j)).reg < N.nRegions := hrsl _ (by simp [Sweep.nbrRegs])
  have hr2 : (N.arc (sj N (succP N.arcs.length j))).reg < N.nRegions :=
    hrsl _ (by simp [Sweep.nbrRegs])
  have hS₄ : SEnv P W C N Mod R₀ ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) c₄ :=
    ⟨hL.hG, hW3, hL₄.hctx, hL.hNF, by rw [t4]; exact htag, by rw [t4]; exact hMod, hR,
      by rw [n4]; exact hn, e4, h4, d4, by rw [← hR]; exact hy⟩
  have hsc := lhScanK_mono (hCh _ hr0) (hCh _ hr1) (hCh _ hr2)
  -- 5. the chords
  refine (lhScan_irs hI₄ hK hS₄ rfl hL₄.hNW hL₄.hE r0 r1 r2 hr0 hr1 hr2 a₁
    (by unfold localK at hroom; omega)).mono (K' := lhScanK Dc Dc Dc) hsc ?_
  rintro c₅ ⟨⟨L₂, a₂, s₂, g₂, d₂⟩, fr5⟩
  have hLL₁ : L ⊆ L₁ := by
    rcases hL₁ with rfl | ⟨τ, rfl, -⟩
    · exact le_rfl
    · exact Set.subset_insert _ _
  refine ⟨⟨L₂, a₂, hLL₁.trans s₂, fun τ hτ => ?_, fun hgeo => ?_⟩, fun r h1 h2 h3 => ?_, ?_, ?_⟩
  · rcases g₂ τ hτ with h | h
    · rcases hL₁ with rfl | ⟨τ', rfl, hτ', hg'⟩
      · exact Or.inl h
      · rcases h with rfl | h
        · exact Or.inr ⟨hτ', hg'⟩
        · exact Or.inl h
    · exact Or.inr h
  · obtain ⟨h, hxh, hhn, hyz, hsec, hzt⟩ := hgeo
    obtain ⟨hfree, hmem⟩ := Sweep.local_hit_mem C hL.hP hD hL.hNF
      (x := ⟨c.nreg lE, c.nreg lH⟩) hxh (by rw [hQn]; exact hhn) he hpp.1 hpp.2.1 hyz hsec hy
      hzt hj1 hl1 hl2 (gathered_keys hL.hNF hrsl (m := c₃.nmem) (AB := c₃.nreg gBase)
        (by rw [gB3, hm3]; exact g4)) hho.2.2.2
    refine ⟨hfree, ?_⟩
    rcases hmem with hlo | ⟨r, hr, k, hk, hca, hpos⟩
    · exact s₂ (comp₁ hfree hzt hlo)
    · have hk' : k ∈ (N.region (N.arc (sj N (predP N.arcs.length j))).reg).chords ++
          ((N.region (N.arc (sj N j)).reg).chords ++
            (N.region (N.arc (sj N (succP N.arcs.length j))).reg).chords) := by
        simp only [Sweep.nbrRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [hk]
      obtain ⟨τ, hτ, hτpos⟩ := d₂ hzt k hk' hca
      have hne : dirOf (c.nreg lD) ≠ 0 := by rcases hσ' with h | h <;> rw [h] <;> norm_num
      have := Chazelle.Visibility.rayPt_injective _ hne (hτpos.symm.trans hpos)
      rw [← this]; exact hτ
  · have hS : ¬ SSet r := fun h => h2 (by unfold SSet sw at h; unfold LHW sw; omega)
    rw [fr5.1 r h1 hS (by unfold LHW sw at h2; unfold accA sw; omega)
      (fun h => h2 (by subst h; unfold lO LHW sw; omega))
      (fun h => h2 (by subst h; unfold lO LHW sw; omega)) h3,
      k4 r h1 h2 h3, k3 r h1 h2 h3, k2 r h1 h2 h3, k1 r h1 h2 h3]
  · have := fr5.2.1; omega
  · intro a ha
    rw [fr5.2.2 a (by omega), hm4 a (by omega), hm3, hm2 a (by omega), hm1 a ha]

end

end SweepIo

end Chazelle.Core
