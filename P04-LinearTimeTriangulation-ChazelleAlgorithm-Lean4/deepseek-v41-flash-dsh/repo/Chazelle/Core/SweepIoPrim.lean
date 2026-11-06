module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoRun
public import Chazelle.Core.SweepPrimArr
public import Chazelle.Core.SweepPrimAbs
public import Chazelle.Core.SweepPrimOff

/-!
# The sweep RAM (WP-D), answers: calls of the primitives

Each primitive of `SweepPrim` (`arrivalPos`, `absKey`, `absCmp`, `offCmp`) reads its inputs from
`50200 …` and writes its outputs from `50210` on.  The wrappers here copy the inputs from
registers of the answer stage, run the primitive, and copy the outputs to scratch registers of
the answer stage (band `bSweep`, from `sw 700` on); their run-step lemmas (`IRS`) state the
primitive's postcondition on the destination registers and that every other register outside
the oracle bands is unchanged.

* `cps`, `regB_cps`: blocks of register copies.
* `ChainCtx`: the facts a primitive needs about the chain descriptor at a register.
* `callArr_irs`, `callAbs_irs`, `callAbsCmp_irs`, `callOff_irs`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

/-! ## Blocks of copies -/

/-- A block of register copies `d := s`. -/
def cps (l : List (ℕ × ℕ)) : List Instr := l.map fun p => .copyN p.1 p.2

theorem cps_length (l : List (ℕ × ℕ)) : (cps l).length = l.length := ⊚ cps

/-- **The effect of a block of copies** with distinct targets, no source being a target. -/
theorem regB_cps (m : ℕ → ℕ) : ∀ (l : List (ℕ × ℕ)) (f : ℕ → ℕ),
    (l.map Prod.fst).Nodup → (∀ p ∈ l, ∀ q ∈ l, p.2 ≠ q.1) →
    (∀ p ∈ l, regB m (cps l) f p.1 = f p.2) ∧
      ∀ r, r ∉ l.map Prod.fst → regB m (cps l) f r = f r
  | [], f, _, _ => ⟨fun p hp => by simp at hp, fun r _ => rfl⟩
  | (d, s) :: l, f, hnd, hsrc => by
    have hnd' := List.nodup_cons.1 hnd
    have hsrc' : ∀ p ∈ l, ∀ q ∈ l, p.2 ≠ q.1 := fun p hp q hq =>
      hsrc p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)
    obtain ⟨ih1, ih2⟩ := regB_cps m l (upd f d (f s)) hnd'.2 hsrc'
    have hcps : cps ((d, s) :: l) = .copyN d s :: cps l := rfl
    Ξ hcps
    ϴ regB, regI
    refine ⟨fun p hp => ?_, fun r hr => ?_⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · Ξ ih2 _ (by simpa using hnd'.1)
        simp
      · Ξ ih1 p hp
        have : p.2 ≠ d := hsrc p (List.mem_cons_of_mem _ hp) (d, s) List.mem_cons_self
        Θ upd, this
    · ϴ' List.map_cons, List.mem_cons, not_or at hr
      Ξ ih2 r hr.2
      Θ upd, hr.1

/-- The side conditions of a block of copies into scratch registers. -/
theorem okB_cps (W : ℕ) (m : ℕ → ℕ) : ∀ (l : List (ℕ × ℕ)) (f : ℕ → ℕ),
    (∀ p ∈ l, IScr p.1) → okB W m (cps l) f
  | [], _, _ => trivial
  | (d, s) :: l, _f, h => ⟨h (d, s) List.mem_cons_self,
      okB_cps W m l _ fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

theorem iscr_sw {r : ℕ} (h1 : 240700 ≤ r) (h2 : r < 250000) : IScr r := Or.inl ⟨h1, h2⟩

theorem not_oracle_sw {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r ∉ oracleBands := by
  rw [band_sw h1 h2]; decide

/-! ## The chain of a descriptor register -/

/-- The facts a primitive needs about the chain descriptor at the address held in register
`dsc`. -/
def ChainCtx (P : Polygon) (W : ℕ) (c : Config) (dsc : ℕ) (C : Chain) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P (c.nreg ALLOC) c.nmem (c.nreg dsc) ∧
    (∃ H, ChainDescAt c.nmem (c.nreg dsc) (Qof P) H C ∧ HostRegular P.n H) ∧ C.P.Simple ∧
    2 * C.m + 7 ≤ W

/-- The chain context transported along a step that keeps the descriptor register, the memory
below the allocator, and does not lower the allocator. -/
theorem ChainCtx.transport {P : Polygon} {W : ℕ} {c c' : Config} {dsc dsc' : ℕ} {C : Chain}
    (h : ChainCtx P W c dsc C) (hr : c'.nreg dsc' = c.nreg dsc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    ChainCtx P W c' dsc' C := by
  obtain ⟨hG, hW, hwf, ⟨H, hC, hreg⟩, hP, hWm⟩ := h
  obtain ⟨hC', hwf'⟩ := chainDesc_keep hwf hC hm hA
  Ξ' ← hr at hC' hwf'
  exact ⟨hG, hW, hwf', ⟨H, hC', hreg⟩, hP, hWm⟩

/-- The primitive's precondition from the chain context, at `50200`. -/
theorem primPre_of {P : Polygon} {W : ℕ} {c : Config} {C : Chain}
    {Inp : Polygon → ℕ → Chain → Config → Prop} (h : ChainCtx P W c 50200 C) (hin : Inp P W C c) :
    PrimPre Inp P W c := by
  obtain ⟨hG, hW, hwf, ⟨H, hC, -⟩, -, -⟩ := h
  exact ⟨hG, hW, hwf, H, C, hC, hin⟩

/-- The host of a chain context is regular, at any host pointer. -/
theorem ChainCtx.hostReg {P : Polygon} {W : ℕ} {c : Config} {dsc : ℕ} {C : Chain}
    (h : ChainCtx P W c dsc C) :
    ∀ H', HostAt c.nmem (c.nmem (c.nreg dsc)) H' → HostRegular P.n H' := by
  obtain ⟨-, -, -, ⟨H, hC, hreg⟩, -, -⟩ := h
  intro H' hH'
  Ξ ← NFLoc.hostAt_unique hC.1 hH'
  exact hreg

/-! ## A generic call -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **Copy in, run a primitive, copy out.** -/
def callP (ins : List (ℕ × ℕ)) (s : Stmt) (outs : List (ℕ × ℕ)) : Stmt :=
  .seq (block (cps ins)) (.seq s (block (cps outs)))

/-- **The run step of a primitive call**: the inputs are copied to oracle registers, the
primitive meets its contract from there, and the outputs are copied to scratch registers outside
the oracle bands. -/
theorem callP_irs {ins outs : List (ℕ × ℕ)} {s : Stmt} {B' : Finset ℕ}
    {Pre : Polygon → ℕ → Config → Prop} {Post : Polygon → Config → Config → Prop} {K : ℕ}
    (hs : Meets s B' Pre Post (fun _ _ => K)) (hB : B' ⊆ oracleBands) (hI : IInv W c₀ c)
    (hin1 : (ins.map Prod.fst).Nodup) (hin2 : ∀ p ∈ ins, ∀ q ∈ ins, p.2 ≠ q.1)
    (hin3 : ∀ p ∈ ins, bandOf p.1 ∈ oracleBands)
    (hout1 : (outs.map Prod.fst).Nodup) (hout2 : ∀ p ∈ outs, ∀ q ∈ outs, p.2 ≠ q.1)
    (hout3 : ∀ p ∈ outs, 240700 ≤ p.1 ∧ p.1 < 250000)
    (hpre : ∀ c₁ : Config, c₁.nmem = c.nmem → c₁.nreg ALLOC = c.nreg ALLOC →
      (∀ p ∈ ins, c₁.nreg p.1 = c.nreg p.2) →
      (∀ r, r ∉ ins.map Prod.fst → c₁.nreg r = c.nreg r) → Pre P W c₁)
    (hroom : c.nreg ALLOC + (ins.length + K + outs.length) ≤ W) :
    IRS P W c₀ (callP ins s outs) c (ins.length + K + outs.length)
      (fun c' => ∃ c₁ c₂, c₁.nmem = c.nmem ∧ (∀ p ∈ ins, c₁.nreg p.1 = c.nreg p.2) ∧
        (∀ r, r ∉ ins.map Prod.fst → c₁.nreg r = c.nreg r) ∧ Post P c₁ c₂ ∧
        (∀ p ∈ outs, c'.nreg p.1 = c₂.nreg p.2) ∧
        (∀ r, bandOf r ∉ oracleBands → r ∉ outs.map Prod.fst → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hsc1 : ∀ p ∈ ins, IScr p.1 := fun p hp => Or.inr (hin3 p hp)
  have hsc2 : ∀ p ∈ outs, IScr p.1 := fun p hp => iscr_sw (hout3 p hp).1 (hout3 p hp).2
  refine (IRS.seq (K₂ := K + outs.length)
    (IRS.block (P := P) (cps ins) hI (okB_cps W _ ins _ hsc1)) ?_).mono
    (by rw [cps_length]; omega) (fun _ h => h)
  intro c₁ hI₁ hA₁ hA₁' hc₁
  subst hc₁
  obtain ⟨e1, e2⟩ := regB_cps c.nmem ins c.nreg hin1 hin2
  have hA1 : regB c.nmem (cps ins) c.nreg ALLOC = c.nreg ALLOC :=
    e2 ALLOC (fun h => by
      obtain ⟨p, hp, hpa⟩ := List.mem_map.1 h
      have := hin3 p hp
      Ξ' hpa at this
      exact absurd this (⌖))
  set c₁ : Config := { c with nreg := regB c.nmem (cps ins) c.nreg } with hc₁def
  have hpre₁ : Pre P W c₁ := hpre c₁ rfl hA1 e1 e2
  refine IRS.seq (IRS.callO hs hB hI₁ hpre₁ (by
    show regB c.nmem (cps ins) c.nreg ALLOC + K ≤ W
    rw [hA1]; Ξ' cps_length at hA₁'; omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hpost, -, hm₂, hk₂⟩
  refine (IRS.block (P := P) (cps outs) hI₂ (okB_cps W _ outs _ hsc2)).mono (Ρ cps_length)
    ?_
  intro c' hc'
  subst hc'
  obtain ⟨f1, f2⟩ := regB_cps c₂.nmem outs c₂.nreg hout1 hout2
  refine ⟨c₁, c₂, rfl, e1, e2, hpost, f1, fun r hr ho hra => ?_, ?_, ?_⟩
  · show regB c₂.nmem (cps outs) c₂.nreg r = c.nreg r
    Ξ f2 r ho, hk₂ r hr hra
    show regB c.nmem (cps ins) c.nreg r = c.nreg r
    exact e2 r (fun h => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact hr (hin3 p hp))
  · show c.nreg ALLOC ≤ regB c₂.nmem (cps outs) c₂.nreg ALLOC
    rw [f2 ALLOC (fun h => by
      obtain ⟨p, hp, hpa⟩ := List.mem_map.1 h
      have := hout3 p hp; Ξ' hpa at this; unfold ALLOC at this; omega)]
    have : c₁.nreg ALLOC = c.nreg ALLOC := hA1
    omega
  · intro a ha
    show c₂.nmem a = c.nmem a
    exact hm₂ a (by show a < regB c.nmem (cps ins) c.nreg ALLOC; rw [hA1]; exact ha)

end

end SweepIo

end Chazelle.Core

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem nodup2 {a b : ℕ} (h1 : a ≠ b) : [a, b].Nodup := ⊚ h1

theorem primBands_oracle : primBands ⊆ oracleBands := ⌖

theorem band5_oracle {r : ℕ} (h1 : 50000 ≤ r) (h2 : r < 60000) : bandOf r ∈ oracleBands := by
  have : bandOf r = bLocate := by unfold bandOf bLocate; omega
  rw [this]; decide

theorem nodup3 {a b d : ℕ} (h1 : a ≠ b) (h2 : a ≠ d) (h3 : b ≠ d) : [a, b, d].Nodup := by
  Θ h1, h2, h3

theorem nodup4 {a b d e : ℕ} (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ e) (h4 : b ≠ d) (h5 : b ≠ e)
    (h6 : d ≠ e) : [a, b, d, e].Nodup := by
  Θ h1, h2, h3, h4, h5, h6

/-! ## `arrivalPos` -/

/-- **The result of an arrival-position call** at registers `f, p, hc`: flag `1` and a proper
arrival position, or flag `0` and no arrival position. -/
def ArrAt (P : Polygon) (C : Chain) (e h ρ f p hc : ℕ) : Prop :=
  f ≤ 1 ∧
    (f = 1 → p < (chainModel C).W.n ∧ ProperPos (chainModel C) (Qof P) P.n ⟨p, hc⟩ ∧
      Sweep.Arrival (chainModel C).W ((chainModel C).pos (Qof P) ⟨e, h⟩) (-dirOf ρ) p
        ((chainModel C).param (Qof P) ⟨p, hc⟩)) ∧
    (f ≠ 1 → ∀ p t, ¬ Sweep.Arrival (chainModel C).W ((chainModel C).pos (Qof P) ⟨e, h⟩)
      (-dirOf ρ) p t)

/-- `arrivalPos` on the descriptor `dsc`, the position `(re, rh)`, the reversed direction code
`rd`, with the outputs in `o, o + 1, o + 2`. -/
def callArr (dsc re rh rd o : ℕ) : Stmt :=
  callP [(50200, dsc), (50201, re), (50202, rh), (50203, rd)] arrivalPos
    [(o, 50210), (o + 1, 50211), (o + 2, 50212)]

set_option maxRecDepth 20000 in
theorem callArr_irs {dsc re rh rd o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000 ∧
      240000 ≤ rd ∧ rd < 250000) (ho : 240700 ≤ o ∧ o + 2 < 250000)
    (he : c.nreg re < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg re, c.nreg rh⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨c.nreg re, c.nreg rh⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 35007 ≤ W) :
    IRS P W c₀ (callArr dsc re rh rd o) c 35007
      (fun c' => ArrAt P C (c.nreg re) (c.nreg rh) (c.nreg rd) (c'.nreg o) (c'.nreg (o + 1))
          (c'.nreg (o + 2)) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ o + 1 → r ≠ o + 2 → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(50200, dsc), (50201, re), (50202, rh), (50203, rd)])
    (outs := [(o, 50210), (o + 1, 50211), (o + 2, 50212)]) arrivalPos_meets primBands_oracle hI
    (nodup4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨band5_oracle (by norm_num) (by norm_num), band5_oracle (by norm_num) (by norm_num),
          band5_oracle (by norm_num) (by norm_num), band5_oracle (by norm_num) (by norm_num)⟩)
    (nodup3 (by omega) (by omega) (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g0, g1, g2, g3⟩ := e1
      refine primPre_of (hctx.transport g0 (fun a _ => by rw [hm]) (by rw [hA])) ?_
      refine ⟨⟨?_, ?_, ?_⟩, hctx.2.2.2.2.1, hctx.2.2.2.2.2⟩
      · rw [g1]; exact he
      · rw [g1, g2]; exact hpp
      · rw [g1, g2]; exact hy)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g0, g1, g2, g3⟩ := e1
  obtain ⟨k0, k1, k2⟩ := f1
  obtain ⟨H, hC, -⟩ := hctx.2.2.2.1
  have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 50200) (Qof P) H C := by rw [hm, g0]; exact hC
  have hres := hpost H C hC₁
  unfold ArrOut ArrRes at hres
  rw [g1, g2, g3] at hres
  obtain ⟨r1, r2, r3⟩ := hres
  refine ⟨⟨by rw [k0]; exact r1, fun hf => ?_, fun hf => ?_⟩, fun r hr h0 h1 h2 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega)
    hra, hA, hm'⟩
  · rw [k0] at hf; rw [k1, k2]; exact r2 hf
  · rw [k0] at hf; exact r3 hf

/-! ## `absKey` and `absCmp` -/

/-- An abscissa record survives a copy of its four words. -/
theorem absRec_transport {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) (h3 : c'.nreg (r' + 3) = c.nreg (r + 3)) :
    AbsRec P c' r' x R := by
  obtain ⟨hR, h⟩ := h
  refine ⟨hR, ?_⟩
  rcases h with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, hx, s, hs, hl, he⟩
  · exact Or.inl ⟨by rw [h0, k], hx⟩
  · exact Or.inr (Or.inl ⟨by rw [h0, k], hx⟩)
  · refine Or.inr (Or.inr ⟨by rw [h0, k], hx, s, ?_, hl, he⟩)
    have e2 : c'.nreg (r' + 1 + 1) = c.nreg (r + 1 + 1) := by
      rw [show r' + 1 + 1 = r' + 2 by ring, show r + 1 + 1 = r + 2 by ring]; exact h2
    have e3 : c'.nreg (r' + 1 + 2) = c.nreg (r + 1 + 2) := by
      rw [show r' + 1 + 2 = r' + 3 by ring, show r + 1 + 2 = r + 3 by ring]; exact h3
    cases s with
    | vtx i => exact ⟨by rw [h1]; exact hs.1, by rw [e2]; exact hs.2⟩
    | onEdge e k => exact ⟨by rw [h1]; exact hs.1, by rw [e2]; exact hs.2.1, by rw [e3]; exact hs.2.2⟩

/-- `absKey` on the descriptor `dsc` and the position `(re, rh)`, outputs at `o … o + 3`. -/
def callAbs (dsc re rh o : ℕ) : Stmt :=
  callP [(50200, dsc), (50201, re), (50202, rh)] absKey
    [(o, 50210), (o + 1, 50211), (o + 2, 50212), (o + 3, 50213)]

set_option maxRecDepth 20000 in
theorem callAbs_irs {dsc re rh o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000)
    (ho : 240700 ≤ o ∧ o + 3 < 250000)
    (he : c.nreg re < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg re, c.nreg rh⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨c.nreg re, c.nreg rh⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 16707 ≤ W) :
    IRS P W c₀ (callAbs dsc re rh o) c 16707
      (fun c' => AbsRec P c' o ((chainModel C).pos (Qof P) ⟨c.nreg re, c.nreg rh⟩).1 C.radius ∧
        (∀ r, bandOf r ∉ oracleBands → (r < o ∨ o + 3 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(50200, dsc), (50201, re), (50202, rh)])
    (outs := [(o, 50210), (o + 1, 50211), (o + 2, 50212), (o + 3, 50213)]) absKey_meets
    primBands_oracle hI
    (nodup3 (by norm_num) (by norm_num) (by norm_num))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨band5_oracle (by norm_num) (by norm_num), band5_oracle (by norm_num) (by norm_num),
          band5_oracle (by norm_num) (by norm_num)⟩)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g0, g1, g2⟩ := e1
      have hctx₁ := hctx.transport g0 (fun a _ => by rw [hm]) (by rw [hA])
      refine primPre_of hctx₁ ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [g1]; exact he
      · rw [g1, g2]; exact hpp
      · rw [g1, g2]; exact hy
      · rw [hm, g0]; exact hctx.hostReg)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g0, g1, g2⟩ := e1
  obtain ⟨k0, k1, k2, k3⟩ := f1
  obtain ⟨H, hC, -⟩ := hctx.2.2.2.1
  have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 50200) (Qof P) H C := by rw [hm, g0]; exact hC
  have hres := hpost H C hC₁
  unfold AbsKeyOut at hres
  rw [g1, g2] at hres
  refine ⟨absRec_transport hres k0 k1 k2 k3, fun r hr h0 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega)
    hra, hA, hm'⟩

/-- `absCmp` of the records at `a … a + 3` and `b … b + 3`, output bit at `o`. -/
def callAbsCmp (a b o : ℕ) : Stmt :=
  callP [(50201, a), (50202, a + 1), (50203, a + 2), (50204, a + 3), (50205, b),
    (50206, b + 1), (50207, b + 2), (50208, b + 3)] absCmp [(o, 50210)]

set_option maxRecDepth 20000 in
theorem callAbsCmp_irs {a b o : ℕ} (hI : IInv W c₀ c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (hr : 240000 ≤ a ∧ a + 3 < 250000 ∧ 240000 ≤ b ∧ b + 3 < 250000)
    (ho : 240700 ≤ o ∧ o < 250000) {x₁ x₂ R : ℝ} (h₁ : AbsRec P c a x₁ R)
    (h₂ : AbsRec P c b x₂ R) (hroom : c.nreg ALLOC + 269 ≤ W) :
    IRS P W c₀ (callAbsCmp a b o) c 269
      (fun c' => BitIs c' o (x₁ < x₂) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hb : ∀ r, 50201 ≤ r → r ≤ 50208 → bandOf r ∈ oracleBands := fun r h1 h2 =>
    band5_oracle (by omega) (by omega)
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(50201, a), (50202, a + 1), (50203, a + 2), (50204, a + 3), (50205, b),
      (50206, b + 1), (50207, b + 2), (50208, b + 3)])
    (outs := [(o, 50210)]) absCmp_meets primBands_oracle hI
    (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hb _ le_rfl (by norm_num), hb _ (by norm_num) (by norm_num),
          hb _ (by norm_num) (by norm_num), hb _ (by norm_num) (by norm_num),
          hb _ (by norm_num) (by norm_num), hb _ (by norm_num) (by norm_num),
          hb _ (by norm_num) (by norm_num), hb _ (by norm_num) le_rfl⟩)
    (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := e1
      exact ⟨hG, hW, x₁, x₂, R, absRec_transport h₁ g1 g2 g3 g4,
        absRec_transport h₂ g5 g6 g7 g8⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := e1
  have hres := hpost x₁ x₂ R (absRec_transport h₁ g1 g2 g3 g4) (absRec_transport h₂ g5 g6 g7 g8)
  refine ⟨BitIs.of_eq hres f1, fun r hr h0 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega)
    hra, hA, hm'⟩

/-! ## `offCmp` -/

/-- `offCmp` on the descriptor `dsc`, the positions `(ex, hx)`, `(ey, hy)` and the base `g`,
output bits at `o`, `o + 1`. -/
def callOff (dsc ex hx ey hy g o : ℕ) : Stmt :=
  callP [(50200, dsc), (50201, ex), (50202, hx), (50203, ey), (50204, hy), (50205, g)] offCmp
    [(o, 50210), (o + 1, 50211)]

set_option maxRecDepth 20000 in
theorem callOff_irs {dsc ex hx ey hy g o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ ex ∧ ex < 250000 ∧ 240000 ≤ hx ∧ hx < 250000 ∧
      240000 ≤ ey ∧ ey < 250000 ∧ 240000 ≤ hy ∧ hy < 250000 ∧ 240000 ≤ g ∧ g < 250000)
    (ho : 240700 ≤ o ∧ o + 1 < 250000)
    (hex : c.nreg ex < (chainModel C).W.n) (hey : c.nreg ey < (chainModel C).W.n)
    (hg : c.nreg g < (chainModel C).W.n)
    (hpx : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg ex, c.nreg hx⟩)
    (hpy : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg ey, c.nreg hy⟩)
    (h6x : c.nreg hx = 0 → 6 ≤ c.nreg ex) (h6y : c.nreg hy = 0 → 6 ≤ c.nreg ey)
    (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ (callOff dsc ex hx ey hy g o) c 11008
      (fun c' =>
        BitIs c' o (off (chainModel C).W.n (c.nreg g)
            ((chainModel C).key (Qof P) ⟨c.nreg ex, c.nreg hx⟩) <
          off (chainModel C).W.n (c.nreg g) ((chainModel C).key (Qof P) ⟨c.nreg ey, c.nreg hy⟩)) ∧
        BitIs c' (o + 1) (off (chainModel C).W.n (c.nreg g)
            ((chainModel C).key (Qof P) ⟨c.nreg ey, c.nreg hy⟩) <
          off (chainModel C).W.n (c.nreg g) ((chainModel C).key (Qof P) ⟨c.nreg ex, c.nreg hx⟩)) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ o + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hb : ∀ r, 50200 ≤ r → r ≤ 50205 → bandOf r ∈ oracleBands := fun r h1 h2 =>
    band5_oracle (by omega) (by omega)
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [(50200, dsc), (50201, ex), (50202, hx), (50203, ey), (50204, hy), (50205, g)])
    (outs := [(o, 50210), (o + 1, 50211)]) offCmp_meets primBands_oracle hI
    (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hb _ le_rfl (by norm_num), hb _ (by norm_num) (by norm_num),
          hb _ (by norm_num) (by norm_num), hb _ (by norm_num) (by norm_num),
          hb _ (by norm_num) (by norm_num), hb _ (by norm_num) le_rfl⟩)
    (nodup2 (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (fun c₁ hm hA e1 e2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1
      obtain ⟨g0, g1, g2, g3, g4, g5⟩ := e1
      have hctx₁ := hctx.transport g0 (fun a _ => by rw [hm]) (by rw [hA])
      refine primPre_of hctx₁ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hctx.2.2.2.2.2⟩
      · rw [g1]; exact hex
      · rw [g3]; exact hey
      · rw [g5]; exact hg
      · rw [g1, g2]; exact hpx
      · rw [g3, g4]; exact hpy
      · rw [g1, g2]; exact h6x
      · rw [g3, g4]; exact h6y)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine h.mono (by simp) ?_
  rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := e1
  obtain ⟨k0, k1⟩ := f1
  obtain ⟨H, hC, -⟩ := hctx.2.2.2.1
  have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 50200) (Qof P) H C := by rw [hm, g0]; exact hC
  have hres := hpost H C hC₁
  unfold OffOut at hres
  simp only [g1, g2, g3, g4, g5] at hres
  refine ⟨BitIs.of_eq hres.1 k0, BitIs.of_eq hres.2 k1, fun r hr h0 h1 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]; omega)
    hra, hA, hm'⟩

end

end SweepIo

end Chazelle.Core
