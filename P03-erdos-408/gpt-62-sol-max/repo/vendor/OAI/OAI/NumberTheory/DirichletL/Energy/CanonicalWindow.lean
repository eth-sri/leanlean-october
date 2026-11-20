module

public import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

namespace OAI.SevenEighths

open scoped ContDiff

/-- Window parameters common to the canonical main and error energy estimates. -/
structure CanonicalEnergyWindow (α : Type*) where
  Wslot : ℝ→ℂ
  aslot : ℝ
  bslot : ℝ
  Mcap : ℝ
  Lslot : ℝ
  εremove : ℝ
  lo : ℝ
  hi : ℝ
  κ : ℝ
  a : ℝ
  b : ℝ
  Mslot : ℝ
  εmask : ℝ
  hMslot : 0≤Mslot
  hεmask : 0<εmask
  haPlain : 0<a
  hbPlain : 0≤b
  L : ℝ
  hL : 0≤L
  degree : ℕ
  S : Finset (ℕ×ℕ)
  ha : 0<aslot
  hWs : Function.support Wslot⊆Set.Icc aslot bslot
  hW : ContDiff ℝ ∞ Wslot
  hMcap : 0≤Mcap
  hLs : 0≤Lslot
  hε : 0<εremove
  hκsmall : (1/6:ℝ)≤κ
  hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta
  hκ : 2*HeckeZeroSupremum.beta-1≤κ
  N : ℕ
  lower : ℝ
  upper : ℝ
  a0 : ℝ
  θsource : ℝ
  hlower : 0<lower
  hupper : 1≤upper
  ha0 : 0<a0
  hθsource : 0<θsource
  lows : α→ℝ
  highs : α→ℝ
  hhighs : ∀i,0≤highs i

/-- Restrict the source endpoint data to a choice of slots. -/
def CanonicalEnergyWindow.reindex {α γ : Type*} (cfg : CanonicalEnergyWindow α) (f : γ → α) :
    CanonicalEnergyWindow γ :=
  { cfg with
    lows := cfg.lows ∘ f
    highs := cfg.highs ∘ f
    hhighs := fun i => cfg.hhighs (f i) }

/-- The part of the scale loss independent of the column's moving conductor. -/
noncomputable abbrev CanonicalEnergyWindow.paidLoss {α : Type*} (cfg : CanonicalEnergyWindow α)
    (Bcap εchild δ reserve θclip mesh : ℝ) : ℝ :=
  (Bcap+Bcap)*cfg.εmask+εchild+cfg.εremove+(δ+reserve+cfg.θsource)/6+θclip/3+cfg.κ*mesh

end OAI.SevenEighths
