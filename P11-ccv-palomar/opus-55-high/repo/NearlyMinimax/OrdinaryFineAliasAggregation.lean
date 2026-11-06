module

public import NearlyMinimax.OrdinaryFineAliasSpatialEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Finite aggregation of the genuine all-count ordinary fine aliases.
The source's actual target scales and rounded saddle supply the guards. -/
𝛅
open scoped BigOperators Topology
𝚨
𝚩
𝚭
𝚬

def ordinaryFineAliasTargetSet (d D : ℕ) (L N mu : ℝ) : Finset ℕ :=
  (Finset.range $ D+1 ).filter fun r => 3 ≤ r ∧ L < higherBandTargetScale d r N mu

def ordinaryFineAliasFamilyRawAction (I : Finset ℕ)
    (ad bd lam L : ℝ) (T : 𝙜) (M q : ℕ) (C a V eta : ℝ)
    (U : 𝙇) (p g w : 𝙔)
    (c : 𝖲) (y : 𝙈) : ℝ :=
  ∑ r ∈ I, ordinaryFineAliasRawAction ad bd lam L (T r) M r q C a V eta U p g w c y

𝗃 𝔎 ἀ d q R ad bd c0 C a rho
def ordinaryAliasFamilySpatialPrefactor (d q R : ℕ) (ad bd c0 C a rho : ℝ) : ℝ :=
  ((R+1 : ℕ) : ℝ)^2 * 𝔎 ordinaryAliasSpatialPrefactor

theorem ordinaryAliasFamilySpatialPrefactor_nonneg d q R ad bd c0 C a rho :
    0 ≤ 𝔎 ordinaryAliasFamilySpatialPrefactor :=
  𝖧₁ $ ordinaryAliasSpatialPrefactor_nonneg ..

𝗇 𝔊 densityIntervalExponent ad bd
𝗇 𝔄 lowerSaddleCoefficient s d 𝔊
𝗇 𝔅 lowerSaddleTheta s d 𝔊
𝗇 𝔇 𝔊+1
𝗇 𝔈 shrunkDensityExponent ad bd
𝗇 𝔉 lowerSaddleN s d 𝔄 𝔅 Cw 𝔈 x
𝗇 𝔍 lowerAliasCutoff s d 𝔄 𝔅 Cw 𝔇 𝔈 x
/-- Numerical guards for the actual canonical fine-alias scale. -/
structure OrdinaryFineAliasSaddleGuards (s : ℝ) (d : ℕ) (ad bd Cw x : ℝ) : Prop where
  dimension : 𝘚
  degree : (lowerSaddleD d 𝔄 x : ℝ) ≤
    ((𝙊+8)/4+1)*(lowerSaddleM 𝔄 x : ℝ)
  cutoff : 1 ≤ 𝔍
  logarithm : Real.log (1+Real.log 𝔉) ≤
      lowerSaddleM 𝔄 x
  targets : ∀ r ∈ ordinaryFineAliasTargetSet d
    (lowerSaddleD d 𝔄 x)
    𝔍
    𝔉
    $ lowerSaddleMu d 𝔄
      𝔅 Cw x ,
    𝘠₁ ∧ r ≤ lowerAliasFineTargetBound d
      𝔅 𝔇

/-- All guards come from the canonical rounded saddle and actual shrunk
endpoints, with a fixed number of fine targets before count/spatial tuples. -/
theorem eventually_ordinaryFineAlias_saddle_guards {s ad bd : ℝ} {d : ℕ}
    (hs : 𝚊₁) (hd : 𝚄 < d) (haD : 𝖼) (hab : 𝖽) Cw :
    ∀ᶠ x in atTop, OrdinaryFineAliasSaddleGuards s d ad bd Cw x := by
  let tau := 𝔊
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd $ densityIntervalExponent_pos haD hab
  have hM := lowerSaddleM_tendsto_atTop hm
  filter_upwards [actual_lowerAlias_hierarchy hs hd haD hab (Cact := 1) (Cs := 1)
       𝖠₄   𝖠₄  Cw,
    hM.eventually $ eventually_ge_atTop 1 ] with x hh hM1
  rcases hh with ⟨hell,_,_hbase,hlog,_hgap,_hq21,_hq1,_hDq,_hco,_hsingle,_hRM,hactive⟩
  have hd5 : 𝘚 := by
    have h : 𝗦<d := 𝖡₄
    aesop
  refine ⟨hd5, lowerSaddleD_le_fixed_linear  𝖡₄  hM1, hell.le, hlog, ?_⟩
  intro r hr
  have hrmem := (Finset.mem_filter.mp hr).2
  bound
