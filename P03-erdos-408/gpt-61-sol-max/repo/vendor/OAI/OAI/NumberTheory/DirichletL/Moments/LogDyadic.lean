module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization
public import OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simp_all [logAnnulus]
  have hlo : 1/4<Real.exp x := lt_of_not_ge (fun h=>hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=>hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro CompactIccSpace.isCompact_Icc fun x hx => Decidable.byContradiction fun hn => hx (OAI.SevenEighths.CenteredMomentLogDyadic.logAnnulus_support hn)

theorem logAnnulus_norm  x  : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

theorem logAnnulus_log  q H  (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window  n   q  (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp_all [actual_dyadic_log_window, windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
