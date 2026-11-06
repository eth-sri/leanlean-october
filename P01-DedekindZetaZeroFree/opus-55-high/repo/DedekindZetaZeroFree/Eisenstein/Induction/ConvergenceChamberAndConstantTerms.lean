module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPEisensteinChamber

open MeasureTheory KPGlobalEisensteinData

def chamber : Set ℂ := {s | (1 / 3 : ℝ) < s.re}
