/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.Instances.Complex
/-! # Continuing a local charge identity along a connected complex neighborhood -/
public section
open Filter Topology Set
namespace DOZZ.Proofs
/-- A local equality of meromorphic functions continues to every regular point of a connected domain. -/
theorem roots_eq_of_meromorphic_continuation V (hV : IsPreconnected V)
    (f g : ℂ → ℂ) (hf : MeromorphicOn f V) (hg : MeromorphicOn g V)
    a b (ha : a ∈ V) (hb : b ∈ V) (he : f =ᶠ[nhds a] g)
    (hfc : ContinuousAt f b) (hgc : ContinuousAt g b) : f b = g b := by
  have horder := meromorphicOrderAt_eq_top_iff.mpr ((he.filter_mono nhdsWithin_le_nhds).mono fun z hz => sub_eq_zero.mpr hz)
  have horderb := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hV ha hb horder
  have heqb : (fun z => f z - g z) =ᶠ[nhdsWithin b {b}ᶜ] (fun _ => (0 : ℂ)) := (meromorphicOrderAt_eq_top_iff.mp horderb)
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((hfc.sub hgc).tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heqb.symm))
end DOZZ.Proofs
