import GradedNear.Builder
import GradedNear.BurgessReduction
import GradedNear.Cert.Bins
import GradedNear.Cert.Sound
import GradedNear.Conj
import GradedNear.Entry
import GradedNear.Interval.Sound
import GradedNear.Parabolic
import GradedNear.Response
import GradedNear.Row
import GradedNear.Row.CheckSound
import GradedNear.Statement
import GradedNear.ZeroForm
import IntervalCore
import LeafNumCore

/-!
# The graded near lemma and the leaf-certificate checker (Palomar Solution)

The compared theorems (see `comparator.json`) are proved in the library:
* `GradedNear.graded_near_lemma`: `GradedNear/Analytic.lean`;
* `GradedNear.response_lemma`: `GradedNear/Response.lean`;
* `GradedNear.graded_near_threshold`: `GradedNear/Analytic.lean`;
* `GradedNear.keptBound_single`, `GradedNear.keptBound_pair` and
  `GradedNear.single_zero_threshold`: `GradedNear/Analytic.lean`;
* `GradedNear.Cert.near_row_of_bins`: `GradedNear/Cert/Bins.lean`;
* `GradedNear.Cert.checkLeaf_sound`, `GradedNear.Cert.checkLeaf_lt` and
  `GradedNear.Cert.certified`: `GradedNear/Cert/Sound.lean`, with the row relaxations in
  `GradedNear/Cert/Relax.lean`.
-/
