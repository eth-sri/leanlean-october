module

public import QPBT.Palomar.Main
import QPBT.Algebra.FieldBasis
import QPBT.Algebra.Pauli
import QPBT.Combining.Defs
import QPBT.Combining.DirectLowDegreeCore
import QPBT.Combining.DirectLowDegree
import QPBT.Combining.Apply
import QPBT.Combining.ErrorBounds
import QPBT.Combining.Witnesses
import QPBT.Combining.Lines
import QPBT.Combining.Points
import QPBT.Combining.ExtendedLines
import QPBT.Extraction
import QPBT.Games.CondLinear
import QPBT.Games.Defs
import QPBT.Games.DistanceTheorems.ProjectiveRounding
import QPBT.Games.DistanceTheorems.Support
import QPBT.Games.DistanceTheorems.TensorSupport
import QPBT.Games.MeasurementCompression
import QPBT.Games.Sandwich.Defs
import QPBT.Games.StrategyClasses
import QPBT.Observables.Anticommuting
import QPBT.Observables.Defs
import QPBT.Observables.ExpandedDefs
import QPBT.Observables.LineDefs
import QPBT.Observables.LineMeasurement
import QPBT.Observables.LineMeasurement.Expanded
import QPBT.Observables.LineMeasurement.Projector
import QPBT.Observables.PointConsistency
import QPBT.Observables.WinImplications.Approx
import QPBT.Observables.WinImplications.ApproxLines
import QPBT.Observables.WinImplications.Averages
import QPBT.Observables.WinImplications.CommutingObs
import QPBT.Observables.WinImplications.InterchangedCommutation
import QPBT.Observables.WinImplications.LowDegree
import QPBT.Observables.WinImplications.PointObs
import QPBT.Observables.WinImplications.Setup
import QPBT.Observables.WinImplications.TwistedCommutation
import QPBT.Palomar.Definitions
import QPBT.Palomar.Main
import QPBT.Test.Completeness
import QPBT.Test.LowDegreeGame
import QPBT.Test.LowDegreeGameMeasurements
import QPBT.Test.MagicSquare
import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Measurements
import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget
import QPBT.Test.MagicSquareTheorems.Rigidity.Relations
import QPBT.Test.PauliBasisTest
import QPBT.Test.Soundness
import QPBT.Test.SoundnessDefs

/-! # Verified quantum Pauli basis test results

The Solution supplies the four registered theorems and the fixed-field construction.
The imported axiom audit fails the build if any registered result uses an unexpected axiom.
-/
