module

import Solution

/-! Run this file with `lake env lean AxiomReport.lean` after building
`Solution`. Missing names are errors. These reports concern the proof
declarations, so the specification-only Challenge is never imported here. -/

#print axioms Density.euclidean
#print axioms Density.integerLp
#print axioms Density.nonEuclideanLp
