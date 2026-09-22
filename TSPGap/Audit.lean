/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic
import TSPGap.AxiomCheck
import TSPGap.SongLayered
import TSPGap.SongLargeBundle
import TSPGap.SongMarginalShift
import TSPGap.SongPairedTables
import TSPGap.SongPairedInputs
import TSPGap.SongPairedPrefix
import TSPGap.SongPairedStart
import TSPGap.SongPairedProfiles
import TSPGap.SongWindowKernel
import TSPGap.SongOriginalRanks
import TSPGap.SongWindowReuse
import TSPGap.SongWindowTransfers
import TSPGap.SongWindowMeans
import TSPGap.SongWindowTails
import TSPGap.SongWindowGeometry
import TSPGap.SongWindowFace
import TSPGap.SongWindowInputs
import TSPGap.SongWindowBridge
import TSPGap.SongWindowAssembly
import TSPGap.ThreeCountZero
import TSPGap.SongPairedWindow
import TSPGap.SongPairedCapacity
import TSPGap.SongPairedHappy
import TSPGap.SongPairedProbability
import TSPGap.SongPairedBundle
import TSPGap.SongRefinedPaired
import TSPGap.TreeDist
import TSPGap.Uncrossing
import TSPGap.RestrictedLP
import TSPGap.Polygon
import TSPGap.BlackBoxes
import TSPGap.ExcludedCycles
import TSPGap.ExcludedCombs
import TSPGap.PolygonConfigurations
import TSPGap.CircularOnes
import TSPGap.TuckerMatrices
import TSPGap.TuckerSufficiency
import TSPGap.TuckerReduction
import TSPGap.TuckerIncidenceGraph
import TSPGap.TuckerArrangement
import TSPGap.TuckerArrangementCore
import TSPGap.TuckerRotation
import TSPGap.TuckerTheorem6
import TSPGap.TuckerForbidden
import TSPGap.TuckerTheorem7
import TSPGap.TuckerTwins
import TSPGap.TuckerInducedCycles
import TSPGap.InsideAtoms
import TSPGap.Components
import TSPGap.BadEvents
import TSPGap.MainTheorem
import TSPGap.PolygonFamily
import TSPGap.Theorem52
import TSPGap.Tour
import TSPGap.Euler
import TSPGap.OJoin
import TSPGap.TreePolytope
import TSPGap.GraphRank
import TSPGap.KruskalTree
import TSPGap.EdmondsTree
import TSPGap.ExpFamilyLimit
import TSPGap.MaxEntropyExistence
import TSPGap.ScaledMarginals
import TSPGap.MultiGraph
import TSPGap.MultiGraphWalks
import TSPGap.MultiGraphContract
import TSPGap.SeymourTheorem
import TSPGap.SubdivisionPacking
import TSPGap.EdmondsJoin
import TSPGap.BernoulliCount
import TSPGap.BinomialPoisson
import TSPGap.Split
import TSPGap.OneSideLaminar
import TSPGap.PolygonInterval
import TSPGap.PolygonReflect
import TSPGap.OneSideHierarchy
import TSPGap.OneSidePair
import TSPGap.OneSideStructure
import TSPGap.OneSideAtoms
import TSPGap.NearCycle
import TSPGap.Leaves
import TSPGap.TheoremB3
import TSPGap.HierarchyExistence
import TSPGap.Theorem61
import TSPGap.MaxEntropyLimit
import TSPGap.Stable
import TSPGap.StableLimit
import TSPGap.HalfPlanePoles
import TSPGap.HalfPlaneRational
import TSPGap.HalfPlanePartialFractions
import TSPGap.HalfPlaneResidues
import TSPGap.StableLogDerivative
import TSPGap.CapacityProfiles
import TSPGap.ResidueBasis
import TSPGap.ResidueMatrix
import TSPGap.HomogeneousLine
import TSPGap.HomogeneousProductization
import TSPGap.NonnegativeEndpoint
import TSPGap.CapacityMatrix
import TSPGap.CapacitySupportReduction
import TSPGap.CapacitySupportRank
import TSPGap.CapacityLeaves
import TSPGap.RigidProductization
import TSPGap.CapacityRestriction
import TSPGap.CapacityZeroColumn
import TSPGap.CapacityLeafColumn
import TSPGap.CapacityRemoval
import TSPGap.CapacityActive
import TSPGap.CapacityFactors
import TSPGap.CapacitySpectator
import TSPGap.CapacityInduction
import TSPGap.CapacityBound
import TSPGap.UnivariateCapacity
import TSPGap.HomogeneousCapacitySlice
import TSPGap.CountProjection
import TSPGap.CountProjectionStable
import TSPGap.CountCapacityExtraction
import TSPGap.ThreeCountCapacity
import TSPGap.GroupedCountPolynomial
import TSPGap.ThreeBlockPolynomial
import TSPGap.ThreeMeanCapacity
import TSPGap.Lemma2122Capacity
import TSPGap.Lemma523Budget
import TSPGap.RefinedLemma523Budget
import TSPGap.Fact28
import TSPGap.Determinant
import TSPGap.CauchyBinet
import TSPGap.Incidence
import TSPGap.TreeStability
import TSPGap.Rayleigh
import TSPGap.RayleighCondition
import TSPGap.FederMihail
import TSPGap.RankSequence
import TSPGap.FaceStability
import TSPGap.TreeFace
import TSPGap.MarkerStability
import TSPGap.ProjectedLayers
import TSPGap.AdjacentLayers
import TSPGap.LayerTails
import TSPGap.LogConcave
import TSPGap.ThreeCell
import TSPGap.Conditioning
import TSPGap.CountEstimates
import TSPGap.CountDeficit
import TSPGap.Lemma57
import TSPGap.CutRepair
import TSPGap.Flow
import TSPGap.Selected
import TSPGap.Prop56
import TSPGap.Coupling
import TSPGap.Lemma226
import TSPGap.TreeExchange
import TSPGap.Lemma227
import TSPGap.AtomPath
import TSPGap.BundleProjection
import TSPGap.Lemma227Bundle
import TSPGap.MaxFace
import TSPGap.ThreeAtomFace
import TSPGap.BundleSetup
import TSPGap.TwoAtomFace
import TSPGap.LemmaA1Cells
import TSPGap.Lemma517Counts
import TSPGap.Lemma517
import TSPGap.Lemma523
import TSPGap.LemmaA1
import TSPGap.LemmaA1Tails
import TSPGap.LemmaA1Kernel
import TSPGap.LemmaA1KernelBudget
import TSPGap.LemmaA1Conditioning
import TSPGap.LemmaA1Package
import TSPGap.LemmaA1Transfer
import TSPGap.Lemma515
import TSPGap.LemmaA1Assembly
import TSPGap.TreeDistBridge
import TSPGap.TreeDistSetup
import TSPGap.TreeDistInstances
import TSPGap.Theorem528Defs
import TSPGap.Theorem528
import TSPGap.Lemma525
import TSPGap.MatchingInputs
import TSPGap.Lemma516
import TSPGap.Lemma62
import TSPGap.PaymentDefs
import TSPGap.HappyEvents
import TSPGap.DegreePartitionExists
import TSPGap.EdgeRefinement
import TSPGap.RefinementLift
import TSPGap.FiberTreeModel
import TSPGap.FiberTreeSupport
import TSPGap.FiberTreeFaces
import TSPGap.Lemma521Indexed
import TSPGap.Lemma522Indexed
-- Retained tail proofs are no longer imported by the capacity-based 5.22 route.
import TSPGap.PoissonTailSharp
import TSPGap.Lemma522PointMass
import TSPGap.Lemma522UpperTail
import TSPGap.Lemma522KernelSharp
import TSPGap.LemmaA1Indexed
import TSPGap.Lemma524Indexed
import TSPGap.Lemma527Indexed
import TSPGap.Lemma523Indexed
import TSPGap.RefinementStability
import TSPGap.RefinedDegreePartition
import TSPGap.RefinedDescendants
import TSPGap.RefinedLawData
import TSPGap.Fact28Functional
import TSPGap.RefinedTreeCondIndep
import TSPGap.RefinedCondIndepTransport
import TSPGap.RefinedTreeFace
import TSPGap.RefinedTreeFaceIndep
import TSPGap.RefinedPaymentTransport
import TSPGap.RefinedHappyEvents
import TSPGap.RefinedSection5Setup
import TSPGap.RefinedLemma521
import TSPGap.RefinedLemma522
import TSPGap.RefinedLemmaA1
import TSPGap.RefinedLemma524
import TSPGap.RefinedLemma527
import TSPGap.Lemma527GurvitsInstances
import TSPGap.RefinedTheorem528
import TSPGap.RefinedLemma525
import TSPGap.RefinedTopThinnings
import TSPGap.RefinedRectangularTransfer
import TSPGap.RefinedClaim75
import TSPGap.RefinedNestedRectangular
import TSPGap.RefinedClaim74
import TSPGap.RefinedReductionData
import TSPGap.RefinedLemmaSevenThreeConsumer
import TSPGap.ReductionCertificate
import TSPGap.RefinedReductionPush
import TSPGap.RefinedPaymentEndpoint
import TSPGap.RefinedPolygonCompatibility
import TSPGap.RefinedPolygonTopCases
import TSPGap.PolygonIncrease
import TSPGap.RefinedLemma78
import TSPGap.PolygonIncreaseBottom
import TSPGap.RefinedLemma77
import TSPGap.Lemma710
import TSPGap.Lemma79
import TSPGap.Lemma711
import TSPGap.Lemma77
import TSPGap.PresentationCompatibility
import TSPGap.MainPaymentExistence
import TSPGap.RefinedLemma523
import TSPGap.ReductionData
import TSPGap.TopIncreaseSetup
import TSPGap.SlackVector
import TSPGap.PaymentProperties
import TSPGap.NearCycleProperty
import TSPGap.SlackExpectation
import TSPGap.TopThinningsExists
import TSPGap.MainPaymentCore
import TSPGap.PolygonEvent
import TSPGap.PolygonIndep
import TSPGap.EvenCount
import TSPGap.Observation432
import TSPGap.Corollary510
import TSPGap.Corollary511
import TSPGap.BottomGuarantees
import TSPGap.RectangularTransfer
import TSPGap.Claim75
import TSPGap.Claim74
import TSPGap.ReductionCertificates
import TSPGap.AncestorLayers
import TSPGap.LemmaSevenThreeArith
import TSPGap.LemmaSevenThreeConsumer
import TSPGap.Lemma76
import TSPGap.NestedRectangular
import TSPGap.OddCount
import TSPGap.Lemma2122Tails
import TSPGap.Lemma2122Kernel
import TSPGap.LawPackage
import TSPGap.Lemma521
import TSPGap.BernoulliRecursion
import TSPGap.Lemma522
import TSPGap.Lemma2122Instances
import TSPGap.Lemma524Independence
import TSPGap.Lemma524Kernel
import TSPGap.Lemma524Assembly
import TSPGap.Lemma527Tools
import TSPGap.RankTail
import TSPGap.ClaimA2
import TSPGap.ConcentratedMean
import TSPGap.Lemma527Core
import TSPGap.Lemma527Generic
import TSPGap.Lemma527BudgetCore
import TSPGap.CountConcentration
import TSPGap.Lemma527Absent
import TSPGap.Lemma527Setup
import TSPGap.Lemma527Present
import TSPGap.Lemma527
import TSPGap.Statement
import TSPGap.EndToEnd
import TSPGap.Bernoulli
import TSPGap.Hoeffding
import TSPGap.Poisson
import TSPGap.SongBadIncidentKernel
import TSPGap.SongRefinedBadIncident
import TSPGap.SongRefinedGoodness
import TSPGap.SongMatching
import TSPGap.SongRefinedSmallBundle
import TSPGap.SongRefinedHalfBundle
import TSPGap.SongRefinedWindow
import TSPGap.SongRefinedTheorem528
import TSPGap.SongBottomGuarantees
import TSPGap.SongTopThinnings
import TSPGap.BundleTopThinningDensity
import TSPGap.SongReductionData
import TSPGap.SongAncestorMass
import TSPGap.BundleReductionProjection
import TSPGap.SongAncestorEstimate
import TSPGap.BundleTopIncrease
import TSPGap.SongTopPaymentGeometry
import TSPGap.SongTopEndpoints
import TSPGap.SongTopPayment
import TSPGap.BundlePolygonReduction
import TSPGap.BundlePolygonTopCases
import TSPGap.BundlePolygonIncrease
import TSPGap.PolygonInteriorPaymentProbability
import TSPGap.SongPolygonBoundaryProbability
import TSPGap.BundlePolygonDegreePayment
import TSPGap.SongPolygonPayment
import TSPGap.SongBottomArithmetic
import TSPGap.SongBottomPayment
import TSPGap.BundleGoodEdges
import TSPGap.BundleSlackVector
import TSPGap.BundleDegreePayment
import TSPGap.BundleNearCyclePayment
import TSPGap.SongGlobalPayment
import TSPGap.JointBadEvents
import TSPGap.TwoSideRepair
import TSPGap.OneSideRepair
import TSPGap.SeparatedRepair
import TSPGap.SongPaymentExistence
import TSPGap.SongThresholdWeights
import TSPGap.SongThresholdSlack
import TSPGap.SongLayeredExistence
import TSPGap.RandomJoinTour
import TSPGap.LayeredTour
import TSPGap.SongEndToEnd

/-!
# Enforced axiom audit

Every declaration listed below is checked for transitive dependence on
only `propext`, `Classical.choice` and `Quot.sound`. The inventory contains
2,530 checks of 2,510 distinct declarations. An additional axiom, an
admitted proof or a missing declaration makes the build fail.

For a printed report on a particular result, use `#print axioms` in a
Lean file importing `TSPGap`. The public endpoint footprints are also
checked exactly in `TSPGapChecks.lean`.
-/

#check_tsp_axioms TSPGap.kko_gap
#check_tsp_axioms TSPGap.Bernoulli.evenMass_eq
#check_tsp_axioms TSPGap.Bernoulli.evenMass_le
#check_tsp_axioms TSPGap.Bernoulli.evenMass_le_of_sum_le
#check_tsp_axioms TSPGap.Bernoulli.exp_neg_le_prod_mul_pow
#check_tsp_axioms TSPGap.Bernoulli.logConcave_tail_sum_le
#check_tsp_axioms TSPGap.Bernoulli.logConcave_tail_weighted_sum_le
#check_tsp_axioms TSPGap.Bernoulli.logConcave_mean_est
#check_tsp_axioms TSPGap.Bernoulli.exists_min_three_valued
#check_tsp_axioms TSPGap.Bernoulli.exists_max_three_valued
#check_tsp_axioms TSPGap.Bernoulli.exp_neg_le_prod_mul_rpow
#check_tsp_axioms TSPGap.Bernoulli.poi_mul_le_choose_mul
#check_tsp_axioms TSPGap.Bernoulli.poi_le_probCount
#check_tsp_axioms TSPGap.Bernoulli.sum_probCount_add_probGE
#check_tsp_axioms TSPGap.Bernoulli.poi_tail_le_probGE

-- The two scaled-marginal exports (2026-09-11), the former boxes
-- `edmonds_spanningTree_polytope` and `maxEntropy_exists`: the scaled subtour-LP point in
-- Edmonds' spanning-tree polytope (the full vertex set is the equality case), and the
-- max-entropy marginals from the generic Gibbs-limit theorem through the finite-sum estimate.
#check_tsp_axioms TSPGap.scaled_inTreePolytope
#check_tsp_axioms TSPGap.edmonds_spanningTree_polytope
#check_tsp_axioms TSPGap.abs_marginal_sub_le
#check_tsp_axioms TSPGap.partitionFn_eq_of_isLambdaUniform
#check_tsp_axioms TSPGap.exists_maxEntropyLimit
#check_tsp_axioms TSPGap.maxEntropy_exists

/-! ### Acceptance: every declaration formerly admitted in `BlackBoxes.lean`

The nine statements that file ever declared as black boxes, in the order they were
discharged.  Eight are theorems now and must report only the three standard axioms; the
ninth, KKO22 Lemma 4.30, is **not** listed because it was retired rather than proved — it had
no consumer (the second half of Corollary 5.8 is `arrowLeft_disjoint_arrowRight`, listed
above and axiom-clean) and its transcription had dropped the paper's positive-area
hypothesis.  Together with the `sorry` scan in this file's header, this block is the
repository-wide milestone: **no admitted statement remains anywhere.** -/
#check_tsp_axioms TSPGap.kCycle_two_div_le                        -- KKO22 Lem 4.19 (2026-09-06)
#check_tsp_axioms TSPGap.polygonRep_exists                        -- BG polygon rep (2026-09-08)
#check_tsp_axioms TSPGap.eq_of_outsideIn_eq                       -- KKO22 Lem 4.23 (2026-09-09)
#check_tsp_axioms TSPGap.cross_arc_of_almostDiagonal              -- KKO22 Fact 4.26 (2026-09-09)
#check_tsp_axioms TSPGap.edmondsJohnson_ojoin                     -- KKO22 Prop 2.4 (2026-09-10)
#check_tsp_axioms TSPGap.binomial_lowerTail_le_shifted_poisson    -- Hoe56 Thm 4 (2026-09-11)
#check_tsp_axioms TSPGap.edmonds_spanningTree_polytope            -- KKO22 Fact 2.2 (2026-09-11)
#check_tsp_axioms TSPGap.maxEntropy_exists                        -- KKO22 Thm 2.1 (2026-09-11)
#check_tsp_axioms TSPGap.TreeDist.expectedCard_eq_sum
#check_tsp_axioms TSPGap.TreeDist.probEvent_meets_le_sum
#check_tsp_axioms TSPGap.TreeDist.probEvent_or_le
#check_tsp_axioms TSPGap.TreeDist.probEvent_not
#check_tsp_axioms TSPGap.TreeDist.prob_badEvent_le
#check_tsp_axioms TSPGap.TreeDist.prob_badEvent_le_of_mass
#check_tsp_axioms TSPGap.nearMinCut_inter
#check_tsp_axioms TSPGap.nearMinCut_union
#check_tsp_axioms TSPGap.nearMinCut_sdiff
#check_tsp_axioms TSPGap.one_sub_half_le_pairSum_inter_sdiff
#check_tsp_axioms TSPGap.one_sub_half_le_pairSum_sdiff_compl
#check_tsp_axioms TSPGap.pairSum_le_of_subset
#check_tsp_axioms TSPGap.le_pairSum_of_subset
#check_tsp_axioms TSPGap.le_pairSum_of_union
#check_tsp_axioms TSPGap.arcSet_left_injective
#check_tsp_axioms TSPGap.PolygonRep.two_le_card_outsideIn
#check_tsp_axioms TSPGap.PolygonRep.outsideIn_injective
#check_tsp_axioms TSPGap.PolygonRep.crossesOnLeft_or_crossesOnRight
#check_tsp_axioms TSPGap.PolygonRep.not_crossesOnLeft_and_crossesOnRight
#check_tsp_axioms TSPGap.PolygonRep.exists_isLp
#check_tsp_axioms TSPGap.PolygonRep.IsLp.unique
#check_tsp_axioms TSPGap.PolygonRep.card_outsideIn_inter_right
#check_tsp_axioms TSPGap.PolygonRep.exists_isSR
#check_tsp_axioms TSPGap.PolygonRep.IsSR.unique
#check_tsp_axioms TSPGap.PolygonRep.IsSL.unique
#check_tsp_axioms TSPGap.PolygonRep.cutSum_eq_arrow_sum
#check_tsp_axioms TSPGap.PolygonRep.sum_arrowCirc_le
#check_tsp_axioms TSPGap.IsThreeCycle.isKCycle
#check_tsp_axioms TSPGap.isCrossingComponent_crossComp
#check_tsp_axioms TSPGap.exists_isCrossingComponent_mem
#check_tsp_axioms TSPGap.mem_of_isNearMinCut_of_union_atoms
#check_tsp_axioms TSPGap.PolygonRep.outsideIn_inter_right_eq_arc
#check_tsp_axioms TSPGap.PolygonRep.exists_atom_disjoint
#check_tsp_axioms TSPGap.PolygonRep.inter_eq_of_crossesOnRight_of_start_eq
#check_tsp_axioms TSPGap.PolygonRep.inter_subset_inter_of_crossesOnRight
#check_tsp_axioms TSPGap.PolygonRep.inter_subset_inter_of_crossesOnRight_of_le
#check_tsp_axioms TSPGap.val_sub_of_le
#check_tsp_axioms TSPGap.PolygonRep.outsideIn_inter_left_eq_arc
#check_tsp_axioms TSPGap.PolygonRep.inter_chain_of_crossesOnRight
#check_tsp_axioms TSPGap.PolygonRep.inter_isSR_subset
#check_tsp_axioms TSPGap.PolygonRep.crossesOnRight_of_shared_rightPoint
#check_tsp_axioms TSPGap.PolygonRep.card_outsideIn_inter_eq_of_shared_rightPoint
#check_tsp_axioms TSPGap.PolygonRep.isSR_of_shared_rightPoint
#check_tsp_axioms TSPGap.PolygonRep.arrowRight_eq_of_shared_rightPoint
#check_tsp_axioms TSPGap.PolygonRep.crossesOnLeft_iff_crossesOnRight_swap
#check_tsp_axioms TSPGap.PolygonRep.crossesOnLeft_of_shared_leftPoint
#check_tsp_axioms TSPGap.PolygonRep.isSL_of_shared_leftPoint
#check_tsp_axioms TSPGap.PolygonRep.arrowLeft_eq_of_shared_leftPoint
#check_tsp_axioms TSPGap.PolygonRep.inter_eq_of_extends_both_sides
#check_tsp_axioms TSPGap.PolygonRep.cutEdges_subset_union_of_inter_eq
#check_tsp_axioms TSPGap.PolygonRep.no_outside_atom_diag
#check_tsp_axioms TSPGap.PolygonRep.arrowLeft_disjoint_arrowRight_of_diag
#check_tsp_axioms TSPGap.PolygonRep.arrowLeft_disjoint_arrowRight
#check_tsp_axioms TSPGap.PolygonRep.arrowCirc_subset_union
#check_tsp_axioms TSPGap.PolygonRep.cutEdges_eq_arrow_union
#check_tsp_axioms TSPGap.PolygonRep.cut_card_eq_two_of_counts
#check_tsp_axioms TSPGap.PolygonRep.bad_event_of_cut_card_ne_two
#check_tsp_axioms TSPGap.PolygonRep.bad_event_at_polygon_points
#check_tsp_axioms TSPGap.PolygonRep.one_sub_le_sum_badEdges
#check_tsp_axioms TSPGap.PolygonRep.arc_union_ne_univ
#check_tsp_axioms TSPGap.PolygonRep.rightmost_wlog
#check_tsp_axioms TSPGap.PolygonRep.exists_rightmost
#check_tsp_axioms TSPGap.arcSet_union_of_mem
#check_tsp_axioms TSPGap.PolygonRep.outsideIn_union_eq_arc
#check_tsp_axioms TSPGap.PolygonRep.out_subset_iff_mem_arc
#check_tsp_axioms TSPGap.PolygonRep.exists_atom_disjoint_of_isArcOf
#check_tsp_axioms TSPGap.PolygonRep.not_crossesOnLeftArc_and_crossesOnRightArc
#check_tsp_axioms TSPGap.PolygonRep.outsideIn_inter_rightArc_eq_arc
#check_tsp_axioms TSPGap.PolygonRep.outsideIn_inter_leftArc_eq_arc
#check_tsp_axioms TSPGap.PolygonRep.inter_eq_of_crossesOnLeftArc_of_len_eq
#check_tsp_axioms TSPGap.PolygonRep.inter_subset_inter_of_crossesOnLeftArc
#check_tsp_axioms TSPGap.PolygonRep.inter_subset_isLStar
#check_tsp_axioms TSPGap.PolygonRep.not_mem_sdiff_isLStar
#check_tsp_axioms TSPGap.PolygonRep.inter_subset_inter_of_crossesOnRightArc
#check_tsp_axioms TSPGap.PolygonRep.card_inter_lt_of_start_notMem
#check_tsp_axioms TSPGap.PolygonRep.crossesOnRight_of_rightmost
#check_tsp_axioms TSPGap.PolygonRep.crossesOnRight_of_witness
#check_tsp_axioms TSPGap.PolygonRep.eq_of_isSR_of_subset
#check_tsp_axioms TSPGap.PolygonRep.exists_isLStar
#check_tsp_axioms TSPGap.PolygonRep.isAlmostDiagonal_inter
#check_tsp_axioms TSPGap.PolygonRep.IsArcOf.unique
#check_tsp_axioms TSPGap.PolygonRep.isAlmostDiagonal_of_mem
#check_tsp_axioms TSPGap.PolygonRep.disjoint_arrowLeft_arrowRight_of_crossing
#check_tsp_axioms TSPGap.no_threeCycle
#check_tsp_axioms TSPGap.PolygonRep.sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight
#check_tsp_axioms TSPGap.PolygonRep.sum_arrowCirc_le'

-- The `e₀` layer (KKO22 §5's distinguished edge).
#check_tsp_axioms TSPGap.RootEdge.edge_notMem_cutEdges
#check_tsp_axioms TSPGap.cutSum_restrict
#check_tsp_axioms TSPGap.AvoidsRootEdge.mono
#check_tsp_axioms TSPGap.AvoidsRootEdge.union

-- KKO22 Theorem 5.2 (the assembly).
#check_tsp_axioms TSPGap.RootEdge.restrict_nonneg
#check_tsp_axioms TSPGap.slack_nonneg
#check_tsp_axioms TSPGap.le_slack_cutSum
#check_tsp_axioms TSPGap.expect_slack_le
#check_tsp_axioms TSPGap.exists_slack_vector

-- The polygon family (quantifying over polygons) and KKO22 Fact 4.9.
#check_tsp_axioms TSPGap.atomOf_eq_of_mem_atoms
#check_tsp_axioms TSPGap.PolygonFamily.rootAtom_eq
#check_tsp_axioms TSPGap.PolygonFamily.eq_of_separates
#check_tsp_axioms TSPGap.PolygonFamily.card_separating_le_one
#check_tsp_axioms TSPGap.PolygonFamily.card_badEvents_le_four
#check_tsp_axioms TSPGap.exists_slack_vector_of_family

-- The concrete bad events (wiring section 5's lemmas to Theorem 5.2's interface).
#check_tsp_axioms TSPGap.cutEdges_subset_edgeFinset
#check_tsp_axioms TSPGap.probEvent_occursRight_le
#check_tsp_axioms TSPGap.probEvent_occursLeft_le
#check_tsp_axioms TSPGap.one_sub_le_sum_badEdgesRight
#check_tsp_axioms TSPGap.occurs_of_cut_card_ne_two
#check_tsp_axioms TSPGap.badEdgesRight_subset_arrowRight
#check_tsp_axioms TSPGap.badEdgesLeft_subset_arrowLeft
#check_tsp_axioms TSPGap.exists_occurring_badEvent
#check_tsp_axioms TSPGap.exists_occurring_badEvent_of_polygon
#check_tsp_axioms TSPGap.PolygonRep.isAlmostDiagonal_union
#check_tsp_axioms TSPGap.PolygonRep.sdiff_disjoint_of_crossesOnLeftArc_of_crossesOnRightArc

-- Crossing-component separation (the reduction underlying Theorem 4.5).
#check_tsp_axioms TSPGap.IsCrossingComponent.eq_of_mem_of_mem
#check_tsp_axioms TSPGap.IsCrossingComponent.not_crossing_of_ne
#check_tsp_axioms TSPGap.IsCrossingComponent.eq_of_crossing

-- Theorem 4.5 itself (= [Ben97, Lemma 4.1.7]), no longer a black box.
#check_tsp_axioms TSPGap.sideSubset_const
#check_tsp_axioms TSPGap.away_subset_of_step
#check_tsp_axioms TSPGap.exists_atomOf_union_atomOf_eq_univ
#check_tsp_axioms TSPGap.exists_atom_union_eq_univ

-- The rooted orientation (KKO22 §4.2), and the refutation it repairs.
#check_tsp_axioms TSPGap.Crossing.compl_left
#check_tsp_axioms TSPGap.IsCrossingComponent.compl_mem
#check_tsp_axioms TSPGap.not_nonempty_polygonRep
#check_tsp_axioms TSPGap.crossing_of_avoidsRootEdge
#check_tsp_axioms TSPGap.IsRootedCrossingComponent.compl_notMem
#check_tsp_axioms TSPGap.exists_isRootedCrossingComponent_mem
#check_tsp_axioms TSPGap.exists_atom_union_eq_univ_rooted
#check_tsp_axioms TSPGap.exists_polygonFamily

-- KKO22 Theorem 5.2 at the *genuine* bad events: the assembly's last
-- hypothesis (`hsat`) and the two applications.  These depend on the declared
-- boxes only — no hypothesis of Theorem 5.2 is assumed any longer.
#check_tsp_axioms TSPGap.PolygonRep.arrowRight_subset_cutEdges_of_isLp
#check_tsp_axioms TSPGap.PolygonRep.arrowLeft_subset_cutEdges_of_isRp
#check_tsp_axioms TSPGap.exists_occurring_badEvent_of_family
#check_tsp_axioms TSPGap.exists_slack_vector_of_polygonFamily
#check_tsp_axioms TSPGap.exists_slack_vector_of_subtourLP

-- The output layer: shortcutting an Euler tour to a Hamiltonian cycle.  These
-- take no assumption of the KKO development at all.
#check_tsp_axioms TSPGap.listCost_le_of_sublist
#check_tsp_axioms TSPGap.exists_hamiltonianCycle_of_nodup
#check_tsp_axioms TSPGap.exists_hamiltonianCycle_le_of_spanning_walk

-- KKO22 §6.2: the handshake bridge and the feasibility of the O-join vector.
#check_tsp_axioms TSPGap.odd_cutEdges_inter_of_odd_inter_oddVerts
#check_tsp_axioms TSPGap.even_card_oddVerts
#check_tsp_axioms TSPGap.ojoinFeasible_of_slack
#check_tsp_axioms TSPGap.TreeDist.expect_sum_eq
#check_tsp_axioms TSPGap.TreeDist.exists_le_expect

-- KKO22 §2.1: the root-edge reduction, proved (no assumption of its own).
#check_tsp_axioms TSPGap.splitPoint_mem_subtourLP
#check_tsp_axioms TSPGap.lpCost_splitCost
#check_tsp_axioms TSPGap.gap_of_rooted_gap

-- KKO22 Appendix A: the near-cycle interface, the slack vector of
-- Theorem A.12, and Lemma A.8's charging map.  All assumption-free.
#check_tsp_axioms TSPGap.NearCycle.group_disjoint
#check_tsp_axioms TSPGap.NearCycle.group_subset_cutEdges_interval
#check_tsp_axioms TSPGap.NearCycle.even_cut_of_cutHappy_left
#check_tsp_axioms TSPGap.NearCycle.even_cut_of_cutHappy_right
#check_tsp_axioms TSPGap.NearCycle.exists_happySlack
#check_tsp_axioms TSPGap.NearCycle.exists_happySlack_of_charging
#check_tsp_axioms TSPGap.card_charged_le_two
#check_tsp_axioms TSPGap.TreeDist.probEvent_mono
#check_tsp_axioms TSPGap.prob_card_eq_one
#check_tsp_axioms TSPGap.prob_card_eq_two

-- Appendix A's probability bounds.  These consume Corollary 2.12, which is
-- now proved (`SubtreeProbability.lean`), so they are axiom-clean.
#check_tsp_axioms TSPGap.prob_group_eq_one
#check_tsp_axioms TSPGap.prob_cut_card_eq_two
#check_tsp_axioms TSPGap.prob_cutHappy_left
#check_tsp_axioms TSPGap.prob_cutHappy_right

-- Lemma A.8 for the two hierarchies together, and Theorem A.12 with its
-- probabilistic hypothesis discharged.
#check_tsp_axioms TSPGap.card_charged_le_four
#check_tsp_axioms TSPGap.prob_Fails_le
#check_tsp_axioms TSPGap.prob_Increase_le
#check_tsp_axioms TSPGap.exists_happySlack_of_hierarchies

-- The bridge from §4's arcs to this file's intervals.
#check_tsp_axioms TSPGap.mem_arcSet_iff_rotated_le
#check_tsp_axioms TSPGap.arcSet_eq_Icc_rotated
#check_tsp_axioms TSPGap.PolygonRep.eq_biUnion_arc
#check_tsp_axioms TSPGap.PolygonRep.root_notMem_arc
#check_tsp_axioms TSPGap.PolygonRep.exists_interval_eq
#check_tsp_axioms TSPGap.intervalLaminar_of_setLaminar

-- Appendix A at a real one-side-crossed component.  It carried `sorryAx` for the declared
-- inputs of `NearCycle.lean` until those were proved (2026-09-09); it is clean now.
#check_tsp_axioms TSPGap.exists_happySlack_of_oneSideComponent

-- The endpoints of `e₀` are leaves of every tree in the support.
#check_tsp_axioms TSPGap.card_cut_inter_eq_one_of_expectedCard
#check_tsp_axioms TSPGap.cutSum_restrict_endpoint
#check_tsp_axioms TSPGap.rootEdge_notMem_of_prob
#check_tsp_axioms TSPGap.card_cut_inter_rootPair

-- KKO22 Lemma 2.11 and Corollary 2.12, proved (`SubtreeProbability.lean`):
-- the localized handshake, the geodesic tree bound `|T ∩ E(S)| ≤ |S| − 1`,
-- one-sided Markov at a ceiling, and the three-count argument.  This
-- discharges the former box `prob_exactlyOne_betweenEdges`; repo-wide boxes
-- drop 18 → 17.
#check_tsp_axioms TSPGap.sum_cutSum_singleton_local
#check_tsp_axioms TSPGap.card_internal_inter_add_one_le
#check_tsp_axioms TSPGap.TreeDist.probEvent_card_eq_of_expected
#check_tsp_axioms TSPGap.prob_internal_card
#check_tsp_axioms TSPGap.card_between_eq_one_of_counts
#check_tsp_axioms TSPGap.prob_exactlyOne_betweenEdges

-- The probability interface.  `not_isLambdaUniform` is a *refutation* and so
-- must be axiom-clean; `exists_join_le_of_feasible` carried only
-- `BlackBoxes.edmondsJohnson_ojoin` until 2026-09-10 and is axiom-clean since
-- (`EdmondsJoin.lean`).
#check_tsp_axioms TSPGap.starTree_isSpanningTree
#check_tsp_axioms TSPGap.not_isLambdaUniform
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.of_closed
#check_tsp_axioms TSPGap.exists_join_le_of_feasible

-- The binomial–Poisson comparison (2026-09-11), the former box
-- `binomial_lowerTail_le_shifted_poisson`: the split perturbation and the finite
-- padded-binomial bound, the point-mass limit at an independent size, and the
-- comparison itself, in the stronger form without an upper clause on the threshold.
-- Its consumer `Bernoulli.poi_tail_le_probGE` (KKO21 Lemma 2.22) is now axiom-clean.
#check_tsp_axioms TSPGap.Bernoulli.probLE_split
#check_tsp_axioms TSPGap.Bernoulli.exists_shift_binomTail_le
#check_tsp_axioms TSPGap.Bernoulli.binom_tendsto_poi
#check_tsp_axioms TSPGap.Bernoulli.exists_shift_binomTail_le_poisson
#check_tsp_axioms TSPGap.binomial_lowerTail_le_shifted_poisson
#check_tsp_axioms TSPGap.Bernoulli.poi_tail_le_probGE

-- What passes to the max-entropy limit (Milestone 5's entry point).
#check_tsp_axioms TSPGap.tendsto_of_approx
#check_tsp_axioms TSPGap.limitClosed_le
#check_tsp_axioms TSPGap.limitClosed_forall
#check_tsp_axioms TSPGap.LimitClosed.and
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.expect_le
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.le_probEvent
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.expect_mul_le

-- Milestone 5, first layer: real stability and generating polynomials.  This
-- layer is definitions and easy closures only; the forward link from
-- `IsRealStable` to `RayleighNonneg` is proved later, in `Rayleigh.lean`, and
-- the reverse (full BBL) is deferred/optional.
#check_tsp_axioms TSPGap.sqExp_injective
#check_tsp_axioms TSPGap.prod_X_eq_monomial
#check_tsp_axioms TSPGap.coeff_genPoly
#check_tsp_axioms TSPGap.genPoly_injective
#check_tsp_axioms TSPGap.eval_map_genPoly
#check_tsp_axioms TSPGap.eval_genPoly
#check_tsp_axioms TSPGap.isMultiAffine_genPoly
#check_tsp_axioms TSPGap.IsRealStable.ne_zero
#check_tsp_axioms TSPGap.IsRealStable.mul
#check_tsp_axioms TSPGap.IsRealStableOrZero.mul
#check_tsp_axioms TSPGap.IsRealStable.const_mul
#check_tsp_axioms TSPGap.IsRealStable.rename
#check_tsp_axioms TSPGap.IsRealStableOrZero.rename
#check_tsp_axioms TSPGap.IsRealStable.scale

-- Milestone 5, the stability adapter: real stability survives the max-entropy
-- limit at fixed rank.  This is the line-restriction argument, *not* BBL.
#check_tsp_axioms TSPGap.lineRestrict_monic
#check_tsp_axioms TSPGap.lineRestrict_natDegree
#check_tsp_axioms TSPGap.lineRestrict_ne_zero
#check_tsp_axioms TSPGap.zeroFree_of_approx_monic
#check_tsp_axioms TSPGap.lineRestrict_coeff_sub_le
#check_tsp_axioms TSPGap.isRealStable_of_approx
#check_tsp_axioms TSPGap.limitClosed_fixedRankStable
#check_tsp_axioms TSPGap.TreeDist.fixedRankNormalized
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.realStable_of_fixedRank
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.realStable

-- Adapter 2: Fact 2.8 at the limit, in cross-multiplied form.  Depends on
-- neither BBL nor the weighted matrix-tree development.
#check_tsp_axioms TSPGap.limitClosed_condIndepCross
#check_tsp_axioms TSPGap.condIndep_of_cross
#check_tsp_axioms TSPGap.InducesTreeOn.glue
#check_tsp_axioms TSPGap.limitClosed_treeCondIndep
#check_tsp_axioms TSPGap.treeCondIndep_of_lambdaUniform
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.treeCondIndep
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.condIndep

-- Weighted determinant stability: the first link of the chain to λ-uniform
-- tree stability.  No graph theory, no Cauchy--Binet, no BBL.
#check_tsp_axioms TSPGap.FullRowRank.vecMul_eq_zero
#check_tsp_axioms TSPGap.det_weightedGram_ne_zero
#check_tsp_axioms TSPGap.eval_map_detPoly
#check_tsp_axioms TSPGap.isRealStable_detPoly

-- Cauchy--Binet, from the coefficient of X^|r| in det(1+XAB) = det(1+XBA).
-- No permutation expansion; everything sign-free.
#check_tsp_axioms TSPGap.det_mul_eq_sum_principalMinors
#check_tsp_axioms TSPGap.gramMinor_map
#check_tsp_axioms TSPGap.det_gram_comm
#check_tsp_axioms TSPGap.det_weighted_eq_sum_gramMinor
#check_tsp_axioms TSPGap.detPoly_eq_sum_gramMinor
#check_tsp_axioms TSPGap.detPoly_eq_genPoly
#check_tsp_axioms TSPGap.coeff_detPoly
#check_tsp_axioms TSPGap.isMultiAffine_detPoly

-- The reduced oriented incidence matrix, via total unimodularity.
-- `T.card = k` is spent exactly twice: squareness in `gramMinor_of_tu`, and
-- loop-freeness via the zero column.  The connectivity bridge is hypothesis-free.
#check_tsp_axioms TSPGap.isTotallyUnimodular_incidence
#check_tsp_axioms TSPGap.isTotallyUnimodular_reducedIncidence
#check_tsp_axioms TSPGap.vecMul_reducedIncidence
#check_tsp_axioms TSPGap.fullRowRank_reducedIncidence
#check_tsp_axioms TSPGap.gramMinor_of_tu
#check_tsp_axioms TSPGap.not_fullRowRank_of_zero_col
#check_tsp_axioms TSPGap.fullRowRank_colsOn_reducedIncidence_iff
#check_tsp_axioms TSPGap.gramMinor_reducedIncidence

-- The last link: lambda-uniform tree stability, and its passage to the limit.
-- Strict positivity enters exactly twice: lam > 0 for the coordinate scaling,
-- Z > 0 only to make Z⁻¹ nonzero.  No partition-function identity.
#check_tsp_axioms TSPGap.bind₁_scale_genPoly
#check_tsp_axioms TSPGap.const_mul_genPoly
#check_tsp_axioms TSPGap.detPoly_reducedIncidence_eq_treeGenPoly
#check_tsp_axioms TSPGap.isRealStable_weightedSpanningTree
#check_tsp_axioms TSPGap.isRealStable_genPoly_of_lambdaUniform
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.treeRealStable

-- The FORWARD stability-to-Rayleigh implication, and pairwise negative
-- correlation.  The reverse BBL direction is deferred/optional: it was mainly a
-- candidate limit adapter, which `StableLimit.lean` made unnecessary.
#check_tsp_axioms TSPGap.genPoly_coeff_self
#check_tsp_axioms TSPGap.pderiv_genPoly
#check_tsp_axioms TSPGap.genPoly_split
#check_tsp_axioms TSPGap.rayleighDiff_genPoly
#check_tsp_axioms TSPGap.rayleighNonneg_genPoly_ne
#check_tsp_axioms TSPGap.rayleighNonneg_genPoly
#check_tsp_axioms TSPGap.IsRealStable.rayleighNonneg
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.negCorrelation

-- Conditioning: one specialization family, two ends.  t = 0 conditions out,
-- the t^2 coefficient conditions in, t = 1 forgets the coordinate.  All the
-- conditional inequalities are cross-multiplied, so zero-mass events are
-- harmless and no conditional distribution is constructed.
#check_tsp_axioms TSPGap.nonneg_of_quadratic_nonneg
#check_tsp_axioms TSPGap.rayleighNonneg_specializeWeight
#check_tsp_axioms TSPGap.rayleighNonneg_deleteWeight
#check_tsp_axioms TSPGap.rayleighNonneg_projectWeight
#check_tsp_axioms TSPGap.rayleighNonneg_contractWeight
#check_tsp_axioms TSPGap.RayleighNonneg.pderiv
#check_tsp_axioms TSPGap.negCorrelation_of_rayleighNonneg
#check_tsp_axioms TSPGap.negCorrelation_contract
#check_tsp_axioms TSPGap.negCorrelation_delete
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.negCorrelation_contract
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.negCorrelation_delete

-- Feder--Mihail, generic weight layer.  The active set `K` carries the
-- induction; masses are unnormalized and every correlation is cross-multiplied.
-- `coordinate_event_negCorrelation` is the coordinate--event theorem.
#check_tsp_axioms TSPGap.weightMass_mono
#check_tsp_axioms TSPGap.NegCorrelated.smul
#check_tsp_axioms TSPGap.EventDependsOn.outSection
#check_tsp_axioms TSPGap.EventDependsOn.inSection
#check_tsp_axioms TSPGap.outSection_le_inSection
#check_tsp_axioms TSPGap.WeightSupportedOn.contract
#check_tsp_axioms TSPGap.FixedRankWeight.contract
#check_tsp_axioms TSPGap.weightMass_deleteWeight
#check_tsp_axioms TSPGap.weightMass_contractWeight
#check_tsp_axioms TSPGap.sum_mem_weightMass
#check_tsp_axioms TSPGap.sum_influence_eq_zero
#check_tsp_axioms TSPGap.influence_cross_bound
#check_tsp_axioms TSPGap.fourCell_negCorrelated
#check_tsp_axioms TSPGap.exists_nonneg_influence
#check_tsp_axioms TSPGap.exists_nonneg_influence_contract
#check_tsp_axioms TSPGap.le_weightMass
#check_tsp_axioms TSPGap.weightMass_eq_zero_of_marginal
#check_tsp_axioms TSPGap.exists_posMarginal_nonneg_influence
#check_tsp_axioms TSPGap.exists_posMarginal_nonneg_influence_contract
#check_tsp_axioms TSPGap.weightMass_split_mem
#check_tsp_axioms TSPGap.negCorrelated_of_no_coOccurrence
#check_tsp_axioms TSPGap.rayleighNegCorrelated_mem
#check_tsp_axioms TSPGap.weightMass_contract_blind
#check_tsp_axioms TSPGap.weightMass_delete_blind
#check_tsp_axioms TSPGap.negCorrelated_mem_of_cells
#check_tsp_axioms TSPGap.coordinate_event_negCorrelation
#check_tsp_axioms TSPGap.negCorrelated_mem_of_monotone

-- Feder--Mihail's second induction: two increasing events with disjoint
-- dependency witnesses.  Selection happens inside A's witness; disjointness
-- puts that coordinate outside B's, so the two influences have opposite signs.
#check_tsp_axioms TSPGap.exists_posCorrelated_mem_of_dependsOn
#check_tsp_axioms TSPGap.twoCell_negCorrelated
#check_tsp_axioms TSPGap.negCorrelated_of_sections
#check_tsp_axioms TSPGap.negCorrelated_of_constDep
#check_tsp_axioms TSPGap.increasing_events_negCorrelation
#check_tsp_axioms TSPGap.negCorrelated_of_disjoint_monotone

-- Complement algebra: negation swaps the sign and preserves the witness, so the
-- three remaining patterns are inclusion--exclusion away.  Then one bridge to
-- `TreeDist` and four hypothesis-free event exports.
#check_tsp_axioms TSPGap.weightMass_not
#check_tsp_axioms TSPGap.decreasing_events_negCorrelation
#check_tsp_axioms TSPGap.mixed_events_posCorrelation
#check_tsp_axioms TSPGap.mixed_events_posCorrelation'
#check_tsp_axioms TSPGap.weightMass_treeDist
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.negAssoc_increasing
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.negAssoc_decreasing
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.posAssoc_increasing_decreasing
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.posAssoc_decreasing_increasing

-- The finite-cylinder layer: conditioning on a cylinder is repeated contraction
-- and deletion, so a finite induction over its coordinates gives the
-- cross-multiplied conditional statement, with no positivity for the cylinder
-- and no disjointness between the cylinder and the witnesses.
#check_tsp_axioms TSPGap.weightMass_cylinder_contract
#check_tsp_axioms TSPGap.weightMass_cylinder_delete
#check_tsp_axioms TSPGap.cylinder_negCorrelated
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.negAssoc_cylinder

-- Rank sequences, increment 1 (`RankSequence.lean`): the rank polynomial
-- along `F` is real-rooted, by the homogeneous tilt `λ = 1 + iδ` — no
-- boundary specialization, no multivariate Hurwitz, and the scaling
-- identity is one sum rearrangement rather than homogeneity API.
#check_tsp_axioms TSPGap.coeff_rankPoly
#check_tsp_axioms TSPGap.eval_smul_map_genPoly
#check_tsp_axioms TSPGap.aeval_rankPoly_ne_zero_of_im_pos
#check_tsp_axioms TSPGap.im_eq_zero_of_aeval_rankPoly

-- Rank sequences, increment 2: the Bernoulli rank law.  Roots nonpositive
-- from positivity on the positive axis; the factorization pulled back from
-- ℂ through the injective coefficient map (no splits-transfer lemma); the
-- coefficient bridge via `Finset.prod_add`; and the hypothesis-free export
-- at the max-entropy limit.
#check_tsp_axioms TSPGap.Bernoulli.probCount_eq_coeff
#check_tsp_axioms TSPGap.exists_factorization_of_roots_real
#check_tsp_axioms TSPGap.exists_bernoulli_rank_law
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.exists_bernoulli_rank_law

-- Conditioned extreme faces (`FaceStability.lean`): external-field scaling
-- into the fixed-rank limit adapter — no new Hurwitz theorem and no boundary
-- specialization.  Deletion and cylinders are minimum-cost faces; contraction
-- is recovered by cancelling `X e`, which never vanishes in the open upper
-- half-plane.
#check_tsp_axioms TSPGap.isRealStable_genPoly_faceDist
#check_tsp_axioms TSPGap.isRealStableOrZero_genPoly_faceWeight
#check_tsp_axioms TSPGap.isRealStableOrZero_genPoly_deleteWeight
#check_tsp_axioms TSPGap.exists_bernoulli_rank_law_faceDist
#check_tsp_axioms TSPGap.isRealStableOrZero_genPoly_cylinderFaceWeight
#check_tsp_axioms TSPGap.isRealStable_genPoly_cylinderFaceDist
#check_tsp_axioms TSPGap.exists_bernoulli_rank_law_cylinder
#check_tsp_axioms TSPGap.genPoly_delete_add_X_mul_contract
#check_tsp_axioms TSPGap.isRealStableOrZero_genPoly_contractWeight

-- The tree face (`TreeFace.lean`): on a spanning tree the cardinality
-- equality |E(S) ∩ T| + 1 = |S| IS `InducesTreeOn S T` — the count-to-
-- connectivity direction reuses the geodesic tree bound twice, on a
-- reachability class and its complement, with no forest machinery.
#check_tsp_axioms TSPGap.reachable_internalEdges_of_card
#check_tsp_axioms TSPGap.inducesTreeOn_iff_card

-- The marker calculus, increment 1 (`MarkerStability.lean`): the signed
-- reflection `y^d·P(−1/y)` and certified marker differentiation — the
-- Gauss–Lucas closure with a stable-or-zero leading-coefficient certificate
-- excluding the degenerate slice.
#check_tsp_axioms TSPGap.eval₂_markerReflect_eq_zero_iff
#check_tsp_axioms TSPGap.MarkerStable.markerReflect
#check_tsp_axioms TSPGap.markerStableOrZero_derivative

-- The marker calculus, increment 2 (`ProjectedLayers.lean`): the projected
-- layers, the master evaluation identity (no rename — Fubini over
-- `S ↦ S ∩ F`), the width-zero and width-one extraction identities, and the
-- endpoint certificates by conditioning onto the extreme face, collapsing to
-- the marker, and cancelling the marker power.
#check_tsp_axioms TSPGap.totalMass_projLayer
#check_tsp_axioms TSPGap.eval₂_markerPoly
#check_tsp_axioms TSPGap.markerStable_markerPoly
#check_tsp_axioms TSPGap.extraction_exact
#check_tsp_axioms TSPGap.extraction_adjacent
#check_tsp_axioms TSPGap.isRealStableOrZero_projLayer_min
#check_tsp_axioms TSPGap.isRealStableOrZero_projLayer_max

-- The marker calculus, increment 3(a) (`AdjacentLayers.lean`): the
-- projected event-mass bridge with its `EventDependsOn` adapter, Bernoulli
-- interval support (positive mass exactly on `[a, b]`, before any global
-- induction), and the endpoint promotions from stable-or-zero to stable.
#check_tsp_axioms TSPGap.weightMass_projLayer
#check_tsp_axioms TSPGap.weightMass_projLayer_of_dependsOn
#check_tsp_axioms TSPGap.probCount_pos_iff
#check_tsp_axioms TSPGap.exists_layer_interval
#check_tsp_axioms TSPGap.isRealStable_projLayer_endpoints

-- The marker calculus, increment 3(b): the certified descent — both
-- derivative blocks with explicit certificates, the tagged bridge weight
-- on `Option ι` with stability by direct evaluation, the layer harvest
-- through marker-contraction, and the zero-safe adjacent exports.
#check_tsp_axioms TSPGap.markerStable_adjacent_pair
#check_tsp_axioms TSPGap.isRealStable_genPoly_taggedWeight
#check_tsp_axioms TSPGap.isRealStable_projLayer_of_tagged
#check_tsp_axioms TSPGap.isRealStable_projLayer_interval
#check_tsp_axioms TSPGap.adjacent_layer_mono
#check_tsp_axioms TSPGap.adjacent_layer_anti

-- The marker calculus, increment 4: layer tails and KKO21 Lemma 5.4 —
-- iterated layer comparisons, the finite layer partition, the
-- exact-layer-versus-tail cross inequality, and the division-free
-- aggregation `m·W(A ≤ n_A)·W(B ≥ n_B) ≤ s·M²` with its mirror.
#check_tsp_axioms TSPGap.layer_le_mono
#check_tsp_axioms TSPGap.layer_le_anti
#check_tsp_axioms TSPGap.weightMass_layer_partition
#check_tsp_axioms TSPGap.crossTail
#check_tsp_axioms TSPGap.layerProduct_le_of_le_ge
#check_tsp_axioms TSPGap.layerProduct_le_of_ge_le

-- Log-concavity of the Bernoulli count law, by the order-two
-- Pólya-frequency closure (log-concavity alone is NOT convolution-closed).
#check_tsp_axioms TSPGap.pf2_convolve
#check_tsp_axioms TSPGap.pf2_bernoulli_prod
#check_tsp_axioms TSPGap.Bernoulli.probCount_logConcave

-- KKO21 Corollary 5.5, the shifted three-cell case: the pure arithmetic,
-- the layer-conditioned log-concavity bridge, and the two public bounds.
#check_tsp_axioms TSPGap.three_cell_le_two_mul
#check_tsp_axioms TSPGap.three_cell_cross
#check_tsp_axioms TSPGap.three_cell_refined
#check_tsp_axioms TSPGap.weightMass_three_cells_shift
#check_tsp_axioms TSPGap.weightMass_three_cells
#check_tsp_axioms TSPGap.layer_logConcave
-- The shifted adapter (baselines `kA`, `kB`, layer `kA+kB+2`, target
-- `(kA+1, kB+1)`) and the unshifted statements it now specializes to.
#check_tsp_axioms TSPGap.three_cell_setup_shifted
#check_tsp_axioms TSPGap.three_cell_bound_shifted_two
#check_tsp_axioms TSPGap.three_cell_bound_shifted
#check_tsp_axioms TSPGap.three_cell_bound_two
#check_tsp_axioms TSPGap.three_cell_bound

-- Lemma 5.7 infrastructure, increment 1: expected counts, Markov at zero,
-- conditioning on avoidance (cylinder at `I = ∅`) with its normalization
-- bridges, and the two-sided homogeneous conditional bound.
#check_tsp_axioms TSPGap.expCard_eq_sum_marginal
#check_tsp_axioms TSPGap.expCard_univ
#check_tsp_axioms TSPGap.le_weightMass_avoid
#check_tsp_axioms TSPGap.weightMass_avoidWeight
#check_tsp_axioms TSPGap.fixedRankNormalized_avoidDist
#check_tsp_axioms TSPGap.isRealStable_genPoly_avoidDist
#check_tsp_axioms TSPGap.weightMass_avoidDist_mul
#check_tsp_axioms TSPGap.marginal_avoid_ge
#check_tsp_axioms TSPGap.expCard_avoid_ge
#check_tsp_axioms TSPGap.expCard_avoid_le

-- Lemma 5.7 infrastructure, increment 2: the Bernoulli mean identity, the
-- exponential bound at zero (no shifted-Poisson comparison needed), and the
-- `k = 2` point-mass wrapper over `poi_le_probCount` with its constants.
#check_tsp_axioms TSPGap.expCard_eq_sum_layer
#check_tsp_axioms TSPGap.sum_atomProb_mem
#check_tsp_axioms TSPGap.sum_range_mul_probCount
#check_tsp_axioms TSPGap.expCard_eq_sum_of_rankLaw
#check_tsp_axioms TSPGap.probCount_zero_le_exp
#check_tsp_axioms TSPGap.one_sub_exp_ge
#check_tsp_axioms TSPGap.sq_mul_exp_neg_ge
#check_tsp_axioms TSPGap.mul_exp_neg_ge
#check_tsp_axioms TSPGap.probCount_two_ge

-- ⭐ KKO21 Lemma 5.7, assembled: conditioning on avoidance, the two mean
-- branches, and the three-cell bound.  No black box, no coupling.
#check_tsp_axioms TSPGap.expCard_avoidDist_mul
#check_tsp_axioms TSPGap.two_mul_weightMass_le_one_ge
#check_tsp_axioms TSPGap.one_sub_exp_le_weightMass_one_le
#check_tsp_axioms TSPGap.probCount_two_ge_low
#check_tsp_axioms TSPGap.weightMass_layer_two_ge_high
#check_tsp_axioms TSPGap.weightMass_layer_two_ge_low
#check_tsp_axioms TSPGap.weightMass_conj_avoid_le
#check_tsp_axioms TSPGap.lemma_5_7

-- The cut-oriented repair: the paper applies Lemma 5.7 at `α = γ − η`
-- without checking `α < 0.001`, which can fail.  Capping repairs it.
#check_tsp_axioms TSPGap.cut_target_le_cube
#check_tsp_axioms TSPGap.cut_target_le_const
#check_tsp_axioms TSPGap.cut_repair

-- Proposition 5.6, increment 2: max-flow/min-cut for the four-layer
-- network, standalone (Mathlib has no flow theory).
#check_tsp_axioms TSPGap.ReachRow.erase_or
#check_tsp_axioms TSPGap.reachRow_slack
#check_tsp_axioms TSPGap.exists_better_of_reach
#check_tsp_axioms TSPGap.exists_max_flow
#check_tsp_axioms TSPGap.exists_flow_of_cut

-- Proposition 5.6, increment 3: the selected subweight.  The paper's
-- "event" takes a real fraction of each atomic cell, so it is a subweight,
-- not a predicate on trees.
#check_tsp_axioms TSPGap.pairCell_unique
#check_tsp_axioms TSPGap.weightMass_selectedWeight
#check_tsp_axioms TSPGap.weightMass_pairCell_selected
#check_tsp_axioms TSPGap.totalMass_selectedWeight
#check_tsp_axioms TSPGap.weightMass_mem_selected_left
#check_tsp_axioms TSPGap.weightMass_mem_selected_right
#check_tsp_axioms TSPGap.card_eq_one_of_selected
#check_tsp_axioms TSPGap.fixedRankWeight_selected
#check_tsp_axioms TSPGap.isSelectedWeight_selectedWeight
#check_tsp_axioms TSPGap.sum_compl_subtype
#check_tsp_axioms TSPGap.marginal_deviation_le

-- ⭐ KKO21 Proposition 5.6, assembled: the unconditional flow network, the
-- rectangular pair-cell identity, and the corrected TV constant.
#check_tsp_axioms TSPGap.sum_pairCellMass_rect
#check_tsp_axioms TSPGap.tv_closure
#check_tsp_axioms TSPGap.prop_5_6
#check_tsp_axioms TSPGap.prop_5_6_conditional

-- Finite weighted Strassen, off the same flow theorem, and the
-- adjacent-layer covering it yields (no Hahn-Banach, no separate Strassen).
#check_tsp_axioms TSPGap.exists_coupling_of_dominates
#check_tsp_axioms TSPGap.exists_adjacent_covering

-- Lemma 2.26, pieces 1 and 3: the singleton-complement identities (the
-- projection along `univ.erase e` IS delete/contract), the packaged
-- single-edge coupling, and the aggregation with the graph exchange as an
-- explicit hypothesis on the supports.
#check_tsp_axioms TSPGap.projLayer_erase_contract
#check_tsp_axioms TSPGap.projLayer_erase_delete
#check_tsp_axioms TSPGap.exists_edge_covering
#check_tsp_axioms TSPGap.sum_contract_eq
#check_tsp_axioms TSPGap.totalMass_split_delete_contract
#check_tsp_axioms TSPGap.expCard_split_delete_contract
#check_tsp_axioms TSPGap.expCard_delete_le_of_exchange

-- Lemma 2.26, piece 2 and the assembly: the counting definition of
-- `IsSpanningTree` really is a tree, the bridge step that separates the
-- endpoints of `e` in `S`, the exchange itself, its degree form, and
-- Lemma 2.26 for a literal edge (division-free, plus the divided corollary).
#check_tsp_axioms TSPGap.isTree_fromEdgeSet_of_spanningTree
#check_tsp_axioms TSPGap.not_reachable_of_spanningTree_insert
#check_tsp_axioms TSPGap.tree_exchange
#check_tsp_axioms TSPGap.card_inter_cut_le_exchange
#check_tsp_axioms TSPGap.expCard_delete_le_cut
#check_tsp_axioms TSPGap.expCard_delete_le_cut_conditional

-- Lemma 2.27: the three isolated numeric steps, the exclusion of the two path
-- events (a distance argument, needing only connectivity), the measure algebra
-- that turns it into `1 - P[e,f in T]`, and the theorem.
#check_tsp_axioms TSPGap.cond_path_bound
#check_tsp_axioms TSPGap.joint_ge_of_cond_le
#check_tsp_axioms TSPGap.side_bound_of_cond_gt
#check_tsp_axioms TSPGap.not_onUVPath_both
#check_tsp_axioms TSPGap.path_masses_le
#check_tsp_axioms TSPGap.lemma_2_27

-- The contracted-tree path adapter for KKO22 Lemmas 5.17/5.23: atoms stay
-- vertex sets and bundles stay edge sets, so only the *path between two
-- atoms* needs an adapter.  The conditioning (atoms induce trees) is what
-- upgrades the exchange's single pair of endpoints to the all-pairs event.
#check_tsp_axioms TSPGap.exists_setDist
#check_tsp_axioms TSPGap.support_subset_of_inside
#check_tsp_axioms TSPGap.exists_walk_of_inside
#check_tsp_axioms TSPGap.onAtomPath_of_onUVPath
#check_tsp_axioms TSPGap.setDist_add_setDist_le_of_onAtomPath
#check_tsp_axioms TSPGap.not_onAtomPath_both

-- Lemma 2.26 at an edge bundle.  Binary support first (`card_inter_bundle_le_one`);
-- then the bundle is two adjacent projected layers along `univ \ E`, so the same
-- covering coupling applies; the lower layer's forgotten bundle edge is recovered
-- by a nonzero-summand witness, which suffices because neither the count nor the
-- path event depends on which one it is.
#check_tsp_axioms TSPGap.card_inter_bundle_le_one
#check_tsp_axioms TSPGap.exists_witness_of_bundleContract
#check_tsp_axioms TSPGap.projLayer_sdiff_top
#check_tsp_axioms TSPGap.projLayer_sdiff_bundle
#check_tsp_axioms TSPGap.totalMass_split_bundle
#check_tsp_axioms TSPGap.expCard_split_bundle
#check_tsp_axioms TSPGap.expCard_avoid_le_of_exchange
#check_tsp_axioms TSPGap.card_inter_le_bundle_exchange
#check_tsp_axioms TSPGap.expCard_avoid_le_bundle
#check_tsp_axioms TSPGap.expCard_avoid_le_bundle_conditional

-- Lemma 2.27 at edge bundles: the three numeric lemmas and the four-cell
-- measure algebra are reused unchanged, the latter in its generic form.
#check_tsp_axioms TSPGap.path_masses_le_generic
#check_tsp_axioms TSPGap.expCard_eq_weightMass_one
#check_tsp_axioms TSPGap.betweenEdges_subset_cutEdges
#check_tsp_axioms TSPGap.lemma_2_27_bundle

-- Generic maximum-face conditioning: for a stable fixed-rank law supported on
-- |T ∩ F| <= m, conditioning on |T ∩ F| = m moves counts inside F up and
-- counts outside F down, each by at most the deficiency q = m - E[F_T].
-- Inside comes from layer monotonicity, outside from Feder-Mihail plus
-- fixed-rank conservation; everything cross-multiplied by the face mass.
#check_tsp_axioms TSPGap.setCost_indicatorCost
#check_tsp_axioms TSPGap.one_sub_faceDeficiency_le_faceMass
#check_tsp_axioms TSPGap.marginal_face_ge
#check_tsp_axioms TSPGap.marginal_face_le
#check_tsp_axioms TSPGap.expCard_face_inside_lower
#check_tsp_axioms TSPGap.expCard_face_inside_upper
#check_tsp_axioms TSPGap.expCard_face_outside_upper
#check_tsp_axioms TSPGap.expCard_face_outside_lower

-- Stability of the conditioned law transfers through the COMPLEMENTARY cost:
-- `isRealStableOrZero_genPoly_faceWeight` conditions on a MINIMUM-cost face, and
-- our `m` is a maximum, but on rank-r support |S ∩ F| = m iff |S \ F| = r - m,
-- and r - m really is the minimum of |S \ F|.
#check_tsp_axioms TSPGap.faceWeight_max_eq_compl
#check_tsp_axioms TSPGap.le_rank_of_faceMass_pos
#check_tsp_axioms TSPGap.isRealStableOrZero_genPoly_maxFace
#check_tsp_axioms TSPGap.isRealStable_genPoly_maxFaceDist
#check_tsp_axioms TSPGap.abs_weightMass_face_sub_le
#check_tsp_axioms TSPGap.abs_condProb_sub_le
#check_tsp_axioms TSPGap.faceDeficiency_union

-- The three-atom face and KKO22 Eq. (24).  The face is over the UNION OF THE
-- THREE internal edge sets, not the internal edges of the union; the bundle
-- marginals are transferred by the OUTSIDE expCard bounds, not by the event
-- perturbation bound (before conditioning a tree may meet a bundle twice).
#check_tsp_axioms TSPGap.betweenEdges_subset_compl_threeAtom
#check_tsp_axioms TSPGap.card_inter_threeAtom_split
#check_tsp_axioms TSPGap.card_inter_threeAtom_le
#check_tsp_axioms TSPGap.card_inter_threeAtom_eq_iff
#check_tsp_axioms TSPGap.expCard_faceDist
#check_tsp_axioms TSPGap.eq_24_alternative

-- Lemma 5.17's structural layer: support-complete bundles and the cut
-- partition; the connectivity baselines that survive conditioning a bundle
-- out; and the bundle-present face, which is the maximum face at m = 1 on a
-- one-hot support, together with its commutation with avoidance.
#check_tsp_axioms TSPGap.bundle_disjoint
#check_tsp_axioms TSPGap.card_inter_cut_split
#check_tsp_axioms TSPGap.exists_crossing_edge
#check_tsp_axioms TSPGap.one_le_card_cut_inter_atom
#check_tsp_axioms TSPGap.one_le_card_inter_sdiff_of_avoid
#check_tsp_axioms TSPGap.totalMass_le_expCard_avoid
#check_tsp_axioms TSPGap.totalMass_presentWeight_eq_expCard
#check_tsp_axioms TSPGap.isRealStable_genPoly_presentDist
#check_tsp_axioms TSPGap.present_avoid_comm
#check_tsp_axioms TSPGap.avoid_avoid_comm

-- Consuming support completeness (ThreeCell needs genuine Finset.Disjoint,
-- which the ambient sets have because delta(u) cap delta(v) = betweenEdges u v),
-- and the normalized present/avoid restriction.
#check_tsp_axioms TSPGap.inter_bundle_eq_of_supportComplete
#check_tsp_axioms TSPGap.cutEdges_inter_cutEdges
#check_tsp_axioms TSPGap.disjoint_punctured_cuts
#check_tsp_axioms TSPGap.inter_punctured_eq_of_supportComplete
#check_tsp_axioms TSPGap.avoidDist_smul
#check_tsp_axioms TSPGap.avoidDist_faceDist
#check_tsp_axioms TSPGap.avoidDist_presentWeight_comm

-- Lemma 5.17's count estimates.  KKO's 0.029 is not available at the stated
-- mean range: at k = 4 the l = 3 branch is tight and gives 0.028, which still
-- clears 3*eps since 0.49*0.028*0.13 = 0.0017836 > 0.0015.
#check_tsp_axioms TSPGap.exp_3502_le
#check_tsp_axioms TSPGap.poi_ge_of_bounds
#check_tsp_axioms TSPGap.probCount_four_ge
#check_tsp_axioms TSPGap.weightMass_le_one_ge
#check_tsp_axioms TSPGap.weightMass_one_le_ge
#check_tsp_axioms TSPGap.two_mul_weightMass_three_le
#check_tsp_axioms TSPGap.weightMass_le_two_ge_of_baseline

-- The residual shift: an a.s. baseline of one makes P[N=0] = 0, which forces
-- a deterministic coordinate q_j = 1 in the rank law; zeroing it shifts the
-- whole count sequence down by one, at residual mean sum q - 1.
#check_tsp_axioms TSPGap.exists_eq_one_of_probCount_zero
#check_tsp_axioms TSPGap.sum_update_zero
#check_tsp_axioms TSPGap.probCount_succ_update_zero
#check_tsp_axioms TSPGap.probCount_one_eq_of_zero
#check_tsp_axioms TSPGap.probCount_one_le_exp_of_zero
#check_tsp_axioms TSPGap.weightMass_two_le_ge_of_baseline

-- The sharp k = 1 estimate: Hoeffding's extremal theorem, not the Poisson
-- surrogate -- the 0.0582 value is attained, so no approximation reaches it.
#check_tsp_axioms TSPGap.probCount_one_ge
#check_tsp_axioms TSPGap.weightMass_eq_two_ge_of_baseline

-- The division-free three-cell closures feeding Lemma 5.17's kernel.
#check_tsp_axioms TSPGap.weightMass_two_two_ge
#check_tsp_axioms TSPGap.weightMass_one_one_ge

-- The two orientation kernels, unoriented in their inputs.
#check_tsp_axioms TSPGap.two_two_kernel
#check_tsp_axioms TSPGap.one_one_kernel

-- The present-side conditional comparisons: presence lowers marginals off a
-- one-hot bundle, and — by conservation at fixed rank — by at most 1 − E[F].
#check_tsp_axioms TSPGap.marginal_present_le
#check_tsp_axioms TSPGap.expCard_present_le
#check_tsp_axioms TSPGap.expCard_present_ge

-- Lemma 5.17 assembled: the outside face transfer, the two branches, the
-- conditioned disjunction, and the paper-facing wrapper.
#check_tsp_axioms TSPGap.abs_expCard_faceDist_sub_le
#check_tsp_axioms TSPGap.branch_two_two
#check_tsp_axioms TSPGap.branch_one_one
#check_tsp_axioms TSPGap.lemma_5_17_conditioned
#check_tsp_axioms TSPGap.lemma_5_17

-- Lemma 5.23's tail layer: Markov for a sum of two counts, the oriented core
-- at raw avoid weights (division-free, no rank or stability), and the
-- paper-facing disjunction that is Lemma A.1's hypothesis for one bundle.
#check_tsp_axioms TSPGap.two_mul_weightMass_sum_two_le
#check_tsp_axioms TSPGap.two_mul_weightMass_sum_le_one_ge
#check_tsp_axioms TSPGap.expCard_avoidWeight_le
#check_tsp_axioms TSPGap.avoid_tail_mass_of_405
#check_tsp_axioms TSPGap.lemma_5_23_core

-- KKO21 Lemma A.1: two-atom geometry, literal cells, PF₂ bootstrap,
-- elementary tails, the conditioned analytic kernel, and stability of the
-- sequentially conditioned law.
#check_tsp_axioms TSPGap.card_inter_twoAtom_split
#check_tsp_axioms TSPGap.card_inter_twoAtom_le
#check_tsp_axioms TSPGap.card_inter_twoAtom_eq_iff
#check_tsp_axioms TSPGap.inducesTreeOn_union_iff_bundle_present
#check_tsp_axioms TSPGap.bundleSanitize_subset
#check_tsp_axioms TSPGap.disjoint_bundleSanitize
#check_tsp_axioms TSPGap.disjoint_bundleSanitize_puncturedCut
#check_tsp_axioms TSPGap.inter_bundleSanitize_eq_of_supportComplete
#check_tsp_axioms TSPGap.pf2_rank_two_ge
#check_tsp_axioms TSPGap.weightMass_rank_two_ge
#check_tsp_axioms TSPGap.weightMass_two_le_ge_of_baseline_19989
#check_tsp_axioms TSPGap.weightMass_le_two_ge_of_baseline_2502
#check_tsp_axioms TSPGap.lemma_A1_conditioned_kernel
#check_tsp_axioms TSPGap.lemmaA1Tau_support
#check_tsp_axioms TSPGap.lemmaA1Sigma_support
#check_tsp_axioms TSPGap.lemmaA1Sigma_oneHot
#check_tsp_axioms TSPGap.lemmaA1Nu_fixedRankNormalized_stable

-- The conditioned tail package: the kernel's nine hypotheses from means and
-- two transferred tails.  The PF₂ bootstrap runs at p_3 >= 0.14 (KKO's 1/4 is
-- 0.2507 at the true residual mean); the decreasing-cell tails come from the
-- antitone layer monotonicity, not from a Poisson comparison above mean 2.
#check_tsp_axioms TSPGap.rpow_ge_one_sub_mul
#check_tsp_axioms TSPGap.weightMass_one_le_ge_997
#check_tsp_axioms TSPGap.weightMass_one_le_ge_4977
#check_tsp_axioms TSPGap.weightMass_le_two_ge_of_mean
#check_tsp_axioms TSPGap.weightMass_eq_three_ge_of_baseline
#check_tsp_axioms TSPGap.lemma_A1_conditioned

-- The transfers through Lemma A.1's three conditionings: decreasing events
-- gain from a maximum face (present = the face at m = 1), lose at most E[C]
-- under avoidance, and presence rescales the bundle's own marginals.
#check_tsp_axioms TSPGap.weightMass_face_ge_of_antitone
#check_tsp_axioms TSPGap.weightMass_faceDist_ge_of_antitone
#check_tsp_axioms TSPGap.weightMass_avoidWeight_ge_sub_expCard
#check_tsp_axioms TSPGap.weightMass_avoidDist_ge_sub_expCard
#check_tsp_axioms TSPGap.expCard_presentWeight_of_subset
#check_tsp_axioms TSPGap.expCard_presentDist_of_subset

-- Lemma 5.15's analytic core: 2-2 goodness (p_{<=2} + p_{>=4} >= 3 eps), the
-- mean, and PF_2 give the low tail p_{<=2} >= 0.4 eps.
#check_tsp_axioms TSPGap.expCard_ge_truncated_moment
#check_tsp_axioms TSPGap.weightMass_four_cells_of_baseline
#check_tsp_axioms TSPGap.lemma_5_15_low_tail

-- KKO21 Lemma A.1 assembled: the sanitized cells, the three laws, the
-- eleven nu-means from the x-data, Lemma 5.15 at the two-atom face, the two
-- transferred tails, the package, and the 0.4987 lift to the ambient
-- 2-1-1 happy event.
#check_tsp_axioms TSPGap.lemma_A1

-- The TreeDist bridge and the TreeDist-facing instances of 5.17, 5.23, A.1:
-- expected counts are x-masses, the face deficiency is exactly
-- sum (x(delta(a))/2 - 1), the full between set is support complete, and the
-- hierarchy's children are the atoms.  Stability is treeRealStable, so these
-- inherit the IsMaxEntropyLimit route (axiom-clean).
#check_tsp_axioms TSPGap.expCard_prob_eq_sum
#check_tsp_axioms TSPGap.faceDeficiency_threeAtom_eq
#check_tsp_axioms TSPGap.faceDeficiency_twoAtom_eq
#check_tsp_axioms TSPGap.lemma_5_17_treeDist
#check_tsp_axioms TSPGap.lemma_5_23_treeDist
#check_tsp_axioms TSPGap.lemma_A1_treeDist
#check_tsp_axioms TSPGap.Hierarchy.pairData
#check_tsp_axioms TSPGap.Hierarchy.tripleData
#check_tsp_axioms TSPGap.lemma_5_24_treeDist
#check_tsp_axioms TSPGap.lemma_5_27_treeDist

-- Theorem 5.28's vocabulary: δ(S∖v) = δ(S) △ δ(v), x(δ→(v)) ≥ 1 − ε/2, and
-- δ→(v) as the disjoint union of the sibling bundles.
#check_tsp_axioms TSPGap.cutSum_arrow_ge
#check_tsp_axioms TSPGap.Hierarchy.cutEdges_sdiff_eq_biUnion
#check_tsp_axioms TSPGap.Hierarchy.cutSum_arrow_eq_sum

-- Theorem 5.28 (with Lemmas 5.21-5.22 as the input h2122).
#check_tsp_axioms TSPGap.theorem_5_28
#check_tsp_axioms TSPGap.two_half_bundles_211
#check_tsp_axioms TSPGap.lemma_5_25_of_le
#check_tsp_axioms TSPGap.lemma_5_25
#check_tsp_axioms TSPGap.lemma_5_25_B
#check_tsp_axioms TSPGap.upSum_le_one_add
#check_tsp_axioms TSPGap.cutSum_biUnion_eq
#check_tsp_axioms TSPGap.sum_upSum_eq
#check_tsp_axioms TSPGap.Hierarchy.touchSum_ge
#check_tsp_axioms TSPGap.Hierarchy.touchSum_ge_card
#check_tsp_axioms TSPGap.Hierarchy.topSum_ge
#check_tsp_axioms TSPGap.isGoodBundle_of_face
#check_tsp_axioms TSPGap.bad_unique_of_lemma_5_17
#check_tsp_axioms TSPGap.MatchingInputs.of_bad_up
#check_tsp_axioms TSPGap.MatchingInputs.isGoodBundle_of_card_three
#check_tsp_axioms TSPGap.isRealStable_genPoly_faceDist_max
#check_tsp_axioms TSPGap.setCost_nestedCost_eq_iff
#check_tsp_axioms TSPGap.faceDist_faceDist
#check_tsp_axioms TSPGap.nestedLaw_outside
#check_tsp_axioms TSPGap.Hierarchy.nestedData
#check_tsp_axioms TSPGap.probCount_one_ge_low
#check_tsp_axioms TSPGap.probCount_two_ge_mid
#check_tsp_axioms TSPGap.tails_of_baseline
#check_tsp_axioms TSPGap.bernoulli_newton_two
#check_tsp_axioms TSPGap.lemma_5_16_kernel
#check_tsp_axioms TSPGap.lemma_5_16
#check_tsp_axioms TSPGap.lemma_5_16_bad_up
#check_tsp_axioms TSPGap.Hierarchy.matchingInputs
#check_tsp_axioms TSPGap.Hierarchy.sum_touch_pairSum
#check_tsp_axioms TSPGap.Hierarchy.badIncident_card_even
#check_tsp_axioms TSPGap.Hierarchy.hall_inequality
#check_tsp_axioms TSPGap.cutCap_ge_of_hall
#check_tsp_axioms TSPGap.exists_saturating_flow
#check_tsp_axioms TSPGap.sum_bundleAlloc
#check_tsp_axioms TSPGap.bundleAlloc_bound
#check_tsp_axioms TSPGap.lemma_6_2
#check_tsp_axioms TSPGap.exists_thinning
#check_tsp_axioms TSPGap.TreeDist.expect_density_mul
#check_tsp_axioms TSPGap.TreeDist.expect_density
#check_tsp_axioms TSPGap.TreeDist.exists_thinning
#check_tsp_axioms TSPGap.reduction_pair_bounds

-- §7's uniform thinnings, reduction events, reduction vector, matching data,
-- increase (33), bottom increase (32) and slack vector (34).
#check_tsp_axioms TSPGap.isRescaling_rescaleWeight
#check_tsp_axioms TSPGap.IsRescaling.sum_mul
#check_tsp_axioms TSPGap.IsUniformThinning.sum_mul
#check_tsp_axioms TSPGap.IsUniformThinning.weightMass_mul
#check_tsp_axioms TSPGap.IsUniformThinning.weightMass_le
#check_tsp_axioms TSPGap.isUniformThinning_thinWeight
#check_tsp_axioms TSPGap.TreeDist.probEvent_mul_expect_density
#check_tsp_axioms TSPGap.TreeDist.probEvent_mul_expect_density_indicator
#check_tsp_axioms TSPGap.theorem_5_28_cases
#check_tsp_axioms TSPGap.Hierarchy.sum_ordered_pairs_eq
#check_tsp_axioms TSPGap.Hierarchy.exists_between_children_of_isEdgeParent
#check_tsp_axioms TSPGap.TopThinnings.probEvent_mul_expect_rho
#check_tsp_axioms TSPGap.TopThinnings.reduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.BottomThinning.totalMass_mul_expect_rho
#check_tsp_axioms TSPGap.ReductionData.reduction_le
#check_tsp_axioms TSPGap.ReductionData.reduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.exists_matchingData
#check_tsp_axioms TSPGap.MatchingData.sum_increase_of_odd
#check_tsp_axioms TSPGap.MatchingData.expect_increase
#check_tsp_axioms TSPGap.MatchingData.expect_increase_add_le
#check_tsp_axioms TSPGap.BottomThinning.increase_ge_left
#check_tsp_axioms TSPGap.PaymentData.slack_lower
#check_tsp_axioms TSPGap.PaymentData.slack_eq_zero_of_not_mem_goodEdges
#check_tsp_axioms TSPGap.PaymentData.sum_slack_nonneg_of_odd
#check_tsp_axioms TSPGap.good_mass_of_degree
#check_tsp_axioms TSPGap.PaymentData.left_unhappy
#check_tsp_axioms TSPGap.PaymentData.right_unhappy
#check_tsp_axioms TSPGap.PaymentData.expect_slack_top_le
#check_tsp_axioms TSPGap.PaymentData.expect_slack_bottom_le
#check_tsp_axioms TSPGap.twoOneOneGood_of_not_half
#check_tsp_axioms TSPGap.happyEvent_ge
#check_tsp_axioms TSPGap.PaymentData.paymentCore
#check_tsp_axioms TSPGap.IsMainPayment.of_core
#check_tsp_axioms TSPGap.selected_lift_le
#check_tsp_axioms TSPGap.exists_polygonBase
#check_tsp_axioms TSPGap.treeFace_indep
#check_tsp_axioms TSPGap.polygonLaw_indep
#check_tsp_axioms TSPGap.weightMass_selected_inside
#check_tsp_axioms TSPGap.weightMass_selected_cross
#check_tsp_axioms TSPGap.PolygonBase.happy
#check_tsp_axioms TSPGap.sum_even_probCount
#check_tsp_axioms TSPGap.evenCount_le
#check_tsp_axioms TSPGap.Hierarchy.exists_child_superset
#check_tsp_axioms TSPGap.Hierarchy.observation_4_32
#check_tsp_axioms TSPGap.Hierarchy.disjoint_partA_or_partB
#check_tsp_axioms TSPGap.cutEdges_subset_internal_union_cut
#check_tsp_axioms TSPGap.oddCount_le
#check_tsp_axioms TSPGap.one_sub_sum_le_prod
#check_tsp_axioms TSPGap.probCount_zero_ge
#check_tsp_axioms TSPGap.oddCount_ge
#check_tsp_axioms TSPGap.odd_split_le
#check_tsp_axioms TSPGap.odd_split_le_num
#check_tsp_axioms TSPGap.even_split_le
#check_tsp_axioms TSPGap.exp_two_ge_sharp
#check_tsp_axioms TSPGap.exp_two_mul_sub_two_le_sharp
#check_tsp_axioms TSPGap.even_split_le_num
#check_tsp_axioms TSPGap.card_dout_le_one
#check_tsp_axioms TSPGap.card_split_of_subcut
#check_tsp_axioms TSPGap.tv_subset
#check_tsp_axioms TSPGap.expCard_union_face_avoid
#check_tsp_axioms TSPGap.cutEdges_eq_din_union_dout
#check_tsp_axioms TSPGap.subset_eq_din_union_dout
#check_tsp_axioms TSPGap.disjoint_din_dout
#check_tsp_axioms TSPGap.mean_bounds_of_subset_part
#check_tsp_axioms TSPGap.mean_bounds_of_part
#check_tsp_axioms TSPGap.insideDetermined_mem
#check_tsp_axioms TSPGap.PolygonBase.expCard_inside
#check_tsp_axioms TSPGap.PolygonBase.expCard_split
#check_tsp_axioms TSPGap.weightMass_eq_zero_of_support
#check_tsp_axioms TSPGap.din_disjoint_dout
#check_tsp_axioms TSPGap.corollary_5_10
#check_tsp_axioms TSPGap.one_le_card_din
#check_tsp_axioms TSPGap.weightMass_din_eq_zero
#check_tsp_axioms TSPGap.expCard_polygonLaw_eq_zero
#check_tsp_axioms TSPGap.corollary_5_10_core

-- KKO Corollary 5.11: `P[u not left happy | E_S] ≤ 0.56797`.
#check_tsp_axioms TSPGap.card_split_of_subset
#check_tsp_axioms TSPGap.sdiff_subset_partC
#check_tsp_axioms TSPGap.PolygonBase.weightMass_meets_le
#check_tsp_axioms TSPGap.corollary_5_11_even_core
#check_tsp_axioms TSPGap.corollary_5_11_part
#check_tsp_axioms TSPGap.corollary_5_11
#check_tsp_axioms TSPGap.corollary_5_11_right
#check_tsp_axioms TSPGap.IsRescaling.weightMass_le
#check_tsp_axioms TSPGap.exists_bottomThinning
#check_tsp_axioms TSPGap.outsideDetermined_inducesTree
#check_tsp_axioms TSPGap.isRectangularAt_twoTwoTwoHappy
#check_tsp_axioms TSPGap.isRectangularAt_happyEventOf
#check_tsp_axioms TSPGap.exists_topThinnings
#check_tsp_axioms TSPGap.inducesTree_iff_of_support
#check_tsp_axioms TSPGap.IsRectangularAt.weightMass_factor
#check_tsp_axioms TSPGap.IsRectangularAt.thin_weightMass_le
#check_tsp_axioms TSPGap.IsRectangularAt.thin_expCard_le
#check_tsp_axioms TSPGap.one_add_add_sq_div_two_le_exp
#check_tsp_axioms TSPGap.sub_sq_le_one_sub_exp_neg_two_mul
#check_tsp_axioms TSPGap.weightMass_din_treeFace_eq_zero
#check_tsp_axioms TSPGap.claim_7_5_core
#check_tsp_axioms TSPGap.claim_7_5
#check_tsp_axioms TSPGap.claim_7_5_nested
#check_tsp_axioms TSPGap.one_le_card_din_treeFace
#check_tsp_axioms TSPGap.weightMass_even_add_total_le_expCard
#check_tsp_axioms TSPGap.card_crossing_eq_one_of_sides
#check_tsp_axioms TSPGap.claim_7_4
#check_tsp_axioms TSPGap.ite_instance_congr
#check_tsp_axioms TSPGap.TopThinnings.expect_rho_le
#check_tsp_axioms TSPGap.BottomThinning.expect_rho_le
#check_tsp_axioms TSPGap.ReductionData.topRect
#check_tsp_axioms TSPGap.ReductionData.bottomGuar
#check_tsp_axioms TSPGap.ReductionData.expect_rho_bottom_odd_le
#check_tsp_axioms TSPGap.Hierarchy.ancestors
#check_tsp_axioms TSPGap.tail_antitone
#check_tsp_axioms TSPGap.upSum_antitone
#check_tsp_axioms TSPGap.sum_layer_eq
#check_tsp_axioms TSPGap.isEdgeParent_of_mem_layer
#check_tsp_axioms TSPGap.exists_lastAbove
#check_tsp_axioms TSPGap.exists_lastAboveFrom
#check_tsp_axioms TSPGap.Hierarchy.ancestors_comparable
#check_tsp_axioms TSPGap.Hierarchy.subset_of_card_le_of_mem_ancestors
#check_tsp_axioms TSPGap.exists_lastAboveFrom_of_mem
#check_tsp_axioms TSPGap.lastAbove_root_or_parent
#check_tsp_axioms TSPGap.mem_layer_iff
#check_tsp_axioms TSPGap.layer_eq_inter_sdiff
#check_tsp_axioms TSPGap.layer_eq_biUnion
#check_tsp_axioms TSPGap.layer_parent_classification
#check_tsp_axioms TSPGap.not_isEdgeParent_of_mem_root_tail
#check_tsp_axioms TSPGap.layer_eq_biUnion_fibers
#check_tsp_axioms TSPGap.layer_fibers_disjoint
#check_tsp_axioms TSPGap.sum_layer_eq_sum_fibers
#check_tsp_axioms TSPGap.goodSiblings
#check_tsp_axioms TSPGap.badSiblings
#check_tsp_axioms TSPGap.sum_siblings_split
#check_tsp_axioms TSPGap.isBottomEdge_of_mem_layer
#check_tsp_axioms TSPGap.isGoodTopEdge_of_mem_good_fiber
#check_tsp_axioms TSPGap.TopThinnings.rho_eq_zero_of_not_good
#check_tsp_axioms TSPGap.TopThinnings.reduction_eq_zero_of_bad_bundle
#check_tsp_axioms TSPGap.TopThinnings.sum_reduction_bad_fiber
#check_tsp_axioms TSPGap.reduction_eq_zero_of_mem_root_tail
#check_tsp_axioms TSPGap.sum_reduction_root_tail
#check_tsp_axioms TSPGap.sum_expect_reduction_root_tail_odd
#check_tsp_axioms TSPGap.eq40_absorb_bottom
#check_tsp_axioms TSPGap.eq41_of_mass_slack
#check_tsp_axioms TSPGap.eq41_slack_of_bottom_floor
#check_tsp_axioms TSPGap.eq41_slack_of_inactive_floor
#check_tsp_axioms TSPGap.eq42_of_weighted_saving
#check_tsp_axioms TSPGap.eq41_ceiling
#check_tsp_axioms TSPGap.eq41_bottom_num
#check_tsp_axioms TSPGap.eq41_anchor
#check_tsp_axioms TSPGap.eq41_inactive_num
#check_tsp_axioms TSPGap.eq41_bottom_frac_num
#check_tsp_axioms TSPGap.sum_split_three
#check_tsp_axioms TSPGap.goodTop_le_one_add
#check_tsp_axioms TSPGap.oddReductionMass
#check_tsp_axioms TSPGap.oddReductionMass_split
#check_tsp_axioms TSPGap.ssubset_of_isEdgeParent
#check_tsp_axioms TSPGap.exists_bundle_of_isEdgeParent
#check_tsp_axioms TSPGap.reduction_eq_zero_of_inactive
#check_tsp_axioms TSPGap.oddReductionMass_inactive_eq_zero
#check_tsp_axioms TSPGap.oddReductionMass_bottom_le
#check_tsp_axioms TSPGap.ReductionData.expect_reduction_top
#check_tsp_axioms TSPGap.ReductionData.expect_reduction_bottom
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_le
#check_tsp_axioms TSPGap.TopThinnings.expect_rho_odd_le
#check_tsp_axioms TSPGap.edgeInside_of_mem_cut_of_not_mem_cut
#check_tsp_axioms TSPGap.subset_child_of_common_descendant
#check_tsp_axioms TSPGap.exists_good_bundle_of_mem_goodTop
#check_tsp_axioms TSPGap.exists_good_bundle_of_mem_goodTop_window
#check_tsp_axioms TSPGap.expect_reduction_top_odd_le
#check_tsp_axioms TSPGap.oddReductionMass_le_of_pointwise
#check_tsp_axioms TSPGap.thin_odd_le_of_good_bundle
#check_tsp_axioms TSPGap.expect_reduction_odd_le_of_window
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_window_le
#check_tsp_axioms TSPGap.upSum_eq_sum_inter
#check_tsp_axioms TSPGap.parent_subset_of_ssubset
#check_tsp_axioms TSPGap.upSum_le_upSum_parent
#check_tsp_axioms TSPGap.exists_good_bundle_of_mem_window
#check_tsp_axioms TSPGap.fFactor_eq_one_of_gt
#check_tsp_axioms TSPGap.fFactor_eq_one_of_lt
#check_tsp_axioms TSPGap.case2_saving_rate
#check_tsp_axioms TSPGap.exists_good_bundle_of_mem_parent_window
#check_tsp_axioms TSPGap.upSum_sandwich
#check_tsp_axioms TSPGap.expect_reduction_odd_le_of_parent_window
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_parent_window_le
#check_tsp_axioms TSPGap.expect_reduction_odd_le_of_root_window
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_root_window_le
#check_tsp_axioms TSPGap.case2_eq41_of_large_part
#check_tsp_axioms TSPGap.good_mass_gt_of_small_parts
#check_tsp_axioms TSPGap.good_mass_window_ge
#check_tsp_axioms TSPGap.good_bound_of_window
#check_tsp_axioms TSPGap.case2_saving_ge
#check_tsp_axioms TSPGap.case2_eq42
#check_tsp_axioms TSPGap.case2_assemble
#check_tsp_axioms TSPGap.epsB_eq_of_both
#check_tsp_axioms TSPGap.epsB_le_one_hundredth
#check_tsp_axioms TSPGap.eq40_absorb_bottom_specialized
#check_tsp_axioms TSPGap.case2_assemble_specialized
#check_tsp_axioms TSPGap.case2_assemble_eq41_specialized
#check_tsp_axioms TSPGap.case2_target_of_branches
#check_tsp_axioms TSPGap.case2_eq41_factor
#check_tsp_axioms TSPGap.case2_eq41_factor_lower
#check_tsp_axioms TSPGap.oddReductionMass_split_subset
#check_tsp_axioms TSPGap.goodTop_sdiff_window
#check_tsp_axioms TSPGap.goodTop_window_subset
#check_tsp_axioms TSPGap.case2_common
#check_tsp_axioms TSPGap.case2_large_branch
#check_tsp_axioms TSPGap.case2_close_of_window
#check_tsp_axioms TSPGap.case2_small_branch
#check_tsp_axioms TSPGap.case2_target
#check_tsp_axioms TSPGap.assemble_of_eq40
#check_tsp_axioms TSPGap.assemble_eq41_of_eq40
#check_tsp_axioms TSPGap.case3_cF_lower
#check_tsp_axioms TSPGap.case3_rate_le
#check_tsp_axioms TSPGap.case3_eq42
#check_tsp_axioms TSPGap.case3_eq41_of_bottom_floor
#check_tsp_axioms TSPGap.case3_eq41_of_inactive_floor
#check_tsp_axioms TSPGap.case3_close_of_good
#check_tsp_axioms TSPGap.case3_close_of_eq41
#check_tsp_axioms TSPGap.fFactor_eq_sub_of_fractional
#check_tsp_axioms TSPGap.thin_odd_le_of_good_bundle_nested
#check_tsp_axioms TSPGap.expect_reduction_odd_le_of_parent
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_parent_le
#check_tsp_axioms TSPGap.case3_target
#check_tsp_axioms TSPGap.exists_good_bundle_of_mem_upper_window
#check_tsp_axioms TSPGap.expect_reduction_odd_le_of_upper_window
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_upper_window_le
#check_tsp_axioms TSPGap.expect_reduction_odd_le_of_upper_root
#check_tsp_axioms TSPGap.oddReductionMass_goodTop_upper_root_le
#check_tsp_axioms TSPGap.goodTop_sdiff
#check_tsp_axioms TSPGap.goodTop_mass_ge_of_subset
#check_tsp_axioms TSPGap.case1b_branch
#check_tsp_axioms TSPGap.oddReductionMass_le_of_goodTop
#check_tsp_axioms TSPGap.twoOneOneSiblings
#check_tsp_axioms TSPGap.notTwoOneOne_eq
#check_tsp_axioms TSPGap.sum_twoOneOne_split
#check_tsp_axioms TSPGap.inactive_of_mem_bad_fiber
#check_tsp_axioms TSPGap.sum_bad_fibers_le_inactive
#check_tsp_axioms TSPGap.twoOneOneWindow
#check_tsp_axioms TSPGap.twoOneOneWindow_subset_layer
#check_tsp_axioms TSPGap.sum_twoOneOneWindow
#check_tsp_axioms TSPGap.not_isBottomEdge_of_mem_fiber
#check_tsp_axioms TSPGap.isGoodTopEdge_of_mem_twoOneOneWindow
#check_tsp_axioms TSPGap.mem_goodTopPart_of_mem_twoOneOneWindow
#check_tsp_axioms TSPGap.twoOneOne_window_mass_ge
#check_tsp_axioms TSPGap.oddReductionMass_twoOneOneWindow_le
#check_tsp_axioms TSPGap.close_of_good_window
#check_tsp_axioms TSPGap.case1a_of_side
#check_tsp_axioms TSPGap.case1a_branch
#check_tsp_axioms TSPGap.inactive_of_mem_root_tail
#check_tsp_axioms TSPGap.upSum_root_le_inactive
#check_tsp_axioms TSPGap.lemma_7_3
#check_tsp_axioms TSPGap.one_sub_le_fFactor
#check_tsp_axioms TSPGap.zFactor_eq_one_of_card_lt
#check_tsp_axioms TSPGap.zFactor_eq_two_of
#check_tsp_axioms TSPGap.MatchingData.coeff_mul_upSum_mul_zFactor_le
#check_tsp_axioms TSPGap.MatchingData.expect_increase_zFactor_le
#check_tsp_axioms TSPGap.oddReductionMass_tail_le
#check_tsp_axioms TSPGap.threeAtom_identities
#check_tsp_axioms TSPGap.threeAtom_heavy
#check_tsp_axioms TSPGap.threeAtom_m_ge
#check_tsp_axioms TSPGap.lemma76_arith_three
#check_tsp_axioms TSPGap.epsEta_le_eps1_div_400
#check_tsp_axioms TSPGap.lemma76_arith_low
#check_tsp_axioms TSPGap.lemma76_arith_high
#check_tsp_axioms TSPGap.exists_third_atom
#check_tsp_axioms TSPGap.lemma76_three
#check_tsp_axioms TSPGap.lemma76_four_low
#check_tsp_axioms TSPGap.lemma76_four_high
#check_tsp_axioms TSPGap.lemma_7_6
#check_tsp_axioms TSPGap.lemma_7_2_of_lemma_7_3
#check_tsp_axioms TSPGap.lemma_7_2
#check_tsp_axioms TSPGap.lemma_5_25_B_of_le
#check_tsp_axioms TSPGap.expect_reduction_top_odd_le₂
#check_tsp_axioms TSPGap.thin_odd_le_trivial
#check_tsp_axioms TSPGap.thin_odd_le_of_twoOneOne
#check_tsp_axioms TSPGap.outsidePart_nested
#check_tsp_axioms TSPGap.OutsideDetermined.descend
#check_tsp_axioms TSPGap.insidePart_nested_union
#check_tsp_axioms TSPGap.insidePart_disjoint_outside
#check_tsp_axioms TSPGap.InducesTree.glue_nested
#check_tsp_axioms TSPGap.IsRectangularAt.nested
#check_tsp_axioms TSPGap.treeFace_not_inducesTree_le
#check_tsp_axioms TSPGap.claim_7_5_nested'
#check_tsp_axioms TSPGap.Hierarchy.mem_cuts_of_mem_children
#check_tsp_axioms TSPGap.DegreePartition.A_subset
#check_tsp_axioms TSPGap.DegreePartition.B_subset
#check_tsp_axioms TSPGap.DegreePartition.C_subset
#check_tsp_axioms TSPGap.DegreePartitions.Bat
#check_tsp_axioms TSPGap.DegreePartitions.Cat
#check_tsp_axioms TSPGap.TwoOneOneCaseOf
#check_tsp_axioms TSPGap.happyEventOf
#check_tsp_axioms TSPGap.DegreePartitions.ControlsDescendants
#check_tsp_axioms TSPGap.DegreePartition.ControlsDescendants.disjoint_of_mem
#check_tsp_axioms TSPGap.outsideDetermined_inter_self
#check_tsp_axioms TSPGap.outsideDetermined_inter_disjoint
#check_tsp_axioms TSPGap.IsRectangularAt.and_const
#check_tsp_axioms TSPGap.isRectangularAt_ite
#check_tsp_axioms TSPGap.isRectangularAt_twoTwoHappy
#check_tsp_axioms TSPGap.isRectangularAt_twoTwoHappy'
#check_tsp_axioms TSPGap.isRectangularAt_twoOneOneHappy
#check_tsp_axioms TSPGap.isRectangularAt_twoOneOneHappy'
#check_tsp_axioms TSPGap.isRectangularAt_happyEventOf'
#check_tsp_axioms TSPGap.isRectangularAt_twoTwoTwoHappy_fst
#check_tsp_axioms TSPGap.isRectangularAt_twoTwoTwoHappy_snd
#check_tsp_axioms TSPGap.TopRectangular
#check_tsp_axioms TSPGap.IsRectangularAt.weightMass_factor'
#check_tsp_axioms TSPGap.mem_tail
#check_tsp_axioms TSPGap.Hierarchy.mem_ancestors
#check_tsp_axioms TSPGap.DegreePartition.ControlsDescendants
#check_tsp_axioms TSPGap.DegreePartitions.Aat

-- Lemmas 5.21/5.22's Poisson-branch tails (Lemma 2.21 instances; no Hoeffding).
#check_tsp_axioms TSPGap.probCount_two_ge_small
#check_tsp_axioms TSPGap.probCount_two_ge_high
#check_tsp_axioms TSPGap.weightMass_eq_four_ge_of_baseline_two
#check_tsp_axioms TSPGap.weightMass_eq_three_ge_of_baseline_high
#check_tsp_axioms TSPGap.lemma_5_22_kernel
#check_tsp_axioms TSPGap.lemma_5_21_kernel
#check_tsp_axioms TSPGap.LawData.avoid
#check_tsp_axioms TSPGap.LawData.present
#check_tsp_axioms TSPGap.twoAtomTauData
#check_tsp_axioms TSPGap.lemma_5_21
#check_tsp_axioms TSPGap.probCount_succ_split
#check_tsp_axioms TSPGap.weightMass_two_le_ge_of_mean_199
#check_tsp_axioms TSPGap.lemma_5_22
#check_tsp_axioms TSPGap.lemma_5_21_treeDist
#check_tsp_axioms TSPGap.lemma_5_22_treeDist

-- Lemma 5.24's independence step: four cross-multiplied instances of Fact
-- 2.8 at S = u u v give P_nu[A and B] = P_nu[A] P_nu[B] for inside/outside
-- determined events under the conditioned law, with no positivity.
#check_tsp_axioms TSPGap.insideDetermined_inter
#check_tsp_axioms TSPGap.outsideDetermined_inter
#check_tsp_axioms TSPGap.insideDetermined_inducesTree
#check_tsp_axioms TSPGap.condIndep_conditioned
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.condIndep_conditioned

-- Lemma 5.24's analytic kernel: one three-cell call at (X, Y) from the
-- 0.2 eps two-count and the 0.63 / 0.245 tails.
#check_tsp_axioms TSPGap.lemma_5_24_kernel

-- Lemma 5.24 assembled: Lemma A.1's setup, the kernel, Fact 2.8 for the
-- parity correction, and the 0.4987 lift.
#check_tsp_axioms TSPGap.lemma_5_24

-- Lemma 5.27's generic tools: the near-certain conditional bound, Claim
-- A.2's quadratic dichotomy, and KKO Cor 2.19 (geometric tail of a PF2 rank
-- law bounding the mean).
#check_tsp_axioms TSPGap.weightMass_and_ge_sub
#check_tsp_axioms TSPGap.dichotomy_of_quadratic
#check_tsp_axioms TSPGap.PF2.decay
#check_tsp_axioms TSPGap.mean_le_of_pf2
#check_tsp_axioms TSPGap.sum_range_probCount_eq_one

-- Claim A.2 (generic): the between-bundle of the outer atoms is nearly
-- present or nearly absent, by log-concavity and the quadratic dichotomy.
#check_tsp_axioms TSPGap.claim_A2

-- Corollary 2.19 at the weight level (general and the k = 2 instance).
#check_tsp_axioms TSPGap.expCard_le_of_concentrated
#check_tsp_axioms TSPGap.expCard_le_two_add_of_concentrated

-- Lemma 5.27: the core at the conditioned law (Lemma 2.21 at k = 1 with
-- piecewise exp bounds, Markov, the union bound) and the Z-absent case.
#check_tsp_axioms TSPGap.weightMass_eq_one_ge_of_mean
#check_tsp_axioms TSPGap.lemma_5_27_core
#check_tsp_axioms TSPGap.lemma_5_27_absent
#check_tsp_axioms TSPGap.lemma_5_27_eq56
#check_tsp_axioms TSPGap.lemma_5_27_dichotomy
#check_tsp_axioms TSPGap.lemma_5_27_present
#check_tsp_axioms TSPGap.lemma_5_27

-- KKO22 Theorem B.3, proved (`Theorem61.lean`), and Theorem 6.1 above it.
#check_tsp_axioms TSPGap.exists_payment_hierarchy
#check_tsp_axioms TSPGap.slack_mixture_good_gain
#check_tsp_axioms TSPGap.slack_mixture_bad_gain
#check_tsp_axioms TSPGap.exists_slack_pair_sharp
#check_tsp_axioms TSPGap.exists_slack_pair
#check_tsp_axioms TSPGap.kko_eq_nine
#check_tsp_axioms TSPGap.kkoEps_le_gain

-- Towards Theorem B.3: the payment shared by Types 2, 4 and 5.
#check_tsp_axioms TSPGap.payment_of_pay
#check_tsp_axioms TSPGap.payment_of_nonneg
#check_tsp_axioms TSPGap.exists_slackStar_bothSides
#check_tsp_axioms TSPGap.exists_slackStar_oneSide
#check_tsp_axioms TSPGap.NearCycle.partA_union_partB_union_partC
#check_tsp_axioms TSPGap.Hierarchy.children_disjoint
#check_tsp_axioms TSPGap.negPart_le_sum
#check_tsp_axioms TSPGap.payment_of_negPart
#check_tsp_axioms TSPGap.payment_of_classification
#check_tsp_axioms TSPGap.NearCycle.one_sub_le_sum_sideEdges_left
#check_tsp_axioms TSPGap.NearCycle.sum_upEdges_le_left
#check_tsp_axioms TSPGap.NearCycle.sideEdges_eq_betweenEdges
#check_tsp_axioms TSPGap.NearCycle.isNearMinCut_outerCut
#check_tsp_axioms TSPGap.NearCycle.one_sub_half_le_sum_sideEdges
#check_tsp_axioms TSPGap.NearCycle.sum_upEdges_le_one_add

-- Definition B.1's parent calculus: `p(S)` is `IsChildOf`, `p(e)` is
-- `IsEdgeParent`, and neither is stored by the hierarchy.
#check_tsp_axioms TSPGap.Hierarchy.exists_isEdgeParent
#check_tsp_axioms TSPGap.Hierarchy.IsEdgeParent.unique
#check_tsp_axioms TSPGap.Hierarchy.isEdgeParent_of_between_children
#check_tsp_axioms TSPGap.Hierarchy.Presents.isEdgeParent_of_mem_sideEdges

-- Type 4's local package: the split `δ(S) = A ⊍ D ⊍ F` and the payment it
-- feeds.  `payment_of_leftmost/rightmost` take Theorem B.2 as a hypothesis,
-- so they are axiom-clean; `exists_mainPayment` is proved in `MainPaymentExistence.lean`.
#check_tsp_axioms TSPGap.NearCycle.upEdges_sdiff_partA_subset_partC
#check_tsp_axioms TSPGap.NearCycle.upEdges_sdiff_partB_subset_partC
#check_tsp_axioms TSPGap.NearCycle.exists_split_left
#check_tsp_axioms TSPGap.NearCycle.exists_split_right
#check_tsp_axioms TSPGap.NearCycle.nonempty_outerCut_sdiff_interval
#check_tsp_axioms TSPGap.NearCycle.sideEdges_subset_edges
#check_tsp_axioms TSPGap.payment_of_leftmost
#check_tsp_axioms TSPGap.payment_of_rightmost
#check_tsp_axioms TSPGap.good_mass_of_nested

-- Components of the induced family `N_{η,≤1}`, and the family of them.
#check_tsp_axioms TSPGap.isOneSideComponent_oneSideComp
#check_tsp_axioms TSPGap.exists_isOneSideComponent_mem
#check_tsp_axioms TSPGap.IsOneSideComponent.eq_of_mem_of_mem
#check_tsp_axioms TSPGap.IsOneSideComponent.not_crossing_of_ne
#check_tsp_axioms TSPGap.OneSideFamily.mem_rootAtom
#check_tsp_axioms TSPGap.OneSideFamily.avoidsRootEdge_outerCut
#check_tsp_axioms TSPGap.OneSideFamily.subset_outerCut
-- The family's polygon, `polygonRep_exists_oneSide`, is proved (2026-09-08).
#check_tsp_axioms TSPGap.exists_oneSideFamily

-- The component-to-near-cycle correspondence: Appendix A's near-cycle for a
-- component IS Definition B.1's near-cycle cut of the hierarchy.
#check_tsp_axioms TSPGap.PolygonRep.toNearCycle_root
#check_tsp_axioms TSPGap.PolygonRep.toNearCycle_atom_iff
#check_tsp_axioms TSPGap.PolygonRep.toNearCycle_avoids
#check_tsp_axioms TSPGap.Hierarchy.presents_of_atoms
#check_tsp_axioms TSPGap.OneSideFamily.IsHierarchyOf.presents
-- The seam: it carried `sorryAx` for Appendix A's inputs until those were proved
-- (2026-09-09); it is clean now.
#check_tsp_axioms TSPGap.OneSideFamily.exists_slackStar_of_index

-- Globalizing Appendix A: the group support, and the disjointness it buys.
#check_tsp_axioms TSPGap.NearCycle.happySlack_eq_zero
#check_tsp_axioms TSPGap.boundary_of_mem_chargeSet'
#check_tsp_axioms TSPGap.Hierarchy.Presents.isEdgeParent_of_mem_group
#check_tsp_axioms TSPGap.TreeDist.expect_sum'
#check_tsp_axioms TSPGap.OneSideFamily.exists_slackStar_global

-- Lemma A.13: the triangle is Theorem A.12 at `k = 0`.  Its only assumed
-- input was Corollary 2.12, now proved — so the whole triangle chain is
-- axiom-clean: no near-cycle input, and no polygon.
#check_tsp_axioms TSPGap.middleAtoms_zero
#check_tsp_axioms TSPGap.triangle_pairSum_le
#check_tsp_axioms TSPGap.triangle_le_pairSum_compl
#check_tsp_axioms TSPGap.rootEdge_notMem_betweenEdges_left
#check_tsp_axioms TSPGap.exists_happySlack_triangle
#check_tsp_axioms TSPGap.Hierarchy.presents_of_atom_iff
#check_tsp_axioms TSPGap.exists_slackStar_triangle

-- The five-type classification, and the payment it feeds.
#check_tsp_axioms TSPGap.Hierarchy.exists_isChildOf
#check_tsp_axioms TSPGap.Hierarchy.IsChildOf.unique
#check_tsp_axioms TSPGap.OneSideFamily.mem_relevantAtoms
#check_tsp_axioms TSPGap.OneSideFamily.IsHierarchyOf.classify
#check_tsp_axioms TSPGap.payment_of_interval
#check_tsp_axioms TSPGap.payment_of_nearCycleCut
#check_tsp_axioms TSPGap.payment_of_hierarchy

-- Theorem B.3 assembled.  It carried `sorryAx` for Appendix A's inputs and the polygon of
-- an induced component until those were proved; it is clean now.
#check_tsp_axioms TSPGap.NearCycle.nonempty_outerCut_sdiff_of_proper
#check_tsp_axioms TSPGap.exists_slackStar_hierarchy
#check_tsp_axioms TSPGap.exists_payment_of_hierarchy

-- The end-to-end theorem.  Until 2026-09-10 its `sorryAx` covered the polygon boxes and
-- the four named inputs of `OJoin.lean`; the last of these, Edmonds–Johnson, is proved
-- (`EdmondsJoin.lean`), and both are **axiom-clean**; since 2026-09-11 `BlackBoxes.lean`
-- holds no box at all.
#check_tsp_axioms TSPGap.exists_tour_of_rootEdge
#check_tsp_axioms TSPGap.kko_gap

-- Definition 5.18 under the small-edge hypothesis, and the price of that
-- hypothesis.  All three are proved outright; none should reach `sorryAx`.
#check_tsp_axioms TSPGap.exists_subset_sum_mem_Icc
#check_tsp_axioms TSPGap.exists_degreePartition_of_small
#check_tsp_axioms TSPGap.smallCutEdges_two_le_card_mul
#check_tsp_axioms TSPGap.exists_degreePartitions_of_small

-- The bridge from KKO21's closed near-min-cut convention to KKO22's strict one.
#check_tsp_axioms TSPGap.IsNearMinCut.cut_lt_of_lt

-- The parallel-edge refinement layer, file 1: the object, the bridge identity,
-- and existence.  All proved outright.
#check_tsp_axioms TSPGap.cutEdges_subset_edgeFinset
#check_tsp_axioms TSPGap.EdgeRefinement.sum_piecesOver
#check_tsp_axioms TSPGap.exists_edgeRefinement

-- Refinement layer, file 2: the lift of a tree law to pieces projects back.
#check_tsp_axioms TSPGap.EdgeRefinement.sum_transversals_prod_q
#check_tsp_axioms TSPGap.EdgeRefinement.lift_pushforward
#check_tsp_axioms TSPGap.EdgeRefinement.lift_total
#check_tsp_axioms TSPGap.EdgeRefinement.lift_marginal
#check_tsp_axioms TSPGap.EdgeRefinement.lift_probEvent

-- Refinement layer, file 3: the lifted law is real stable.
#check_tsp_axioms TSPGap.EdgeRefinement.sum_lift_mul_prod
#check_tsp_axioms TSPGap.EdgeRefinement.isRealStable_genPoly_lift
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.refinedTreeRealStable

-- Refinement layer, file 4: Definition 5.18 on pieces, at every hierarchy cut,
-- with no hypothesis on the original edges.
#check_tsp_axioms TSPGap.EdgeRefinement.exists_degreePartitionOn
#check_tsp_axioms TSPGap.exists_refinement_degreePartitions

-- Refinement layer, file 5: the descendant clause on pieces, and the mass gate
-- that makes seeding a side with a qualifier's pieces legitimate.
#check_tsp_axioms TSPGap.EdgeRefinement.qualifyingPieces_weight_bounds
#check_tsp_axioms TSPGap.minQualifier_unique_of_subset
#check_tsp_axioms TSPGap.minQualifier_not_three
#check_tsp_axioms TSPGap.EdgeRefinement.mkPartition
#check_tsp_axioms TSPGap.EdgeRefinement.exists_degreePartitionOn_controls
#check_tsp_axioms TSPGap.exists_refinement_degreePartitions_controls

-- Refinement layer, file 6: the lifted law as a generic weight.  Rank, support,
-- the guarded cardinality bridge, projected events/expectations/`expCard`, and
-- face/avoid conditioning commuting with the lift.  All proved outright.
#check_tsp_axioms TSPGap.EdgeRefinement.fixedRankWeight_liftWeight
#check_tsp_axioms TSPGap.EdgeRefinement.weightSupportedOn_liftWeight
#check_tsp_axioms TSPGap.EdgeRefinement.liftWeight_pushforward
#check_tsp_axioms TSPGap.EdgeRefinement.card_inter_piecesOver_of_transversal
#check_tsp_axioms TSPGap.EdgeRefinement.weightMass_liftWeight_project
#check_tsp_axioms TSPGap.EdgeRefinement.expCard_liftWeight
#check_tsp_axioms TSPGap.EdgeRefinement.faceWeight_liftWeight
#check_tsp_axioms TSPGap.EdgeRefinement.avoidWeight_liftWeight
#check_tsp_axioms TSPGap.EdgeRefinement.setCost_comp_base_of_transversal
#check_tsp_axioms TSPGap.EdgeRefinement.faceWeight_liftWeight_cost

-- Fact 2.8 for determined functions (base side), and step 2's scaffolding on
-- pieces: the section split, gluing, and topology through the projection.
#check_tsp_axioms TSPGap.TreeCondIndep.functional
#check_tsp_axioms TSPGap.EdgeRefinement.sum_transversals_split
#check_tsp_axioms TSPGap.EdgeRefinement.RefinedInducesTreeOn.glue

-- Step 2's transport: Fact 2.8 on the base carries to the lifted law through
-- the product kernel.  All proved outright.
#check_tsp_axioms TSPGap.EdgeRefinement.sum_transversals_factor
#check_tsp_axioms TSPGap.EdgeRefinement.treeCondIndep_liftWeight
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.refinedTreeCondIndep

-- Step 2's consumer-facing half: the determinacy combinators, the piece tree
-- face and its support bridge, and Fact 2.8 at the piece tree face.
#check_tsp_axioms TSPGap.EdgeRefinement.refinedInsideDetermined_project
#check_tsp_axioms TSPGap.EdgeRefinement.refinedTreeFace_liftProb
#check_tsp_axioms TSPGap.EdgeRefinement.inducesTreeOn_project_iff_card
#check_tsp_axioms TSPGap.EdgeRefinement.refinedTreeFace_unwind
#check_tsp_axioms TSPGap.EdgeRefinement.refinedCondIndep_conditioned
#check_tsp_axioms TSPGap.EdgeRefinement.refinedTreeFace_indep
#check_tsp_axioms TSPGap.IsMaxEntropyLimit.refinedCondIndep_conditioned

-- Step 3: the piece payment core and the conditional-averaging theorem that
-- sends it to the base `PaymentCore`, with the negative-part concavity step.
#check_tsp_axioms TSPGap.EdgeRefinement.kernelAvg_negPart_le
#check_tsp_axioms TSPGap.EdgeRefinement.expect_kernelAvg
#check_tsp_axioms TSPGap.PiecePaymentCore.paymentCore
#check_tsp_axioms TSPGap.PiecePaymentCore.isMainPayment

-- Step 4, first file: the happy events on pieces, the piece partition family,
-- KKO's H_{e,u} on pieces, and rectangularity at both endpoints.
#check_tsp_axioms TSPGap.EdgeRefinement.exists_degreePartitionsOn_controls
#check_tsp_axioms TSPGap.EdgeRefinement.weightMass_liftProb_twoTwoHappyOn
#check_tsp_axioms TSPGap.EdgeRefinement.isTwoTwoTwoGood_iff_on
#check_tsp_axioms TSPGap.EdgeRefinement.HappyWrtOn.not_odd
#check_tsp_axioms TSPGap.EdgeRefinement.isRectangularAtOn_twoOneOneHappyOn
#check_tsp_axioms TSPGap.EdgeRefinement.isRectangularAtOn_twoTwoTwoHappyOn

-- The §5 genericization, pilot: the fiber tree model and its certificates,
-- Lemma 5.21 over a model, the identity-model wrapper (statement unchanged),
-- and the lifted-piece instance.
#check_tsp_axioms TSPGap.FiberTreeModel.card_inter_fiberOver_of_transversal
#check_tsp_axioms TSPGap.faceLawData
#check_tsp_axioms TSPGap.FiberTreeModel.TwoAtomCountData.ofSupport
#check_tsp_axioms TSPGap.FiberTreeModel.TwoAtomOneHotData.ofSupport
#check_tsp_axioms TSPGap.FiberTreeModel.twoAtomFaceData
#check_tsp_axioms TSPGap.lemma_5_21_indexed
#check_tsp_axioms TSPGap.lemma_5_22_indexed
#check_tsp_axioms TSPGap.lemma_5_21
#check_tsp_axioms TSPGap.EdgeRefinement.refinedPairData
#check_tsp_axioms TSPGap.lemma_5_21_liftProb
#check_tsp_axioms TSPGap.lemma_5_22_liftProb

-- The §5 genericization, fourth core: Lemma A.1 over a model with support
-- completeness and sanitization generic in the bundle and the union-crossing
-- certificate; the identity wrapper (statement unchanged) and the
-- lifted-piece instance.
#check_tsp_axioms TSPGap.card_split_of_supportCompleteOn
#check_tsp_axioms TSPGap.FiberTreeModel.nu_fixedRankNormalized_stable
#check_tsp_axioms TSPGap.FiberTreeModel.TwoAtomCrossData.ofSupport
#check_tsp_axioms TSPGap.lemma_A1_indexed
#check_tsp_axioms TSPGap.lemma_A1_liftProb

-- The §5 genericization, fifth core: Lemma 5.24 over a model, parameterized by
-- its two conditioned-independence identities (Fact 2.8 at `u ∪ v`, supplied
-- by the wrappers from the base and the refined Fact 2.8) and the union-tree
-- certificate; the identity wrapper (statement unchanged) and the
-- lifted-piece instance.
#check_tsp_axioms TSPGap.FiberTreeModel.TwoAtomUnionData.ofSupport
#check_tsp_axioms TSPGap.lemma_5_24_indexed
#check_tsp_axioms TSPGap.lemma_5_24_liftProb

-- The §5 genericization, sixth core: Lemma 5.27 over a model in four
-- checkpoints (Eq. (56), the `Z` dichotomy, the two cases, the assembly),
-- with the three-atom certificate extended by the far bundle; the identity
-- wrappers (statements unchanged) and the lifted-piece instance.
#check_tsp_axioms TSPGap.FiberTreeModel.ThreeAtomUzData.ofSupport
#check_tsp_axioms TSPGap.lemma_5_27_eq56_indexed
#check_tsp_axioms TSPGap.lemma_5_27_dichotomy_indexed
#check_tsp_axioms TSPGap.lemma_5_27_absent_indexed
#check_tsp_axioms TSPGap.lemma_5_27_present_indexed
#check_tsp_axioms TSPGap.lemma_5_27_indexed
#check_tsp_axioms TSPGap.lemma_5_27_liftProb

-- The §5 genericization, the two assemblies on pieces: Theorem 5.28 and
-- Lemma 5.25 for the lifted law, from the piece instances of 5.21–5.24, A.1
-- and 5.27, with the one transfer of a good bundle's 2-2 hypothesis.
#check_tsp_axioms TSPGap.EdgeRefinement.weightMass_tau_liftProb_twoTwo
#check_tsp_axioms TSPGap.theorem_5_28_liftProb
#check_tsp_axioms TSPGap.two_half_bundles_211_liftProb
#check_tsp_axioms TSPGap.lemma_5_25_liftProb
#check_tsp_axioms TSPGap.lemma_5_25_B_of_le_liftProb

-- The §5 genericization's endpoint: the top thinning data on pieces, with the
-- rectangularity certificate in the piece sense.
#check_tsp_axioms TSPGap.EdgeRefinement.theorem_5_28_cases_on
#check_tsp_axioms TSPGap.EdgeRefinement.happyEventOn_ge
#check_tsp_axioms TSPGap.EdgeRefinement.exists_topThinningsOn

-- The §5 genericization, second core: Lemma 5.23 over a model with the
-- three-atom certificate and Eq. (24) as an explicit certificate; the
-- identity wrapper (statement unchanged) and the lifted-piece instance.
#check_tsp_axioms TSPGap.FiberTreeModel.ThreeAtomOneHotData.ofSupport
#check_tsp_axioms TSPGap.FiberTreeModel.eqTwentyFourAlt_id
#check_tsp_axioms TSPGap.lemma_5_23_indexed
#check_tsp_axioms TSPGap.lemma_5_23_core
#check_tsp_axioms TSPGap.EdgeRefinement.eqTwentyFourAlt_liftProb
#check_tsp_axioms TSPGap.EdgeRefinement.refinedTripleData
#check_tsp_axioms TSPGap.lemma_5_23_liftProb

-- The restricted LP (audit round 16's repair): the capability predicate the
-- probabilistic layer consumes, its bridge from a genuine subtour-LP point,
-- and the instance layer re-plumbed on it.
#check_tsp_axioms TSPGap.restrict_isRestrictedLP
#check_tsp_axioms TSPGap.IsRestrictedLP.of_subtourLP
#check_tsp_axioms TSPGap.IsRestrictedLP.pairSum_le_of_subset
#check_tsp_axioms TSPGap.triangle_pairSum_le_of_cut_lower
#check_tsp_axioms TSPGap.IsRestrictedLP.triangle_pairSum_le
#check_tsp_axioms TSPGap.Hierarchy.two_le_cutSum

-- The §7 piece zone (the user's route 2): the piece rectangular transfer,
-- Claims 7.5 and 7.4 on pieces, nested rectangularity on pieces, the piece
-- reduction data, and Lemma 7.3 on pieces.
#check_tsp_axioms TSPGap.EdgeRefinement.weightMass_refinedTreeFace_count
#check_tsp_axioms TSPGap.EdgeRefinement.IsRectangularAtOn.weightMass_factor
#check_tsp_axioms TSPGap.EdgeRefinement.IsRectangularAtOn.thin_weightMass_le
#check_tsp_axioms TSPGap.EdgeRefinement.claim_7_5_core_on
#check_tsp_axioms TSPGap.EdgeRefinement.claim_7_5_on
#check_tsp_axioms TSPGap.EdgeRefinement.IsRectangularAtOn.nested
#check_tsp_axioms TSPGap.EdgeRefinement.claim_7_5_nested'_on
#check_tsp_axioms TSPGap.card_crossing_eq_one_of_sides_on
#check_tsp_axioms TSPGap.EdgeRefinement.claim_7_4_on
#check_tsp_axioms TSPGap.EdgeRefinement.liftExpect_project_odd
#check_tsp_axioms TSPGap.EdgeRefinement.TopThinningsOn.rho_eq_zero_of_odd
#check_tsp_axioms TSPGap.EdgeRefinement.TopThinningsOn.reduction_le
#check_tsp_axioms TSPGap.ReductionDataOn.expect_reduction_bottom
#check_tsp_axioms TSPGap.ReductionDataOn.expect_reduction_top
#check_tsp_axioms TSPGap.ReductionDataOn.expect_rho_bottom_odd_le
#check_tsp_axioms TSPGap.twoOneOne_window_mass_ge_on
#check_tsp_axioms TSPGap.case1a_branch_on
#check_tsp_axioms TSPGap.lemma_7_3_on

-- The partition-free reduction certificate and the kernel push: the base
-- data are a certificate (Lemma 7.3 as `HasOddMassBounds`), and the piece
-- data push to one with the same odd-mass bounds.
#check_tsp_axioms TSPGap.TopThinnings.toDensities
#check_tsp_axioms TSPGap.ReductionCertificate.reduction_le
#check_tsp_axioms TSPGap.ReductionCertificate.reduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.ReductionCertificate.oddReductionMass_tail_le
#check_tsp_axioms TSPGap.ReductionData.toCertificate_reduction
#check_tsp_axioms TSPGap.ReductionData.toCertificate_hasOddMassBounds
#check_tsp_axioms TSPGap.EdgeRefinement.kernelAvg_mul_odd
#check_tsp_axioms TSPGap.EdgeRefinement.TopThinningsOn.push
#check_tsp_axioms TSPGap.ReductionDataOn.push_reduction
#check_tsp_axioms TSPGap.ReductionDataOn.push_oddReductionMass
#check_tsp_axioms TSPGap.ReductionDataOn.push_hasOddMassBounds

-- The payment layer, certificate-generic: the cores at `PaymentCertificate`
-- and `ReductionCertificate`, and the `PaymentData` / `ReductionData` wrappers.
#check_tsp_axioms TSPGap.PaymentCertificate.slack_lower
#check_tsp_axioms TSPGap.PaymentCertificate.slack_eq_zero_of_not_mem_goodEdges
#check_tsp_axioms TSPGap.PaymentCertificate.sum_slack_nonneg_of_odd
#check_tsp_axioms TSPGap.PaymentCertificate.expect_slack_top_le
#check_tsp_axioms TSPGap.PaymentCertificate.expect_slack_bottom_le
#check_tsp_axioms TSPGap.PaymentCertificate.left_unhappy
#check_tsp_axioms TSPGap.PaymentCertificate.right_unhappy
#check_tsp_axioms TSPGap.PaymentCertificate.paymentCore
#check_tsp_axioms TSPGap.PaymentData.toCertificate
#check_tsp_axioms TSPGap.PaymentData.paymentCore
#check_tsp_axioms TSPGap.ReductionCertificate.lemma_7_6
#check_tsp_axioms TSPGap.ReductionCertificate.lemma_7_2
#check_tsp_axioms TSPGap.lemma_7_2

-- The piece route at the payment layer: Lemma 7.2 at the pushed certificate.
#check_tsp_axioms TSPGap.ReductionDataOn.pushPayment
#check_tsp_axioms TSPGap.ReductionDataOn.push_lemma_7_2

-- §7.2 on the piece side: the degree/polygon compatibility (inclusion form),
-- the provenance sidecar from the piece top thinnings, the polygon increase
-- on an edge set with Eq. (50), and Lemma 7.8 at the pushed reduction.
#check_tsp_axioms TSPGap.EdgeRefinement.DegreePartitionOn.polygonCompatible_of_controls
#check_tsp_axioms TSPGap.EdgeRefinement.DegreePartitionOn.PolygonCompatible.happy_of_twoOneOneHappyOn
#check_tsp_axioms TSPGap.EdgeRefinement.DegreePartitionOn.PolygonCompatible.sum_inter_side_le
#check_tsp_axioms TSPGap.ReductionDataOn.polygonTopCases
#check_tsp_axioms TSPGap.NearCycle.increaseOn_union_le
#check_tsp_axioms TSPGap.BottomThinning.increase_le_up_add_arrow
#check_tsp_axioms TSPGap.ReductionCertificate.expect_increaseOn_up_le
#check_tsp_axioms TSPGap.ReductionDataOn.push_expect_mul
#check_tsp_axioms TSPGap.ReductionDataOn.lemma_7_8

-- §7.2, the bottom edges: Eq. (51), the Lemma 7.7 assembly with the two
-- polygon-parent bounds as inputs, Lemma 7.10 and Lemma 7.9.
#check_tsp_axioms TSPGap.ReductionCertificate.expect_increaseOn_arrow_le_bottom
#check_tsp_axioms TSPGap.ReductionCertificate.expect_increase_rootCut_eq_zero
#check_tsp_axioms TSPGap.NearCycle.upEdges_atom_subset_partC
#check_tsp_axioms TSPGap.ReductionDataOn.lemma_7_7_of_polygon_bounds
#check_tsp_axioms TSPGap.weightMass_singleton_ge
#check_tsp_axioms TSPGap.lemma_7_10_core
#check_tsp_axioms TSPGap.lemma_7_10_left
#check_tsp_axioms TSPGap.lemma_7_10_right
#check_tsp_axioms TSPGap.lemma_7_9_arith
#check_tsp_axioms TSPGap.ReductionCertificate.lemma_7_9

-- §7.2, the interior atoms and the assembly: Corollary 2.24 under a generic tree law,
-- Lemma 7.11, Lemma 7.7 at the pushed reduction, and the payment core fed by
-- Lemma 7.2 and Lemma 7.7 only.
#check_tsp_axioms TSPGap.weightMass_not_card_eq_le
#check_tsp_axioms TSPGap.weightMass_between_eq_one_ge
#check_tsp_axioms TSPGap.weightMass_one_one_ge_of_means
#check_tsp_axioms TSPGap.polygonLaw_inside_bounds
#check_tsp_axioms TSPGap.lemma_7_11_core
#check_tsp_axioms TSPGap.lemma_7_11_happy
#check_tsp_axioms TSPGap.ReductionCertificate.lemma_7_11
#check_tsp_axioms TSPGap.ReductionDataOn.lemma_7_7
#check_tsp_axioms TSPGap.ReductionDataOn.push_paymentCore

-- The Main Payment Theorem: the presentation compatibility and the assembly of
-- KKO22 Theorem B.2 from §5–§7 (formerly the box `exists_mainPayment`).
#check_tsp_axioms TSPGap.NearCycle.eq_one_or_lastIdx_of_root_mass
#check_tsp_axioms TSPGap.Hierarchy.Presents.partitionCompatible
#check_tsp_axioms TSPGap.exists_mainPayment
#check_tsp_axioms TSPGap.exists_payment_hierarchy

-- KKO22 Lemma A.1 from the k-cycle bound (BG08 Lemma 22, proved in ExcludedCycles.lean).
#check_tsp_axioms TSPGap.IsOneSideComponent.no_kCycle
#check_tsp_axioms TSPGap.oneSide_no_inside_atoms

-- Euler's theorem for edge multisets, and the O-join output theorem it discharges
-- (formerly the declared assumption `exists_spanning_closed_walk`).
#check_tsp_axioms TSPGap.exists_walk_of_parity
#check_tsp_axioms TSPGap.exists_longer_closed_walk
#check_tsp_axioms TSPGap.exists_eulerian_closed_walk
#check_tsp_axioms TSPGap.exists_spanning_closed_walk_core
#check_tsp_axioms TSPGap.exists_spanning_closed_walk

-- BG08 Lemma 22 = KKO22 Lemma 4.19, formerly the box `kCycle_two_div_le`: the k-cycle
-- inequality, three-way submodularity, and the bound; `no_threeCycle` follows.
#check_tsp_axioms TSPGap.cutSum_union_add_sum_inter_le
#check_tsp_axioms TSPGap.three_way_submodular
#check_tsp_axioms TSPGap.kCycle_two_div_le
#check_tsp_axioms TSPGap.no_threeCycle

-- BG08 Lemma 23: near-minimum cuts (η < 2/5) contain no comb.
#check_tsp_axioms TSPGap.comb_cutSum_le
#check_tsp_axioms TSPGap.no_comb

-- The symmetric certificate (2026-09-07): the closure and its atoms, the rooted-side
-- recovery, and Lemma A.1's no-cycle theorem for the closure.
#check_tsp_axioms TSPGap.atoms_symmetrize
#check_tsp_axioms TSPGap.mem_of_mem_symmetrize_of_notMem
#check_tsp_axioms TSPGap.IsOneSideComponent.no_three_crossing
#check_tsp_axioms TSPGap.IsOneSideComponent.no_kCycle_symmetrize

-- The configuration hypotheses of the polygon core and their adapters at a rooted
-- crossing component (BG08 Lemmas 22–23 at the symmetric closure).
#check_tsp_axioms TSPGap.noKCycle_of_nearMin
#check_tsp_axioms TSPGap.noComb_of_nearMin
#check_tsp_axioms TSPGap.IsRootedCrossingComponent.noKCycle_symmetrize
#check_tsp_axioms TSPGap.IsRootedCrossingComponent.noComb_symmetrize
#check_tsp_axioms TSPGap.IsRootedCrossingComponent.mem_iff_mem_symmetrize_notMem

-- Tucker foundation (2026-09-07): cyclic enumerations, arc and interval rows, the pivot
-- normalization and the cut theorem, the invariances, and the export data.
#check_tsp_axioms TSPGap.CircularOnes.mem_arcSet_iff_of_notMem
#check_tsp_axioms TSPGap.CircularOnes.mem_arcSet_iff_of_le
#check_tsp_axioms TSPGap.CircularOnes.IsArcRow.compl
#check_tsp_axioms TSPGap.CircularOnes.HasCircularOnes.compl
#check_tsp_axioms TSPGap.CircularOnes.HasCircularOnes.mono
#check_tsp_axioms TSPGap.CircularOnes.HasCircularOnes.map
#check_tsp_axioms TSPGap.CircularOnes.isIntervalRow_cutEnum_of_isArcRow
#check_tsp_axioms TSPGap.CircularOnes.isArcRow_uncutEnum_of_isIntervalRow
#check_tsp_axioms TSPGap.CircularOnes.hasCircularOnes_iff_hasConsecutiveOnes_pivot
#check_tsp_axioms TSPGap.CircularOnes.exists_data_of_hasCircularOnes

-- Tucker's theorem (2026-09-07): the frozen patterns and configurations, the
-- overlap decomposition, and the sufficiency direction modulo the prime lemma.
#check_tsp_axioms TSPGap.Tucker.IsTuckerFree.restrict
#check_tsp_axioms TSPGap.Tucker.hasConsecutiveOnes_iff_list
#check_tsp_axioms TSPGap.Tucker.nesting
#check_tsp_axioms TSPGap.Tucker.isPrime_component
#check_tsp_axioms TSPGap.Tucker.exists_c1pList_of_tuckerFree
#check_tsp_axioms TSPGap.Tucker.hasConsecutiveOnes_of_tuckerFree

-- BG08 Proposition 6, first tranche (2026-09-07): pivot rows are atom rows of members
-- avoiding the pivot; the combs of `MIV`/`MV` and the 3-cycles of `MI 0`/`MIII 0`.
#check_tsp_axioms TSPGap.Tucker.exists_of_mem_pivotFamily
#check_tsp_axioms TSPGap.Tucker.config_rows
#check_tsp_axioms TSPGap.Tucker.isComb_of_config_MIV
#check_tsp_axioms TSPGap.Tucker.isComb_of_config_MV
#check_tsp_axioms TSPGap.Tucker.isThreeCycle_of_config_MI0
#check_tsp_axioms TSPGap.Tucker.isThreeCycle_of_config_MIII0

-- Tucker's route of record (2026-09-08): the incidence graph, avoiding paths and their
-- chain form, asteroidal triples, and necessity (Lemma 4).
#check_tsp_axioms TSPGap.Tucker.avoidingPath_iff_chain
#check_tsp_axioms TSPGap.Tucker.IsAsteroidalTriple.mono
#check_tsp_axioms TSPGap.Tucker.not_asteroidal_of_c1pList

-- Tucker's Theorem 6, first tranche (2026-09-08): the trivial-set and component reductions,
-- Lemma 3, and the assembled sufficiency theorem modulo the core step.
#check_tsp_axioms TSPGap.Tucker.exists_superset_of_pairwise_share
#check_tsp_axioms TSPGap.Tucker.exists_c1pList_of_no_asteroidal

-- Tucker's Theorem 6, core step, first tranche (2026-09-08): element distances, Lemma 4 in
-- distance form (non-strict), diameter points, and Lemma 2 with the size hypothesis.
#check_tsp_axioms TSPGap.Tucker.edist_le_of_between
#check_tsp_axioms TSPGap.Tucker.exists_diameterPoint
#check_tsp_axioms TSPGap.Tucker.isConnected_erase_of_diameterPoint
#check_tsp_axioms TSPGap.Tucker.edist_end_eq_of_diameterPoint

-- Tucker's Theorem 6 complete (2026-09-08): the transfer step, the rotation claim, the final
-- order, the core step, and the unconditional sufficiency theorem.
#check_tsp_axioms TSPGap.Tucker.not_avoidChain_of_transfer
#check_tsp_axioms TSPGap.Tucker.claimHolds
#check_tsp_axioms TSPGap.Tucker.exists_c1pList_of_claim
#check_tsp_axioms TSPGap.Tucker.coreStep
#check_tsp_axioms TSPGap.Tucker.exists_c1pList_of_no_asteroidal'

-- Tucker's Theorem 7, the frame (2026-09-08): the minimal instance and the compositions
-- modulo `MinimalTriplePattern` (Theorem 7 for minimal instances).
#check_tsp_axioms TSPGap.Tucker.exists_minimal_asteroidal
#check_tsp_axioms TSPGap.Tucker.hasConsecutiveOnes_of_tuckerFree'
#check_tsp_axioms TSPGap.Tucker.Setup.not_tuckerFree
#check_tsp_axioms TSPGap.Tucker.minimalTriplePattern
#check_tsp_axioms TSPGap.Tucker.hasConsecutiveOnes_of_tuckerFree_tucker
#check_tsp_axioms TSPGap.Tucker.primeLemma
#check_tsp_axioms TSPGap.Tucker.hasConsecutiveOnes_of_tuckerFree_decomp
#check_tsp_axioms TSPGap.exists_kCycle_of_inducedKCycle
#check_tsp_axioms TSPGap.Tucker.isTuckerFree_pivotFamily

-- The BG polygon core (2026-09-08): BG08 Lemmas 11–12 and Proposition 10 (`no_disjoint`,
-- `lemma12`, `exists_outside_mem`), Propositions 13–15 and 20 (`cor14`, `subset_of_trace`,
-- `no_nested_same_trace`), KKO22 Fact 4.8 (`not_cover`), the representation
-- (`polygonRep_exists_of_connected`) and the two producers that retire the boxes
-- `polygonRep_exists` (BlackBoxes) and `polygonRep_exists_oneSide` (TheoremB3).
#check_tsp_axioms TSPGap.BG.no_disjoint
#check_tsp_axioms TSPGap.BG.lemma12
#check_tsp_axioms TSPGap.BG.exists_outside_mem
#check_tsp_axioms TSPGap.BG.IsBGFamily.cor14
#check_tsp_axioms TSPGap.BG.IsBGFamily.subset_of_trace
#check_tsp_axioms TSPGap.BG.IsBGFamily.no_nested_same_trace
#check_tsp_axioms TSPGap.BG.IsBGFamily.not_cover
#check_tsp_axioms TSPGap.BG.polygonRep_exists_of_connected
#check_tsp_axioms TSPGap.BG.polygonRep_exists_of_nearMin
#check_tsp_axioms TSPGap.polygonRep_exists
#check_tsp_axioms TSPGap.polygonRep_exists_oneSide

-- KKO22 Lemma 4.23 and Fact 4.26 without contraction (2026-09-09, `audits/qa/q17`): a union
-- of atoms with two atoms on each side crosses a member (Theorem 4.5 for `{A}`), the
-- augmented family `symmetrize (insert A (insert B 𝒞))` is a BG family, and BG08
-- Proposition 20 / Corollary 14 finish.  These retire the boxes `eq_of_outsideIn_eq` and
-- `cross_arc_of_almostDiagonal` of `BlackBoxes.lean`.
#check_tsp_axioms TSPGap.BG.exists_cross_of_union_atoms
#check_tsp_axioms TSPGap.BG.isBGFamily_symmetrize_of_cross
#check_tsp_axioms TSPGap.BG.trace_bounds_of_cross
#check_tsp_axioms TSPGap.eq_of_outsideIn_eq
#check_tsp_axioms TSPGap.cross_arc_of_almostDiagonal

-- The one-side tranche (2026-09-09): KKO21 Fact 4.11 (`oneSide_laminar_split`, with the
-- 3-cycle exclusion rather than the no-inside-atoms property — see `notes.md`), the
-- interval coordinates and the reflection, Lemmas 4.12–4.14, the interior adjacent-pair
-- estimate (Lemma 4.18), Lemmas 4.16/4.17/4.19, Theorem A.3 (`oneSide_structure`, formerly
-- an assumption in NearCycle.lean), the laminarity of uncrossed cuts, atoms and outer cuts
-- (`OneSideAtoms.lean`), and KKO22 Facts B.4/B.5 (`exists_hierarchy_of_oneSideFamily`,
-- formerly an assumption in TheoremB3.lean; `x₀(e₀) = 1` is spent in `rootCut_isUncrossed`).
#check_tsp_axioms TSPGap.PolygonRep.openLeft_or_openRight
#check_tsp_axioms TSPGap.oneSide_laminar_split
#check_tsp_axioms TSPGap.PolygonRep.reflect_openLeft
#check_tsp_axioms TSPGap.PolygonRep.common_ancestorR
#check_tsp_axioms TSPGap.PolygonRep.exists_crossesOnRight_of_strictParentL
#check_tsp_axioms TSPGap.PolygonRep.exists_left_interval
#check_tsp_axioms TSPGap.PolygonRep.pair_nearMin
#check_tsp_axioms TSPGap.PolygonRep.adjacent_mass
#check_tsp_axioms TSPGap.PolygonRep.atom_nearMin
#check_tsp_axioms TSPGap.PolygonRep.outer_nearMin
#check_tsp_axioms TSPGap.PolygonRep.root_middle_le
#check_tsp_axioms TSPGap.oneSide_structure
#check_tsp_axioms TSPGap.PolygonRep.atom_laminar_of_not_crossing
#check_tsp_axioms TSPGap.PolygonRep.subset_atom_of_ssubset_outer
#check_tsp_axioms TSPGap.atoms_laminar_of_ne
#check_tsp_axioms TSPGap.outer_laminar_of_ne
#check_tsp_axioms TSPGap.outer_injective_of_ne
#check_tsp_axioms TSPGap.cutSum_pair_of_rootEdge
#check_tsp_axioms TSPGap.rootCut_isUncrossed
#check_tsp_axioms TSPGap.OneSideFamily.laminar
#check_tsp_axioms TSPGap.OneSideFamily.nearMin_of_mem
#check_tsp_axioms TSPGap.OneSideFamily.isChildOf_outerCut_iff
#check_tsp_axioms TSPGap.OneSideFamily.exists_nearCycle_of_two_children
#check_tsp_axioms TSPGap.OneSideFamily.degreeRule
#check_tsp_axioms TSPGap.exists_hierarchy_of_oneSideFamily

-- The max-entropy tree distribution (2026-09-10): Edmonds' theorem for the spanning-tree
-- polytope of `K_n` (`TreePolytope`, `GraphRank`, `KruskalTree`, `EdmondsTree`), the
-- exponential-family limit over finite configurations (`ExpFamilyLimit`), and their
-- instantiation `exists_maxEntropy_treeDist` (formerly an assumption in OJoin.lean).  The
-- root-edge hypothesis is spent in `restrict_inTreePolytope` (the total `n − 1`).
#check_tsp_axioms TSPGap.sum_cutSum_singleton_inside
#check_tsp_axioms TSPGap.restrict_inTreePolytope
#check_tsp_axioms TSPGap.sum_le_sub_numComp
#check_tsp_axioms TSPGap.card_add_numComp_of_isAcyclic
#check_tsp_axioms TSPGap.exists_acyclic_of_chain
#check_tsp_axioms TSPGap.exists_isKruskal
#check_tsp_axioms TSPGap.weight_le_of_isKruskal
#check_tsp_axioms TSPGap.exists_spanningTree_le_weight
#check_tsp_axioms TSPGap.exists_treeDist_of_inTreePolytope
#check_tsp_axioms TSPGap.exists_treeDist_restrict
#check_tsp_axioms TSPGap.ExpFamily.inner_le_logPart
#check_tsp_axioms TSPGap.ExpFamily.exists_isMinOn_obj
#check_tsp_axioms TSPGap.ExpFamily.marginal_eq_of_isMinOn
#check_tsp_axioms TSPGap.ExpFamily.exists_gibbs_limit
#check_tsp_axioms TSPGap.gibbsTreeDist_isLambdaUniform
#check_tsp_axioms TSPGap.exists_maxEntropy_treeDist
#check_tsp_axioms TSPGap.exists_tour_of_rootEdge

-- Edmonds–Johnson, tranche 1 (2026-09-10): labelled multigraphs, the boundary modulo two,
-- joins and even sets, the minimum-join criterion (Cornuéjols Remark 2.6 in even-set form),
-- walks with edge labels, cycle extraction from an even set, the arcs of a cycle, longest
-- paths in a forest, the star contraction with the terminal-set transform, the lifting of
-- joins, and the contraction inequality (`card_restrict_le`) from (♠), itself from the cycle
-- bound (★) (`sharp_of_cycles`).
#check_tsp_axioms TSPGap.MGraph.odd_symmDiff
#check_tsp_axioms TSPGap.MGraph.isMinJoin_iff
#check_tsp_axioms TSPGap.MGraph.odd_card_inter_cut
#check_tsp_axioms TSPGap.MGraph.even_wt_of_isEven
#check_tsp_axioms TSPGap.MGraph.Walk.deg_edgeSet_add_eq
#check_tsp_axioms TSPGap.MGraph.Walk.exists_cycle_of_isEven
#check_tsp_axioms TSPGap.MGraph.Walk.exists_arcs
#check_tsp_axioms TSPGap.MGraph.Walk.deg_eq_one_of_longest
#check_tsp_axioms TSPGap.MGraph.isJoin_restrict
#check_tsp_axioms TSPGap.MGraph.exists_lift_join
#check_tsp_axioms TSPGap.MGraph.sharp_of_cycles
#check_tsp_axioms TSPGap.MGraph.card_restrict_le

-- Edmonds–Johnson, tranche 2 (2026-09-10): Seymour's theorem (the claim, (★), the induction
-- on the vertex count through the star contraction, packings lifted through `expand`), the
-- subdivision packing for positive integer weights (Cornuéjols Theorem 2.7), weak duality,
-- the real-cost approximation `w_k = ⌈k c⌉ + 1`, the complete graph as a multigraph, and
-- the former box `edmondsJohnson_ojoin`, now proved.  `exists_join_le_of_feasible`,
-- previously the only consumer of that box, is axiom-clean — and so are
-- `exists_tour_of_rootEdge` and `kko_gap` (listed above): the box was the last one on the
-- end-to-end path.
#check_tsp_axioms TSPGap.MGraph.claim_mem_of_wt_eq_zero
#check_tsp_axioms TSPGap.MGraph.two_le_wt_cycle
#check_tsp_axioms TSPGap.MGraph.seymour
#check_tsp_axioms TSPGap.MGraph.isMinJoin_liftJ
#check_tsp_axioms TSPGap.MGraph.exists_packing_of_weights
#check_tsp_axioms TSPGap.MGraph.card_le_sum_of_packing
#check_tsp_axioms TSPGap.MGraph.exists_join_le_of_weights
#check_tsp_axioms TSPGap.MGraph.exists_join_cost_le
#check_tsp_axioms TSPGap.exists_join_kn
#check_tsp_axioms TSPGap.edmondsJohnson_ojoin
#check_tsp_axioms TSPGap.exists_join_le_of_feasible

-- Constant recovery (2026-09-11): the PF2 lower-tail repair and its stable-weight
-- adapter. No payment or endpoint constant is changed by these auxiliary results.
#check_tsp_axioms TSPGap.truncated_mean_le
#check_tsp_axioms TSPGap.deficit_three_bounds
#check_tsp_axioms TSPGap.lower_tail_three_ge_of_pf2_deficit
#check_tsp_axioms TSPGap.Bernoulli.probCount_le_two_ge_of_deficit
#check_tsp_axioms TSPGap.weightMass_le_two_ge_of_deficit
#check_tsp_axioms TSPGap.point_mass_two_ge_of_pf2_deficit
#check_tsp_axioms TSPGap.lemma522_recovered_constant
#check_tsp_axioms TSPGap.binomial_three_tail_lt_deficit

-- Appendix A coefficient recovery (2026-09-12): sharp probability kernels,
-- half-weight atom incidences, the 44αη charge, and the 125ηβ hierarchy repair.
#check_tsp_axioms TSPGap.NearCycle.fails_of_odd
#check_tsp_axioms TSPGap.NearCycle.incidenceSlack_nonneg
#check_tsp_axioms TSPGap.NearCycle.incidence_cutSum
#check_tsp_axioms TSPGap.NearCycle.incidenceSlack_payment
#check_tsp_axioms TSPGap.NearCycle.expect_incidenceSlack
#check_tsp_axioms TSPGap.NearCycle.expect_incidenceSlack_le
#check_tsp_axioms TSPGap.NearCycle.incidenceSlack_eq_zero
#check_tsp_axioms TSPGap.NearCycle.card_incident_le
#check_tsp_axioms TSPGap.NearCycle.exists_happySlack_of_hierarchies_sharp
#check_tsp_axioms TSPGap.between_subset_cut_of_subsets
#check_tsp_axioms TSPGap.between_disjoint_of_carriers
#check_tsp_axioms TSPGap.sum_remainder_two_le
#check_tsp_axioms TSPGap.restricted_between_mass_ge
#check_tsp_axioms TSPGap.prob_cut_two_of_crossing_chain
#check_tsp_axioms TSPGap.prob_side_one_of_groups
#check_tsp_axioms TSPGap.prob_side_one_of_crossing
#check_tsp_axioms TSPGap.prob_cut_two_of_near_neighbors
#check_tsp_axioms TSPGap.prob_side_one_of_near_neighbor
#check_tsp_axioms TSPGap.PolygonRep.ivl_disjoint_root
#check_tsp_axioms TSPGap.PolygonRep.ivl_avoids
#check_tsp_axioms TSPGap.PolygonRep.prob_cut_two_openRight
#check_tsp_axioms TSPGap.PolygonRep.prob_cut_two_member
#check_tsp_axioms TSPGap.PolygonRep.root_mass_ge_of_boundary
#check_tsp_axioms TSPGap.PolygonRep.prob_side_one_member
#check_tsp_axioms TSPGap.PolygonRep.prob_cut_two_atom
#check_tsp_axioms TSPGap.PolygonRep.prob_side_one_first_atom
#check_tsp_axioms TSPGap.PolygonRep.prob_side_one_last_atom
#check_tsp_axioms TSPGap.PolygonRep.toNearCycle_atom_eq_ivl
#check_tsp_axioms TSPGap.PolygonRep.nearCycle_interval_eq_ivl
#check_tsp_axioms TSPGap.PolygonRep.prob_fails_sharp_read
#check_tsp_axioms TSPGap.exists_happySlack_of_oneSideComponent_sharp
#check_tsp_axioms TSPGap.exists_happySlack_triangle_sharp
#check_tsp_axioms TSPGap.exists_slackStar_oneSide_sharp
#check_tsp_axioms TSPGap.OneSideFamily.exists_slackStar_of_index_sharp
#check_tsp_axioms TSPGap.exists_slackStar_triangle_sharp
#check_tsp_axioms TSPGap.exists_slackStar_hierarchy_sharp
#check_tsp_axioms TSPGap.exists_payment_of_hierarchy_sharp
#check_tsp_axioms TSPGap.exists_payment_hierarchy_sharp
#check_tsp_axioms TSPGap.exists_slack_pair_125

-- The separate probability recovery: all shifted tails, the PF2 point-mass
-- bootstrap, and the sharpened two-stage kernel.
#check_tsp_axioms TSPGap.Bernoulli.poi_tail_le_probGE_of_pred_lt
#check_tsp_axioms TSPGap.exp_199_ge_sharp
#check_tsp_axioms TSPGap.poisson_lower_two_le
#check_tsp_axioms TSPGap.poisson_lower_one_le
#check_tsp_axioms TSPGap.Bernoulli.probGE_two_ge_sharp
#check_tsp_axioms TSPGap.weightMass_two_le_ge_of_mean_199_sharp
#check_tsp_axioms TSPGap.probCount_two_ge_mid_sharp
#check_tsp_axioms TSPGap.probCount_three_ge_high
#check_tsp_axioms TSPGap.probCount_two_ge_high_sharp
#check_tsp_axioms TSPGap.weightMass_eq_three_ge_of_baseline_high_sharp
#check_tsp_axioms TSPGap.lemma_5_22_kernel_sharp
#check_tsp_axioms TSPGap.epsPRecovered_eq
#check_tsp_axioms TSPGap.epsPRecovered_pos
#check_tsp_axioms TSPGap.epsP_le_recovered
#check_tsp_axioms TSPGap.exists_mainPayment_recovered
#check_tsp_axioms TSPGap.exists_payment_hierarchy_recovered
#check_tsp_axioms TSPGap.exists_slack_pair_of_payment
#check_tsp_axioms TSPGap.exists_slack_pair_recovered

-- Lemma 5.27 at the first Gurvits threshold (2026-09-12): stronger A.1
-- tails, PF2 concentration, and exact original-measure failure accounting.
-- This tranche leaves the global thinning mass and gap constant unchanged.
#check_tsp_axioms TSPGap.lemma_A1_conditioned_kernel_budget
#check_tsp_axioms TSPGap.lemma_A1_conditioned_budget
#check_tsp_axioms TSPGap.lemma_A1_indexed_budget
#check_tsp_axioms TSPGap.concentration_two_of_pf2
#check_tsp_axioms TSPGap.Bernoulli.probCount_two_ge_of_small_lower_tail
#check_tsp_axioms TSPGap.weightMass_two_ge_of_small_lower_tail
#check_tsp_axioms TSPGap.lemma_5_27_eq56_gurvits
#check_tsp_axioms TSPGap.lemma_5_27_core_scaled
#check_tsp_axioms TSPGap.lemma527_absent_budget_old
#check_tsp_axioms TSPGap.lemma527_present_budget_old
#check_tsp_axioms TSPGap.lemma527_absent_budget_gurvits
#check_tsp_axioms TSPGap.lemma527_present_budget_gurvits
#check_tsp_axioms TSPGap.lemma_5_27_absent_indexed_of_defect
#check_tsp_axioms TSPGap.lemma_5_27_present_indexed_of_defect
#check_tsp_axioms TSPGap.lemma_5_27_gurvits_indexed
#check_tsp_axioms TSPGap.lemma_5_27_gurvits
#check_tsp_axioms TSPGap.lemma_5_27_gurvits_liftProb
#check_tsp_axioms TSPGap.lemma_5_27_gurvits_treeDist

-- Capacity prerequisites (2026-09-13): local poles, nonnegative residues,
-- stability's logarithmic-derivative sign, and the seven-subset numerical
-- profiles. These do not yet prove productization or the new 5.21/5.22 bounds.
#check_tsp_axioms TSPGap.im_div_pow_le_at_zero
#check_tsp_axioms TSPGap.exists_upper_pow_eq_I
#check_tsp_axioms TSPGap.exists_upper_pow_eq_neg_I
#check_tsp_axioms TSPGap.pole_coefficient_nonneg
#check_tsp_axioms TSPGap.pole_order_eq_one_and_residue_pos
#check_tsp_axioms TSPGap.simple_pole_of_real_factorizations
#check_tsp_axioms TSPGap.rootMultiplicity_le_succ_of_nonposImaginaryQuotient
#check_tsp_axioms TSPGap.residue_pos_of_nonposImaginaryQuotient
#check_tsp_axioms TSPGap.nonnegative_residues_at_nodes
#check_tsp_axioms TSPGap.nonnegative_partialFractions_nodal
#check_tsp_axioms TSPGap.roots_nodup_of_coprime_nonposImaginaryQuotient
#check_tsp_axioms TSPGap.nonnegative_partialFractions_of_coprime
#check_tsp_axioms TSPGap.aeval_ne_zero_of_monic_splits
#check_tsp_axioms TSPGap.degree_div_gcd_lt
#check_tsp_axioms TSPGap.nonnegative_residues_common_denominator
#check_tsp_axioms TSPGap.polynomial_logDeriv_im_nonpos
#check_tsp_axioms TSPGap.eval_coordinateSlice
#check_tsp_axioms TSPGap.derivative_coordinateSlice
#check_tsp_axioms TSPGap.mvPolynomial_logDeriv_im_nonpos
#check_tsp_axioms TSPGap.threeMeanProfile_of_seven
#check_tsp_axioms TSPGap.lemma521_capacity_profile
#check_tsp_axioms TSPGap.lemma522_capacity_profile
#check_tsp_axioms TSPGap.lemma521_capacity_budget
#check_tsp_axioms TSPGap.lemma522_capacity_budget

-- Homogeneous productization (2026-09-13): the residue matrix, its line-
-- polynomial inputs, and exact pointwise productization. Positive degree,
-- normalization and real stability remain explicit; no capacity or new
-- probability bound is asserted by these declarations.
#check_tsp_axioms TSPGap.nodal_roots_dvd
#check_tsp_axioms TSPGap.linearQuotient_eq_nodal_erase
#check_tsp_axioms TSPGap.eval_sum_nodal_erase
#check_tsp_axioms TSPGap.residues_unique
#check_tsp_axioms TSPGap.coeff_linearQuotient_top
#check_tsp_axioms TSPGap.sum_residues_eq_coeff
#check_tsp_axioms TSPGap.derivative_eq_sum_residues
#check_tsp_axioms TSPGap.eulerRemainder_eq_sum_residues
#check_tsp_axioms TSPGap.exists_residueTable
#check_tsp_axioms TSPGap.ResidueTable.column_sum
#check_tsp_axioms TSPGap.ResidueTable.weighted_expansion
#check_tsp_axioms TSPGap.ResidueTable.row_sum
#check_tsp_axioms TSPGap.ResidueTable.weighted_row_sum
#check_tsp_axioms TSPGap.RootOccurrence.count_pos
#check_tsp_axioms TSPGap.card_rootOccurrence
#check_tsp_axioms TSPGap.prod_rootOccurrence
#check_tsp_axioms TSPGap.ResidueTable.matrix_nonneg
#check_tsp_axioms TSPGap.ResidueTable.matrix_column_sum
#check_tsp_axioms TSPGap.ResidueTable.matrix_row_sum
#check_tsp_axioms TSPGap.ResidueTable.matrix_weighted_row_sum
#check_tsp_axioms TSPGap.ResidueTable.matrix_product
#check_tsp_axioms TSPGap.diagonalLine_C
#check_tsp_axioms TSPGap.diagonalLine_X
#check_tsp_axioms TSPGap.eval_diagonalLine
#check_tsp_axioms TSPGap.aeval_diagonalLine
#check_tsp_axioms TSPGap.homogeneous_support_sum
#check_tsp_axioms TSPGap.diagonalMonomial_natDegree
#check_tsp_axioms TSPGap.natDegree_diagonalLine_le
#check_tsp_axioms TSPGap.coeff_diagonalLine_homogeneous
#check_tsp_axioms TSPGap.monic_diagonalLine
#check_tsp_axioms TSPGap.eval_scale_homogeneous
#check_tsp_axioms TSPGap.derivative_diagonalLine
#check_tsp_axioms TSPGap.euler_diagonalLine
#check_tsp_axioms TSPGap.aeval_diagonalLine_ne_zero
#check_tsp_axioms TSPGap.im_eq_zero_of_aeval_diagonalLine
#check_tsp_axioms TSPGap.splits_diagonalLine
#check_tsp_axioms TSPGap.diagonalLine_pderiv_quotient
#check_tsp_axioms TSPGap.degree_diagonalLine_pderiv_lt
#check_tsp_axioms TSPGap.roots_prod_diagonalLine
#check_tsp_axioms TSPGap.exists_diagonalLine_residueTable
#check_tsp_axioms TSPGap.homogeneous_productization

-- Fixed-marginal support reduction (2026-09-13). Rigidity is constructed,
-- not a premise on the stable polynomial. The leaf bounds cover empty/zero
-- support correctly; the profile-removal capacity induction remains next.
#check_tsp_axioms TSPGap.exists_neg_of_sum_zero
#check_tsp_axioms TSPGap.exists_nonnegative_ray_endpoint
#check_tsp_axioms TSPGap.CapacityMatrix.row_value_pos
#check_tsp_axioms TSPGap.CapacityMatrix.value_pos
#check_tsp_axioms TSPGap.CapacityMatrix.log_value
#check_tsp_axioms TSPGap.CapacityMatrix.value_le_of_logValue_le
#check_tsp_axioms TSPGap.CapacityMatrix.logValue_mix
#check_tsp_axioms TSPGap.CapacityMatrix.endpoint_value_le
#check_tsp_axioms TSPGap.CapacityMatrix.mem_support
#check_tsp_axioms TSPGap.CapacityMatrix.IsBalanced.neg
#check_tsp_axioms TSPGap.CapacityMatrix.SupportedBy.neg
#check_tsp_axioms TSPGap.CapacityMatrix.SupportedBy.trans
#check_tsp_axioms TSPGap.CapacityMatrix.support_subset
#check_tsp_axioms TSPGap.CapacityMatrix.IsBalanced.exists_neg
#check_tsp_axioms TSPGap.CapacityMatrix.exists_supported_endpoint
#check_tsp_axioms TSPGap.CapacityMatrix.exists_smaller_of_not_rigid
#check_tsp_axioms TSPGap.CapacityMatrix.exists_rigid_reduction
#check_tsp_axioms TSPGap.CapacityMatrix.edgeLift_supported
#check_tsp_axioms TSPGap.CapacityMatrix.edgeLift_injective
#check_tsp_axioms TSPGap.CapacityMatrix.totalDiff_marginalMap
#check_tsp_axioms TSPGap.CapacityMatrix.totalDiff_surjective
#check_tsp_axioms TSPGap.CapacityMatrix.marginalMap_edgeLift_injective
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.support_card_le
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.of_supportedBy
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.transpose
#check_tsp_axioms TSPGap.CapacityMatrix.support_card_eq_sum_rowDegree
#check_tsp_axioms TSPGap.CapacityMatrix.IsStochastic.rowDegree_pos
#check_tsp_axioms TSPGap.CapacityMatrix.twice_card_le_edges_add_leaves
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.card_add_one_le_columns_add_leaves
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.exists_row_leaf
#check_tsp_axioms TSPGap.CapacityMatrix.IsStochastic.leaf_row
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.exists_column_leaf
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.exists_column_leaf_ne
#check_tsp_axioms TSPGap.homogeneous_rigid_productization

-- Capacity deletion steps (2026-09-13). Actual row/column subtypes,
-- normalized target-zero removal, target-one leaf removal, deterministic
-- row factors and the absolute subset-error shift. These are not yet a
-- full capacity bound or a change to the probability/gap constants.
#check_tsp_axioms TSPGap.CapacityMatrix.zeroColumn_value_bound
#check_tsp_axioms TSPGap.CapacityMatrix.zeroColumn_error_interval
#check_tsp_axioms TSPGap.CapacityMatrix.leafColumn_value_bound
#check_tsp_axioms TSPGap.CapacityMatrix.leafColumn_error_interval
#check_tsp_axioms TSPGap.CapacityMatrix.exists_row_of_column_leaf
#check_tsp_axioms TSPGap.AtMostErrorProfile.shift_of_between
#check_tsp_axioms TSPGap.ThreeMeanProfile.atMost
#check_tsp_axioms TSPGap.CapacityMatrix.columnSum_nonneg
#check_tsp_axioms TSPGap.CapacityMatrix.entry_le_columnSum
#check_tsp_axioms TSPGap.CapacityMatrix.entry_le_one
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.eraseRow
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.eraseColumn
#check_tsp_axioms TSPGap.CapacityMatrix.IsStochastic.eraseRow
#check_tsp_axioms TSPGap.CapacityMatrix.columnSum_eq_entry_add_eraseRow
#check_tsp_axioms TSPGap.CapacityMatrix.value_eq_row_mul_eraseRow
#check_tsp_axioms TSPGap.CapacityMatrix.rowSum_eraseColumn
#check_tsp_axioms TSPGap.CapacityMatrix.rowSubset_le_one_sub
#check_tsp_axioms TSPGap.CapacityMatrix.value_nonneg
#check_tsp_axioms TSPGap.CapacityMatrix.IsStochastic.eraseColumn_of_zero
#check_tsp_axioms TSPGap.CapacityMatrix.value_eraseColumn_of_zero
#check_tsp_axioms TSPGap.CapacityMatrix.columnSum_eq_of_leaf
#check_tsp_axioms TSPGap.CapacityMatrix.IsStochastic.eraseLeaf
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.eraseLeaf
#check_tsp_axioms TSPGap.CapacityMatrix.columnSum_eraseLeaf
#check_tsp_axioms TSPGap.CapacityMatrix.value_eq_row_mul_eraseLeaf
#check_tsp_axioms TSPGap.CapacityMatrix.eraseLeaf_value_le
#check_tsp_axioms TSPGap.CapacityMatrix.eraseLeaf_subset_deficit
#check_tsp_axioms TSPGap.CapacityMatrix.value_eq_coord_mul_eraseRow
#check_tsp_axioms TSPGap.CapacityMatrix.columnSum_eraseRow_of_deterministic
#check_tsp_axioms TSPGap.CapacityMatrix.one_sub_entry_pos
#check_tsp_axioms TSPGap.CapacityMatrix.IsStochastic.normalizeEraseColumn
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.normalizeEraseColumn
#check_tsp_axioms TSPGap.CapacityMatrix.one_sub_sum_le_prod_one_sub
#check_tsp_axioms TSPGap.CapacityMatrix.normalizeEraseColumn_rowValue
#check_tsp_axioms TSPGap.CapacityMatrix.normalizeEraseColumn_value_le
#check_tsp_axioms TSPGap.CapacityMatrix.normalizeEraseColumn_row_increment
#check_tsp_axioms TSPGap.CapacityMatrix.normalizeEraseColumn_subset_increment

-- Absolute-profile capacity bound (2026-09-13). Termination is on rows plus
-- columns, including empty rows and an isolated spectator. The stable
-- polynomial bound is pointwise; coefficient extraction remains separate.
#check_tsp_axioms TSPGap.AtMostErrorProfile.congr
#check_tsp_axioms TSPGap.AtMostErrorProfile.singleton
#check_tsp_axioms TSPGap.AtMostErrorProfile.subtype_shift
#check_tsp_axioms TSPGap.active_subtype_eq
#check_tsp_axioms TSPGap.CapacityMatrix.zeroColumn_profile
#check_tsp_axioms TSPGap.CapacityMatrix.leafColumn_profile
#check_tsp_axioms TSPGap.CapacityMatrix.deterministicRow_profile
#check_tsp_axioms TSPGap.CapacityMatrix.card_delete_add_one
#check_tsp_axioms TSPGap.CapacityMatrix.active_card_delete
#check_tsp_axioms TSPGap.CapacityMatrix.targetValue_nonneg
#check_tsp_axioms TSPGap.CapacityMatrix.targetValue_erase
#check_tsp_axioms TSPGap.CapacityMatrix.targetValue_decrement
#check_tsp_axioms TSPGap.CapacityMatrix.profileProduct_zero
#check_tsp_axioms TSPGap.CapacityMatrix.profileProduct_succ
#check_tsp_axioms TSPGap.CapacityMatrix.profileProduct_nonneg
#check_tsp_axioms TSPGap.CapacityMatrix.profileProduct_le_one
#check_tsp_axioms TSPGap.CapacityMatrix.columnDegree_pos_of_mass_pos
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.rows_lt_columns_of_no_leaf
#check_tsp_axioms TSPGap.CapacityMatrix.rowDegree_erase_zero
#check_tsp_axioms TSPGap.CapacityMatrix.IsRigid.active_column_leaf
#check_tsp_axioms TSPGap.CapacityMatrix.rigid_profile_lower_bound
#check_tsp_axioms TSPGap.CapacityMatrix.rigid_profile_lower_bound_nonneg
#check_tsp_axioms TSPGap.CapacityMatrix.stochastic_profile_lower_bound
#check_tsp_axioms TSPGap.homogeneous_profile_lower_bound

-- One-step coefficient extraction (2026-09-13). The uniform one-variable
-- bound and the homogeneous positive-slice bridge are single-step results;
-- the next block certifies repetition. Probability/gap upgrades are separate.
#check_tsp_axioms TSPGap.constantCoeff_le_eval
#check_tsp_axioms TSPGap.eval_le_exp_tangent
#check_tsp_axioms TSPGap.coeff_one_ge_of_capacity_of_constant_zero
#check_tsp_axioms TSPGap.coeff_one_ge_exp_neg_one_mul_capacity
#check_tsp_axioms TSPGap.eval_realCoordinateSlice
#check_tsp_axioms TSPGap.aeval_realCoordinateSlice
#check_tsp_axioms TSPGap.derivative_realCoordinateSlice
#check_tsp_axioms TSPGap.coeff_one_realCoordinateSlice
#check_tsp_axioms TSPGap.coeff_nonneg_realCoordinateSlice
#check_tsp_axioms TSPGap.eval_complex_scale_homogeneous
#check_tsp_axioms TSPGap.aeval_realCoordinateSlice_ne_zero
#check_tsp_axioms TSPGap.splits_realCoordinateSlice
#check_tsp_axioms TSPGap.homogeneous_capacity_extraction_one

-- Repeated count extraction (2026-09-13). Stable-or-zero projected layers
-- certify all three steps, including the baseline-one variant. The mean
-- profile to grouped-polynomial capacity bridge remains separate.
#check_tsp_axioms TSPGap.sum_projectCount_mul
#check_tsp_axioms TSPGap.weightMass_projectCount
#check_tsp_axioms TSPGap.totalMass_projectCount
#check_tsp_axioms TSPGap.eval_genPoly_projectCount
#check_tsp_axioms TSPGap.weightNonneg_projectCount
#check_tsp_axioms TSPGap.exists_of_projectCount_ne_zero
#check_tsp_axioms TSPGap.weightSupportedOn_projectCount
#check_tsp_axioms TSPGap.fixedRankWeight_projectCount
#check_tsp_axioms TSPGap.projectCount_eq_zero_of_rank_lt
#check_tsp_axioms TSPGap.projectCount_eq_projLayer
#check_tsp_axioms TSPGap.inter_projectCount_witness
#check_tsp_axioms TSPGap.projectCount_preserves_lower_count
#check_tsp_axioms TSPGap.projLayer_const_mul
#check_tsp_axioms TSPGap.isRealStableOrZero_projLayer_unnormalized
#check_tsp_axioms TSPGap.isRealStableOrZero_projectCount
#check_tsp_axioms TSPGap.prod_blockScale
#check_tsp_axioms TSPGap.weightNonneg_outsideTilt
#check_tsp_axioms TSPGap.fixedRankWeight_outsideTilt
#check_tsp_axioms TSPGap.isRealStable_outsideTilt
#check_tsp_axioms TSPGap.eval_countSlice
#check_tsp_axioms TSPGap.coeff_countSlice
#check_tsp_axioms TSPGap.coeff_nonneg_countSlice
#check_tsp_axioms TSPGap.splits_countSlice
#check_tsp_axioms TSPGap.projectCount_eval_lower_bound
#check_tsp_axioms TSPGap.coeff_two_ge_exp_neg_one_mul_capacity
#check_tsp_axioms TSPGap.countSlice_coeff_zero_of_lower_count
#check_tsp_axioms TSPGap.projectCount_eval_lower_bound_two
#check_tsp_axioms TSPGap.blockScale_pos
#check_tsp_axioms TSPGap.totalMass_projectCount_three
#check_tsp_axioms TSPGap.three_counts_ge_of_capacity
#check_tsp_axioms TSPGap.three_counts_one_ge_of_capacity
#check_tsp_axioms TSPGap.three_counts_shifted_ge_of_capacity

-- Three means to three count masses (2026-09-14): grouped polynomials,
-- support-only baseline subtraction, and the normalized mean-profile bridge.
-- Indexed 5.21/5.22 upgrades and endpoint propagation remain separate.
#check_tsp_axioms TSPGap.groupedCountExponent
#check_tsp_axioms TSPGap.groupedCountPoly
#check_tsp_axioms TSPGap.groupedCountExponent_apply
#check_tsp_axioms TSPGap.degree_groupedCountExponent
#check_tsp_axioms TSPGap.monomial_groupedCountExponent
#check_tsp_axioms TSPGap.eval_one_groupedCountPoly
#check_tsp_axioms TSPGap.coeff_groupedCountPoly_nonneg
#check_tsp_axioms TSPGap.eval_pderiv_groupedCountPoly
#check_tsp_axioms TSPGap.eval_pderiv_groupedCountPoly_of_support
#check_tsp_axioms TSPGap.monomial_mul_groupedCountPoly
#check_tsp_axioms TSPGap.groupedCountPoly_zero
#check_tsp_axioms TSPGap.isRealStable_groupedCountPoly
#check_tsp_axioms TSPGap.isHomogeneous_groupedCountPoly
#check_tsp_axioms TSPGap.threeBlock
#check_tsp_axioms TSPGap.threeBlockIndex
#check_tsp_axioms TSPGap.threeBlockPoly
#check_tsp_axioms TSPGap.threeBlockIndex_eq_some
#check_tsp_axioms TSPGap.groupedCountExponent_threeBlock
#check_tsp_axioms TSPGap.threeBlockIndex_eval
#check_tsp_axioms TSPGap.threeBlock_baseline
#check_tsp_axioms TSPGap.eval_one_threeBlockPoly
#check_tsp_axioms TSPGap.eval_pderiv_threeBlockPoly
#check_tsp_axioms TSPGap.isRealStable_threeBlockPoly
#check_tsp_axioms TSPGap.isHomogeneous_threeBlockPoly
#check_tsp_axioms TSPGap.eval_threeBlockPoly_mul
#check_tsp_axioms TSPGap.AtMostErrorProfile.map
#check_tsp_axioms TSPGap.threeProfileExtension
#check_tsp_axioms TSPGap.threeProfileExtension_apply
#check_tsp_axioms TSPGap.profileProduct_threeProfileExtension
#check_tsp_axioms TSPGap.threeProfileExtension_bounds
#check_tsp_axioms TSPGap.homogeneous_degree_pos_of_three_profile
#check_tsp_axioms TSPGap.three_mean_polynomial_lower_bound
#check_tsp_axioms TSPGap.three_counts_ge_of_mean_profile

-- Capacity-strengthened 5.21/5.22 exports; the old thresholds remain wrappers.
#check_tsp_axioms TSPGap.one_div_twentyone_le_exp_neg_three
#check_tsp_axioms TSPGap.lemma521_capacity_profile_of_le_milli
#check_tsp_axioms TSPGap.lemma_5_21_kernel_capacity
#check_tsp_axioms TSPGap.lemma_5_22_kernel_capacity
#check_tsp_axioms TSPGap.lemma_5_21_indexed_capacity
#check_tsp_axioms TSPGap.lemma_5_22_indexed_capacity
#check_tsp_axioms TSPGap.lemma_5_21_capacity
#check_tsp_axioms TSPGap.lemma_5_22_capacity
#check_tsp_axioms TSPGap.lemma_5_21_liftProb_capacity
#check_tsp_axioms TSPGap.lemma_5_22_liftProb_capacity

-- The existing 5.23 tail feeds the parameterized A.1 proof at ell = 99.75.
#check_tsp_axioms TSPGap.lemma_A1_two_percent_tail_budget
#check_tsp_axioms TSPGap.lemma_A1_two_percent_happy_budget
#check_tsp_axioms TSPGap.lemma_A1_indexed_of_tail_two_percent
#check_tsp_axioms TSPGap.lemma_A1_of_tail_two_percent
#check_tsp_axioms TSPGap.lemma_A1_treeDist_of_tail_two_percent
#check_tsp_axioms TSPGap.lemma_5_23_happy_treeDist
#check_tsp_axioms TSPGap.lemma_A1_liftProb_of_tail_two_percent
#check_tsp_axioms TSPGap.lemma_5_23_happy_liftProb

-- Capacity-based probability propagation through the full payment and tour chain.
#check_tsp_axioms TSPGap.Section5Budget.recovered
#check_tsp_axioms TSPGap.Section5Budget.capacity
#check_tsp_axioms TSPGap.Section5Budget.le_common
#check_tsp_axioms TSPGap.Section5Budget.fallback
#check_tsp_axioms TSPGap.lemma_5_21_treeDist_capacity
#check_tsp_axioms TSPGap.lemma_5_22_treeDist_capacity
#check_tsp_axioms TSPGap.theorem_5_28_budget
#check_tsp_axioms TSPGap.theorem_5_28_capacity
#check_tsp_axioms TSPGap.theorem_5_28_liftProb_budget
#check_tsp_axioms TSPGap.theorem_5_28_liftProb_capacity
#check_tsp_axioms TSPGap.two_half_bundles_211_capacity
#check_tsp_axioms TSPGap.lemma_5_25_of_le_capacity
#check_tsp_axioms TSPGap.lemma_5_25_B_of_le_capacity
#check_tsp_axioms TSPGap.two_half_bundles_211_liftProb_capacity
#check_tsp_axioms TSPGap.lemma_5_25_of_le_liftProb_capacity
#check_tsp_axioms TSPGap.lemma_5_25_B_of_le_liftProb_capacity
#check_tsp_axioms TSPGap.EdgeRefinement.theorem_5_28_cases_on_budget
#check_tsp_axioms TSPGap.EdgeRefinement.twoOneOneGoodOn_of_not_half_capacity
#check_tsp_axioms TSPGap.EdgeRefinement.happyEventOn_ge_capacity
#check_tsp_axioms TSPGap.EdgeRefinement.exists_topThinningsOn_budget
#check_tsp_axioms TSPGap.EdgeRefinement.exists_topThinningsOn_capacity
#check_tsp_axioms TSPGap.case1a_branch_on_capacity
#check_tsp_axioms TSPGap.lemma_7_3_on_capacity
#check_tsp_axioms TSPGap.ReductionDataOn.push_hasOddMassBounds_capacity
#check_tsp_axioms TSPGap.ReductionDataOn.push_lemma_7_2_capacity
#check_tsp_axioms TSPGap.ReductionDataOn.push_paymentCore_capacity
#check_tsp_axioms TSPGap.epsPCapacity_eq
#check_tsp_axioms TSPGap.epsPCapacity_pos
#check_tsp_axioms TSPGap.epsP_le_capacity
#check_tsp_axioms TSPGap.exists_mainPayment_capacity
#check_tsp_axioms TSPGap.exists_payment_hierarchy_capacity
#check_tsp_axioms TSPGap.exists_slack_pair_capacity

-- Song arithmetic and finite layering. The threshold producers remain explicit
-- hypotheses; these declarations do not replace the verified gap theorem.
#check_tsp_axioms TSPGap.Song.parameter_bounds
#check_tsp_axioms TSPGap.Song.a_bounds
#check_tsp_axioms TSPGap.Song.aBot_bounds
#check_tsp_axioms TSPGap.Song.g₀_eq
#check_tsp_axioms TSPGap.Song.a_pos
#check_tsp_axioms TSPGap.Song.a_lt_one
#check_tsp_axioms TSPGap.Song.g₀_pos
#check_tsp_axioms TSPGap.Song.H_pos
#check_tsp_axioms TSPGap.Song.H_lt_one
#check_tsp_axioms TSPGap.Song.small_denominator_bounds
#check_tsp_axioms TSPGap.Song.epsilon_eq
#check_tsp_axioms TSPGap.Song.exp_neg_three_gt
#check_tsp_axioms TSPGap.Song.large_product_margin
#check_tsp_axioms TSPGap.Song.small_product_margin
#check_tsp_axioms TSPGap.Song.polygon_product_margin
#check_tsp_axioms TSPGap.Song.window_product_margin
#check_tsp_axioms TSPGap.Song.mixed_product_margin
#check_tsp_axioms TSPGap.Song.competing_half_margin
#check_tsp_axioms TSPGap.Song.paired_product_margins
#check_tsp_axioms TSPGap.Song.ancestor_margins
#check_tsp_axioms TSPGap.Song.top_payment_margins
#check_tsp_axioms TSPGap.Song.bottom_burden_margins
#check_tsp_axioms TSPGap.Song.bottom_absorption_margin
#check_tsp_axioms TSPGap.Song.pi_den_pos
#check_tsp_axioms TSPGap.Song.pi_antitone
#check_tsp_axioms TSPGap.Song.repair_nonneg
#check_tsp_axioms TSPGap.Song.repair_mono
#check_tsp_axioms TSPGap.Song.kappa_envelope
#check_tsp_axioms TSPGap.Song.final_arithmetic
#check_tsp_axioms TSPGap.ThresholdSlack.beta_zero
#check_tsp_axioms TSPGap.ThresholdSlack.beta_nonneg
#check_tsp_axioms TSPGap.ThresholdSlack.beta_sub
#check_tsp_axioms TSPGap.ThresholdSlack.beta_mono
#check_tsp_axioms TSPGap.ThresholdSlack.beta_sub_le
#check_tsp_axioms TSPGap.ThresholdSlack.beta_mul_two_add
#check_tsp_axioms TSPGap.ThresholdSlack.level_zero
#check_tsp_axioms TSPGap.ThresholdSlack.level_last
#check_tsp_axioms TSPGap.ThresholdSlack.level_nonneg
#check_tsp_axioms TSPGap.ThresholdSlack.level_mono
#check_tsp_axioms TSPGap.ThresholdSlack.level_pos
#check_tsp_axioms TSPGap.ThresholdSlack.level_le
#check_tsp_axioms TSPGap.ThresholdSlack.level_succ_sub
#check_tsp_axioms TSPGap.ThresholdSlack.increment_nonneg
#check_tsp_axioms TSPGap.ThresholdSlack.increment_le
#check_tsp_axioms TSPGap.ThresholdSlack.sum_increment
#check_tsp_axioms TSPGap.ThresholdSlack.combined_lower
#check_tsp_axioms TSPGap.ThresholdSlack.combined_cut_lower
#check_tsp_axioms TSPGap.ThresholdSlack.combined_expect
#check_tsp_axioms TSPGap.ThresholdSlack.prefix_cut_bound
#check_tsp_axioms TSPGap.ThresholdSlack.combined_cut_feasible
#check_tsp_axioms TSPGap.ThresholdSlack.combined_cut_feasible_of_root_notMem
#check_tsp_axioms TSPGap.ThresholdSlack.sum_levels
#check_tsp_axioms TSPGap.ThresholdSlack.sum_level_increment_le
#check_tsp_axioms TSPGap.ThresholdSlack.totalGain_lower_bound
#check_tsp_axioms TSPGap.Song.lowerBound_le_totalGain
#check_tsp_axioms TSPGap.Song.totalGain_gt_target
#check_tsp_axioms TSPGap.Song.layered_slack_of_certificates

-- Song large-bundle producer. These give an original-law happy mass, not
-- a Song payment certificate or a replacement end-to-end gap theorem.
#check_tsp_axioms TSPGap.Song.expCard_split
#check_tsp_axioms TSPGap.Song.present_mean_bounds
#check_tsp_axioms TSPGap.Song.clean_present_avoid_support
#check_tsp_axioms TSPGap.Song.cleanBundleData
#check_tsp_axioms TSPGap.Song.large_mean_profile
#check_tsp_axioms TSPGap.Song.hierarchy_error_budget
#check_tsp_axioms TSPGap.Song.large_profile_budget
#check_tsp_axioms TSPGap.Song.large_bundle_kernel
#check_tsp_axioms TSPGap.Song.largeBundleData
#check_tsp_axioms TSPGap.Song.large_probability_product
#check_tsp_axioms TSPGap.Song.LargeBundleData.happy_mass
#check_tsp_axioms TSPGap.Song.lemma_5_22_indexed
-- End Song large-bundle producer.

-- Song central-rank and marginal-shift foundation (Lemmas 12 and 20).
-- These do not yet construct the paired-bundle tables or payment producer.
#check_tsp_axioms TSPGap.Song.rankRatio_bounds
#check_tsp_axioms TSPGap.Song.rankPsi_nonneg
#check_tsp_axioms TSPGap.Song.rankPsi_le_rankPhi
#check_tsp_axioms TSPGap.Song.mean_le_rankPsi
#check_tsp_axioms TSPGap.Song.central_mass_mean_le
#check_tsp_axioms TSPGap.Song.expCard_le_rankPsi
#check_tsp_axioms TSPGap.Song.rankPsi_le_expCard
#check_tsp_axioms TSPGap.Song.rank_concentration
#check_tsp_axioms TSPGap.Song.shift_le_of_residual
#check_tsp_axioms TSPGap.Song.shift_le_rankPhi
#check_tsp_axioms TSPGap.Song.avoid_shift_le
#check_tsp_axioms TSPGap.Song.avoid_shift
#check_tsp_axioms TSPGap.Song.present_shift
-- End Song concentration foundation.

-- Song paired-bundle final-avoidance tables. The initial conditioning
-- chains and the happy-event probability producer remain separate.
#check_tsp_axioms TSPGap.Song.avoid_near_certain
#check_tsp_axioms TSPGap.Song.paired_avoid_bounds
#check_tsp_axioms TSPGap.Song.paired_absent_budget
#check_tsp_axioms TSPGap.Song.paired_present_budget
#check_tsp_axioms TSPGap.Song.paired_absent_table
#check_tsp_axioms TSPGap.Song.paired_present_table
#check_tsp_axioms TSPGap.Song.paired_absent_means
#check_tsp_axioms TSPGap.Song.paired_present_means
-- End Song paired-bundle tables.

-- Song paired-bundle input conditioning. The early face/Z/C/e(B) stages
-- and the probability extraction are not supplied by this shared block.
#check_tsp_axioms TSPGap.Song.restriction_near_certain
#check_tsp_axioms TSPGap.Song.restriction_compose
#check_tsp_axioms TSPGap.Song.avoid_overlap_ge
#check_tsp_axioms TSPGap.Song.paired_input_setup
#check_tsp_axioms TSPGap.Song.paired_input_support
#check_tsp_axioms TSPGap.Song.paired_input_unwind
#check_tsp_axioms TSPGap.Song.paired_input_mass_ge
#check_tsp_axioms TSPGap.Song.paired_input_near_certain
#check_tsp_axioms TSPGap.Song.paired_input_mean_bounds
#check_tsp_axioms TSPGap.Song.paired_input_profile
-- End Song paired-bundle inputs.

-- Song paired-bundle earlier prefixes. Initial atom-face means and
-- geometry still require the fiber-tree instance; no new gap is asserted.
#check_tsp_axioms TSPGap.Song.expCard_avoid_sdiff
#check_tsp_axioms TSPGap.Song.avoid_overlap_le
#check_tsp_axioms TSPGap.Song.avoid_chain_mass
#check_tsp_axioms TSPGap.Song.onehot_mean_add_avoid
#check_tsp_axioms TSPGap.Song.avoid_prefix_setup
#check_tsp_axioms TSPGap.Song.restriction_expCard_le
#check_tsp_axioms TSPGap.Song.restriction_expCard_bound
#check_tsp_axioms TSPGap.Song.present_prefix_setup
#check_tsp_axioms TSPGap.Song.present_prefix_support
#check_tsp_axioms TSPGap.Song.present_prefix_unwind
#check_tsp_axioms TSPGap.Song.present_prefix_mean_bounds
#check_tsp_axioms TSPGap.Song.paired_absent_prefix_mass
#check_tsp_axioms TSPGap.Song.paired_present_prefix_mass
#check_tsp_axioms TSPGap.Song.paired_present_conservation_budget
-- End Song paired-bundle prefixes.

-- Song paired-bundle initial fiber-tree inputs. The original central
-- rank probabilities and coefficient/happiness extraction remain separate.
#check_tsp_axioms TSPGap.Song.PairedBoundaryGeometry.present_disjoint
#check_tsp_axioms TSPGap.Song.PairedBoundaryGeometry.absent_disjoint
#check_tsp_axioms TSPGap.Song.paired_boundary_geometry
#check_tsp_axioms TSPGap.Song.paired_atom_law
#check_tsp_axioms TSPGap.Song.partition_side_means
#check_tsp_axioms TSPGap.Song.paired_face_bounds
#check_tsp_axioms TSPGap.Song.paired_overlap_mean
#check_tsp_axioms TSPGap.Song.paired_prefix_pair
#check_tsp_axioms TSPGap.Song.paired_prefixes_indexed
#check_tsp_axioms TSPGap.Song.paired_dichotomy_indexed
-- End Song paired-bundle initial inputs.

-- Song paired-bundle pruned ranks and original-law profiles.
#check_tsp_axioms TSPGap.Song.count_prune_shift
#check_tsp_axioms TSPGap.Song.paired_count_geometry_of_cuts
#check_tsp_axioms TSPGap.Song.paired_count_geometry_indexed
#check_tsp_axioms TSPGap.Song.PairedCountGeometry.rank_events
#check_tsp_axioms TSPGap.Song.PairedCountGeometry.absent_rank_events
#check_tsp_axioms TSPGap.Song.PairedCountGeometry.present_rank_events
#check_tsp_axioms TSPGap.Song.PairedStartData.profile
#check_tsp_axioms TSPGap.Song.paired_absent_profile
#check_tsp_axioms TSPGap.Song.paired_present_profile
#check_tsp_axioms TSPGap.Song.PairedInputBounds.absent_table
#check_tsp_axioms TSPGap.Song.PairedInputBounds.present_table
-- End Song paired-bundle pruned ranks.

-- Song window splitting and original-rank bridge.
#check_tsp_axioms TSPGap.Song.window_split_bounds
#check_tsp_axioms TSPGap.Song.window_kernel
#check_tsp_axioms TSPGap.Song.window_mass_gt
#check_tsp_axioms TSPGap.Song.rank_two_mass_bound
#check_tsp_axioms TSPGap.Song.original_rank_budget
#check_tsp_axioms TSPGap.Song.original_rank_of_small_tail
#check_tsp_axioms TSPGap.Song.paired_original_ranks
#check_tsp_axioms TSPGap.Song.window_reuse_parameters
#check_tsp_axioms TSPGap.Song.window_reused_kernel
#check_tsp_axioms TSPGap.Song.window_reuse_mass_budget
#check_tsp_axioms TSPGap.Song.window_reused_unwind
-- End Song window splitting and original ranks.

-- Song actual window conditioning and tail transfers.
#check_tsp_axioms TSPGap.Song.clean_bundle_part_mean
#check_tsp_axioms TSPGap.Song.clean_bundle_antitone
#check_tsp_axioms TSPGap.Song.window_conditioning
#check_tsp_axioms TSPGap.Song.WindowConditioningData.unwind
#check_tsp_axioms TSPGap.Song.window_mean_bounds
#check_tsp_axioms TSPGap.Song.window_low_tail_arith
#check_tsp_axioms TSPGap.Song.window_low_tail
#check_tsp_axioms TSPGap.Song.window_tail_budgets
#check_tsp_axioms TSPGap.Song.window_clean_low_tail
#check_tsp_axioms TSPGap.Song.window_original_tail
-- End Song actual window conditioning.

-- Song window fiber-tree geometry and conditioning inputs.
#check_tsp_axioms TSPGap.Song.windowPuncture
#check_tsp_axioms TSPGap.Song.window_cut_outside
#check_tsp_axioms TSPGap.Song.window_punctures_disjoint
#check_tsp_axioms TSPGap.Song.window_puncture_card
#check_tsp_axioms TSPGap.Song.window_puncture_expCard
#check_tsp_axioms TSPGap.Song.window_puncture_baseline
#check_tsp_axioms TSPGap.Song.window_good_tail
#check_tsp_axioms TSPGap.Song.window_sanitized_cover
#check_tsp_axioms TSPGap.Song.window_sanitized_away
#check_tsp_axioms TSPGap.Song.window_conditioning_indexed
#check_tsp_axioms TSPGap.Song.window_puncture_means
#check_tsp_axioms TSPGap.Song.window_low_tail_indexed
#check_tsp_axioms TSPGap.Song.window_kernel_low_tail
#check_tsp_axioms TSPGap.Song.window_means_indexed
#check_tsp_axioms TSPGap.Song.window_happy_of_cells
-- End Song window fiber-tree inputs.

-- Song window assembly and non-goodness rank consequence.
#check_tsp_axioms TSPGap.Song.window_punctured_union_le
#check_tsp_axioms TSPGap.Song.window_restore_bundle_le
#check_tsp_axioms TSPGap.Song.window_kernel_original_tail
#check_tsp_axioms TSPGap.Song.window_happy_of_raw_cells
#check_tsp_axioms TSPGap.Song.window_unwind_cells
#check_tsp_axioms TSPGap.Song.window_happy_indexed
#check_tsp_axioms TSPGap.Song.window_original_mean
#check_tsp_axioms TSPGap.Song.window_rank_of_not_happy
-- End Song window assembly.

-- Song paired extraction and happy-event bridges.
#check_tsp_axioms TSPGap.projectCount_eval_lower_bound_zero
#check_tsp_axioms TSPGap.three_counts_zero_ge_of_capacity
#check_tsp_axioms TSPGap.three_counts_zero_ge_of_mean_profile
#check_tsp_axioms TSPGap.Song.paired_original_ranks_of_not_happy
#check_tsp_axioms TSPGap.Song.paired_absent_mean_profile
#check_tsp_axioms TSPGap.Song.paired_present_mean_profile
#check_tsp_axioms TSPGap.Song.paired_absent_counts
#check_tsp_axioms TSPGap.Song.exp_neg_two_ge_eighth
#check_tsp_axioms TSPGap.Song.paired_present_counts
#check_tsp_axioms TSPGap.Song.paired_count_split
#check_tsp_axioms TSPGap.Song.paired_cut_counts
#check_tsp_axioms TSPGap.Song.paired_happy_of_raw_cells
#check_tsp_axioms TSPGap.Song.paired_absent_baseline
-- End Song paired extraction.

-- Song paired original-law assembly and hierarchy instance.
#check_tsp_axioms TSPGap.Song.PairedStartData.final_unwind
#check_tsp_axioms TSPGap.Song.paired_absent_probability
#check_tsp_axioms TSPGap.Song.paired_present_probability
#check_tsp_axioms TSPGap.Song.paired_happy_of_ranks_indexed
#check_tsp_axioms TSPGap.Song.lemma_5_27_indexed
#check_tsp_axioms TSPGap.Song.lemma_5_27_liftProb
-- End Song paired original-law assembly.

-- Song bad-incident analytic kernel.
#check_tsp_axioms TSPGap.binomial_one_tail_antitone
#check_tsp_axioms TSPGap.exp_eighteen_elevenths_le
#check_tsp_axioms TSPGap.binomial_one_tail_ge
#check_tsp_axioms TSPGap.bernoulli_le_one_ge_seven_sixteenths
#check_tsp_axioms TSPGap.Song.probCount_two_ge_thin
#check_tsp_axioms TSPGap.Song.weightMass_eq_three_ge_thin
#check_tsp_axioms TSPGap.Song.exp_neg_half_le
#check_tsp_axioms TSPGap.Song.bad_incident_thin_constants
#check_tsp_axioms TSPGap.Song.bad_incident_newton
#check_tsp_axioms TSPGap.Song.bad_incident_thin
#check_tsp_axioms TSPGap.Song.weightMass_le_two_ge_seven_sixteenths
#check_tsp_axioms TSPGap.Song.bad_incident_kernel
-- End Song bad-incident analytic kernel.

-- Song bad-incident hierarchy and refinement bridge.
#check_tsp_axioms TSPGap.Hierarchy.nestedData_of_small_error
#check_tsp_axioms TSPGap.Hierarchy.nestedData
#check_tsp_axioms TSPGap.weightMass_costFace_le_tau
#check_tsp_axioms TSPGap.Song.nested_data
#check_tsp_axioms TSPGap.Song.nested_two_two_gt
#check_tsp_axioms TSPGap.Song.lemma_5_16
#check_tsp_axioms TSPGap.Song.bad_up
#check_tsp_axioms TSPGap.Song.lemma_5_16_liftProb
#check_tsp_axioms TSPGap.Song.bad_up_liftProb
-- End Song bad-incident hierarchy and refinement bridge.

-- Song goodness policy and matching inputs.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.IsGood
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGood_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.half_of_not_good
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.mass_lt_of_not_good
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.mass_of_good_of_half
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGood_iff_of_half
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGood_comm
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGood_mono
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.matchingInputs_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.IsBadIncident
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isBadIncident_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingInputs.upSum_le_of_badIncident
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingInputs.sum_bad_pairSum_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingInputs.badIncident_card_even
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingInputs.isGood_of_card_three
#check_tsp_axioms TSPGap.Song.goodness
#check_tsp_axioms TSPGap.Song.isGood_implies_legacy
#check_tsp_axioms TSPGap.Song.four_h_of_face
#check_tsp_axioms TSPGap.Song.lemma_5_17
#check_tsp_axioms TSPGap.Song.adjacent_good
#check_tsp_axioms TSPGap.Song.isGood_of_up
#check_tsp_axioms TSPGap.Song.bad_up_of_not_good
#check_tsp_axioms TSPGap.Song.bad_unique
#check_tsp_axioms TSPGap.Song.matchingInputs
#check_tsp_axioms TSPGap.Song.isGood_of_card_three
#check_tsp_axioms TSPGap.Song.badIncident_card_even
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.IsGoodIndexed
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.mass_of_goodIndexed_of_half
#check_tsp_axioms TSPGap.EdgeRefinement.isGoodIndexed_liftProb_iff
#check_tsp_axioms TSPGap.Song.mass_liftProb_of_good
#check_tsp_axioms TSPGap.Song.lemma_5_17_liftProb
#check_tsp_axioms TSPGap.Song.adjacent_good_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_27_liftProb_of_good
-- End Song goodness policy and matching inputs.

-- Song Hall condition and matching allocation.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.rowCap
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.touchCap
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.rowCap_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.rowCap_comm
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.rowCap_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.touchCap_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.badCap_touch_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.badCap_all_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.touchCap_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.rowCapacity
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.arcCapacity
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.cutCap_ge_of_hall
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.exists_saturating_flow
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.bundleAlloc_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.bundleAlloc_support
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.row_sum_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.bundleAlloc_bound
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.col_sum_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.sum_bundleAlloc
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.exists_matchingData_of_hall
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.m_eq_zero_of_not
#check_tsp_axioms TSPGap.Song.hall_bad_coefficient
#check_tsp_axioms TSPGap.Song.hall_proper_arith
#check_tsp_axioms TSPGap.Song.hall_three_arith
#check_tsp_axioms TSPGap.Song.hall_four_sparse_arith
#check_tsp_axioms TSPGap.Song.hall_four_bad_arith
#check_tsp_axioms TSPGap.Song.hall_many_arith
#check_tsp_axioms TSPGap.Song.demand_le
#check_tsp_axioms TSPGap.Song.sum_demand_le
#check_tsp_axioms TSPGap.Song.hall_inequality_of_inputs
#check_tsp_axioms TSPGap.Song.hall_inequality
#check_tsp_axioms TSPGap.Song.exists_saturating_flow
#check_tsp_axioms TSPGap.Song.exists_matchingData
#check_tsp_axioms TSPGap.Song.lemma_6_2
#check_tsp_axioms TSPGap.Song.exists_matchingData_seven_mul
-- End Song Hall condition and matching allocation.

-- Song small-bundle probability.
#check_tsp_axioms TSPGap.Song.smallPairSlack
#check_tsp_axioms TSPGap.Song.smallTripleSlack
#check_tsp_axioms TSPGap.Song.smallProbability
#check_tsp_axioms TSPGap.Song.small_slacks
#check_tsp_axioms TSPGap.Song.small_probability_gt
#check_tsp_axioms TSPGap.Song.small_capacity_profile
#check_tsp_axioms TSPGap.Song.small_capacity_kernel
#check_tsp_axioms TSPGap.Song.lemma_5_21_indexed
#check_tsp_axioms TSPGap.Song.lemma_5_21_treeDist
#check_tsp_axioms TSPGap.Song.lemma_5_21_liftProb_margin
#check_tsp_axioms TSPGap.Song.lemma_5_21_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_21_liftProb_seven_mul
-- End Song small-bundle probability.

-- Song balanced half-bundle probability and hierarchy window.
#check_tsp_axioms TSPGap.Song.clean_bundle_part_lower
#check_tsp_axioms TSPGap.Song.window_bundle_part_lower
#check_tsp_axioms TSPGap.Song.HalfBundleMeanBounds
#check_tsp_axioms TSPGap.Song.half_bundle_mean_bounds
#check_tsp_axioms TSPGap.Song.half_bundle_kernel
#check_tsp_axioms TSPGap.Song.halfBundleProbability
#check_tsp_axioms TSPGap.Song.half_bundle_probability_gt
#check_tsp_axioms TSPGap.Song.WindowConditioningData.unwind_trees
#check_tsp_axioms TSPGap.Song.WindowConditioningData.independent
#check_tsp_axioms TSPGap.Song.half_bundle_attach
#check_tsp_axioms TSPGap.Song.lemma_5_24_indexed
#check_tsp_axioms TSPGap.Song.half_bundle_condIndep_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_24_liftProb_margin
#check_tsp_axioms TSPGap.Song.lemma_5_24_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_24_liftProb_seven_mul
#check_tsp_axioms TSPGap.Song.lemma_A1_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_23_liftProb
-- End Song balanced half-bundle probability and hierarchy window.

-- Song common-event hierarchy assembly.
#check_tsp_axioms TSPGap.Song.lemma_5_22_treeDist
#check_tsp_axioms TSPGap.Song.lemma_5_22_liftProb_margin
#check_tsp_axioms TSPGap.Song.lemma_5_22_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_22_liftProb_seven_mul
#check_tsp_axioms TSPGap.Song.nonhalf_twoOneOne_liftProb
#check_tsp_axioms TSPGap.Song.two_half_bundles_211_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_25_liftProb
#check_tsp_axioms TSPGap.Song.lemma_5_25_B_liftProb
#check_tsp_axioms TSPGap.Song.theorem_5_28_liftProb
#check_tsp_axioms TSPGap.Song.theorem_5_28_liftProb_seven_mul
-- End Song common-event hierarchy assembly.

-- Song polygon selection and bottom thinnings.
#check_tsp_axioms TSPGap.PolygonSelection
#check_tsp_axioms TSPGap.PolygonBottomWitness
#check_tsp_axioms TSPGap.PolygonBottomGuarantees
#check_tsp_axioms TSPGap.PolygonSelection.mono
#check_tsp_axioms TSPGap.PolygonSelection.legacy_iff
#check_tsp_axioms TSPGap.PolygonSelection.exists_of_budget
#check_tsp_axioms TSPGap.PolygonSelection.happy
#check_tsp_axioms TSPGap.PolygonSelection.weightMass_inside
#check_tsp_axioms TSPGap.PolygonSelection.weightMass_cross
#check_tsp_axioms TSPGap.PolygonSelection.mean_bounds_of_subset_part
#check_tsp_axioms TSPGap.PolygonSelection.mean_bounds_of_part
#check_tsp_axioms TSPGap.PolygonSelection.expCard_inside
#check_tsp_axioms TSPGap.PolygonSelection.expCard_split
#check_tsp_axioms TSPGap.PolygonSelection.weightMass_meets_le
#check_tsp_axioms TSPGap.PolygonSelection.corollary_5_10_core
#check_tsp_axioms TSPGap.PolygonSelection.corollary_5_11_even_core
#check_tsp_axioms TSPGap.Song.polygonMassFloor
#check_tsp_axioms TSPGap.Song.polygon_mass_margin
#check_tsp_axioms TSPGap.Song.polygon_mass_budget
#check_tsp_axioms TSPGap.Song.polygon_exp_bound
#check_tsp_axioms TSPGap.Song.polygon_parity_bound
#check_tsp_axioms TSPGap.Song.PolygonBase
#check_tsp_axioms TSPGap.Song.exists_polygonBase_margin
#check_tsp_axioms TSPGap.Song.exists_polygonBase
#check_tsp_axioms TSPGap.Song.corollary_5_10_core
#check_tsp_axioms TSPGap.Song.corollary_5_11_even_core
#check_tsp_axioms TSPGap.Song.corollary_5_10
#check_tsp_axioms TSPGap.Song.corollary_5_11_part
#check_tsp_axioms TSPGap.Song.corollary_5_11
#check_tsp_axioms TSPGap.Song.corollary_5_11_right
#check_tsp_axioms TSPGap.Song.BottomGuarantees
#check_tsp_axioms TSPGap.Song.exists_bottomThinning
#check_tsp_axioms TSPGap.Song.exists_bottomThinning_common
#check_tsp_axioms TSPGap.Song.exists_bottomThinning_seven_mul
#check_tsp_axioms TSPGap.PolygonBottomWitness.totalMass_base
#check_tsp_axioms TSPGap.PolygonBottomWitness.weightMass_base
#check_tsp_axioms TSPGap.PolygonBottomWitness.cst_pos
#check_tsp_axioms TSPGap.PolygonBottomWitness.totalMass_raw_pos
#check_tsp_axioms TSPGap.PolygonBottomWitness.totalMass_base_pos
#check_tsp_axioms TSPGap.PolygonBottomWitness.totalMass_raw_mul_weightMass_thin
#check_tsp_axioms TSPGap.PolygonBottomWitness.weightMass_thin_le
#check_tsp_axioms TSPGap.PolygonBottomGuarantees.legacy_iff
-- End Song polygon selection and bottom thinnings.

-- Song top thinnings and density consumers.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.BadCase
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.badCase_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.good_of_not_badCase
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.happyWrtOn_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.good
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.card_eq_two
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.card_eq_two'
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.inducesTree
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.not_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.not_odd_project
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.HappyWrtOn.of_twoTwoTwo
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.happyEventOn_happyWrtOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopRectangularOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.toLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.ofLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.toLegacy_ofLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.ofLegacy_toLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopRectangularOn.legacy_iff
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.IsGoodPair
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.IsCaseThreeOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.caseThreeEventOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.caseThreeThinOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.exists_topThinningsOn_of_inputs
#check_tsp_axioms TSPGap.Song.TopThinningsOn
#check_tsp_axioms TSPGap.Song.TopRectangularOn
#check_tsp_axioms TSPGap.Song.twoTwoHappyOn_ge_of_good
#check_tsp_axioms TSPGap.Song.happyEventOn_ge
#check_tsp_axioms TSPGap.Song.theorem_5_28_cases_on
#check_tsp_axioms TSPGap.Song.exists_topThinningsOn
#check_tsp_axioms TSPGap.Song.exists_topThinningsOn_seven_mul
#check_tsp_axioms TSPGap.Song.exists_topFamily
#check_tsp_axioms TSPGap.Song.exists_topFamily_seven_mul
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.thin_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.thin_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.goodPair_of_thin_ne_zero
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.happy_of_thin_ne_zero
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_le_one
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.expect_rho
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_eq_zero_of_not_good
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_eq_zero_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_eq_zero_of_odd'
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.expect_rho_indicator
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.weightMass_mul_expect_rho
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.expect_rho_indicator_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.expect_rho_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.expect_rho_odd_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.thin_odd_le_trivial
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_eq_of_thin_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.rho_legacy
-- End Song top thinnings and density consumers.

-- Song reduction data and projection.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_eq_zero_of_not
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_eq_zero_of_bad_bundle
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.sum_reduction_bad_fiber
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.reduction_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reductionAt
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reductionAt_of_not
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_eq_of_isEdgeParent
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_top
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_reduction_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_reduction_top
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_eq_zero_of_neither
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_eq_zero_of_noParent
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reductionAt_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.HasTopRectangularOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.HasBottomGuarantees
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.topRect
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.bottomGuar
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.bottomPolygonWitness
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_rho_bottom_odd_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_rho_bottom_notLeftHappy_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_rho_bottom_notRightHappy_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_eq_zero_of_mem_root_tail
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.sum_reduction_root_tail
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.sum_expect_reduction_root_tail_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.toLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.ofLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.toLegacy_ofLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.ofLegacy_toLegacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.hasTopRectangularOn_legacy_iff
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.hasBottomGuarantees_legacy_iff
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_le_one
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.expect_projectedRho
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_eq_zero_of_not_good
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_eq_zero_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_eq_zero_of_odd'
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.thin_ne_zero_of_rho_ne_zero
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_coherent
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.projectedRho_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_projectedReduction
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_top
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_projectedReduction_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_projectedReduction_top
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_eq_zero_of_bad_bundle
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_eq_zero_of_mem_root_tail
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_projectedReduction_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_legacy
#check_tsp_axioms TSPGap.Song.ReductionDataOn
#check_tsp_axioms TSPGap.Song.ReductionGuarantees
#check_tsp_axioms TSPGap.Song.exists_reductionDataOn
#check_tsp_axioms TSPGap.Song.exists_reductionData
#check_tsp_axioms TSPGap.Song.exists_reductionData_seven_mul
#check_tsp_axioms TSPGap.Song.ReductionGuarantees.bottomPolygonWitness
#check_tsp_axioms TSPGap.Song.ReductionGuarantees.expect_rho_bottom_odd_le
#check_tsp_axioms TSPGap.Song.ReductionGuarantees.expect_rho_bottom_notLeftHappy_le
#check_tsp_axioms TSPGap.Song.ReductionGuarantees.expect_rho_bottom_notRightHappy_le
-- End Song reduction data and projection.

-- Song ancestor mass branches.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.IsGoodTopEdge
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGoodTopEdge_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGoodTopEdge_of_mem_good_fiber
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.goodTopPart
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.inactivePart
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.sum_split_three
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.goodTopPart_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.inactivePart_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.exists_good_bundle_of_mem_goodTop
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_split_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.reduction_eq_zero_of_inactive_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_inactive_eq_zero_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_bottom_le_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_le_of_goodTop_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_goodTop_le_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.expect_reduction_top_odd_le_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_le_of_pointwise_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.thin_odd_le_of_good_bundle_nested_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.expect_reduction_odd_le_of_parent_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_goodTop_parent_le_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.projected_oddReductionMass
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_root_tail
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_eq_good_add_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_le_good_add_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_le_of_rates
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_le_of_saving
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_legacy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_split_subset
#check_tsp_axioms TSPGap.Song.ancestor_mass_le
#check_tsp_axioms TSPGap.Song.ancestor_fractional_le
#check_tsp_axioms TSPGap.Song.ancestor_small_tail_le
#check_tsp_axioms TSPGap.Song.ancestor_large_bottom_le
#check_tsp_axioms TSPGap.Song.AncestorBranches
#check_tsp_axioms TSPGap.Song.ancestorBranches
#check_tsp_axioms TSPGap.Song.exists_reductionData_ancestorBranches
#check_tsp_axioms TSPGap.Song.exists_reductionData_ancestorBranches_seven_mul
#check_tsp_axioms TSPGap.Song.ancestor_large_inactive_le
-- End Song ancestor mass branches.

-- Song ancestor windows and complete estimate.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.exists_good_bundle_of_mem_upper_window
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.goodTop_sdiff
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.goodTop_mass_ge_of_subset
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.inactive_of_mem_root_tail
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.upSum_root_le_inactive
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.thin_odd_le_of_good_bundle_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.expect_reduction_odd_le_of_upper_window_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_goodTop_upper_window_le_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.expect_reduction_odd_le_of_upper_root_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_goodTop_upper_root_le_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_goodTop_le_of_window
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.goodSiblings
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.badSiblings
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.sum_siblings_split
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.inactive_of_mem_bad_fiber
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.sum_bad_fibers_le_inactive
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.expect_reduction_top_odd_le₂_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.thin_odd_le_of_twoOneOne_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.twoOneOneSiblings_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.notTwoOneOne_eq_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.sum_twoOneOne_split_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.twoOneOneWindow_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.twoOneOneWindow_subset_layer_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.sum_twoOneOneWindow_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.isGoodTopEdge_of_mem_twoOneOneWindow_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.mem_goodTopPart_of_mem_twoOneOneWindow_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.twoOneOne_window_mass_ge_on
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.oddReductionMass_twoOneOneWindow_le_on
#check_tsp_axioms TSPGap.Song.ancestor_le_of_good_window
#check_tsp_axioms TSPGap.Song.ancestor_middle_tail_le
#check_tsp_axioms TSPGap.Song.ancestor_small_layer_le
#check_tsp_axioms TSPGap.Song.ancestor_large_layer_of_side_le
#check_tsp_axioms TSPGap.Song.ancestor_large_layer_le
#check_tsp_axioms TSPGap.Song.ancestor_high_tail_le
#check_tsp_axioms TSPGap.Song.lemma_23_on
#check_tsp_axioms TSPGap.Song.lemma_23_projected
#check_tsp_axioms TSPGap.Song.AncestorEstimate
#check_tsp_axioms TSPGap.Song.ancestorEstimate
#check_tsp_axioms TSPGap.Song.exists_reductionData_ancestorEstimate
#check_tsp_axioms TSPGap.Song.exists_reductionData_ancestorEstimate_seven_mul
-- End Song ancestor windows and complete estimate.

-- Song actual top payments.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_eq_zero_of_upSum
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_eq_zero_of_not
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.sum_coeff
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.sum_coeff_mul
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_le_one
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_mul_upSum_mul_zFactor
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_mul_upSum_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.increase
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.increase_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.increase_eq_zero_of_not_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.increase_eq_zero_of_not
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.sum_increase_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.sum_increase_of_not_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.expect_increase
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.expect_increase_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.expect_increase_add_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.coeff_mul_upSum_mul_zFactor_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.MatchingData.expect_increase_zFactor_le
#check_tsp_axioms TSPGap.Song.threeAtom_heavy_at
#check_tsp_axioms TSPGap.Song.triangleRetention
#check_tsp_axioms TSPGap.Song.top_payment_rates
#check_tsp_axioms TSPGap.Song.triangle_small_factors
#check_tsp_axioms TSPGap.Song.triangle_matching_retention
#check_tsp_axioms TSPGap.Song.top_endpoint_coarse_le
#check_tsp_axioms TSPGap.Song.top_endpoint_large_le
#check_tsp_axioms TSPGap.Song.top_endpoint_regular_le
#check_tsp_axioms TSPGap.Song.top_pair_regular_le
#check_tsp_axioms TSPGap.Song.top_pair_triangle_le
#check_tsp_axioms TSPGap.Song.top_pair_le
#check_tsp_axioms TSPGap.Song.topSlack
#check_tsp_axioms TSPGap.Song.topSlack_comm
#check_tsp_axioms TSPGap.Song.topSlack_lower_bound
#check_tsp_axioms TSPGap.Song.topSlack_eq_zero_of_bad
#check_tsp_axioms TSPGap.Song.expect_topSlack
#check_tsp_axioms TSPGap.Song.topSlack_expect_le
#check_tsp_axioms TSPGap.Song.TopPaymentData
#check_tsp_axioms TSPGap.Song.exists_topPaymentData
#check_tsp_axioms TSPGap.Song.exists_reductionData_topPayment
#check_tsp_axioms TSPGap.Song.exists_reductionData_topPayment_seven_mul
-- End Song actual top payments.

-- Song actual bottom payments.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.liftExpect_rho_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projected_expect_mul
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_bundle
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_bottom_all
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.sum_projectedReduction
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.max_sum_projectedReduction_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_projectedReduction_le_of_not_bottom
#check_tsp_axioms TSPGap.EdgeRefinement.sum_sdiff_le_of_piece_side
#check_tsp_axioms TSPGap.EdgeRefinement.DegreePartitionOn.PolygonCompatible.sum_sdiff_side_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.liftProb_ne_zero_of_thin_ne_zero
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.TopThinningsOn.event_of_rho_ne_zero
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PolygonTopCases
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.polygonTopCases
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_increaseOn_le_of_top
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_increaseOn_up_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.reduction_arrow_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.sum_inter_arrow_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_increaseOn_arrow_le_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.projectedReduction_eq_zero_of_mem_cutEdges_rootCut
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_increase_rootCut_eq_zero
#check_tsp_axioms TSPGap.PolygonSelection.inside_bounds
#check_tsp_axioms TSPGap.PolygonSelection.interior_happy_core
#check_tsp_axioms TSPGap.PolygonSelection.interior_happy
#check_tsp_axioms TSPGap.Song.boundary_product
#check_tsp_axioms TSPGap.Song.boundary_arith
#check_tsp_axioms TSPGap.Song.boundary_happy_core
#check_tsp_axioms TSPGap.Song.boundary_happy_left
#check_tsp_axioms TSPGap.Song.boundary_happy_right
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.retained_pair_saving
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.ReductionDataOn.expect_increaseOn_arrow_le_degree
#check_tsp_axioms TSPGap.Song.boundary_payment_arith
#check_tsp_axioms TSPGap.Song.expect_boundary_arrow_le
#check_tsp_axioms TSPGap.Song.expect_interior_arrow_le
#check_tsp_axioms TSPGap.Song.J₁_mono
#check_tsp_axioms TSPGap.Song.J₂_mono
#check_tsp_axioms TSPGap.Song.J₃_mono
#check_tsp_axioms TSPGap.Song.J₁_nonneg
#check_tsp_axioms TSPGap.Song.bottom_unhappy_le_t
#check_tsp_axioms TSPGap.Song.degree_burden_le
#check_tsp_axioms TSPGap.Song.boundary_burden_le
#check_tsp_axioms TSPGap.Song.interior_burden_le
#check_tsp_axioms TSPGap.Song.bottom_burdens_le
#check_tsp_axioms TSPGap.Song.bottom_increase_le
#check_tsp_axioms TSPGap.Song.bottomSlack
#check_tsp_axioms TSPGap.Song.bottomSlack_lower_bound
#check_tsp_axioms TSPGap.Song.bottomSlack_expect_le
#check_tsp_axioms TSPGap.Song.BottomPaymentData
#check_tsp_axioms TSPGap.Song.bottomPaymentData
#check_tsp_axioms TSPGap.Song.exists_reductionData_payments
#check_tsp_axioms TSPGap.Song.exists_reductionData_payments_seven_mul
-- End Song actual bottom payments.

-- Song global main payment.
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.goodEdges
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.mem_goodEdges
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.good_mass_of_degree
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_le
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_eq_zero_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_eq_zero_of_neither
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_eq_zero_of_noParent
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_eq_zero_of_no_bundle
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_eq_zero_of_not_happy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.topIncreaseAt
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increaseAt
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.slack
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.topIncreaseAt_eq
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.topIncreaseAt_eq_zero_of_not
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.topIncreaseAt_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increaseAt_of_not
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increaseAt_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase_nonneg
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase_eq_of_isEdgeParent
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase_bottom
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase_top
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase_eq_zero_of_neither
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.increase_eq_zero_of_noParent
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.slack_lower
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.topIncreaseAt_eq_zero_of_bad
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.reduction_eq_zero_of_bad
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.slack_eq_zero_of_not_mem_goodEdges
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.sum_slack_nonneg_of_odd
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.slack_bottom_of_not_happy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.neg_reduction_le_slack
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.left_unhappy
#check_tsp_axioms TSPGap.BundleGoodnessPolicy.PaymentDataOn.right_unhappy
#check_tsp_axioms TSPGap.Song.good_mass_of_degree
#check_tsp_axioms TSPGap.Song.PaymentCore
#check_tsp_axioms TSPGap.Song.PaymentCore.isMainPayment
#check_tsp_axioms TSPGap.Song.TopPaymentData.toPaymentData
#check_tsp_axioms TSPGap.Song.TopPaymentData.slack_top_eq
#check_tsp_axioms TSPGap.Song.TopPaymentData.slack_bottom_eq
#check_tsp_axioms TSPGap.Song.TopPaymentData.paymentCore
#check_tsp_axioms TSPGap.Song.exists_globalPayment
#check_tsp_axioms TSPGap.Song.exists_globalPayment_seven_mul
-- End Song global main payment.

-- Song separate repairs.
#check_tsp_axioms TSPGap.PolygonRep.sum_arrowRight_eq_cutSum
#check_tsp_axioms TSPGap.PolygonRep.sum_arrowCirc_eq_cutSum_sub
#check_tsp_axioms TSPGap.probEvent_arrowRight_ne_one_le
#check_tsp_axioms TSPGap.probEvent_occursRight_le_of_disjoint
#check_tsp_axioms TSPGap.probEvent_occursLeft_le_of_disjoint
#check_tsp_axioms TSPGap.BadEventIndex.probEvent_occurs_le_joint
#check_tsp_axioms TSPGap.expect_slack_le_of_prob_bound
#check_tsp_axioms TSPGap.exists_slack_vector_of_family_joint
#check_tsp_axioms TSPGap.exists_slack_vector_of_polygonFamily_joint
#check_tsp_axioms TSPGap.exists_slack_vector_of_subtourLP_joint
#check_tsp_axioms TSPGap.exists_slackStar_bothSides_joint
#check_tsp_axioms TSPGap.good_mass_of_nested_sharp
#check_tsp_axioms TSPGap.bottom_support_of_group_support
#check_tsp_axioms TSPGap.exists_slackStar_hierarchy_supported
#check_tsp_axioms TSPGap.Song.SeparatedRepair
#check_tsp_axioms TSPGap.Song.SeparatedRepair.one_eq_zero_of_not_bottom
#check_tsp_axioms TSPGap.Song.SeparatedRepair.one_eq_zero_of_not_good
#check_tsp_axioms TSPGap.Song.g₀_le_nested_mass
#check_tsp_axioms TSPGap.Song.exists_separatedRepair
#check_tsp_axioms TSPGap.Song.one_repair_absorption
#check_tsp_axioms TSPGap.Song.SeparatedRepair.expect_main_add_one
#check_tsp_axioms TSPGap.Song.exists_payment_with_repairs
-- End Song separate repairs.

-- Song threshold and endpoint.
#check_tsp_axioms TSPGap.Song.thresholdScale
#check_tsp_axioms TSPGap.Song.thresholdBonus
#check_tsp_axioms TSPGap.Song.thresholdScale_pos
#check_tsp_axioms TSPGap.Song.thresholdScale_ge_one
#check_tsp_axioms TSPGap.Song.thresholdBonus_nonneg
#check_tsp_axioms TSPGap.Song.pi_pos
#check_tsp_axioms TSPGap.Song.pi_le_one
#check_tsp_axioms TSPGap.Song.thresholdScale_sub_bonus
#check_tsp_axioms TSPGap.Song.thresholdScale_saving
#check_tsp_axioms TSPGap.Song.thresholdBonus_mass_balance
#check_tsp_axioms TSPGap.Song.thresholdOffset
#check_tsp_axioms TSPGap.Song.thresholdReweight
#check_tsp_axioms TSPGap.Song.thresholdOffset_sum
#check_tsp_axioms TSPGap.Song.thresholdOffset_sum_nonneg
#check_tsp_axioms TSPGap.Song.thresholdReweight_lower
#check_tsp_axioms TSPGap.Song.thresholdSlack
#check_tsp_axioms TSPGap.Song.thresholdSlack_expect
#check_tsp_axioms TSPGap.Song.thresholdSlack_certificate
#check_tsp_axioms TSPGap.Song.exists_thresholdSlack
#check_tsp_axioms TSPGap.Song.exists_thresholdLayers
#check_tsp_axioms TSPGap.Song.exists_layeredSlack
#check_tsp_axioms TSPGap.exists_tour_of_random_join
#check_tsp_axioms TSPGap.ojoinFeasible_of_all_cut_slack
#check_tsp_axioms TSPGap.exists_tour_of_all_cut_slack
#check_tsp_axioms TSPGap.Song.exists_tour_of_rootEdge
#check_tsp_axioms TSPGap.song_gap
-- End Song threshold and endpoint.
