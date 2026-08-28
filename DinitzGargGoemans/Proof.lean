import DinitzGargGoemans.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DinitzGargGoemans

@[simp] theorem univCommodity :
    (Finset.univ : Finset Commodity) = {.one, .two, .three} := by
  decide

@[simp] theorem univRouteChoice :
    (Finset.univ : Finset RouteChoice) = {.paid, .free} := by
  decide

@[simp] theorem univArc :
    (Finset.univ : Finset Arc) =
      {.sT1, .sT2, .sU, .uV, .uT3, .vT1, .vW, .wT2, .wT3} := by
  decide

theorem routeEdgesValid :
    ∀ k r, edgePath .source (routeEdges k r) (commodityTerminal k) := by
  intro k r
  cases k <;> cases r <;>
    simp [edgePath, routeEdges, commodityTerminal, arcTail, arcHead]

theorem edgePathFromTerminal1 (as : List Arc) (v : Vertex) :
    edgePath .terminal1 as v ↔ as = [] ∧ v = .terminal1 := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.terminal1 = v ↔ v = .terminal1))
  | cons a rest =>
    cases a <;> simp [edgePath, arcTail]

theorem edgePathFromTerminal2 (as : List Arc) (v : Vertex) :
    edgePath .terminal2 as v ↔ as = [] ∧ v = .terminal2 := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.terminal2 = v ↔ v = .terminal2))
  | cons a rest =>
    cases a <;> simp [edgePath, arcTail]

theorem edgePathFromTerminal3 (as : List Arc) (v : Vertex) :
    edgePath .terminal3 as v ↔ as = [] ∧ v = .terminal3 := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.terminal3 = v ↔ v = .terminal3))
  | cons a rest =>
    cases a <;> simp [edgePath, arcTail]

theorem edgePathFromJunctionW (as : List Arc) (v : Vertex) :
    edgePath .junctionW as v ↔
      (as = [] ∧ v = .junctionW) ∨
      (as = [.wT2] ∧ v = .terminal2) ∨
      (as = [.wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.junctionW = v ↔ v = .junctionW))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal2,
        edgePathFromTerminal3]

theorem edgePathFromJunctionV (as : List Arc) (v : Vertex) :
    edgePath .junctionV as v ↔
      (as = [] ∧ v = .junctionV) ∨
      (as = [.vT1] ∧ v = .terminal1) ∨
      (as = [.vW] ∧ v = .junctionW) ∨
      (as = [.vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.vW, .wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.junctionV = v ↔ v = .junctionV))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal1,
        edgePathFromJunctionW]

theorem edgePathFromJunctionU (as : List Arc) (v : Vertex) :
    edgePath .junctionU as v ↔
      (as = [] ∧ v = .junctionU) ∨
      (as = [.uV] ∧ v = .junctionV) ∨
      (as = [.uT3] ∧ v = .terminal3) ∨
      (as = [.uV, .vT1] ∧ v = .terminal1) ∨
      (as = [.uV, .vW] ∧ v = .junctionW) ∨
      (as = [.uV, .vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.uV, .vW, .wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.junctionU = v ↔ v = .junctionU))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal3,
        edgePathFromJunctionV]

theorem edgePathFromSource (as : List Arc) (v : Vertex) :
    edgePath .source as v ↔
      (as = [] ∧ v = .source) ∨
      (as = [.sT1] ∧ v = .terminal1) ∨
      (as = [.sT2] ∧ v = .terminal2) ∨
      (as = [.sU] ∧ v = .junctionU) ∨
      (as = [.sU, .uV] ∧ v = .junctionV) ∨
      (as = [.sU, .uT3] ∧ v = .terminal3) ∨
      (as = [.sU, .uV, .vT1] ∧ v = .terminal1) ∨
      (as = [.sU, .uV, .vW] ∧ v = .junctionW) ∨
      (as = [.sU, .uV, .vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.sU, .uV, .vW, .wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.source = v ↔ v = .source))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal1,
        edgePathFromTerminal2, edgePathFromTerminal3,
        edgePathFromJunctionU]

theorem allSourceTerminalPaths (k : Commodity) (as : List Arc) :
    edgePath .source as (commodityTerminal k) ↔
      as = routeEdges k .paid ∨ as = routeEdges k .free := by
  cases k with
  | one =>
    simpa [routeEdges, commodityTerminal] using
      (edgePathFromSource as .terminal1)
  | two =>
    simpa [routeEdges, commodityTerminal] using
      (edgePathFromSource as .terminal2)
  | three =>
    simpa [routeEdges, commodityTerminal] using
      (edgePathFromSource as .terminal3)

theorem strictDggRoundingImpWeak
    [Fintype Commodity] [Fintype RouteChoice] [Fintype Arc]
    [Nonempty Commodity]
    {I : PathFlowInstance Commodity RouteChoice Arc}
    {f : Commodity → RouteChoice → ℚ}
    {q : Commodity → RouteChoice}
    (h : strictDggRounding I f q) : weakDggRounding I f q := by
  rcases h with ⟨routing, bound, cost⟩
  exact ⟨routing, fun a => (bound a).le, cost⟩

theorem counterexampleWellFormed :
    wellFormedInstance counterexampleInstance := by
  constructor
  · intro k
    cases k <;> simp [counterexampleInstance, demandAmount]
  · intro a
    cases a <;> norm_num [counterexampleInstance, arcCapacity, arcCost]

theorem counterexampleMaximumDemand :
    maximumDemand counterexampleInstance = 15 := by
  simp [maximumDemand, counterexampleInstance, demandAmount,
    Finset.max'_insert, Finset.max'_singleton]
  norm_num

theorem splitFlowMeetsDemands :
    ∀ k, (∑ r, splitFlow k r) = demandAmount k := by
  intro k
  cases k <;> simp [splitFlow, demandAmount, Finset.sum_insert]
  all_goals norm_num

theorem fractionalLoadEqCapacity :
    ∀ a, fractionalLoad counterexampleInstance splitFlow a = arcCapacity a := by
  intro a
  cases a <;>
    simp [fractionalLoad, counterexampleInstance, counterexampleUses,
      routeEdges, splitFlow, arcCapacity, Finset.sum_insert]
  all_goals norm_num

theorem fractionalCostValue :
    fractionalCost counterexampleInstance splitFlow = 58 := by
  rw [fractionalCost]
  simp_rw [fractionalLoadEqCapacity]
  simp [counterexampleInstance, arcCost, arcCapacity, Finset.sum_insert]
  norm_num

theorem unsplittableLoadSU (q : Commodity → RouteChoice) :
    unsplittableLoad counterexampleInstance q .sU =
      (if q .one = .free then 15 else 0) +
        (if q .two = .free then 10 else 0) + 15 := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, h1, h2, h3, Finset.sum_insert]
  all_goals norm_num

theorem unsplittableLoadUV (q : Commodity → RouteChoice) :
    unsplittableLoad counterexampleInstance q .uV =
      (if q .one = .free then 15 else 0) +
        (if q .two = .free then 10 else 0) +
        (if q .three = .free then 15 else 0) := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, h1, h2, h3, Finset.sum_insert]
  all_goals norm_num

theorem unsplittableLoadVW (q : Commodity → RouteChoice) :
    unsplittableLoad counterexampleInstance q .vW =
      (if q .two = .free then 10 else 0) +
        (if q .three = .free then 15 else 0) := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, h1, h2, h3, Finset.sum_insert]

theorem unsplittableCostEqPaidCount (q : Commodity → RouteChoice) :
    unsplittableCost counterexampleInstance q = 30 * paidCount q := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableCost, unsplittableLoad, counterexampleInstance,
      counterexampleUses, routeEdges, demandAmount, arcCost, h1, h2, h3,
      paidCount, Finset.sum_insert]
  all_goals norm_num

theorem boundedRoutingHasTwoPaid (q : Commodity → RouteChoice)
    (bound : ∀ a,
      unsplittableLoad counterexampleInstance q a ≤
        fractionalLoad counterexampleInstance splitFlow a +
          maximumDemand counterexampleInstance) :
    2 ≤ paidCount q := by
  have hsu := bound .sU
  have huv := bound .uV
  have hvw := bound .vW
  simp only [fractionalLoadEqCapacity, counterexampleMaximumDemand] at hsu huv hvw
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, arcCapacity, paidCount, h1, h2, h3,
      Finset.sum_insert] at hsu huv hvw ⊢
  all_goals linarith

theorem boundedUnsplittableCost (q : Commodity → RouteChoice)
    (bound : ∀ a,
      unsplittableLoad counterexampleInstance q a ≤
        fractionalLoad counterexampleInstance splitFlow a +
          maximumDemand counterexampleInstance) :
    60 ≤ unsplittableCost counterexampleInstance q := by
  have count := boundedRoutingHasTwoPaid q bound
  have countQ : (2 : ℚ) ≤ (paidCount q : ℚ) := by
    exact_mod_cast count
  rw [unsplittableCostEqPaidCount]
  linarith

theorem splitFlowFeasible :
    fractionalFeasible counterexampleInstance splitFlow := by
  refine ⟨counterexampleWellFormed, ?_, ?_, ?_, ?_⟩
  · intro k r
    cases k <;> cases r <;> norm_num [splitFlow]
  · intro k r h
    simp [counterexampleInstance] at h
  · intro k
    simpa [counterexampleInstance] using splitFlowMeetsDemands k
  · intro a
    rw [fractionalLoadEqCapacity]
    simp [counterexampleInstance]

theorem noWeakDggRounding :
    ¬ weakDggProperty counterexampleInstance splitFlow := by
  intro h
  rcases h with ⟨q, hq⟩
  rcases hq with ⟨routing, bound, cost⟩
  have lower := boundedUnsplittableCost q bound
  have upper := cost
  have fractional := fractionalCostValue
  linarith

theorem noStrictDggRounding :
    ¬ strictDggProperty counterexampleInstance splitFlow := by
  intro h
  rcases h with ⟨q, hq⟩
  exact noWeakDggRounding ⟨q, strictDggRoundingImpWeak hq⟩

theorem dggCounterexampleWitness :
    dggCounterexample counterexampleInstance splitFlow := by
  exact ⟨counterexampleWellFormed, splitFlowFeasible, noWeakDggRounding⟩

theorem weakDggCostConjectureFalse :
    ¬ (∀ (I : PathFlowInstance Commodity RouteChoice Arc)
        (f : Commodity → RouteChoice → ℚ),
        wellFormedInstance I ∧ fractionalFeasible I f →
          weakDggProperty I f) := by
  intro h
  exact noWeakDggRounding
    (h counterexampleInstance splitFlow
      ⟨counterexampleWellFormed, splitFlowFeasible⟩)

theorem strictDggCostConjectureFalse :
    ¬ (∀ (I : PathFlowInstance Commodity RouteChoice Arc)
        (f : Commodity → RouteChoice → ℚ),
        wellFormedInstance I ∧ fractionalFeasible I f →
          strictDggProperty I f) := by
  intro h
  exact noStrictDggRounding
    (h counterexampleInstance splitFlow
      ⟨counterexampleWellFormed, splitFlowFeasible⟩)

end DinitzGargGoemans
