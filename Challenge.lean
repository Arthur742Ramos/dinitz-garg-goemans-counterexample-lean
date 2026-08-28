import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.Order
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Lemmas

open scoped BigOperators

namespace DinitzGargGoemans

/-! A finite rational path-flow model for the Dinitz--Garg--Goemans
counterexample.  The definitions are repeated here so that this statement
surface has no dependency on the completed solution module. -/

structure PathFlowInstance (Commodity Route Arc : Type*) where
  admissible : Commodity → Route → Prop
  demand : Commodity → ℚ
  capacity : Arc → ℚ
  cost : Arc → ℚ
  uses : Commodity → Route → Arc → Prop

noncomputable def fractionalLoad
    [Fintype Commodity] [Fintype Route]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ) (a : Arc) : ℚ := by
  classical
  exact ∑ k, ∑ r, if I.uses k r a then f k r else 0

noncomputable def fractionalCost
    [Fintype Commodity] [Fintype Route] [Fintype Arc]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ) : ℚ :=
  ∑ a, I.cost a * fractionalLoad I f a

noncomputable def maximumDemand
    [Fintype Commodity] [Nonempty Commodity]
    (I : PathFlowInstance Commodity Route Arc) : ℚ := by
  classical
  exact (Finset.univ.image I.demand).max' (by simp)

def wellFormedInstance
    (I : PathFlowInstance Commodity Route Arc) : Prop :=
  (∀ k, 0 < I.demand k ∧ ∃ r, I.admissible k r) ∧
    ∀ a, 0 ≤ I.capacity a ∧ 0 ≤ I.cost a

noncomputable def fractionalFeasible
    [Fintype Commodity] [Fintype Route]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ) : Prop :=
  wellFormedInstance I ∧
    (∀ k r, 0 ≤ f k r) ∧
    (∀ k r, ¬ I.admissible k r → f k r = 0) ∧
    (∀ k, (∑ r, f k r) = I.demand k) ∧
    (∀ a, fractionalLoad I f a ≤ I.capacity a)

def unsplittableRouting
    (I : PathFlowInstance Commodity Route Arc)
    (q : Commodity → Route) : Prop :=
  ∀ k, I.admissible k (q k)

noncomputable def unsplittableLoad
    [Fintype Commodity]
    (I : PathFlowInstance Commodity Route Arc)
    (q : Commodity → Route) (a : Arc) : ℚ := by
  classical
  exact ∑ k, if I.uses k (q k) a then I.demand k else 0

noncomputable def unsplittableCost
    [Fintype Commodity] [Fintype Arc]
    (I : PathFlowInstance Commodity Route Arc)
    (q : Commodity → Route) : ℚ :=
  ∑ a, I.cost a * unsplittableLoad I q a

noncomputable def weakDggRounding
    [Fintype Commodity] [Fintype Route] [Fintype Arc] [Nonempty Commodity]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ)
    (q : Commodity → Route) : Prop :=
  unsplittableRouting I q ∧
    (∀ a, unsplittableLoad I q a ≤ fractionalLoad I f a + maximumDemand I) ∧
    unsplittableCost I q ≤ fractionalCost I f

noncomputable def strictDggRounding
    [Fintype Commodity] [Fintype Route] [Fintype Arc] [Nonempty Commodity]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ)
    (q : Commodity → Route) : Prop :=
  unsplittableRouting I q ∧
    (∀ a, unsplittableLoad I q a < fractionalLoad I f a + maximumDemand I) ∧
    unsplittableCost I q ≤ fractionalCost I f

noncomputable def weakDggProperty
    [Fintype Commodity] [Fintype Route] [Fintype Arc] [Nonempty Commodity]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ) : Prop :=
  ∃ q, weakDggRounding I f q

noncomputable def strictDggProperty
    [Fintype Commodity] [Fintype Route] [Fintype Arc] [Nonempty Commodity]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ) : Prop :=
  ∃ q, strictDggRounding I f q

noncomputable def dggCounterexample
    [Fintype Commodity] [Fintype Route] [Fintype Arc] [Nonempty Commodity]
    (I : PathFlowInstance Commodity Route Arc)
    (f : Commodity → Route → ℚ) : Prop :=
  wellFormedInstance I ∧ fractionalFeasible I f ∧ ¬ weakDggProperty I f

inductive Vertex where
  | source
  | junctionU
  | junctionV
  | junctionW
  | terminal1
  | terminal2
  | terminal3
deriving DecidableEq

instance : Fintype Vertex :=
  Fintype.ofList
    [.source, .junctionU, .junctionV, .junctionW,
      .terminal1, .terminal2, .terminal3]
    (by intro x; cases x <;> simp)

inductive Commodity where
  | one
  | two
  | three
deriving DecidableEq

instance : Fintype Commodity :=
  Fintype.ofList [.one, .two, .three]
    (by intro x; cases x <;> simp)

instance : Nonempty Commodity := ⟨Commodity.one⟩

inductive Arc where
  | sT1
  | sT2
  | sU
  | uV
  | uT3
  | vT1
  | vW
  | wT2
  | wT3
deriving DecidableEq

instance : Fintype Arc :=
  Fintype.ofList
    [.sT1, .sT2, .sU, .uV, .uT3, .vT1, .vW, .wT2, .wT3]
    (by intro x; cases x <;> simp)

inductive RouteChoice where
  | paid
  | free
deriving DecidableEq

instance : Fintype RouteChoice :=
  Fintype.ofList [.paid, .free]
    (by intro x; cases x <;> simp)

instance : Nonempty RouteChoice := ⟨RouteChoice.paid⟩

def arcTail : Arc → Vertex
  | .sT1 => .source
  | .sT2 => .source
  | .sU => .source
  | .uV => .junctionU
  | .uT3 => .junctionU
  | .vT1 => .junctionV
  | .vW => .junctionV
  | .wT2 => .junctionW
  | .wT3 => .junctionW

def arcHead : Arc → Vertex
  | .sT1 => .terminal1
  | .sT2 => .terminal2
  | .sU => .junctionU
  | .uV => .junctionV
  | .uT3 => .terminal3
  | .vT1 => .terminal1
  | .vW => .junctionW
  | .wT2 => .terminal2
  | .wT3 => .terminal3

def commodityTerminal : Commodity → Vertex
  | .one => .terminal1
  | .two => .terminal2
  | .three => .terminal3

def edgePath : Vertex → List Arc → Vertex → Prop
  | u, [], v => u = v
  | u, a :: as, v => arcTail a = u ∧ edgePath (arcHead a) as v

def routeEdges : Commodity → RouteChoice → List Arc
  | .one, .paid => [.sT1]
  | .one, .free => [.sU, .uV, .vT1]
  | .two, .paid => [.sT2]
  | .two, .free => [.sU, .uV, .vW, .wT2]
  | .three, .paid => [.sU, .uT3]
  | .three, .free => [.sU, .uV, .vW, .wT3]

def demandAmount : Commodity → ℚ
  | .one => 15
  | .two => 10
  | .three => 15

def arcCapacity : Arc → ℚ
  | .sT1 => 10
  | .sT2 => 6
  | .sU => 24
  | .uV => 14
  | .uT3 => 10
  | .vT1 => 5
  | .vW => 9
  | .wT2 => 4
  | .wT3 => 5

def arcCost : Arc → ℚ
  | .sT1 => 2
  | .sT2 => 3
  | .sU => 0
  | .uV => 0
  | .uT3 => 2
  | .vT1 => 0
  | .vW => 0
  | .wT2 => 0
  | .wT3 => 0

def counterexampleUses (k : Commodity) (r : RouteChoice) (a : Arc) : Prop :=
  a ∈ routeEdges k r

def counterexampleInstance : PathFlowInstance Commodity RouteChoice Arc :=
  { admissible := fun _ _ => True
    demand := demandAmount
    capacity := arcCapacity
    cost := arcCost
    uses := counterexampleUses }

def splitFlow : Commodity → RouteChoice → ℚ
  | .one, .paid => 10
  | .one, .free => 5
  | .two, .paid => 6
  | .two, .free => 4
  | .three, .paid => 10
  | .three, .free => 5

def paidCount (q : Commodity → RouteChoice) : ℕ :=
  (if q .one = .paid then 1 else 0) +
  (if q .two = .paid then 1 else 0) +
  (if q .three = .paid then 1 else 0)

/-! The following declarations are the advertised statement surface.  Their
proofs are intentionally omitted here and supplied by `Solution.lean`. -/

theorem allSourceTerminalPaths (k : Commodity) (as : List Arc) :
    edgePath .source as (commodityTerminal k) ↔
      as = routeEdges k .paid ∨ as = routeEdges k .free := by
  sorry

theorem splitFlowFeasible :
    fractionalFeasible counterexampleInstance splitFlow := by
  sorry

theorem fractionalCostValue :
    fractionalCost counterexampleInstance splitFlow = 58 := by
  sorry

theorem boundedUnsplittableCost (q : Commodity → RouteChoice)
    (bound : ∀ a,
      unsplittableLoad counterexampleInstance q a ≤
        fractionalLoad counterexampleInstance splitFlow a +
          maximumDemand counterexampleInstance) :
    60 ≤ unsplittableCost counterexampleInstance q := by
  sorry

theorem dggCounterexampleWitness :
    dggCounterexample counterexampleInstance splitFlow := by
  sorry

theorem weakDggCostConjectureFalse :
    ¬ (∀ (I : PathFlowInstance Commodity RouteChoice Arc)
        (f : Commodity → RouteChoice → ℚ),
        wellFormedInstance I ∧ fractionalFeasible I f →
          weakDggProperty I f) := by
  sorry

theorem strictDggCostConjectureFalse :
    ¬ (∀ (I : PathFlowInstance Commodity RouteChoice Arc)
        (f : Commodity → RouteChoice → ℚ),
        wellFormedInstance I ∧ fractionalFeasible I f →
          strictDggProperty I f) := by
  sorry

end DinitzGargGoemans
