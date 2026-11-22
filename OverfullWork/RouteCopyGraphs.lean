module

public import OverfullWork.LayerGrowthBounds

@[expose] public section


/-! # Actual removed and added copy graphs of a paired route

Count vertex incidences with List.count before assuming simplicity.
This makes all degree identities exact; Nodup will then give matching
bounds, including the free edges at the two unmatched endpoints.
-/
namespace OverfullWork.PairedRoutes.Route
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {τ : Equiv.Perm V} {F : SimpleGraph V} {U : Finset V} {z : V} {n : ℕ}
set_option maxHeartbeats 16000000

theorem unit_degree_split (a b : V) (hab : a ≠ b) (v : V) :
    (MultiGraph.unitEdge a b hab).degree v=(if v=a then 1 else 0)+(if v=b then 1 else 0) := by
  rw [MultiGraph.degree_unitEdge]
  by_cases ha : v=a <;> by_cases hb : v=b <;> simp_all

theorem count_pair (a b v : V) : [a,b].count v=(if v=a then 1 else 0)+(if v=b then 1 else 0) := by
  by_cases ha : v=a
  · subst v
    by_cases hb : a=b
    · subst b;simp
    · simp [hb,Ne.symm hb]
  · by_cases hb : v=b
    · subst v;simp [ha,Ne.symm ha]
    · simp [ha,Ne.symm ha,hb,Ne.symm hb]

def removedCopies (hNe : ∀ x ∈ U, x ≠ τ x) : {z : V} → {n : ℕ} → Route τ F U z n → MultiGraph V
  | _,_,.single x hx => MultiGraph.unitEdge x (τ x) (hNe x hx)
  | _,_,.snoc p z hz _ => (p.removedCopies hNe).addCopies (MultiGraph.unitEdge z (τ z) (hNe z hz))

def prefixCopies (a : V) : {z : V} → {n : ℕ} →
    (p : Route τ F U z n) → F.Adj a p.first → MultiGraph V
  | _,_,.single x _,ha => MultiGraph.unitEdge a x ha.ne
  | _,_,.snoc (x := x) p z _ he,ha => (p.prefixCopies a ha).addCopies (MultiGraph.unitEdge (τ x) z he.ne)

def addedCopies (p : Route τ F U z n) (a b : V) (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) : MultiGraph V :=
  (p.prefixCopies a ha).addCopies (MultiGraph.unitEdge (τ z) b hb.ne)

theorem degree_removedCopies (p : Route τ F U z n) (hNe : ∀ x ∈ U, x ≠ τ x) (v : V) :
    (p.removedCopies hNe).degree v=p.vertices.count v := by
  induction p with
  | single x hx => rw [removedCopies,unit_degree_split];exact (count_pair _ _ _).symm
  | snoc p z hz he ih =>
    simp only [removedCopies,MultiGraph.degree_addCopies,vertices,List.count_append,unit_degree_split,count_pair,ih]

theorem degree_prefixCopies (p : Route τ F U z n) (a : V) (ha : F.Adj a p.first) (v : V) :
    (p.prefixCopies a ha).degree v+(if v=τ z then 1 else 0)=
      (if v=a then 1 else 0)+p.vertices.count v := by
  induction p with
  | single x hx =>
    have hAx : F.Adj a x := ha
    have hDeg := unit_degree_split a x hAx.ne v
    have hCount := count_pair x (τ x) v
    change (MultiGraph.unitEdge a x hAx.ne).degree v+(if v=τ x then 1 else 0)=
      (if v=a then 1 else 0)+[x,τ x].count v
    omega
  | @snoc x n p z hz he ih =>
    simp only [prefixCopies,MultiGraph.degree_addCopies,vertices,List.count_append,unit_degree_split,count_pair]
    have hh := ih ha
    omega

theorem degree_addedCopies (p : Route τ F U z n) (a b : V)
    (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) (v : V) :
    (p.addedCopies a b ha hb).degree v=
      (if v=a then 1 else 0)+p.vertices.count v+(if v=b then 1 else 0) := by
  have hh := p.degree_prefixCopies a ha v
  simp only [addedCopies,MultiGraph.degree_addCopies,unit_degree_split]
  omega

theorem edgeCount_removedCopies (p : Route τ F U z n) (hNe : ∀ x ∈ U, x ≠ τ x) :
    (p.removedCopies hNe).edgeCount=n+1 := by
  induction p with
  | single x hx => exact MultiGraph.edgeCount_unitEdge _ _ _
  | snoc p z hz he ih =>
    simp only [removedCopies,MultiGraph.edgeCount_addCopies,MultiGraph.edgeCount_unitEdge,ih]

theorem edgeCount_prefixCopies (p : Route τ F U z n) (a : V) (ha : F.Adj a p.first) :
    (p.prefixCopies a ha).edgeCount=n+1 := by
  induction p with
  | single x hx => exact MultiGraph.edgeCount_unitEdge _ _ _
  | snoc p z hz he ih =>
    simp only [prefixCopies,MultiGraph.edgeCount_addCopies,MultiGraph.edgeCount_unitEdge]
    have hh := ih ha
    omega

theorem edgeCount_addedCopies (p : Route τ F U z n) (a b : V)
    (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) : (p.addedCopies a b ha hb).edgeCount=n+2 := by
  simp only [addedCopies,MultiGraph.edgeCount_addCopies,edgeCount_prefixCopies,MultiGraph.edgeCount_unitEdge]

end OverfullWork.PairedRoutes.Route
