module

public import OverfullWork.RouteCopyGraphs

@[expose] public section


/-! # Copy capacities from simplicity and the recorded edge roles

Every removed pair has the selected color. Every added copy belongs to
the recorded free graph. Vertex-list Nodup bounds both copy graphs by
one at each vertex, hence by one on each bundle.
-/
namespace OverfullWork.PairedRoutes.Route
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {τ : Equiv.Perm V} {F : SimpleGraph V} {U : Finset V} {z : V} {n : ℕ}
set_option maxHeartbeats 16000000

theorem count_cons_eq (a v : V) (xs : List V) :
    (a::xs).count v=xs.count v+(if v=a then 1 else 0) := by
  by_cases ha : v=a
  · subst v;simp
  · simp [ha,Ne.symm ha]

theorem degree_added_count (p : Route τ F U z n) (a b : V)
    (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) (v : V) :
    (p.addedCopies a b ha hb).degree v=(a :: (p.vertices ++ [b])).count v := by
  rw [p.degree_addedCopies a b ha hb v]
  simp only [count_cons_eq,List.count_append,List.count_nil]
  omega

theorem removed_degree_le_one (p : Route τ F U z n) (hNe : ∀ x ∈ U, x ≠ τ x)
    (hp : p.vertices.Nodup) (v : V) : (p.removedCopies hNe).degree v ≤ 1 := by
  rw [p.degree_removedCopies]
  exact List.nodup_iff_count_le_one.mp hp v

theorem added_degree_le_one (p : Route τ F U z n) (a b : V)
    (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) (hp : (a :: (p.vertices ++ [b])).Nodup) (v : V) :
    (p.addedCopies a b ha hb).degree v ≤ 1 := by
  rw [p.degree_added_count a b ha hb v]
  exact List.nodup_iff_count_le_one.mp hp v

theorem unit_positive_eq (a b : V) (hab : a ≠ b) (e : Sym2 V)
    (he : 0 < (MultiGraph.unitEdge a b hab).mult e) : e=s(a,b) := by
  by_contra hn
  change 0 < (if e=s(a,b) then 1 else 0) at he
  rw [if_neg hn] at he
  omega

theorem removed_positive_pair (p : Route τ F U z n) (hNe : ∀ x ∈ U, x ≠ τ x)
    (e : Sym2 V) (he : 0 < (p.removedCopies hNe).mult e) : ∃ x ∈ U, e=s(x,τ x) := by
  induction p with
  | single x hx => exact ⟨x,hx,unit_positive_eq _ _ _ e he⟩
  | snoc p z hz hEdge ih =>
    change 0 < (p.removedCopies hNe).mult e+(MultiGraph.unitEdge z (τ z) (hNe z hz)).mult e at he
    by_cases hp : 0 < (p.removedCopies hNe).mult e
    · exact ih hp
    · have hz' : 0 < (MultiGraph.unitEdge z (τ z) (hNe z hz)).mult e := by omega
      exact ⟨z,hz,unit_positive_eq _ _ _ e hz'⟩

theorem prefix_positive_free (p : Route τ F U z n) (a : V) (ha : F.Adj a p.first)
    (e : Sym2 V) (he : 0 < (p.prefixCopies a ha).mult e) : ∃ x y, F.Adj x y ∧ e=s(x,y) := by
  induction p with
  | single x hx => exact ⟨a,x,ha,unit_positive_eq _ _ _ e he⟩
  | @snoc x n p z hz hEdge ih =>
    change 0 < (p.prefixCopies a ha).mult e+(MultiGraph.unitEdge (τ x) z hEdge.ne).mult e at he
    by_cases hp : 0 < (p.prefixCopies a ha).mult e
    · exact ih ha hp
    · have hz' : 0 < (MultiGraph.unitEdge (τ x) z hEdge.ne).mult e := by omega
      exact ⟨τ x,z,hEdge,unit_positive_eq _ _ _ e hz'⟩

theorem added_positive_free (p : Route τ F U z n) (a b : V)
    (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) (e : Sym2 V)
    (he : 0 < (p.addedCopies a b ha hb).mult e) : ∃ x y, F.Adj x y ∧ e=s(x,y) := by
  change 0 < (p.prefixCopies a ha).mult e+(MultiGraph.unitEdge (τ z) b hb.ne).mult e at he
  by_cases hp : 0 < (p.prefixCopies a ha).mult e
  · exact p.prefix_positive_free a ha e hp
  · have hb' : 0 < (MultiGraph.unitEdge (τ z) b hb.ne).mult e := by omega
    exact ⟨τ z,b,hb,unit_positive_eq _ _ _ e hb'⟩

theorem removed_le_of_pairs (p : Route τ F U z n) (hNe : ∀ x ∈ U, x ≠ τ x)
    (hp : p.vertices.Nodup) (L : MultiGraph V) (hPairs : ∀ x ∈ U, 1 ≤ L.mult s(x,τ x)) :
    ∀ e, (p.removedCopies hNe).mult e ≤ L.mult e := by
  intro e
  have hOne := (p.removedCopies hNe).mult_le_one_of_degrees (p.removed_degree_le_one hNe hp) e
  by_cases he : 0 < (p.removedCopies hNe).mult e
  · obtain ⟨x,hx,hEq⟩ := p.removed_positive_pair hNe e he
    rw [hEq]
    exact (show (p.removedCopies hNe).mult s(x,τ x) ≤ 1 by simpa only [hEq] using hOne).trans (hPairs x hx)
  · omega

theorem added_le_of_free (p : Route τ F U z n) (a b : V)
    (ha : F.Adj a p.first) (hb : F.Adj (τ z) b) (hp : (a :: (p.vertices ++ [b])).Nodup)
    (N : MultiGraph V) (hFree : ∀ x y, F.Adj x y → 0 < N.mult s(x,y)) :
    ∀ e, (p.addedCopies a b ha hb).mult e ≤ N.mult e := by
  intro e
  have hOne := (p.addedCopies a b ha hb).mult_le_one_of_degrees (p.added_degree_le_one a b ha hb hp) e
  by_cases he : 0 < (p.addedCopies a b ha hb).mult e
  · obtain ⟨x,y,hxy,hEq⟩ := p.added_positive_free a b ha hb e he
    have hPos := hFree x y hxy
    rw [hEq] at hOne ⊢
    omega
  · omega

end OverfullWork.PairedRoutes.Route
