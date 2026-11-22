module

public import OverfullWork.DirectedListRoutes

@[expose] public section


/-! Actual directed short paths avoiding a prescribed vertex set.
Finite ball-growth proof of the directed argument in KLO Lemma 6.6.
No undirected connectivity or Hamiltonian existence is substituted. -/
namespace OverfullWork.DirectedRobustShortPaths
open Finset DirectedRobustExpansion DirectedListRoutes
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 8000000

noncomputable def ball (D : Digraph V) (Z : Finset V) (x : V) (k : ℕ) : Finset V :=
  univ.filter fun v => ∃ l,Route D x v l ∧ l.length ≤ k ∧ ∀ z∈x :: l,z∉Z

theorem mem_ball (D : Digraph V) (Z : Finset V) (x v : V) (k : ℕ) :
    v∈ball D Z x k ↔ ∃ l,Route D x v l ∧ l.length ≤ k ∧ ∀ z∈x :: l,z∉Z := by
  simp [ball]

theorem outdegree_le_ball_one (D : Digraph V) (Z : Finset V) (x : V) (hx : x∉Z) :
    outDegree D x  ≤  (ball D Z x 1).card+Z.card := by
  let A := univ.filter fun v => D.Adj x v
  have hSub : A\Z⊆ball D Z x 1 := by
    intro v hv
    obtain ⟨hvA,hvZ⟩ := mem_sdiff.mp hv
    have hEdge : D.Adj x v := (mem_filter.mp hvA).2
    apply (mem_ball D Z x v 1).mpr
    refine ⟨[v],snoc_route D (nil_route D x) hEdge,by simp,?_⟩
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl  <;> assumption
  have hh := card_le_card_sdiff_add_card (s:=A) (t:=Z)
  exact hh.trans (Nat.add_le_add_right (card_le_card hSub) _)

theorem neighbourhood_subset_next (D : Digraph V) (Z : Finset V) (x : V)
    (k r : ℕ) (hr : 0 < r) :
    neighbourhood D r (ball D Z x k)\Z⊆ball D Z x (k+1) := by
  intro v hv
  obtain ⟨hvN,hvZ⟩ := mem_sdiff.mp hv
  have hPos : 0 < inNeighbours D (ball D Z x k) v := hr.trans_le (mem_filter.mp hvN).2
  obtain ⟨u,hu⟩ := card_pos.mp hPos
  obtain ⟨huB,hEdge⟩ := mem_filter.mp hu
  obtain ⟨l,hRoute,hLen,hAvoid⟩ := (mem_ball D Z x u k).mp huB
  refine (mem_ball D Z x v (k+1)).mpr ⟨l++[v],snoc_route D hRoute hEdge,by simp;omega,?_⟩
  intro z hz
  change z∈(x :: l)++[v] at hz
  rcases List.mem_append.mp hz with hz|hz
  · exact hAvoid z hz
  · exact List.mem_singleton.mp hz ▸ hvZ

theorem exists_route_of_large_ball (D : Digraph V) (Z : Finset V) (x y : V)
    (t k : ℕ) (hyZ : y∉Z) (hy : t ≤ inDegree D y)
    (hLarge : Fintype.card V < (ball D Z x k).card+t) :
    ∃ l,Route D x y l ∧ l.length ≤ k+1 ∧ ∀ z∈x :: l,z∉Z := by
  let A := univ.filter fun u => D.Adj u y
  have hCount := card_union_add_card_inter (ball D Z x k) A
  have hBound := card_le_univ (ball D Z x k∪A)
  have hA : A.card=inDegree D y := rfl
  have hPos : 0 < ((ball D Z x k)∩A).card := by omega
  obtain ⟨u,hu⟩ := card_pos.mp hPos
  obtain ⟨huB,huA⟩ := mem_inter.mp hu
  have hEdge := (mem_filter.mp huA).2
  obtain ⟨l,hRoute,hLen,hAvoid⟩ := (mem_ball D Z x u k).mp huB
  refine ⟨l++[y],snoc_route D hRoute hEdge,by simp;omega,?_⟩
  intro z hz
  change z∈(x :: l)++[y] at hz
  rcases List.mem_append.mp hz with hz|hz
  · exact hAvoid z hz
  · exact List.mem_singleton.mp hz ▸ hyZ

theorem exists_route_of_robust_growth (D : Digraph V) (Z : Finset V)
    (r r' t k : ℕ) (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hBudget : Z.card+r' ≤ r) (hGrowth : Fintype.card V < t+k*r')
    (x y : V) (hxZ : x∉Z) (hyZ : y∉Z)
    (hx : t+Z.card ≤ outDegree D x) (hy : t ≤ inDegree D y) :
    ∃ l,Route D x y l ∧ l.length ≤ k+2 ∧ ∀ z∈x :: l,z∉Z := by
  by_contra hn
  have hUpper : ∀ j,j ≤ k → (ball D Z x (j+1)).card+t ≤ Fintype.card V := by
    intro j hj
    by_contra hh
    obtain ⟨l,hRoute,hLen,hAvoid⟩ := exists_route_of_large_ball D Z x y t (j+1)
      hyZ hy (Nat.lt_of_not_ge hh)
    exact hn ⟨l,hRoute,by omega,hAvoid⟩
  have hLower : ∀ j,j ≤ k → t+j*r' ≤ (ball D Z x (j+1)).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have hh := outdegree_le_ball_one D Z x hxZ
      simp only [zero_mul,add_zero,zero_add]
      omega
    | succ j ih =>
      intro hj
      have hlo := ih (by omega)
      have hGrow := hRobust (ball D Z x (j+1)) (by omega) (hUpper j (by omega))
      have hSub := card_le_card (neighbourhood_subset_next D Z x (j+1) r (by omega))
      have hDelete := card_le_card_sdiff_add_card
        (s:=neighbourhood D r (ball D Z x (j+1))) (t:=Z)
      rw [Nat.succ_mul]
      omega
  have hlo := hLower k le_rfl
  have hBound := card_le_univ (ball D Z x (k+1))
  omega

/-- Actual simple directed path, represented by its source and tail.
Only the starting outdegree and terminal indegree are needed. -/
theorem exists_short_path_avoiding (D : Digraph V) (Z : Finset V)
    (r r' t : ℕ) (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hBudget : Z.card+r' ≤ r) (x y : V) (hxZ : x∉Z) (hyZ : y∉Z)
    (hx : t+Z.card ≤ outDegree D x) (hy : t ≤ inDegree D y) :
    ∃ l,Route D x y l ∧ (x :: l).Nodup ∧ l.length ≤ Fintype.card V/r'+3 ∧
      ∀ z∈x :: l,z∉Z := by
  have hDiv := Nat.lt_mul_div_succ (Fintype.card V) hr'
  obtain ⟨l,hRoute,hLen,hAvoid⟩ := exists_route_of_robust_growth D Z r r' t
    (Fintype.card V/r'+1) hRobust hr' hBudget (by nlinarith only [hDiv])
    x y hxZ hyZ hx hy
  obtain ⟨s,hs,hSimple,hLength,hSub⟩ := erase_loops D x y l hRoute
  exact ⟨s,hs,hSimple,by omega,fun z hz => hAvoid z (hSub z hz)⟩

end OverfullWork.DirectedRobustShortPaths
