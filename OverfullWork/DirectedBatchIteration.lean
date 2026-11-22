module

public import OverfullWork.DirectedBatchMerge
public import OverfullWork.DirectedBatchResidual

@[expose] public section


/-! The outer induction over disjoint batches. Fresh realizations are made
in the actual residual host, and the reserve losses telescope. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion
open scoped Classical
variable {V I J K : Type*} [Fintype V] [Fintype K]

private theorem disjoint_semidegree_union (A B : Digraph V) (h : Disjoint A B) (v : V) :
    inDegree (A ⊔ B) v = inDegree A v+inDegree B v ∧
    outDegree (A ⊔ B) v = outDegree A v+outDegree B v := by
  let F : Bool → Digraph V := fun i => if i then B else A
  have he : (⨆ i, F i) = A ⊔ B := by
    ext x y
    rw [Digraph.iSup_adj,Digraph.sup_adj]
    constructor
    · rintro ⟨i,hi⟩
      cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hA | hB)
      · exact ⟨false,hA⟩
      · exact ⟨true,hB⟩
  have hd : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j he
    cases i <;> cases j
    · exact (he rfl).elim
    · exact h
    · exact h.symm
    · exact (he rfl).elim
  have hi := inDegree_iSup_of_disjoint F hd v
  have ho := outDegree_iSup_of_disjoint F hd v
  rw [he] at hi ho
  exact ⟨by simpa [F,Nat.add_comm] using hi,by simpa [F,Nat.add_comm] using ho⟩

/-- Execute a disjoint family of batches and return the actual packing
and robust reserve remainder. The next-batch premise is stated on every
processed prefix with its exact cumulative reserve budget. -/
theorem exists_batch_iteration_with_prefix_budget [Fintype J] (D Γ : Digraph V) (L : J → Layout V I)
    (group : K → Finset J) (budget : Finset K → ℕ) (hEmptyBudget : budget ∅ = 0) (hGroups : Pairwise (fun i j => Disjoint (group i) (group j)))
    (hCover : (univ : Finset K).biUnion group = (univ : Finset J))
    (ν τ ν' : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (hRobust : IsRealRobust Γ ν τ)
    (hBudget : ν'*(Fintype.card V:ℝ)+(budget (univ : Finset K):ℝ) ≤ ν*(Fintype.card V:ℝ))
    (hNext : ∀ (S : Finset K) (i : K), i ∉ S →
      ∀ P : PackingPrefix (D ⊔ Γ) L (S.biUnion group),
      (∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ budget S) →
      ∃ Q : PackingPrefix ((D ⊔ Γ) \ P.used) L (group i),
        ∀ v, inDegree (Q.used ⊓ (Γ \ P.used)) v+
          outDegree (Q.used ⊓ (Γ \ P.used)) v + budget S ≤ budget (insert i S)) :
    ∃ P : PackingPrefix (D ⊔ Γ) L (univ : Finset J),
      (∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ budget univ) ∧
      IsRealRobust (Γ \ P.used) ν' τ := by
  have hPartial (S : Finset K) : ∃ P : PackingPrefix (D ⊔ Γ) L (S.biUnion group),
      ∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ budget S := by
    induction S using Finset.induction_on with
    | empty =>
      rw [biUnion_empty]
      let P := PackingPrefix.empty (D ⊔ Γ) L
      have hEmpty : P.used ⊓ Γ = ⊥ := by
        ext x y
        simp only [Digraph.inf_adj,Digraph.bot_adj]
        refine ⟨fun h => ?_,False.elim⟩
        obtain ⟨i,_⟩ := Digraph.iSup_adj.mp h.1
        exact notMem_empty i.val i.prop
      refine ⟨P,fun v => ?_⟩
      rw [hEmpty,hEmptyBudget]
      simp [inDegree,inNeighbours,outDegree,Digraph.bot_adj]
    | @insert i S hi ih =>
      obtain ⟨P,hP⟩ := ih
      obtain ⟨Q,hQ⟩ := hNext S i hi P hP
      have hDis : Disjoint (S.biUnion group) (group i) := by
        apply disjoint_left.mpr
        intro x hx hxi
        obtain ⟨j,hj,hxj⟩ := mem_biUnion.mp hx
        exact disjoint_left.mp (hGroups (ne_of_mem_of_not_mem hj hi)) hxj hxi
      have hSets : (insert i S).biUnion group = (S.biUnion group) ∪ group i := by
        rw [biUnion_insert,union_comm]
      rw [hSets]
      refine ⟨P.merge Q,fun v => ?_⟩
      rw [P.used_merge Q hDis]
      have hSplit : (P.used ⊔ Q.used) ⊓ Γ = (P.used ⊓ Γ) ⊔ (Q.used ⊓ (Γ \ P.used)) := by
        ext x y
        have hq : Q.used.Adj x y → ¬P.used.Adj x y := fun h => (Q.used_le h).2
        simp only [Digraph.inf_adj,Digraph.sup_adj,Digraph.sdiff_adj]
        tauto
      have hArc : Disjoint (P.used ⊓ Γ) (Q.used ⊓ (Γ \ P.used)) := by
        apply disjoint_iff_inf_le.mpr
        intro x y h
        exact h.2.2.2 h.1.1
      rw [hSplit]
      obtain ⟨hIn,hOut⟩ := disjoint_semidegree_union _ _ hArc v
      have hp := hP v
      have hq := hQ v
      omega
  have hWhole := hPartial univ
  rw [hCover] at hWhole
  obtain ⟨P,hP⟩ := hWhole
  have hDiff : Γ \ (P.used ⊓ Γ) = Γ \ P.used := by
    ext x y
    simp only [Digraph.sdiff_adj,Digraph.inf_adj]
    tauto
  refine ⟨P,hP,?_⟩
  rw [← hDiff]
  exact real_robust_after_reserve_use Γ (P.used ⊓ Γ) ν τ ν' _ hν hτ hRobust
    (fun v => (Nat.le_add_right _ _).trans (hP v)) hBudget

theorem exists_batch_iteration [Fintype J] (D Γ : Digraph V) (L : J → Layout V I)
    (group : K → Finset J) (cost : K → ℕ) (hGroups : Pairwise (fun i j => Disjoint (group i) (group j)))
    (hCover : (univ : Finset K).biUnion group = (univ : Finset J))
    (ν τ ν' : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (hRobust : IsRealRobust Γ ν τ)
    (hBudget : ν'*(Fintype.card V:ℝ)+((∑ j, cost j:ℕ):ℝ) ≤ ν*(Fintype.card V:ℝ))
    (hNext : ∀ (S : Finset K) (i : K), i ∉ S →
      ∀ P : PackingPrefix (D ⊔ Γ) L (S.biUnion group),
      (∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ ∑ j ∈ S,cost j) →
      ∃ Q : PackingPrefix ((D ⊔ Γ) \ P.used) L (group i),
        ∀ v, inDegree (Q.used ⊓ (Γ \ P.used)) v+
          outDegree (Q.used ⊓ (Γ \ P.used)) v ≤ cost i) :
    ∃ P : PackingPrefix (D ⊔ Γ) L (univ : Finset J),
      (∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ ∑ j,cost j) ∧
      IsRealRobust (Γ \ P.used) ν' τ := by
  apply exists_batch_iteration_with_prefix_budget D Γ L group (fun S => ∑ j ∈ S,cost j)
    (by simp) hGroups hCover ν τ ν' hν hτ hRobust hBudget
  intro S i hi P hP
  obtain ⟨Q,hQ⟩ := hNext S i hi P hP
  refine ⟨Q,fun v => ?_⟩
  rw [sum_insert hi]
  have := hQ v
  omega

/-- The dense center drops by exactly the number of packed layouts.
The deviations are paid for by the boundary load and reserve budget.
The reserve center does not drop and its deviation grows by at most the
same reserve budget. These are the profiles used when resampling. -/
theorem PackingPrefix.residual_degree_deviations [Fintype I]
    {D Γ : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix (D ⊔ Γ) L S) (hDis : Disjoint D Γ)
    (a b g : ℕ) (d γ eD eΓ : ℝ)
    (hAppearance : ∀ v, DirectedReserveUsage.visits (fun j : S => (L j.val).boundary) v ≤ a)
    (hEndpoint : ∀ v s, (∑ j : S, (L j.val).endpointLoad s v) ≤ b)
    (hReserve : ∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ g)
    (hDense : ∀ v, |(inDegree D v:ℝ)-d| ≤ eD ∧ |(outDegree D v:ℝ)-d| ≤ eD)
    (hΓ : ∀ v, |(inDegree Γ v:ℝ)-γ| ≤ eΓ ∧ |(outDegree Γ v:ℝ)-γ| ≤ eΓ) :
    ∀ v, |(inDegree (D \ P.used) v:ℝ)-(d-(S.card:ℝ))| ≤ eD+(max b (a+g):ℕ) ∧
      |(outDegree (D \ P.used) v:ℝ)-(d-(S.card:ℝ))| ≤ eD+(max b (a+g):ℕ) ∧
      |(inDegree (Γ \ P.used) v:ℝ)-γ| ≤ eΓ+(g:ℝ) ∧
      |(outDegree (Γ \ P.used) v:ℝ)-γ| ≤ eΓ+(g:ℝ) := by
  intro v
  have hG := hReserve v
  have hGin : inDegree (P.used ⊓ Γ) v ≤ g := (Nat.le_add_right _ _).trans hG
  have hGout : outDegree (P.used ⊓ Γ) v ≤ g := (Nat.le_add_left _ _).trans hG
  have hUse := semidegrees_batch_used (D ⊔ Γ) (fun j : S => L j.val) P.round P.disjoint v
    a b (hAppearance v) (hEndpoint v)
  change Fintype.card S ≤ inDegree P.used v+a ∧ inDegree P.used v ≤ Fintype.card S+b ∧
    Fintype.card S ≤ outDegree P.used v+a ∧ outDegree P.used v ≤ Fintype.card S+b at hUse
  rw [Fintype.card_coe] at hUse
  have hNew := dense_semidegrees_after_batch D Γ P.used hDis P.used_le v S.card a b g
    ⟨hUse.1,hUse.2.1⟩ ⟨hUse.2.2.1,hUse.2.2.2⟩ hGin hGout
  have hb : (b:ℝ) ≤ (max b (a+g):ℕ) := by exact_mod_cast le_max_left b (a+g)
  have hag : (a:ℝ)+(g:ℝ) ≤ (max b (a+g):ℕ) := by exact_mod_cast le_max_right b (a+g)
  have dense (x y : ℕ) (h₁ : x ≤ y+S.card+b) (h₂ : y+S.card ≤ x+a+g)
      (h : |(x:ℝ)-d| ≤ eD) :
      |(y:ℝ)-(d-(S.card:ℝ))| ≤ eD+(max b (a+g):ℕ) := by
    obtain ⟨hL,hU⟩ := abs_le.mp h
    have hL' : (x:ℝ) ≤ (y:ℝ)+(S.card:ℝ)+(b:ℝ) := by exact_mod_cast h₁
    have hU' : (y:ℝ)+(S.card:ℝ) ≤ (x:ℝ)+(a:ℝ)+(g:ℝ) := by exact_mod_cast h₂
    exact abs_le.mpr ⟨by linarith only [hL,hL',hb],by linarith only [hU,hU',hag]⟩
  have hDiff : Γ \ (P.used ⊓ Γ) = Γ \ P.used := by
    ext x y
    simp only [Digraph.sdiff_adj,Digraph.inf_adj]
    tauto
  have hi := inDegree_sdiff_add_of_le Γ (P.used ⊓ Γ) inf_le_right v
  have ho := outDegree_sdiff_add_of_le Γ (P.used ⊓ Γ) inf_le_right v
  rw [hDiff] at hi ho
  have reserve (x y u : ℕ) (he : y+u = x) (hu : u ≤ g)
      (h : |(x:ℝ)-γ| ≤ eΓ) : |(y:ℝ)-γ| ≤ eΓ+(g:ℝ) := by
    obtain ⟨hL,hU⟩ := abs_le.mp h
    have he' : (y:ℝ)+(u:ℝ) = (x:ℝ) := by exact_mod_cast he
    have hG : (u:ℝ) ≤ (g:ℝ) := by exact_mod_cast hu
    have hU' : 0 ≤ (u:ℝ) := Nat.cast_nonneg _
    have hg : 0 ≤ (g:ℝ) := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith only [hL,he',hG],by linarith only [hU,he',hU',hg]⟩
  exact ⟨dense _ _ hNew.1 hNew.2.1 (hDense v).1,
    dense _ _ hNew.2.2.1 hNew.2.2.2 (hDense v).2,
    reserve _ _ _ hi hGin (hΓ v).1,reserve _ _ _ ho hGout (hΓ v).2⟩

end OverfullWork.DirectedSpanningConfiguration
