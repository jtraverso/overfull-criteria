module

public import OverfullWork.KuhnOsthusIntervalConcatenation
public import OverfullWork.KuhnOsthusMarkedTours

@[expose] public section


/-! Close two complete interval covers around the whole cycle. The
orbit structure is the return permutation at the initial cluster. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedAbsorbingLadder DirectedSpanningConfiguration
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem intervalSlotPartition (A B S T : Finset V) (hAll : A ∪ B = univ)
    (hMeet : A ∩ B = S ∪ T) (hDis : Disjoint S T) (v : V) :
    (v ∈ A \ T ∨ v ∈ B \ S) ∧ ¬ (v ∈ A \ T ∧ v ∈ B \ S) := by
  have hS (hs : v ∈ S) : v ∈ A ∩ B := hMeet ▸ mem_union_left _ hs
  have hT (ht : v ∈ T) : v ∈ A ∩ B := hMeet ▸ mem_union_right _ ht
  have hCover : v ∈ A ∪ B := hAll ▸ mem_univ _
  refine ⟨?_,?_⟩
  · by_cases hs : v ∈ S
    · exact .inl (mem_sdiff.mpr ⟨(mem_inter.mp (hS hs)).1,fun ht => disjoint_left.mp hDis hs ht⟩)
    · by_cases ht : v ∈ T
      · exact .inr (mem_sdiff.mpr ⟨(mem_inter.mp (hT ht)).2,hs⟩)
      · exact (mem_union.mp hCover).imp (fun ha => mem_sdiff.mpr ⟨ha,ht⟩)
          (fun hb => mem_sdiff.mpr ⟨hb,hs⟩)
  · rintro ⟨h₁,h₂⟩
    obtain ⟨ha,ht⟩ := mem_sdiff.mp h₁
    obtain ⟨hb,hs⟩ := mem_sdiff.mp h₂
    exact (mem_union.mp (hMeet ▸ mem_inter.mpr ⟨ha,hb⟩)).elim hs ht

/-- The two covers give each vertex exactly one incoming and one
outgoing arc. Their union is a permutation factor on the whole graph. -/
theorem IntervalPathCover.exists_winding_factor {G : Digraph V} {A B S T : Finset V}
    (P : IntervalPathCover G A S T) (Q : IntervalPathCover G B T S)
    (hAll : A ∪ B = univ) (hMeet : A ∩ B = S ∪ T) (hDis : Disjoint S T) :
    ∃ σ : Equiv.Perm V, ∀ x y, (P.digraph ⊔ Q.digraph).Adj x y ↔ σ x = y := by
  have hOut (v : V) := intervalSlotPartition A B S T hAll hMeet hDis v
  have hIn (v : V) := intervalSlotPartition A B T S hAll (hMeet.trans (union_comm _ _)) hDis.symm v
  have out (x : V) : ∃ y, (P.digraph ⊔ Q.digraph).Adj x y := by
    rcases (hOut x).1 with h | h
    · obtain ⟨y,hy⟩ := (P.slots x).1.mpr h
      exact ⟨y,.inl hy⟩
    · obtain ⟨y,hy⟩ := (Q.slots x).1.mpr h
      exact ⟨y,.inr hy⟩
  have in' (y : V) : ∃ x, (P.digraph ⊔ Q.digraph).Adj x y := by
    rcases (hIn y).1 with h | h
    · obtain ⟨x,hx⟩ := (P.slots y).2.mpr h
      exact ⟨x,.inl hx⟩
    · obtain ⟨x,hx⟩ := (Q.slots y).2.mpr h
      exact ⟨x,.inr hx⟩
  have hSysP := P.is_path_system
  have hSysQ := Q.is_path_system
  have row {x y z : V} (h₁ : (P.digraph ⊔ Q.digraph).Adj x y)
      (h₂ : (P.digraph ⊔ Q.digraph).Adj x z) : y = z := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hSysP.out_unique h₁ h₂
    · exact ((hOut x).2 ⟨(P.slots x).1.mp ⟨_,h₁⟩,(Q.slots x).1.mp ⟨_,h₂⟩⟩).elim
    · exact ((hOut x).2 ⟨(P.slots x).1.mp ⟨_,h₂⟩,(Q.slots x).1.mp ⟨_,h₁⟩⟩).elim
    · exact hSysQ.out_unique h₁ h₂
  have col {x y z : V} (h₁ : (P.digraph ⊔ Q.digraph).Adj x z)
      (h₂ : (P.digraph ⊔ Q.digraph).Adj y z) : x = y := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hSysP.in_unique h₁ h₂
    · exact ((hIn z).2 ⟨(P.slots z).2.mp ⟨_,h₁⟩,(Q.slots z).2.mp ⟨_,h₂⟩⟩).elim
    · exact ((hIn z).2 ⟨(P.slots z).2.mp ⟨_,h₂⟩,(Q.slots z).2.mp ⟨_,h₁⟩⟩).elim
    · exact hSysQ.in_unique h₁ h₂
  choose succ hSucc using out
  let σ := Equiv.ofBijective succ ⟨
    fun x y he => col (hSucc x) (he.symm ▸ hSucc y),fun y => by
      obtain ⟨x,hx⟩ := in' y
      exact ⟨x,row (hSucc x) hx⟩⟩
  exact ⟨σ,fun x y => ⟨row (hSucc x),fun h => h ▸ hSucc x⟩⟩

omit [Fintype V] in
private theorem trace_word_step (L : List V) (i : ℕ) (hi : i+1 < L.length) :
    (wordGraph L).Adj (L[i]'(by omega)) (L[i+1]) := by
  apply List.infix_iff_getElem?.mpr
  refine ⟨i,by change 2+i ≤ L.length; omega,?_⟩
  intro j hj
  have h : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases h with rfl | rfl
  · simp only [Nat.zero_add,List.getElem?_eq_getElem (show i < L.length by omega)]
    rfl
  · rw [show 1+i=i+1 by omega,List.getElem?_eq_getElem hi]
    rfl

omit [Fintype V] in
private theorem trace_factor_path {G : Digraph V} (p : PathRequest G) (σ : Equiv.Perm V)
    (hP : ∀ x y, (wordGraph p.vertices).Adj x y → σ x = y) (i : ℕ) (hi : i < p.vertices.length) :
    (σ : V → V)^[i] p.source = p.vertices[i] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [iterate_succ_apply',ih (by omega)]
    exact hP _ _ (trace_word_step _ i hi)

omit [Fintype V] in
private theorem trace_factor_path_end {G : Digraph V} (p : PathRequest G) (σ : Equiv.Perm V)
    (hP : ∀ x y, (wordGraph p.vertices).Adj x y → σ x = y) :
    (σ : V → V)^[p.tail.length] p.source = p.target := by
  have hLast := p.route.2
  change p.vertices.getLast? = some p.target at hLast
  rw [List.getLast?_eq_getElem?] at hLast
  have hn : p.vertices.length - 1 = p.tail.length := by simp [PathRequest.vertices]
  rw [hn,List.getElem?_eq_getElem (by simp [PathRequest.vertices])] at hLast
  exact (trace_factor_path p σ hP _ (by simp [PathRequest.vertices])).trans (Option.some.inj hLast)

/-- The return map through the two interval covers records the exact
cycle structure of their union at the initial boundary. -/
theorem IntervalPathCover.exists_winding_factor_with_return {G : Digraph V} {A B S T : Finset V}
    (P : IntervalPathCover G A S T) (Q : IntervalPathCover G B T S)
    (hAll : A ∪ B = univ) (hMeet : A ∩ B = S ∪ T) (hDis : Disjoint S T) :
    ∃ σ : Equiv.Perm V,
      (∀ x y, (P.digraph ⊔ Q.digraph).Adj x y ↔ σ x = y) ∧
      Nonempty (MarkedCycleSegments σ (Embedding.subtype (· ∈ S)) (Q.starts.trans P.starts).symm) := by
  obtain ⟨σ,hσ⟩ := P.exists_winding_factor Q hAll hMeet hDis
  let e := (Q.starts.trans P.starts).symm
  let p (s : S) := P.path (P.starts.symm s)
  let q (s : S) := Q.path (e s)
  have hP (s : S) (x y : V) (h : (wordGraph (p s).vertices).Adj x y) : σ x = y :=
    (hσ x y).mp (.inl (Digraph.iSup_adj.mpr ⟨P.starts.symm s,h⟩))
  have hQ (s : S) (x y : V) (h : (wordGraph (q s).vertices).Adj x y) : σ x = y :=
    (hσ x y).mp (.inr (Digraph.iSup_adj.mpr ⟨e s,h⟩))
  have hStart (s : S) : (p s).source = s.val := by
    have h := (P.ends (P.starts.symm s)).1
    rwa [P.starts.apply_symm_apply] at h
  have hMid (s : S) : (q s).source = (p s).target := by
    change (Q.path (Q.starts.symm (P.starts.symm s))).source = _
    exact ((Q.ends _).1.trans (congrArg Subtype.val (Q.starts.apply_symm_apply _))).trans
      (P.ends _).2.symm
  have hEnd (s : S) : (q s).target = (e s).val := (Q.ends _).2
  have hQpos (s : S) : 0 < (q s).tail.length := by
    by_contra! h
    have hNil : (q s).tail = [] := List.length_eq_zero_iff.mp (by omega)
    have he := (q s).route.2
    rw [hNil] at he
    have hEq : (q s).source = (q s).target := Option.some.inj he
    have hs : (q s).source ∈ T := (Q.ends (e s)).1.symm ▸ (Q.starts (e s)).prop
    have ht : (q s).target ∈ S := (hEnd s).symm ▸ (e s).prop
    exact disjoint_left.mp hDis ht (hEq ▸ hs)
  let len (s : S) := (p s).tail.length+(q s).tail.length
  have hBefore (s : S) (i : ℕ) (hi : i < (p s).vertices.length) :
      (σ : V → V)^[i] s.val = (p s).vertices[i] := by
    rw [← hStart s]
    exact trace_factor_path _ _ (hP s) i hi
  have hAfterStart (s : S) : (σ : V → V)^[(p s).tail.length] s.val = (q s).source := by
    rw [← hStart s,hMid s]
    exact trace_factor_path_end _ _ (hP s)
  have hAfter (s : S) (i : ℕ) (hi : i < (q s).vertices.length) :
      (σ : V → V)^[(p s).tail.length+i] s.val = (q s).vertices[i] := by
    rw [Nat.add_comm,iterate_add_apply,hAfterStart]
    exact trace_factor_path _ _ (hQ s) i hi
  refine ⟨σ,hσ,⟨len,fun s => Nat.add_pos_right _ (hQpos s),?_,?_,?_⟩⟩
  · intro s
    change (σ : V → V)^[(p s).tail.length+(q s).tail.length] s.val = (e s).val
    rw [Nat.add_comm,iterate_add_apply,hAfterStart,trace_factor_path_end _ _ (hQ s),hEnd]
  · intro s i hi hir t
    change (σ : V → V)^[i] s.val ≠ t.val
    by_cases h : i ≤ (p s).tail.length
    · have hLen : (p s).vertices.length = (p s).tail.length+1 := rfl
      have hi' : i < (p s).vertices.length := by omega
      rw [hBefore s i hi']
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
      have hEdge := trace_word_step (p s).vertices k hi'
      have hm := (P.slots ((p s).vertices[k+1])).2.mp ⟨_,Digraph.iSup_adj.mpr ⟨_,hEdge⟩⟩
      exact fun he => (mem_sdiff.mp hm).2 (he.symm ▸ t.prop)
    · let j := i-(p s).tail.length
      have he : i = (p s).tail.length+j := by dsimp [j]; omega
      have hLen : (q s).vertices.length = (q s).tail.length+1 := rfl
      have hj : j+1 < (q s).vertices.length := by dsimp [j,len] at *; omega
      rw [he,hAfter s j (by omega)]
      have hEdge := trace_word_step (q s).vertices j hj
      have hm := (Q.slots ((q s).vertices[j])).1.mp ⟨_,Digraph.iSup_adj.mpr ⟨_,hEdge⟩⟩
      exact fun he => (mem_sdiff.mp hm).2 (he.symm ▸ t.prop)
  · intro v
    have hv : v ∈ A ∪ B := hAll ▸ mem_univ _
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨t,ht⟩ := (P.spans v).mp hv
      let s := P.starts t
      have hp : p s = P.path t := by simp [p,s]
      rw [←hp] at ht
      obtain ⟨i,hi,hv⟩ := List.mem_iff_getElem.mp ht
      have hLen : (p s).vertices.length = (p s).tail.length+1 := rfl
      refine ⟨s,i,?_,(hBefore s i hi).trans hv⟩
      have := hQpos s
      dsimp [len]
      omega
    · obtain ⟨s,hs⟩ := (Q.spans v).mp hv
      let t := e.symm s
      have hq : q t = Q.path s := by simp [q,t]
      rw [←hq] at hs
      obtain ⟨i,hi,hv⟩ := List.mem_iff_getElem.mp hs
      have hLen : (q t).vertices.length = (q t).tail.length+1 := rfl
      by_cases h : i < (q t).tail.length
      · exact ⟨t,(p t).tail.length+i,Nat.add_lt_add_left h _,(hAfter t i hi).trans hv⟩
      · have he : i = (q t).tail.length := by omega
        subst i
        have hv' : (e t).val = v := by
          have hEndTrace := trace_factor_path_end (q t) σ (hQ t)
          have hVertex := trace_factor_path (q t) σ (hQ t) _ hi
          rw [hEndTrace,hEnd] at hVertex
          exact hVertex.trans hv
        exact ⟨e t,0,Nat.add_pos_right _ (hQpos (e t)),hv'⟩

end OverfullWork.DirectedRobustExpansion
