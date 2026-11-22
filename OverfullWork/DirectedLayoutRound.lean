module

public import OverfullWork.DirectedLayoutShortPaths
public import OverfullWork.DirectedSpanningConfiguration

@[expose] public section


/-! Assemble one spanning configuration from its short and long portions.
The fixed arcs are retained as individual copies. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedListRoutes
open scoped Classical
variable {V I : Type*}

/-- The short portion has one route for each flexible occurrence except
the distinguished one. Its interiors avoid the layout and are disjoint. -/
structure ShortPortion (D : Digraph V) (L : Layout V I) (long : I) where
  interior : I → List V
  nonempty : ∀ i ∉ insert long L.fixed, interior i ≠ []
  simple : ∀ i ∉ insert long L.fixed, (L.source i :: interior i ++ [L.target i]).Nodup
  chain : ∀ i ∉ insert long L.fixed, (L.source i :: interior i ++ [L.target i]).IsChain D.Adj
  outside : ∀ i ∉ insert long L.fixed, ∀ x ∈ interior i, x ∉ L.boundary
  disjoint : ∀ i ∉ insert long L.fixed, ∀ j ∉ insert long L.fixed,
    i ≠ j → List.Disjoint (interior i) (interior j)

def ShortPortion.remaining {D : Digraph V} {L : Layout V I} {long : I}
    (S : ShortPortion D L long) (x : V) : Prop :=
  x ∉ L.boundary ∧ ∀ i ∉ insert long L.fixed, x ∉ S.interior i

/-- Realize the short portion in the unused reserve outside the assigned
block and the saturated set. -/
theorem exists_shortPortion [Fintype V] [Fintype I] (D : Digraph V) (L : Layout V I) (long : I)
    (Z : Finset V) {r s t h : ℕ} (hRobust : IsRobustAt D r t) (hs : 0 < s)
    (hLen : Fintype.card V/s+5 ≤ h) (hZ : Disjoint L.boundary Z)
    (hBudget : Z.card+L.boundary.card+(univ \ insert long L.fixed).card*h+s ≤ r)
    (hIn : ∀ v, t ≤ inDegree D v)
    (hOut : ∀ v, t+Z.card+L.boundary.card+(univ \ insert long L.fixed).card*h+1 ≤
      outDegree D v) :
    ∃ S : ShortPortion D L long, ∀ i ∉ insert long L.fixed,
      (S.interior i).length ≤ h ∧ ∀ x ∈ S.interior i, x ∉ Z := by
  let J := (univ : Finset I) \ insert long L.fixed
  have hJ (i : I) : i ∈ J ↔ i ∉ insert long L.fixed := by simp [J]
  obtain ⟨f,hRoute,hDis⟩ := DirectedLayoutShortPaths.exists_shared_endpoint_paths D
    hRobust hs hLen L.boundary L.source L.target L.ends hIn J Z hZ hBudget hOut
  have hDecompose (i : I) (hi : i ∉ insert long L.fixed) :
      ∃ l : List V, f i = l ++ [L.target i] := by
    obtain ⟨hr,_,hlen,_⟩ := hRoute i ((hJ i).2 hi)
    have hn : f i ≠ [] := by
      intro he
      simp [he] at hlen
    have hLast := hr.2
    rw [List.getLast?_cons_of_ne_nil hn] at hLast
    exact List.getLast?_eq_some_iff.mp hLast
  let l (i : I) : List V := if hi : i ∉ insert long L.fixed then
    (hDecompose i hi).choose else []
  have hEq i (hi : i ∉ insert long L.fixed) : f i = l i ++ [L.target i] := by
    simpa only [l,dif_pos hi] using (hDecompose i hi).choose_spec
  have hMem (i : I) (hi : i ∉ insert long L.fixed) (x : V) (hx : x ∈ l i) :
      x ∈ L.source i :: f i := by rw [hEq i hi]; simp [hx]
  have hAvoid (i : I) (hi : i ∉ insert long L.fixed) (x : V) (hx : x ∈ l i) :
      x ∉ Z ∧ x ∉ L.boundary := by
    obtain ⟨_,hND,_,_,hA⟩ := hRoute i ((hJ i).2 hi)
    have hA' := hA x (hMem i hi x hx)
    refine ⟨hA'.1,?_⟩
    intro hb
    rw [hEq i hi] at hND
    rcases hA'.2 hb with rfl | he
    · exact (List.nodup_cons.mp hND).1 (List.mem_append_left _ hx)
    · exact (List.nodup_append.mp (List.nodup_cons.mp hND).2).2.2 x hx
        (L.target i) List.mem_cons_self he
  refine ⟨⟨l,?_,?_,?_,?_,?_⟩,?_⟩
  · intro i hi he
    have hMin := (hRoute i ((hJ i).2 hi)).2.2.1
    simp [hEq i hi,he] at hMin
  · intro i hi
    simpa only [hEq i hi,List.cons_append] using (hRoute i ((hJ i).2 hi)).2.1
  · intro i hi
    simpa only [hEq i hi,List.cons_append] using (hRoute i ((hJ i).2 hi)).1.1
  · exact fun i hi x hx => (hAvoid i hi x hx).2
  · intro i hi j hj he x hx hy
    exact hDis i ((hJ i).2 hi) j ((hJ j).2 hj) he x (hAvoid i hi x hx).2
      (hMem i hi x hx) (hMem j hj x hy)
  · intro i hi
    have hL := (hRoute i ((hJ i).2 hi)).2.2.2.1
    rw [hEq i hi,List.length_cons,List.length_append] at hL
    change (l i).length ≤ h ∧ ∀ x ∈ l i, x ∉ Z
    exact ⟨by omega,fun x hx => (hAvoid i hi x hx).1⟩

/-- Complete the spanning configuration with a long path through exactly
the vertices left over by the short portion. Fixed indices use their own
copies. Each flexible path retains its original choice of host. -/
theorem complete_round {D E : Digraph V} {L : Layout V I} {long : I}
    (hlong : long ∉ L.fixed) (S : ShortPortion D L long)
    (l : List V) (hNonempty : l ≠ [])
    (hSimple : (L.source long :: l ++ [L.target long]).Nodup)
    (hChain : (L.source long :: l ++ [L.target long]).IsChain E.Adj)
    (hSpan : ∀ x, x ∈ l ↔ S.remaining x) :
    ∃ R : Realization (D ⊔ E) L, R.interior long = l ∧
      (∀ i ∉ insert long L.fixed, R.interior i = S.interior i) ∧
      wordGraph (R.word long) ≤ E ∧
      ∀ i ∉ insert long L.fixed, wordGraph (R.word i) ≤ D := by
  let f : I → List V := fun i => if i = long then l else
    if i ∈ L.fixed then [] else S.interior i
  have hLong : f long = l := if_pos rfl
  have hFixed (i) (hi : i ∈ L.fixed) : f i = [] := by
    have hi' : i ≠ long := fun he => hlong (he ▸ hi)
    simp [f,hi,hi']
  have hShort (i) (hi : i ∉ insert long L.fixed) : f i = S.interior i := by
    have h := not_or.mp (Finset.mem_insert.not.mp hi)
    simp [f,h.1,h.2]
  have hOutside (i x) (hx : x ∈ f i) : x ∉ L.boundary := by
    by_cases hi : i = long
    · subst i
      rw [hLong] at hx
      exact ((hSpan x).1 hx).1
    · by_cases hf : i ∈ L.fixed
      · simp [hFixed i hf] at hx
      · have h : i ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim hi hf
        rw [hShort i h] at hx
        exact S.outside i h x hx
  have hDistinct i j (he : i ≠ j) : List.Disjoint (f i) (f j) := by
    intro x hi hj
    by_cases hfi : i ∈ L.fixed
    · simp [hFixed i hfi] at hi
    by_cases hfj : j ∈ L.fixed
    · simp [hFixed j hfj] at hj
    by_cases hil : i = long
    · subst i
      have hj' : j ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim he.symm hfj
      rw [hLong] at hi
      rw [hShort j hj'] at hj
      exact ((hSpan x).1 hi).2 j hj' hj
    by_cases hjl : j = long
    · subst j
      have hi' : i ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim he hfi
      rw [hLong] at hj
      rw [hShort i hi'] at hi
      exact ((hSpan x).1 hj).2 i hi' hi
    have hi' : i ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim hil hfi
    have hj' : j ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim hjl hfj
    exact S.disjoint i hi' j hj' he (hShort i hi' ▸ hi) (hShort j hj' ▸ hj)
  let R : Realization (D ⊔ E) L :=
    ⟨f,?_,hFixed,?_,?_,hOutside,hDistinct,?_⟩
  · refine ⟨R,hLong,hShort,?_,?_⟩
    · apply wordGraph_le
      simpa only [Realization.word,R,hLong] using hChain
    · intro i hi
      apply wordGraph_le
      simpa only [Realization.word,R,hShort i hi] using S.chain i hi
  · intro i
    by_cases he : i = long
    · subst i
      simpa [hLong] using hSimple
    · by_cases hi : i ∈ L.fixed
      · simp [hFixed i hi,(L.ends i).2.2]
      · have hi' : i ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim he hi
        simpa only [hShort i hi'] using S.simple i hi'
  · intro i hi
    by_cases he : i = long
    · subst i
      simpa only [hLong] using hNonempty
    · have hi' : i ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim he hi
      simpa only [hShort i hi'] using S.nonempty i hi'
  · intro i hi
    by_cases he : i = long
    · subst i
      rw [hLong]
      exact hChain.imp (fun _ _ h => Or.inr h)
    · have hi' : i ∉ insert long L.fixed := fun hm => (mem_insert.mp hm).elim he hi
      rw [hShort i hi']
      exact (S.chain i hi').imp (fun _ _ h => Or.inl h)
  · intro x hx
    by_cases hs : S.remaining x
    · exact ⟨long,hLong ▸ (hSpan x).2 hs⟩
    · have he : ∃ i ∉ insert long L.fixed, x ∈ S.interior i := by
        by_contra! he
        exact hs ⟨hx,he⟩
      obtain ⟨i,hi,hm⟩ := he
      exact ⟨i,hShort i hi ▸ hm⟩

end OverfullWork.DirectedSpanningConfiguration
