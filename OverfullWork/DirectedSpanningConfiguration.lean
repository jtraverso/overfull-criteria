module

public import OverfullWork.DirectedListRoutes

@[expose] public section


/-! The output of GGKLO Lemma 7.3, with individual copies of fixed arcs. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion
open scoped Classical
universe u v
variable {V : Type u} {I : Type v}

/-- The indices distinguish layout edge occurrences even for equal ordered
endpoint pairs. The boundary also includes the isolated layout vertices. -/
structure Layout (V : Type u) (I : Type v) where
  boundary : Finset V
  source : I → V
  target : I → V
  fixed : Finset I
  ends : ∀ i, source i ∈ boundary ∧ target i ∈ boundary ∧ source i ≠ target i

/-- Successive ordered pairs of a word form a digraph. -/
def wordGraph (l : List V) : Digraph V where
  Adj x y := List.IsInfix [x,y] l

theorem wordGraph_le {l : List V} {D : Digraph V} (h : l.IsChain D.Adj) :
    wordGraph l ≤ D := by
  intro x y hxy
  exact (h.infix hxy).rel

/-- Each interior is outside the layout and each vertex outside the layout
belongs to exactly one interior. Fixed edge occurrences have empty interiors.
Flexible paths are built in the host digraph and have a nonempty interior. -/
structure Realization (D : Digraph V) (L : Layout V I) where
  interior : I → List V
  simple : ∀ i, (L.source i :: interior i ++ [L.target i]).Nodup
  fixed_empty : ∀ i ∈ L.fixed, interior i = []
  flexible_nonempty : ∀ i ∉ L.fixed, interior i ≠ []
  flexible_chain : ∀ i ∉ L.fixed, (L.source i :: interior i ++ [L.target i]).IsChain D.Adj
  outside : ∀ i x, x ∈ interior i → x ∉ L.boundary
  unique : ∀ i j, i ≠ j → List.Disjoint (interior i) (interior j)
  spans : ∀ x, x ∉ L.boundary → ∃ i, x ∈ interior i

/-- Regard the same paths as paths in a larger host, preserving all edge
and vertex occurrences. -/
def Realization.rehost {D E : Digraph V} {L : Layout V I} (R : Realization D L)
    (h : D ≤ E) : Realization E L :=
  ⟨R.interior,R.simple,R.fixed_empty,R.flexible_nonempty,
    fun i hi => (R.flexible_chain i hi).imp (fun _ _ he => h he),
    R.outside,R.unique,R.spans⟩

def Realization.word {D : Digraph V} {L : Layout V I} (R : Realization D L) (i : I) : List V :=
  L.source i :: R.interior i ++ [L.target i]

def Realization.used {D : Digraph V} {L : Layout V I} (R : Realization D L) : Digraph V :=
  ⨆ i : {i // i ∉ L.fixed}, wordGraph (R.word i.val)

theorem Realization.used_le {D : Digraph V} {L : Layout V I} (R : Realization D L) :
    R.used ≤ D :=
  iSup_le fun i => wordGraph_le (R.flexible_chain i.val i.prop)

private theorem isInfix_cons_cases {l : List V} {x y a : V} (h : List.IsInfix [x,y] (a :: l)) :
    (x = a ∧ l.head? = some y) ∨ List.IsInfix [x,y] l := by
  obtain ⟨p,q,h⟩ := h
  cases p with
  | nil =>
    have he : x :: y :: q = a :: l := h
    cases he
    exact Or.inl ⟨rfl,rfl⟩
  | cons p ps =>
    have he : p :: (ps ++ [x,y] ++ q) = a :: l := h
    exact Or.inr ⟨ps,q,(List.cons.inj he).2⟩

private theorem right_unique (l : List V) (hND : l.Nodup) (x y z : V)
    (hy : (wordGraph l).Adj x y) (hz : (wordGraph l).Adj x z) : y = z := by
  induction l with
  | nil => exact (List.not_mem_nil (hy.mem (by simp : x ∈ [x,y]))).elim
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hND
    rcases isInfix_cons_cases hy with ⟨hxa,hsy⟩ | hty
    · rcases isInfix_cons_cases hz with ⟨_,hsz⟩ | htz
      · exact Option.some.inj (hsy.symm.trans hsz)
      · exact (ha (hxa ▸ htz.mem (by simp : x ∈ [x,z]))).elim
    · rcases isInfix_cons_cases hz with ⟨hxa,_⟩ | htz
      · exact (ha (hxa ▸ hty.mem (by simp : x ∈ [x,y]))).elim
      · exact ih hl hty htz

private theorem exists_successor_iff (p : List V) (b x : V) :
    (∃ y, (wordGraph (p ++ [b])).Adj x y) ↔ x ∈ p := by
  induction p with
  | nil =>
    have hNone (y : V) (h : (wordGraph [b]).Adj x y) : False := by
      have hn := h.length_le
      simp at hn
    exact ⟨fun ⟨y,hy⟩ => (hNone y hy).elim,fun h => (List.not_mem_nil h).elim⟩
  | cons a p ih =>
    constructor
    · rintro ⟨y,hy⟩
      rcases isInfix_cons_cases hy with ⟨rfl,_⟩ | hy
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.mp ⟨y,hy⟩)
    · intro h
      rcases List.mem_cons.mp h with rfl | hp
      · cases p with
        | nil => exact ⟨b,⟨[],[],by simp⟩⟩
        | cons y p => exact ⟨y,⟨[],p ++ [b],rfl⟩⟩
      · obtain ⟨y,hy⟩ := ih.mpr hp
        obtain ⟨s,t,he⟩ := hy
        exact ⟨y,⟨a::s,t,congrArg (List.cons a) he⟩⟩

/-- The terminal vertex is excluded from the set of outgoing endpoints. -/
theorem word_outDegree [Fintype V] (p : List V) (b x : V) (h : (p ++ [b]).Nodup) :
    outDegree (wordGraph (p ++ [b])) x = if x ∈ p then 1 else 0 := by
  by_cases hx : x ∈ p
  · simp only [if_pos hx]
    obtain ⟨y,hy⟩ := (exists_successor_iff p b x).mpr hx
    apply card_eq_one_iff_existsUnique.mpr
    exact ⟨y,mem_filter.mpr ⟨mem_univ _,hy⟩,fun z hz =>
      right_unique _ h _ _ _ (mem_filter.mp hz).2 hy⟩
  · simp only [if_neg hx]
    apply card_eq_zero.mpr
    exact eq_empty_iff_forall_notMem.mpr fun y hy =>
      hx ((exists_successor_iff p b x).mp ⟨y,(mem_filter.mp hy).2⟩)

/-- The initial vertex is excluded from the set of incoming endpoints. -/
theorem word_inDegree [Fintype V] (p : List V) (a x : V) (h : (a :: p).Nodup) :
    inDegree (wordGraph (a :: p)) x = if x ∈ p then 1 else 0 := by
  have hh : inDegree (wordGraph (a :: p)) x =
      outDegree (wordGraph ((a :: p).reverse)) x := by
    unfold inDegree inNeighbours outDegree
    congr 1
    ext y
    simp only [mem_filter,mem_univ,true_and]
    change List.IsInfix [y,x] (a :: p) ↔ List.IsInfix [x,y] (a :: p).reverse
    simpa only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] using
      (List.reverse_infix (l₁ := [y,x]) (l₂ := a :: p)).symm
  rw [hh,List.reverse_cons,word_outDegree _ _ _ (by
    simpa only [List.reverse_cons] using List.nodup_reverse.mpr h)]
  simp only [List.mem_reverse]

private theorem flexible_adj_interior {D : Digraph V} {L : Layout V I} (R : Realization D L)
    {i : I} (hi : i ∉ L.fixed) {x y : V} (h : (wordGraph (R.word i)).Adj x y) :
    x ∈ R.interior i ∨ y ∈ R.interior i := by
  rcases isInfix_cons_cases h with ⟨_,hY⟩ | hTail
  · -- The head of the nonempty interior is the first successor.
    right
    cases he : R.interior i with
    | nil => exact (R.flexible_nonempty i hi he).elim
    | cons w tail =>
      rw [he] at hY
      have hw : w = y := Option.some.inj hY
      simp [hw]
  · left
    have hm : x ∈ R.interior i ++ [L.target i] := hTail.mem (by simp)
    rcases List.mem_append.mp hm with hx | hx
    · exact hx
    · have hEq := List.mem_singleton.mp hx
      exfalso
      obtain ⟨p,q,hpq⟩ := hTail
      have hND := (List.nodup_cons.mp (R.simple i)).2
      rw [← hpq] at hND
      have hLast : (p ++ [x,y] ++ q).getLast? = some (L.target i) := by
        rw [hpq]
        exact (List.getLast?_append_of_ne_nil (R.interior i) (List.cons_ne_nil _ _)).trans rfl
      have hRest : (y :: q).getLast? = some x := by
        rw [hEq]
        have hh : (p ++ (x :: y :: q)).getLast? = some (L.target i) := by
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using hLast
        rw [List.getLast?_append_of_ne_nil p (List.cons_ne_nil _ _),
          List.getLast?_cons_cons] at hh
        exact hh
      have hRestMem : x ∈ y :: q := List.mem_of_getLast? hRest
      have hn : (x :: y :: q).Nodup :=
        (List.nodup_append.mp (show (p ++ (x :: y :: q)).Nodup by
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using hND)).2.1
      exact (List.nodup_cons.mp hn).1 hRestMem

/-- The flexible paths never reuse a host arc, even if two edge occurrences
in the layout share one or both endpoints. -/
theorem Realization.disjoint_flexible {D : Digraph V} {L : Layout V I} (R : Realization D L)
    {i j : I} (hi : i ∉ L.fixed) (hne : i ≠ j) :
    Disjoint (wordGraph (R.word i)) (wordGraph (R.word j)) := by
  apply disjoint_iff_inf_le.mpr
  intro x y h
  obtain ⟨hI,hJ⟩ := h
  have noShared (v : V) (hv : v ∈ R.interior i) (hWord : v ∈ R.word j) : False := by
    have hOut := R.outside i v hv
    change v ∈ L.source j :: R.interior j ++ [L.target j] at hWord
    rcases List.mem_cons.mp hWord with hSrc | hTail
    · exact hOut (hSrc ▸ (L.ends j).1)
    · rcases List.mem_append.mp hTail with hMid | hEnd
      · exact R.unique i j hne hv hMid
      · exact hOut (List.mem_singleton.mp hEnd ▸ (L.ends j).2.1)
  rcases flexible_adj_interior R hi hI with hX | hY
  · exact noShared x hX (hJ.mem (by simp))
  · exact noShared y hY (hJ.mem (by simp))

/-- Keep a prescribed copy distinct from host arcs with the same endpoints.
Every index in the right summand denotes one fixed edge occurrence. -/
def Realization.copies {D : Digraph V} {L : Layout V I} (R : Realization D L) :
    Set ((V × V) ⊕ I) :=
  {c | match c with
      | .inl (x,y) => R.used.Adj x y
      | .inr i => i ∈ L.fixed}

theorem Realization.copies_disjoint {D E : Digraph V} {L K : Layout V I}
    (R : Realization D L) (S : Realization E K)
    (hArc : Disjoint R.used S.used) (hFixed : Disjoint L.fixed K.fixed) :
    Disjoint R.copies S.copies := by
  apply Set.disjoint_left.mpr
  intro c hc hd
  cases c with
  | inl c =>
    have h : (R.used ⊓ S.used).Adj c.1 c.2 := ⟨hc,hd⟩
    exact disjoint_iff_inf_le.mp hArc h
  | inr i => exact Finset.disjoint_left.mp hFixed hc hd

end OverfullWork.DirectedSpanningConfiguration
