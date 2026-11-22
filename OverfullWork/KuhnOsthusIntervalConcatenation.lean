module

public import OverfullWork.KuhnOsthusOrderedPathCover

@[expose] public section


/-! Join ordinary and exceptional interval systems at their common
boundary, preserving the complete set of physical arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedAbsorbingLadder DirectedSpanningConfiguration
open scoped Classical
variable {V : Type*}

private theorem wordGraph_cons_cons_adj (a b x y : V) (L : List V) :
    (wordGraph (a::b::L)).Adj x y ↔ (x = a ∧ y = b) ∨ (wordGraph (b::L)).Adj x y := by
  change [x,y] <:+: a::b::L ↔ _
  rw [List.infix_cons_iff]
  simp only [List.cons_prefix_cons,List.nil_prefix,and_true]
  rfl

private theorem wordGraph_append_at_last (L T : List V) {a x y : V}
    (h : L.getLast? = some a) :
    (wordGraph (L++T)).Adj x y ↔ (wordGraph L).Adj x y ∨ (wordGraph (a::T)).Adj x y := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    cases L with
    | nil =>
      have he : b = a := by simpa using h
      subst b
      have hn : ¬ (wordGraph [a]).Adj x y := by
        intro h'
        have hl := List.IsInfix.length_le (show [x,y] <:+: [a] from h')
        simp at hl
      simp [hn]
    | cons c L =>
      have h' : (c::L).getLast? = some a := by simpa using h
      simp only [List.cons_append,wordGraph_cons_cons_adj]
      have hNext := ih h'
      simp only [List.cons_append] at hNext
      rw [hNext]
      tauto

/-- Regard a cover as living in any host containing all its arcs. -/
def IntervalPathCover.rehost {D G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover D A S T) (h : D ≤ G) : IntervalPathCover G A S T :=
  { path := fun t =>
      ⟨(P.path t).source,(P.path t).target,(P.path t).tail,
        ⟨(P.path t).route.1.imp (fun _ _ he => h he),(P.path t).route.2⟩,(P.path t).simple⟩
    starts := P.starts
    ends := P.ends
    disjoint := P.disjoint
    spans := P.spans }

@[simp] theorem IntervalPathCover.rehost_digraph {D G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover D A S T) (h : D ≤ G) : (P.rehost h).digraph = P.digraph := rfl

private theorem path_tail_avoids_starts {G : Digraph V} {B M T : Finset V}
    (Q : IntervalPathCover G B M T) (t : T) {x : V} (hx : x ∈ (Q.path t).tail) : x ∉ M := by
  intro hm
  let s : T := Q.starts.symm ⟨x,hm⟩
  have hs : (Q.path s).source = x := (Q.ends s).1.trans
    (congrArg Subtype.val (Q.starts.apply_symm_apply ⟨x,hm⟩))
  by_cases h : t = s
  · have hs' : (Q.path t).source = x := (congrArg (fun q => (Q.path q).source) h).trans hs
    exact (List.nodup_cons.mp (Q.path t).simple).1 (hs'.symm ▸ hx)
  · exact Q.disjoint t s h (List.mem_cons_of_mem _ hx) (hs ▸ List.mem_cons_self ..)

/-- Join the two interval covers through their entire shared
boundary. The concatenated paths use exactly the two original
sets of arcs and their endpoint bijection is the composition. -/
theorem IntervalPathCover.exists_concat {G : Digraph V} {A B S M T : Finset V}
    (P : IntervalPathCover G A S M) (Q : IntervalPathCover G B M T)
    (hMeet : A ∩ B = M) :
    ∃ R : IntervalPathCover G (A ∪ B) S T,
      R.digraph = P.digraph ⊔ Q.digraph ∧ R.starts = Q.starts.trans P.starts := by
  let fp (t : T) := P.path (Q.starts t)
  let fq (t : T) := Q.path t
  have hAt (t : T) : (fp t).target = (fq t).source := ((P.ends (Q.starts t)).2).trans (Q.ends t).1.symm
  have hOff (t s : T) : List.Disjoint (fp t).vertices (fq s).tail := by
    intro x h₁ h₂
    have hA := (P.spans x).mpr ⟨Q.starts t,h₁⟩
    have hB := (Q.spans x).mpr ⟨s,List.mem_cons_of_mem _ h₂⟩
    exact path_tail_avoids_starts Q s h₂ (hMeet ▸ mem_inter.mpr ⟨hA,hB⟩)
  let path (t : T) : PathRequest G := {
    source := (fp t).source
    target := (fq t).target
    tail := (fp t).tail ++ (fq t).tail
    route := by
      change ((fp t).vertices ++ (fq t).tail).IsChain G.Adj ∧
        ((fp t).vertices ++ (fq t).tail).getLast? = some (fq t).target
      have hLast : (fp t).vertices.getLast? = some (fq t).source :=
        (fp t).route.2.trans (congrArg some (hAt t))
      refine ⟨(fp t).route.1.append (fq t).route.1.tail ?_,?_⟩
      · intro x hx y hy
        change x ∈ (fp t).vertices.getLast? at hx
        rw [hLast] at hx
        have he : (fq t).source = x := by simpa using hx
        exact he ▸ (fq t).route.1.rel_head? hy
      · rw [List.getLast?_append,hLast]
        have hEnd := (fq t).route.2
        change ([(fq t).source] ++ (fq t).tail).getLast? = some (fq t).target at hEnd
        simpa only [List.getLast?_append,List.getLast?_singleton] using hEnd
    simple := List.nodup_append'.mpr ⟨(fp t).simple,(List.nodup_cons.mp (fq t).simple).2,hOff t t⟩ }
  have hC (t : T) : (path t).vertices = (fp t).vertices ++ (fq t).tail := rfl
  let R : IntervalPathCover G (A ∪ B) S T := {
    path := path
    starts := Q.starts.trans P.starts
    ends := fun t => ⟨(P.ends (Q.starts t)).1,(Q.ends t).2⟩
    disjoint := by
      intro t s hne x ht hs
      rw [hC,List.mem_append] at ht hs
      rcases ht with ht | ht <;> rcases hs with hs | hs
      · exact P.disjoint _ _ (Q.starts.injective.ne hne) ht hs
      · exact hOff t s ht hs
      · exact hOff s t hs ht
      · exact Q.disjoint t s hne (List.mem_cons_of_mem _ ht) (List.mem_cons_of_mem _ hs)
    spans := by
      intro x
      rw [mem_union]
      constructor
      · rintro (hx | hx)
        · obtain ⟨t,ht⟩ := (P.spans x).mp hx
          refine ⟨Q.starts.symm t,?_⟩
          rw [hC,List.mem_append]
          exact .inl (by simpa only [fp,Q.starts.apply_symm_apply] using ht)
        · obtain ⟨t,ht⟩ := (Q.spans x).mp hx
          refine ⟨t,?_⟩
          rw [hC,List.mem_append]
          rcases (List.mem_cons.mp ht) with he | he
          · exact .inl (he.symm ▸ List.mem_of_getLast? ((fp t).route.2.trans (congrArg some (hAt t))))
          · exact .inr he
      · rintro ⟨t,ht⟩
        rw [hC,List.mem_append] at ht
        exact ht.imp (fun h => (P.spans x).mpr ⟨Q.starts t,h⟩)
          (fun h => (Q.spans x).mpr ⟨t,List.mem_cons_of_mem _ h⟩) }
  have hArcs (t : T) (x y : V) :
      (wordGraph (path t).vertices).Adj x y ↔
        (wordGraph (fp t).vertices).Adj x y ∨ (wordGraph (fq t).vertices).Adj x y := by
    rw [hC]
    exact wordGraph_append_at_last _ _ ((fp t).route.2.trans (congrArg some (hAt t)))
  refine ⟨R,?_,rfl⟩
  ext x y
  simp only [IntervalPathCover.digraph,R,Digraph.iSup_adj,Digraph.sup_adj,hArcs]
  constructor
  · rintro ⟨t,ht | ht⟩
    · exact .inl ⟨Q.starts t,ht⟩
    · exact .inr ⟨t,ht⟩
  · rintro (⟨t,ht⟩ | ⟨t,ht⟩)
    · exact ⟨Q.starts.symm t,.inl (by simpa only [fp,Q.starts.apply_symm_apply] using ht)⟩
    · exact ⟨t,.inr ht⟩

end OverfullWork.DirectedRobustExpansion
