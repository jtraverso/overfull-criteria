module

public import OverfullWork.KuhnOsthusExceptionalIntervalSplit
public import OverfullWork.DirectedSpanningConfiguration

@[expose] public section


/-! The paths on the reopened interval, transported to the physical
vertices and read as a digraph using their consecutive ordered pairs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedAbsorbingLadder DirectedSpanningConfiguration
open scoped Classical

/-- A physical path system spanning one interval and one style.
The permutation of the boundary vertices remembers the matching
between initial and final vertices. -/
structure IntervalPathCover {V : Type*} (G : Digraph V) (A S T : Finset V) where
  path : T → PathRequest G
  starts : T ≃ S
  ends : ∀ t, (path t).source = (starts t).val ∧ (path t).target = t.val
  disjoint : ∀ i j, i ≠ j → List.Disjoint (path i).vertices (path j).vertices
  spans : ∀ x, x ∈ A ↔ ∃ t, x ∈ (path t).vertices

/-- Ordered arcs of all the paths in one interval. -/
def IntervalPathCover.digraph {V : Type*} {G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover G A S T) : Digraph V :=
  ⨆ i, wordGraph (P.path i).vertices

theorem IntervalPathCover.digraph_le {V : Type*} {G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover G A S T) : P.digraph ≤ G :=
  iSup_le fun i => wordGraph_le (P.path i).route.1

/-- A physical interval with equal disjoint boundary cells supplies
the coordinates of its reopened quotient. Identify the terminal cell
with the initial cell by a bijection of those two cells. -/
theorem exists_interval_split_coordinates {V : Type*}
    (A S T : Finset V) (hS : S ⊆ A) (hT : T ⊆ A) (hDis : Disjoint S T)
    (hSize : S.card = T.card) :
    let W := ↥(A \ T)
    let B := (univ : Finset W).filter (fun x => x.val ∈ S)
    ∃ (e : W ⊕ ↥B ≃ A) (first : B ≃ S) (last : B ≃ T),
      (∀ b : B, (e (Sum.inl b.val)).val = (first b).val) ∧
      (∀ b : B, (e (Sum.inr b)).val = (last b).val) ∧
      ∀ v : W, (e (Sum.inl v)).val = v.val := by
  classical
  dsimp only
  let W := ↥(A \ T)
  let B := (univ : Finset W).filter (fun x => x.val ∈ S)
  let first : B ≃ S := {
    toFun := fun x => ⟨x.val.val,(mem_filter.mp x.prop).2⟩
    invFun := fun x => ⟨⟨x.val,mem_sdiff.mpr ⟨hS x.prop,fun h => disjoint_left.mp hDis x.prop h⟩⟩,
      mem_filter.mpr ⟨mem_univ _,x.prop⟩⟩
    left_inv := fun x => Subtype.ext (Subtype.ext rfl)
    right_inv := fun x => Subtype.ext rfl }
  let last : B ≃ T := first.trans (Fintype.equivOfCardEq (by
    simpa only [Fintype.card_coe] using hSize))
  let f : W ⊕ B → A := fun x => match x with
    | .inl v => ⟨v.val,(mem_sdiff.mp v.prop).1⟩
    | .inr b => ⟨(last b).val,hT (last b).prop⟩
  have hF : Function.Bijective f := by
    constructor
    · rintro (v|v) (w|w) h
      · exact congrArg Sum.inl (Subtype.ext (congrArg (fun a : A => a.val) h))
      · exact ((mem_sdiff.mp v.prop).2 ((congrArg (fun a : A => a.val) h).symm ▸ (last w).prop)).elim
      · exact ((mem_sdiff.mp w.prop).2 ((congrArg (fun a : A => a.val) h) ▸ (last v).prop)).elim
      · exact congrArg Sum.inr (last.injective (Subtype.ext (congrArg (fun a : A => a.val) h)))
    · intro v
      by_cases hv : v.val ∈ T
      · exact ⟨Sum.inr (last.symm ⟨v.val,hv⟩),
          Subtype.ext (congrArg (fun a : T => a.val) (last.apply_symm_apply ⟨v.val,hv⟩))⟩
      · exact ⟨Sum.inl ⟨v.val,mem_sdiff.mpr ⟨v.prop,hv⟩⟩,Subtype.ext rfl⟩
  exact ⟨Equiv.ofBijective f hF,first,last,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

/-- Transport the split paths along the supplied physical coordinates.
A two-vertex infix specifying a protected arc is transported as well. -/
theorem transport_split_interval_paths {V W : Type*}
    (G : Digraph V) (H : Digraph W) (A S T : Finset V) (B : Finset W)
    (e : W ⊕ B ≃ A) (first : B ≃ S) (last : B ≃ T)
    (hFirst : ∀ b : B, (e (Sum.inl b.val)).val = (first b).val)
    (hLast : ∀ b : B, (e (Sum.inr b)).val = (last b).val)
    (hArc : ∀ x y, (splitIntervalDigraph H B).Adj x y → G.Adj (e x).val (e y).val)
    (P : B → PathRequest (splitIntervalDigraph H B)) (start : Equiv.Perm B)
    (hEnds : ∀ b, (P b).source = Sum.inl (start b).val ∧ (P b).target = Sum.inr b)
    (hDis : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices)
    (hCover : ∀ v, ∃ i, v ∈ (P i).vertices) :
    ∃ Q : IntervalPathCover G A S T,
      ∀ x y, (∃ b, [x,y] <:+: (P b).vertices) →
        Q.digraph.Adj (e x).val (e y).val := by
  let f (x : W ⊕ B) := (e x).val
  have hf : Function.Injective f := Subtype.coe_injective.comp e.injective
  let Q (t : T) : PathRequest G :=
    let p := P (last.symm t)
    ⟨f p.source,f p.target,p.tail.map f,⟨List.isChain_map_of_isChain f hArc p.route.1,by
      change ((p.source :: p.tail).map f).getLast? = some (f p.target)
      rw [List.getLast?_map,p.route.2]
      rfl⟩,p.simple.map hf⟩
  let X : IntervalPathCover G A S T := {
    path := Q
    starts := last.symm.trans (start.trans first)
    ends := by
      intro t
      change f (P (last.symm t)).source = (first (start (last.symm t))).val ∧
        f (P (last.symm t)).target = t.val
      rw [(hEnds _).1,(hEnds _).2]
      exact ⟨hFirst _, (hLast _).trans (congrArg Subtype.val (last.apply_symm_apply t))⟩
    disjoint := by
      intro t t' h
      exact List.disjoint_map hf (hDis _ _ (last.symm.injective.ne h))
    spans := by
      intro x
      constructor
      · intro hx
        let w := e.symm ⟨x,hx⟩
        obtain ⟨i,hi⟩ := hCover w
        refine ⟨last i,?_⟩
        change x ∈ (P (last.symm (last i))).vertices.map f
        rw [last.symm_apply_apply]
        exact List.mem_map.mpr ⟨w,hi,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩
      · rintro ⟨t,ht⟩
        change x ∈ (P (last.symm t)).vertices.map f at ht
        obtain ⟨w,_,rfl⟩ := List.mem_map.mp ht
        exact (e w).prop }
  refine ⟨X,?_⟩
  rintro x y ⟨b,hb⟩
  apply Digraph.iSup_adj.mpr
  refine ⟨last b,?_⟩
  change [f x,f y] <:+: (P (last.symm (last b))).vertices.map f
  rw [last.symm_apply_apply]
  exact hb.map f

private theorem word_arc_succ {V : Type*} [DecidableEq V] (L : List V)
    (hL : L.Nodup) {x y : V} (h : (wordGraph L).Adj x y) :
    L.idxOf y = L.idxOf x+1 := by
  have hx : x ∈ L := h.mem (by simp)
  have hy : y ∈ L := h.mem (by simp)
  obtain ⟨p,hp,hAt⟩ := List.infix_iff_getElem?.mp h
  have hx' : L[p]? = some x := by simpa using hAt 0 (by simp)
  have hy' : L[p+1]? = some y := by simpa [Nat.add_comm] using hAt 1 (by simp)
  have hKey (v : V) (i : ℕ) (hi : i < L.length) (hv : v ∈ L)
      (he : L[i]? = some v) : L.idxOf v = i := by
    have hj := List.idxOf_lt_length_iff.mpr hv
    have hGet := List.getElem?_idxOf hv
    rw [List.getElem?_eq_getElem hj] at hGet
    rw [List.getElem?_eq_getElem hi] at he
    exact hL.getElem_inj_iff.mp (Option.some.inj (hGet.trans he.symm))
  have hLen : p+2 ≤ L.length := by simpa [Nat.add_comm] using hp
  rw [hKey x p (by omega) hx hx',hKey y (p+1) (by omega) hy hy']

/-- Each arc increases its path position. Disjointness makes this a
single rank on the ambient vertex set. -/
theorem IntervalPathCover.exists_rank {V : Type*} {G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover G A S T) :
    ∃ rank : V → ℕ, ∀ x y, P.digraph.Adj x y → rank x < rank y := by
  classical
  let rank (v : V) : ℕ :=
    if h : ∃ t, v ∈ (P.path t).vertices then (P.path h.choose).vertices.idxOf v else 0
  have hRank (v : V) (t : T) (hv : v ∈ (P.path t).vertices) :
      rank v = (P.path t).vertices.idxOf v := by
    have h : ∃ i, v ∈ (P.path i).vertices := ⟨t,hv⟩
    have he : h.choose = t := by
      by_contra hn
      exact P.disjoint _ _ hn h.choose_spec hv
    simp only [rank,dif_pos h,he]
  refine ⟨rank,?_⟩
  intro x y h
  obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp h
  rw [hRank x i (hi.mem (by simp)),hRank y i (hi.mem (by simp))]
  have hIdx : (P.path i).vertices.idxOf y = (P.path i).vertices.idxOf x+1 :=
    word_arc_succ (P.path i).vertices (P.path i).simple hi
  rw [hIdx]
  omega

private theorem word_degree_positive_out {V : Type*} [Fintype V]
    (G : Digraph V) (P : PathRequest G) (x : V) :
    (∃ y, (wordGraph P.vertices).Adj x y) ↔ x ∈ P.vertices ∧ x ≠ P.target := by
  classical
  have hLast : P.vertices.getLast? = some P.target := P.route.2
  have hSplit : P.vertices.dropLast ++ [P.target] = P.vertices :=
    List.dropLast_append_getLast? _ (by simp [hLast])
  have hND : (P.vertices.dropLast ++ [P.target]).Nodup := by rw [hSplit]; exact P.simple
  have hDeg := word_outDegree P.vertices.dropLast P.target x hND
  rw [hSplit] at hDeg
  have hNot := (List.nodup_append.mp hND).2.2
  have hPos : 0 < outDegree (wordGraph P.vertices) x ↔ ∃ y, (wordGraph P.vertices).Adj x y := by
    simp only [outDegree,card_pos,Finset.Nonempty,mem_filter,mem_univ,true_and]
  have hMem : x ∈ P.vertices ↔ x ∈ P.vertices.dropLast ∨ x = P.target := by
    calc
      _ ↔ x ∈ P.vertices.dropLast ++ [P.target] := by rw [hSplit]
      _ ↔ _ := by simp
  rw [←hPos,hDeg,hMem]
  by_cases h : x ∈ P.vertices.dropLast
  · have hx : x ≠ P.target := fun he => hNot x h _ (by simp) he
    simp [h,hx]
  · simp [h]

private theorem word_degree_positive_in {V : Type*} [Fintype V]
    (G : Digraph V) (P : PathRequest G) (x : V) :
    (∃ y, (wordGraph P.vertices).Adj y x) ↔ x ∈ P.vertices ∧ x ≠ P.source := by
  classical
  have hPos : 0 < inDegree (wordGraph P.vertices) x ↔ ∃ y, (wordGraph P.vertices).Adj y x := by
    simp only [inDegree,inNeighbours,card_pos,Finset.Nonempty,mem_filter,mem_univ,true_and]
  rw [←hPos]
  change 0 < inDegree (wordGraph (P.source :: P.tail)) x ↔ _
  rw [word_inDegree P.tail P.source x P.simple]
  by_cases h : x ∈ P.tail
  · have hx : x ≠ P.source := fun he => (List.nodup_cons.mp P.simple).1 (he ▸ h)
    simp [PathRequest.vertices,h,hx]
  · simp [PathRequest.vertices,h]

/-- Vertices other than the final boundary have one outgoing slot.
The dual statement applies to the initial boundary. -/
theorem IntervalPathCover.slots {V : Type*} [Fintype V] {G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover G A S T) (x : V) :
    ((∃ y, P.digraph.Adj x y) ↔ x ∈ A \ T) ∧
      ((∃ y, P.digraph.Adj y x) ↔ x ∈ A \ S) := by
  classical
  constructor
  · constructor
    · rintro ⟨y,hy⟩
      obtain ⟨t,ht⟩ := Digraph.iSup_adj.mp hy
      obtain ⟨hx,hEnd⟩ := (word_degree_positive_out G (P.path t) x).mp ⟨y,ht⟩
      refine mem_sdiff.mpr ⟨(P.spans x).mpr ⟨t,hx⟩,?_⟩
      intro hT
      let t' : T := ⟨x,hT⟩
      have hPlace : (P.path t').target = x := (P.ends t').2
      have hn : t ≠ t' := fun he => hEnd (he.symm ▸ hPlace).symm
      exact P.disjoint t t' hn hx (hPlace ▸ List.mem_of_getLast? (P.path t').route.2)
    · intro h
      obtain ⟨t,ht⟩ := (P.spans x).mp (mem_sdiff.mp h).1
      have hn : x ≠ (P.path t).target := fun he =>
        (mem_sdiff.mp h).2 (he.symm ▸ ((P.ends t).2.symm ▸ t.prop))
      obtain ⟨y,hy⟩ := (word_degree_positive_out G (P.path t) x).mpr ⟨ht,hn⟩
      exact ⟨y,Digraph.iSup_adj.mpr ⟨t,hy⟩⟩
  · constructor
    · rintro ⟨y,hy⟩
      obtain ⟨t,ht⟩ := Digraph.iSup_adj.mp hy
      obtain ⟨hx,hStart⟩ := (word_degree_positive_in G (P.path t) x).mp ⟨y,ht⟩
      refine mem_sdiff.mpr ⟨(P.spans x).mpr ⟨t,hx⟩,?_⟩
      intro hS
      let t' := P.starts.symm ⟨x,hS⟩
      have hPlace : (P.path t').source = x :=
        (P.ends t').1.trans (congrArg Subtype.val (P.starts.apply_symm_apply ⟨x,hS⟩))
      have hn : t ≠ t' := fun he => hStart (he.symm ▸ hPlace).symm
      exact P.disjoint t t' hn hx (hPlace ▸ List.mem_cons_self ..)
    · intro h
      obtain ⟨t,ht⟩ := (P.spans x).mp (mem_sdiff.mp h).1
      have hn : x ≠ (P.path t).source := fun he =>
        (mem_sdiff.mp h).2 (he.symm ▸ ((P.ends t).1.symm ▸ (P.starts t).prop))
      obtain ⟨y,hy⟩ := (word_degree_positive_in G (P.path t) x).mpr ⟨ht,hn⟩
      exact ⟨y,Digraph.iSup_adj.mpr ⟨t,hy⟩⟩

private theorem path_vertex_of_index {V : Type*} [DecidableEq V] {L : List V} {x y : V}
    (hx : x ∈ L) (hy : y ∈ L) (h : L.idxOf x = L.idxOf y) : x = y := by
  have he := List.getElem?_idxOf hx
  rw [h,List.getElem?_idxOf hy] at he
  exact Option.some.inj he.symm

/-- The physical paths give an acyclic digraph with unique incoming
and outgoing arcs at the vertices that have those slots. -/
theorem IntervalPathCover.is_path_system {V : Type*} {G : Digraph V} {A S T : Finset V}
    (P : IntervalPathCover G A S T) : IsDirectedPathSystem P.digraph := by
  classical
  obtain ⟨rank,hRank⟩ := P.exists_rank
  have hRoute {x y : V} (h : Relation.TransGen P.digraph.Adj x y) : rank x < rank y := by
    induction h with
    | single h => exact hRank _ _ h
    | tail _ h ih => exact ih.trans (hRank _ _ h)
  have hWord {x y : V} (h : P.digraph.Adj x y) :
      ∃ t, (wordGraph (P.path t).vertices).Adj x y ∧ x ∈ (P.path t).vertices ∧
        y ∈ (P.path t).vertices := by
    obtain ⟨t,ht⟩ := Digraph.iSup_adj.mp h
    exact ⟨t,ht,ht.mem (by simp),ht.mem (by simp)⟩
  refine ⟨fun x h => (lt_irrefl (rank x)) (hRoute h),?_,?_⟩
  · intro x y z hy hz
    obtain ⟨i,hi,hxi,hyi⟩ := hWord hy
    obtain ⟨j,hj,hxj,hzj⟩ := hWord hz
    have he : i = j := by_contra fun h => P.disjoint i j h hxi hxj
    subst j
    exact path_vertex_of_index hyi hzj
      ((word_arc_succ _ (P.path i).simple hi).trans (word_arc_succ _ (P.path i).simple hj).symm)
  · intro x y z hy hz
    obtain ⟨i,hi,hyi,hxi⟩ := hWord hy
    obtain ⟨j,hj,hzj,hxj⟩ := hWord hz
    have he : i = j := by_contra fun h => P.disjoint i j h hxi hxj
    subst j
    have h₁ : (P.path i).vertices.idxOf x = (P.path i).vertices.idxOf y+1 :=
      word_arc_succ (P.path i).vertices (P.path i).simple hi
    have h₂ : (P.path i).vertices.idxOf x = (P.path i).vertices.idxOf z+1 :=
      word_arc_succ (P.path i).vertices (P.path i).simple hj
    exact path_vertex_of_index hyi hzj (by omega)

end OverfullWork.DirectedRobustExpansion
