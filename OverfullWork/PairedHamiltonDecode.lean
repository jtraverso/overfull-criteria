module

public import OverfullWork.PairedEndpointContraction
public import OverfullWork.OrderedCycleParsing
public import OverfullWork.PathGraphRealization

@[expose] public section


/-! Decoding the actual ordered cycle used in KLO Corollary 6.9.
The input is a cycle written in blocks between its marked vertices:
its edge chain, absence of repeated vertices and spanning property are
checked on the actual contracted digraph. No existence of such a cycle
is asserted here. The output consists of actual host walks, proved to
be simple, mutually vertex-disjoint and spanning. -/
namespace OverfullWork.PairedHamiltonDecode
open Finset DirectedEndpointContraction OrderedCycleCutting
open scoped Classical
variable {V : Type*} [Fintype V] {p : ℕ}
variable (a b : Fin p → V) (ha : Function.Injective a) (hb : Function.Injective b)
  (next : Fin p ≃ Fin p)
set_option maxHeartbeats 12000000

abbrev Interior := Outside (pairedSet a b)

def decoded (body : Fin p → List (Interior a b)) (i : Fin p) : List V :=
  a i :: (body i).map Subtype.val ++ [b i]

theorem interior_ne_a (x : Interior a b) (i : Fin p) : x.val ≠ a i := by
  intro hh
  apply x.property
  rw [hh]
  exact mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)

theorem interior_ne_b (x : Interior a b) (i : Fin p) : x.val ≠ b i := by
  intro hh
  apply x.property
  rw [hh]
  exact mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)

theorem terminal_chain_of_relation (D : Digraph V) (R : V → V → Prop)
    (hDG : ∀ {u v},D.Adj u v → R u v)
    (L : List (Interior a b)) (i : Fin p)
    (h : ((L.map Sum.inl) ++ [Sum.inr i]).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    ((L.map Subtype.val) ++ [b i]).IsChain R := by
  induction L with
  | nil => exact .singleton _
  | cons x xs ih =>
    have hTail := ih h.tail
    cases xs with
    | nil =>
      apply List.IsChain.cons_cons _ hTail
      exact hDG h.rel.2
    | cons y ys =>
      apply List.IsChain.cons_cons _ hTail
      exact hDG h.rel.2

theorem terminal_chain (D : Digraph V) (G : SimpleGraph V)
    (hDG : ∀ {u v},D.Adj u v → G.Adj u v)
    (L : List (Interior a b)) (i : Fin p)
    (h : ((L.map Sum.inl) ++ [Sum.inr i]).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    ((L.map Subtype.val) ++ [b i]).IsChain G.Adj :=
  terminal_chain_of_relation a b ha hb next D G.Adj hDG L i h

theorem decoded_chain_of_relation (D : Digraph V) (R : V → V → Prop)
    (hDG : ∀ {u v},D.Adj u v → R u v)
    (body : Fin p → List (Interior a b)) (i : Fin p)
    (h : (Sum.inr (next.symm i) :: block body i).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    (decoded a b body i).IsChain R := by
  have hTail := terminal_chain_of_relation a b ha hb next D R hDG (body i) i h.tail
  have hEq : next (next.symm i)=i := next.apply_symm_apply i
  cases hL : body i with
  | nil =>
    simp only [decoded,hL,List.map_nil,List.nil_append] at ⊢ hTail
    simp only [block,hL,List.map_nil,List.nil_append] at h
    apply List.IsChain.cons_cons _ hTail
    have he := hDG h.rel.2
    change R (a (next (next.symm i))) (b i) at he
    simpa only [hEq] using he
  | cons x xs =>
    simp only [decoded,hL,List.map_cons,List.cons_append] at ⊢ hTail
    simp only [block,hL,List.map_cons,List.cons_append] at h
    apply List.IsChain.cons_cons _ hTail
    have he := hDG h.rel.2
    change R (a (next (next.symm i))) x.val at he
    simpa only [hEq] using he

theorem decoded_chain (D : Digraph V) (G : SimpleGraph V)
    (hDG : ∀ {u v},D.Adj u v → G.Adj u v)
    (body : Fin p → List (Interior a b)) (i : Fin p)
    (h : (Sum.inr (next.symm i) :: block body i).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    (decoded a b body i).IsChain G.Adj :=
  decoded_chain_of_relation a b ha hb next D G.Adj hDG body i h

theorem decoded_mem (body : Fin p → List (Interior a b)) (i : Fin p) (v : V) :
    v ∈ decoded a b body i ↔
      v=a i ∨ v=b i ∨ ∃ x∈body i,x.val=v := by
  simp only [decoded,List.mem_cons,List.mem_append,List.mem_map,List.mem_singleton,List.not_mem_nil,or_false]
  aesop

theorem decoded_nodup (hab : ∀ i j,a i ≠ b j)
    (body : Fin p → List (Interior a b)) (i : Fin p) (hBody : (body i).Nodup) :
    (decoded a b body i).Nodup := by
  have hMap := hBody.map Subtype.val_injective
  apply List.nodup_cons.mpr
  constructor
  · intro hv
    rcases List.mem_append.mp hv with hv|hv
    · obtain ⟨x,_,he⟩ := List.mem_map.mp hv
      exact interior_ne_a a b x i he
    · exact hab i i (List.mem_singleton.mp hv)
  · apply List.nodup_append.mpr
    refine ⟨hMap,by simp,?_⟩
    intro x hx y hy
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx
    have he := List.mem_singleton.mp hy
    subst y
    exact interior_ne_b a b z i

theorem decoded_disjoint (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j,a i ≠ b j)
    (body : Fin p → List (Interior a b)) (i j : Fin p) (hij : i≠j)
    (hDisjoint : List.Disjoint (body i) (body j)) :
    ∀ v,v∈decoded a b body i → v∉decoded a b body j := by
  intro v hi hj
  rw [decoded_mem] at hi hj
  rcases hi with hi|hi|⟨x,hx,rfl⟩ <;>
    rcases hj with hj|hj|⟨y,hy,he⟩
  · exact hij (ha (hi.symm.trans hj))
  · exact hab i j (hi.symm.trans hj)
  · exact interior_ne_a a b y i (he.trans hi)
  · exact hab j i (hj.symm.trans hi)
  · exact hij (hb (hi.symm.trans hj))
  · exact interior_ne_b a b y i (he.trans hi)
  · exact interior_ne_a a b x j hj
  · exact interior_ne_b a b x j hj
  · have hxy : y=x := Subtype.ext he
    subst y
    exact List.disjoint_left.mp hDisjoint hx hy

/-- Decode ordered contraction blocks into lists. The target relation
can retain arc directions or forget them. -/
theorem lists_of_ordered_cycle (D : Digraph V) (R : V → V → Prop)
    (hDG : ∀ {u v},D.Adj u v → R u v)
    (hab : ∀ i j,a i ≠ b j)
    (body : Fin p → List (Interior a b)) (order : List (Fin p)) (start : Fin p)
    (hAll : ∀ i,i∈order)
    (hOrder : (start :: order).IsChain (fun j i => next j=i))
    (hSimple : (word body order).Nodup)
    (hCover : ∀ w,w∈word body order)
    (hCycle : (Sum.inr start :: word body order).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    ∃ body : Fin p → List (Interior a b),
      (∀ i,(decoded a b body i).IsChain R) ∧ (∀ i,(decoded a b body i).Nodup) ∧
      (∀ i j,i≠j → List.Disjoint (decoded a b body i) (decoded a b body j)) ∧
      ∀ v,∃ i,v ∈ decoded a b body i := by
  have hCut := cut_chain (pairedContraction D a b ha hb next).Adj body order start hCycle
  have hSteps := prescribed_steps next _ order start hOrder hCut
  have hChains : ∀ i,(decoded a b body i).IsChain R :=
    fun i => decoded_chain_of_relation a b ha hb next D R hDG body i (hSteps i (hAll i))
  have hBlocks := (List.nodup_flatMap.mp hSimple).1
  have hPairs := (List.nodup_flatMap.mp hSimple).2
  have hBodies : ∀ i,(body i).Nodup := by
    intro i
    have hh := (hBlocks i (hAll i)).of_append_left
    exact hh.of_map Sum.inl
  have hDis : ∀ i j,i≠j → List.Disjoint (body i) (body j) := by
    intro i j hij
    letI : Std.Symm (fun i j : Fin p => List.Disjoint (block body i) (block body j)) :=
      ⟨fun _ _ hh => hh.symm⟩
    have hh := hPairs.forall (hAll i) (hAll j) hij
    apply List.disjoint_left.mpr
    intro x hx hx'
    have hxBlock : Sum.inl x ∈ block body i := by simp [block,hx]
    have hxBlock' : Sum.inl x ∈ block body j := by simp [block,hx']
    exact List.disjoint_left.mp hh hxBlock hxBlock'
  refine ⟨body,hChains,fun i => decoded_nodup a b hab body i (hBodies i),?_,?_⟩
  · intro i j hij v hv hv'
    exact decoded_disjoint a b ha hb hab body i j hij (hDis i j hij) v hv hv'
  · intro v
    by_cases hvA : ∃ i,a i=v
    · obtain ⟨i,rfl⟩ := hvA
      refine ⟨i,?_⟩
      rw [decoded_mem]
      exact Or.inl rfl
    by_cases hvB : ∃ i,b i=v
    · obtain ⟨i,rfl⟩ := hvB
      refine ⟨i,?_⟩
      rw [decoded_mem]
      exact Or.inr (Or.inl rfl)
    have hv : v∉pairedSet a b := by
      simpa only [pairedSet,mem_union,mem_image,mem_univ,true_and,not_or] using
        And.intro hvA hvB
    let x : Interior a b := ⟨v,hv⟩
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp (hCover (Sum.inl x))
    have hx : x∈body i := by simpa [block] using hi
    refine ⟨i,?_⟩
    rw [decoded_mem]
    exact Or.inr (Or.inr ⟨x,hx,rfl⟩)


/-- An actual ordered Hamilton cycle in block presentation decodes to
an actual spanning linkage. The cycle itself is an explicit input, not
an existence axiom or an additional premise of the final R2 target. -/
theorem paths_of_ordered_cycle (D : Digraph V) (G : SimpleGraph V)
    (hDG : ∀ {u v},D.Adj u v → G.Adj u v)
    (hab : ∀ i j,a i ≠ b j)
    (body : Fin p → List (Interior a b)) (order : List (Fin p)) (start : Fin p)
    (hAll : ∀ i,i∈order)
    (hOrder : (start :: order).IsChain (fun j i => next j=i))
    (hSimple : (word body order).Nodup)
    (hCover : ∀ w,w∈word body order)
    (hCycle : (Sum.inr start :: word body order).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    ∃ P : ∀ i,G.Walk (a i) (b i),
      (∀ i,(P i).IsPath) ∧
      (∀ i j,i≠j → ∀ v,v∈(P i).support → v∉(P j).support) ∧
      ∀ v,∃ i,v∈(P i).support := by
  obtain ⟨pieces,hChain,hND,hDisjoint,hSpan⟩ :=
    lists_of_ordered_cycle a b ha hb next D G.Adj hDG hab body order start
      hAll hOrder hSimple hCover hCycle
  let P : ∀ i,G.Walk (a i) (b i) := fun i =>
    (SimpleGraph.Walk.ofSupport (decoded a b pieces i) (by simp [decoded]) (hChain i)).copy
      (by simp [decoded]) (by simp [decoded])
  have hSupport : ∀ i,(P i).support = decoded a b pieces i := by
    intro i
    simp only [P,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_ofSupport]
  refine ⟨P,?_,?_,?_⟩
  · intro i
    rw [SimpleGraph.Walk.isPath_def,hSupport]
    exact hND i
  · intro i j hij v hi hj
    rw [hSupport] at hi hj
    exact hDisjoint i j hij hi hj
  · intro v
    obtain ⟨i,hi⟩ := hSpan v
    exact ⟨i,by rwa [hSupport]⟩

theorem lists_of_hamilton_cycle (D : Digraph V) (R : V → V → Prop)
    (hDG : ∀ {u v},D.Adj u v → R u v)
    (hab : ∀ i j,a i ≠ b j)
    (init : List (Interior a b ⊕ Fin p)) (start : Fin p)
    (hSimple : (init ++ [Sum.inr start]).Nodup)
    (hCover : ∀ w,w∈init ++ [Sum.inr start])
    (hOrder : (start :: markers (init ++ [Sum.inr start])).IsChain
      (fun j i => next j=i))
    (hCycle : (Sum.inr start :: (init ++ [Sum.inr start])).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    ∃ body : Fin p → List (Interior a b),
      (∀ i,(decoded a b body i).IsChain R) ∧ (∀ i,(decoded a b body i).Nodup) ∧
      (∀ i j,i≠j → List.Disjoint (decoded a b body i) (decoded a b body j)) ∧
      ∀ v,∃ i,v ∈ decoded a b body i := by
  obtain ⟨body,hWord⟩ := exists_cycle_blocks init start hSimple
  apply lists_of_ordered_cycle a b ha hb next D R hDG hab body
    (markers (init ++ [Sum.inr start])) start
  · intro i
    exact (mem_markers _ i).mpr (hCover (Sum.inr i))
  · exact hOrder
  · rw [hWord]
    exact hSimple
  · rw [hWord]
    exact hCover
  · rw [hWord]
    exact hCycle

/-- Decode an ordinary ordered Hamilton cycle list. Its blocks are
extracted internally; only the actual cyclic edge chain, unique and
exhaustive vertex list, and prescribed order of markers are inputs. -/
theorem paths_of_hamilton_cycle (D : Digraph V) (G : SimpleGraph V)
    (hDG : ∀ {u v},D.Adj u v → G.Adj u v)
    (hab : ∀ i j,a i ≠ b j)
    (init : List (Interior a b ⊕ Fin p)) (start : Fin p)
    (hSimple : (init ++ [Sum.inr start]).Nodup)
    (hCover : ∀ w,w∈init ++ [Sum.inr start])
    (hOrder : (start :: markers (init ++ [Sum.inr start])).IsChain
      (fun j i => next j=i))
    (hCycle : (Sum.inr start :: (init ++ [Sum.inr start])).IsChain
      (pairedContraction D a b ha hb next).Adj) :
    ∃ P : ∀ i,G.Walk (a i) (b i),
      (∀ i,(P i).IsPath) ∧
      (∀ i j,i≠j → ∀ v,v∈(P i).support → v∉(P j).support) ∧
      ∀ v,∃ i,v∈(P i).support := by
  obtain ⟨body,hWord⟩ := exists_cycle_blocks init start hSimple
  apply paths_of_ordered_cycle a b ha hb next D G hDG hab body
    (markers (init ++ [Sum.inr start])) start
  · intro i
    exact (mem_markers _ i).mpr (hCover (Sum.inr i))
  · exact hOrder
  · rw [hWord]
    exact hSimple
  · rw [hWord]
    exact hCover
  · rw [hWord]
    exact hCycle

end OverfullWork.PairedHamiltonDecode
