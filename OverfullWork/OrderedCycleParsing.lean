module

public import OverfullWork.OrderedCycleCutting
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Lattice

@[expose] public section


/-! Extract the actual blocks of a marked Hamilton cycle list.
No block family or path-cover certificate is assumed to exist. -/
namespace OverfullWork.OrderedCycleCutting
open scoped Classical
variable {I X : Type*}
set_option maxHeartbeats 6000000

def rawBlock (q : I × List X) : List (X ⊕ I) :=
  q.2.map Sum.inl ++ [Sum.inr q.1]

def markers (l : List (X ⊕ I)) : List I :=
  l.filterMap fun x => match x with | .inl _ => none | .inr i => some i

theorem raw_blocks_exist (init : List (X ⊕ I)) (last : I) :
    ∃ B : List (I × List X),init ++ [Sum.inr last]=B.flatMap rawBlock := by
  induction init with
  | nil => exact ⟨[(last,[])],by simp [rawBlock]⟩
  | cons x xs ih =>
    obtain ⟨B,hB⟩ := ih
    cases x with
    | inr i =>
      refine ⟨(i,[])::B,?_⟩
      simp only [List.cons_append,List.flatMap_cons,rawBlock,List.map_nil,List.nil_append,
        List.singleton_append]
      rw [←hB]
    | inl x =>
      cases B with
      | nil => simp at hB
      | cons q rest =>
        refine ⟨(q.1,x::q.2)::rest,?_⟩
        simpa only [List.flatMap_cons,rawBlock,List.map_cons,List.cons_append] using
          congrArg (List.cons (Sum.inl x)) hB

theorem markers_raw_blocks (B : List (I × List X)) :
    markers (B.flatMap rawBlock)=B.map Prod.fst := by
  induction B with
  | nil => rfl
  | cons q rest ih =>
    simpa [List.flatMap_cons,rawBlock,markers,List.filterMap_append,List.filterMap_map] using ih

theorem raw_block_index_unique (B : List (I × List X))
    (hSimple : (B.flatMap rawBlock).Nodup)
    (q r : I × List X) (hq : q∈B) (hr : r∈B) (hIndex : q.1=r.1) : q=r := by
  by_contra hne
  have hPairs := (List.nodup_flatMap.mp hSimple).2
  letI : Std.Symm (fun q r : I × List X => List.Disjoint (rawBlock q) (rawBlock r)) :=
    ⟨fun _ _ hh => hh.symm⟩
  have hh := hPairs.forall hq hr hne
  exact hh (a:=Sum.inr q.1) (by simp [rawBlock]) (by simp [rawBlock,hIndex])

noncomputable def parsedBody (B : List (I × List X)) (i : I) : List X :=
  if h : ∃ L,(i,L)∈B then Classical.choose h else []

theorem parsedBody_eq (B : List (I × List X))
    (hSimple : (B.flatMap rawBlock).Nodup) (q : I × List X) (hq : q∈B) :
    parsedBody B q.1=q.2 := by
  have h : ∃ L,(q.1,L)∈B := ⟨q.2,hq⟩
  rw [parsedBody,dif_pos h]
  have he := raw_block_index_unique B hSimple (q.1,Classical.choose h) q
    (Classical.choose_spec h) hq rfl
  exact congrArg Prod.snd he

theorem exists_cycle_blocks (init : List (X ⊕ I)) (last : I)
    (hSimple : (init ++ [Sum.inr last]).Nodup) :
    ∃ body : I → List X,
      word body (markers (init ++ [Sum.inr last]))=init ++ [Sum.inr last] := by
  obtain ⟨B,hB⟩ := raw_blocks_exist init last
  have hSimpleB : (B.flatMap rawBlock).Nodup := by rw [←hB];exact hSimple
  refine ⟨parsedBody B,?_⟩
  rw [hB,markers_raw_blocks]
  unfold word
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro q hq
  simp only [Function.comp_apply,block,parsedBody_eq B hSimpleB q hq,rawBlock]

theorem mem_markers (l : List (X ⊕ I)) (i : I) :
    i∈markers l ↔ Sum.inr i∈l := by
  simp only [markers,List.mem_filterMap]
  constructor
  · rintro ⟨x,hx,he⟩
    cases x with
    | inl x => simp at he
    | inr j =>
      have hji : j=i := Option.some.inj he
      subst j
      exact hx
  · intro hi
    exact ⟨Sum.inr i,hi,rfl⟩

end OverfullWork.OrderedCycleCutting
