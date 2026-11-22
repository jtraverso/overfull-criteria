module

public import OverfullWork.KuhnOsthusPathPartitionSizes

@[expose] public section


/-! Insert the exceptional and ordinary pieces into their assigned
complete exceptional path systems. Unassigned slots remain available. -/
namespace OverfullWork.DirectedRobustExpansion

variable {V I K : Type*}

/-- Extend a graph family along a slot assignment. Unassigned slots carry
the empty digraph. -/
def placePathPieces (f : K ↪ I) (D : K → Digraph V) (i : I) : Digraph V :=
  ⟨fun x y => ∃ k, f k = i ∧ (D k).Adj x y⟩

theorem place_path_pieces_at (f : K ↪ I) (D : K → Digraph V) (k : K) :
    placePathPieces f D (f k) = D k := by
  ext x y
  change (∃ j, f j = f k ∧ (D j).Adj x y) ↔ _
  exact ⟨fun ⟨j,hj,he⟩ => f.injective hj ▸ he,fun he => ⟨k,rfl,he⟩⟩

private theorem place_path_pieces_off_range (f : K ↪ I) (D : K → Digraph V) {i : I}
    (hi : i ∉ Set.range f) : placePathPieces f D i = ⊥ := by
  ext x y
  exact ⟨fun ⟨k,hk,_⟩ => hi ⟨k,hk⟩,False.elim⟩

private theorem isDirectedPathSystem_bot : IsDirectedPathSystem (⊥ : Digraph V) := by
  refine ⟨?_,fun h _ => False.elim h,fun h _ => False.elim h⟩
  intro x h
  obtain ⟨_,he,_⟩ := Relation.TransGen.head'_iff.mp h
  exact he

private theorem place_pieces_path_system (f : K ↪ I) (D : K → Digraph V)
    (hD : ∀ k, IsDirectedPathSystem (D k)) (i : I) :
    IsDirectedPathSystem (placePathPieces f D i) := by
  classical
  by_cases hi : i ∈ Set.range f
  · obtain ⟨k,rfl⟩ := hi
    rw [place_path_pieces_at]
    exact hD k
  · rw [place_path_pieces_off_range f D hi]
    exact isDirectedPathSystem_bot

private theorem place_pieces_unique_owner (f : K ↪ I) (D : K → Digraph V)
    {x : V} (r : V → V → V × V)
    (h : ∃! k, ∃ y, (D k).Adj (r x y).1 (r x y).2) :
    ∃! i, ∃ y, (placePathPieces f D i).Adj (r x y).1 (r x y).2 := by
  obtain ⟨k,⟨y,hy⟩,hk⟩ := h
  refine ⟨f k,⟨y,k,rfl,hy⟩,?_⟩
  rintro i ⟨z,l,hl,hz⟩
  exact hl.symm.trans (congrArg f (hk l ⟨z,hz⟩))

private theorem place_pieces_arc_owner {T : Type*} (f : T ↪ I) (D : T → Digraph V)
    (hD : ∀ k l {x y}, (D k).Adj x y → (D l).Adj x y → k = l)
    (i j : I) {x y : V} (hi : (placePathPieces f D i).Adj x y)
    (hj : (placePathPieces f D j).Adj x y) : i = j := by
  obtain ⟨k,rfl,hk⟩ := hi
  obtain ⟨l,rfl,hl⟩ := hj
  exact congrArg f (hD k l hk hl)

theorem exists_path_partition_of_assigned_pieces {L : Type*}
    (H : K → Digraph V) (A : L → Digraph V) (C : I → Digraph V) (Z : Finset V)
    (e : K ↪ I) (a : L ↪ I)
    (hSlots : ∀ k l, e k ≠ a l)
    (hH : ∀ k, IsDirectedPathSystem (H k)) (hA : ∀ l, IsDirectedPathSystem (A l))
    (hC : ∀ i, IsDirectedPathSystem (C i)) (hCover : ∀ i, CoversExceptional (C i) Z)
    (hSide : ∀ k, (∀ {x y}, (H k).Adj x y → x ∈ Z ∧ y ∉ Z) ∨
      (∀ {x y}, (H k).Adj x y → x ∉ Z ∧ y ∈ Z))
    (hInternal : ∀ i {x y}, (C i).Adj x y → x ∈ Z → y ∉ Z)
    (hFreshH : ∀ k v, v ∉ Z → IncidentTo (H k) v → ¬ IncidentTo (C (e k)) v)
    (hFreshA : ∀ l v, IncidentTo (A l) v → ¬ IncidentTo (C (a l)) v)
    (hNormalOut : ∀ i j {x y z}, x ∉ Z →
      (exceptionalPart (C i) Z).Adj x y → (exceptionalPart (C j) Z).Adj x z → y = z)
    (hNormalIn : ∀ i j {x y z}, x ∉ Z →
      (exceptionalPart (C i) Z).Adj y x → (exceptionalPart (C j) Z).Adj z x → y = z)
    (hNormalMatch : ∀ i j {x y z}, x ∉ Z →
      (exceptionalPart (C i) Z).Adj y x → ¬ (exceptionalPart (C j) Z).Adj x z)
    (hHOut : ∀ x ∈ Z, ∃! k, ∃ y, (H k).Adj x y)
    (hHIn : ∀ x ∈ Z, ∃! k, ∃ y, (H k).Adj y x)
    (hHDis : ∀ k l {x y}, (H k).Adj x y → (H l).Adj x y → k = l)
    (hADis : ∀ k l {x y}, (A k).Adj x y → (A l).Adj x y → k = l)
    (hCDis : ∀ i j {x y}, (C i).Adj x y → (C j).Adj x y → i = j)
    (hHADis : ∀ k l {x y}, (H k).Adj x y → ¬ (A l).Adj x y)
    (hHCDis : ∀ k j {x y}, (H k).Adj x y → ¬ (C j).Adj x y)
    (hACDis : ∀ l j {x y}, (A l).Adj x y → ¬ (C j).Adj x y) :
    ∃ Q : Option I → Digraph V,
      (∀ i, IsDirectedPathSystem (Q i) ∧ CoversExceptional (Q i) Z) ∧
      (∀ x y, ((∃ k, (H k).Adj x y) ∨ (∃ l, (A l).Adj x y) ∨ (∃ i, (C i).Adj x y)) ↔
         ∃! i, (Q i).Adj x y) ∧
      (∀ i, Q (some i) ≤ placePathPieces a A i ⊔ placePathPieces e H i ⊔ C i) ∧
      (∀ x y, (Q none).Adj x y → (x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z)) ∧
      (∀ x y, (Q none).Adj x y → ∃ k, (C (e k)).Adj x y ∧
        ((∃ w, (H k).Adj x w) ∨ (∃ w, (H k).Adj w y))) := by
  classical
  let H' := placePathPieces e H
  let A' := placePathPieces a A
  have hSide' (i : I) :
      (∀ {x y}, (H' i).Adj x y → x ∈ Z ∧ y ∉ Z) ∨
      (∀ {x y}, (H' i).Adj x y → x ∉ Z ∧ y ∈ Z) := by
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k,rfl⟩ := hi
      change (∀ {x y}, (placePathPieces e H (e k)).Adj x y → x ∈ Z ∧ y ∉ Z) ∨
        (∀ {x y}, (placePathPieces e H (e k)).Adj x y → x ∉ Z ∧ y ∈ Z)
      rw [place_path_pieces_at]
      exact hSide k
    · left
      intro x y he
      obtain ⟨k,hk,_⟩ := he
      exact (hi ⟨k,hk⟩).elim
  have hFresh' (i : I) (v : V) (hv : v ∉ Z) (he : IncidentTo (H' i) v) :
      ¬ IncidentTo (C i) v := by
    rcases he with ⟨w,k,rfl,hw⟩ | ⟨w,k,rfl,hw⟩
    · exact hFreshH k v hv (Or.inl ⟨w,hw⟩)
    · exact hFreshH k v hv (Or.inr ⟨w,hw⟩)
  have hOrd' (i : I) (v : V) (hv : IncidentTo (A' i) v) :
      ¬ IncidentTo (H' i) v ∧ ¬ IncidentTo (C i) v := by
    obtain ⟨l,hl,he⟩ : ∃ l, a l = i ∧ IncidentTo (A l) v := by
      rcases hv with ⟨w,l,hl,hw⟩ | ⟨w,l,hl,hw⟩
      · exact ⟨l,hl,Or.inl ⟨w,hw⟩⟩
      · exact ⟨l,hl,Or.inr ⟨w,hw⟩⟩
    subst i
    refine ⟨?_,hFreshA l v he⟩
    rintro (⟨_,k,hk,_⟩ | ⟨_,k,hk,_⟩) <;> exact hSlots k l hk
  obtain ⟨Q,hQ,hPartition,hSup,hCross,hResidual⟩ := exists_path_partition_of_prepared_pieces
    H' A' C Z (place_pieces_path_system e H hH) (place_pieces_path_system a A hA)
    hC hCover hSide' hInternal hFresh' hOrd' hNormalOut hNormalIn hNormalMatch
    (fun x hx => place_pieces_unique_owner e H (fun x y => (x,y)) (hHOut x hx))
    (fun x hx => place_pieces_unique_owner e H (fun x y => (y,x)) (hHIn x hx))
    (place_pieces_arc_owner e H hHDis) (place_pieces_arc_owner a A hADis) hCDis
    (fun _ _ _ _ ⟨k,_,hk⟩ ⟨l,_,hl⟩ => hHADis k l hk hl)
    (fun _ _ _ _ ⟨k,_,hk⟩ hc => hHCDis k _ hk hc)
    (fun _ _ _ _ ⟨l,_,hl⟩ hc => hACDis l _ hl hc)
  refine ⟨Q,hQ,?_,hSup,hCross,?_⟩
  · intro x y
    rw [←hPartition]
    constructor
    · rintro (⟨k,hk⟩ | ⟨l,hl⟩ | ⟨i,hi⟩)
      · exact ⟨e k,Or.inl ⟨k,rfl,hk⟩⟩
      · exact ⟨a l,Or.inr (Or.inl ⟨l,rfl,hl⟩)⟩
      · exact ⟨i,Or.inr (Or.inr hi)⟩
    · rintro ⟨i,⟨k,_,hk⟩ | ⟨l,_,hl⟩ | hi⟩
      · exact Or.inl ⟨k,hk⟩
      · exact Or.inr (Or.inl ⟨l,hl⟩)
      · exact Or.inr (Or.inr ⟨i,hi⟩)
  · intro x y h
    obtain ⟨i,hc,⟨w,k,rfl,hk⟩ | ⟨w,k,rfl,hk⟩⟩ := (hResidual x y).mp h
    · exact ⟨k,hc,Or.inl ⟨w,hk⟩⟩
    · exact ⟨k,hc,Or.inr ⟨w,hk⟩⟩

end OverfullWork.DirectedRobustExpansion
