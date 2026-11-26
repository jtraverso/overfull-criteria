module

public import OverfullWork.ChenShanTripartiteCompletion
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Set.Card

@[expose] public section

namespace OverfullWork.ChenShan

variable {I : Type*}

abbrev AbsorberTriangle (I : Type*) := (I ⊕ I) × (I ⊕ I) × Option I

def cycleAbsorberBefore (s : Equiv.Perm I) (i : Fin 3 × I) : AbsorberTriangle I :=
  match i.1 with
  | 0 => (.inl (s i.2), .inr i.2, none)
  | 1 => (.inr i.2, .inr i.2, some i.2)
  | 2 => (.inr i.2, .inl i.2, none)

def cycleAbsorberAfter (s : Equiv.Perm I) (i : Fin 4 × I) : AbsorberTriangle I :=
  match i.1 with
  | 0 => (.inl i.2, .inl i.2, none)
  | 1 => (.inl (s i.2), .inr i.2, some i.2)
  | 2 => (.inr i.2, .inr i.2, none)
  | 3 => (.inr i.2, .inl i.2, some i.2)

def absorberAB (p : AbsorberTriangle I) := (p.1, p.2.1)
def absorberAW (p : AbsorberTriangle I) := (p.1, p.2.2)
def absorberBW (p : AbsorberTriangle I) := (p.2.1, p.2.2)

theorem cycleAbsorberBefore_injective (s : Equiv.Perm I) :
    Function.Injective (absorberAB ∘ cycleAbsorberBefore s) ∧
      Function.Injective (absorberAW ∘ cycleAbsorberBefore s) ∧
      Function.Injective (absorberBW ∘ cycleAbsorberBefore s) := by
  refine ⟨?_,?_,?_⟩ <;> rintro ⟨i,j⟩ ⟨k,l⟩ h <;>
    fin_cases i <;> fin_cases k <;>
    simp_all [absorberAB, absorberAW, absorberBW, cycleAbsorberBefore]

theorem cycleAbsorberAfter_injective (s : Equiv.Perm I) :
    Function.Injective (absorberAB ∘ cycleAbsorberAfter s) ∧
      Function.Injective (absorberAW ∘ cycleAbsorberAfter s) ∧
      Function.Injective (absorberBW ∘ cycleAbsorberAfter s) := by
  refine ⟨?_,?_,?_⟩ <;> rintro ⟨i,j⟩ ⟨k,l⟩ h <;>
    fin_cases i <;> fin_cases k <;>
    simp_all [absorberAB, absorberAW, absorberBW, cycleAbsorberAfter]

/-- Adding the cycle contributes precisely its three classes of edges
to the projection sets of the absorber. -/
theorem cycleAbsorber_projection_ranges (s : Equiv.Perm I) :
    Set.range (absorberAB ∘ cycleAbsorberAfter s) =
      Set.range (absorberAB ∘ cycleAbsorberBefore s) ∪ Set.range (fun i : I => (Sum.inl i, Sum.inl i)) ∧
    Set.range (absorberAW ∘ cycleAbsorberAfter s) =
      Set.range (absorberAW ∘ cycleAbsorberBefore s) ∪ Set.range (fun i : I => (Sum.inl (s i), some i)) ∧
    Set.range (absorberBW ∘ cycleAbsorberAfter s) =
      Set.range (absorberBW ∘ cycleAbsorberBefore s) ∪ Set.range (fun i : I => (Sum.inl i, some i)) := by
  refine ⟨?_,?_,?_⟩
  · ext p
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      fin_cases i
      · exact Or.inr ⟨j,rfl⟩
      · exact Or.inl ⟨(0,j),rfl⟩
      · exact Or.inl ⟨(1,j),rfl⟩
      · exact Or.inl ⟨(2,j),rfl⟩
    · rintro (⟨⟨i,j⟩,rfl⟩ | ⟨j,rfl⟩)
      · fin_cases i
        · exact ⟨(1,j),rfl⟩
        · exact ⟨(2,j),rfl⟩
        · exact ⟨(3,j),rfl⟩
      · exact ⟨(0,j),rfl⟩
  · ext p
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      fin_cases i
      · obtain ⟨l,hl⟩ := s.surjective j
        exact Or.inl ⟨(0,l),by simpa [Function.comp_def, absorberAW, cycleAbsorberBefore,
          cycleAbsorberAfter] using hl⟩
      · exact Or.inr ⟨j,rfl⟩
      · exact Or.inl ⟨(2,j),rfl⟩
      · exact Or.inl ⟨(1,j),rfl⟩
    · rintro (⟨⟨i,j⟩,rfl⟩ | ⟨j,rfl⟩)
      · fin_cases i
        · exact ⟨(0,s j),rfl⟩
        · exact ⟨(3,j),rfl⟩
        · exact ⟨(2,j),rfl⟩
      · exact ⟨(1,j),rfl⟩
  · ext p
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      fin_cases i
      · exact Or.inl ⟨(2,j),rfl⟩
      · exact Or.inl ⟨(1,j),rfl⟩
      · exact Or.inl ⟨(0,j),rfl⟩
      · exact Or.inr ⟨j,rfl⟩
    · rintro (⟨⟨i,j⟩,rfl⟩ | ⟨j,rfl⟩)
      · fin_cases i
        · exact ⟨(2,j),rfl⟩
        · exact ⟨(1,j),rfl⟩
        · exact ⟨(0,j),rfl⟩
      · exact ⟨(3,j),rfl⟩


private theorem decomposition_of_absorber_projections {K : Type*} (f : K → AbsorberTriangle I)
    (hAB : Function.Injective (absorberAB ∘ f)) (hAW : Function.Injective (absorberAW ∘ f))
    (hBW : Function.Injective (absorberBW ∘ f)) :
    Nonempty (TripartiteTriangleDecomposition
      (fun a b => (a,b) ∈ Set.range (absorberAB ∘ f))
      (fun a w => (a,w) ∈ Set.range (absorberAW ∘ f))
      (fun b w => (b,w) ∈ Set.range (absorberBW ∘ f))) := by
  refine ⟨⟨fun a b w => (a,b,w) ∈ Set.range f, ?_, ?_, ?_, ?_⟩⟩
  · rintro a b w ⟨i,hi⟩
    exact ⟨⟨i, congrArg absorberAB hi⟩, ⟨i, congrArg absorberAW hi⟩, ⟨i, congrArg absorberBW hi⟩⟩
  · rintro a b ⟨i,hi⟩
    have ha : (f i).1 = a := congrArg Prod.fst hi
    have hb : (f i).2.1 = b := congrArg Prod.snd hi
    refine ⟨(f i).2.2, ⟨i, by simp only [← ha, ← hb]⟩, ?_⟩
    rintro w ⟨j,hj⟩
    have he : j = i := hAB ((congrArg absorberAB hj).trans hi.symm)
    rw [he] at hj
    exact (congrArg (fun p => p.2.2) hj).symm
  · rintro a w ⟨i,hi⟩
    have ha : (f i).1 = a := congrArg Prod.fst hi
    have hw : (f i).2.2 = w := congrArg Prod.snd hi
    refine ⟨(f i).2.1, ⟨i, by simp only [← ha, ← hw]⟩, ?_⟩
    rintro b ⟨j,hj⟩
    have he : j = i := hAW ((congrArg absorberAW hj).trans hi.symm)
    rw [he] at hj
    exact (congrArg (fun p => p.2.1) hj).symm
  · rintro b w ⟨i,hi⟩
    have hb : (f i).2.1 = b := congrArg Prod.fst hi
    have hw : (f i).2.2 = w := congrArg Prod.snd hi
    refine ⟨(f i).1, ⟨i, by simp only [← hb, ← hw]⟩, ?_⟩
    rintro a ⟨j,hj⟩
    have he : j = i := hBW ((congrArg absorberBW hj).trans hi.symm)
    rw [he] at hj
    exact (congrArg Prod.fst hj).symm

/-- The cycle and its absorber are edge-disjoint on all three pairs
of vertex classes. -/
theorem cycleAbsorber_disjoint_cycle (s : Equiv.Perm I) :
    Disjoint (Set.range (absorberAB ∘ cycleAbsorberBefore s)) (Set.range (fun i : I => (Sum.inl i, Sum.inl i))) ∧
    Disjoint (Set.range (absorberAW ∘ cycleAbsorberBefore s)) (Set.range (fun i : I => (Sum.inl (s i), some i))) ∧
    Disjoint (Set.range (absorberBW ∘ cycleAbsorberBefore s)) (Set.range (fun i : I => (Sum.inl i, some i))) := by
  refine ⟨?_,?_,?_⟩ <;> apply Set.disjoint_left.mpr <;>
    rintro p ⟨⟨row,i⟩,rfl⟩ ⟨j,h⟩ <;> fin_cases row <;>
    simp [absorberAB, absorberAW, absorberBW, cycleAbsorberBefore] at h

/-- Both the absorber and the absorber plus the cycle have exact triangle
decompositions, with the two triangle families of Lemma 4.5. -/
theorem cycleAbsorber_decompositions (s : Equiv.Perm I) :
    Nonempty (TripartiteTriangleDecomposition
      (fun a b => (a,b) ∈ Set.range (absorberAB ∘ cycleAbsorberBefore s))
      (fun a w => (a,w) ∈ Set.range (absorberAW ∘ cycleAbsorberBefore s))
      (fun b w => (b,w) ∈ Set.range (absorberBW ∘ cycleAbsorberBefore s))) ∧
    Nonempty (TripartiteTriangleDecomposition
      (fun a b => (a,b) ∈ Set.range (absorberAB ∘ cycleAbsorberBefore s) ∪
        Set.range (fun i : I => (Sum.inl i, Sum.inl i)))
      (fun a w => (a,w) ∈ Set.range (absorberAW ∘ cycleAbsorberBefore s) ∪
        Set.range (fun i : I => (Sum.inl (s i), some i)))
      (fun b w => (b,w) ∈ Set.range (absorberBW ∘ cycleAbsorberBefore s) ∪
        Set.range (fun i : I => (Sum.inl i, some i)))) := by
  obtain ⟨h0ab,h0aw,h0bw⟩ := cycleAbsorberBefore_injective s
  obtain ⟨h1ab,h1aw,h1bw⟩ := cycleAbsorberAfter_injective s
  obtain ⟨hab, haw, hbw⟩ := cycleAbsorber_projection_ranges s
  refine ⟨decomposition_of_absorber_projections _ h0ab h0aw h0bw, ?_⟩
  simpa only [← hab, ← haw, ← hbw] using decomposition_of_absorber_projections _ h1ab h1aw h1bw


/-- The nine edges per cycle index are distinct. -/
theorem cycleAbsorber_edge_count [Fintype I] (s : Equiv.Perm I) :
    (Set.range (absorberAB ∘ cycleAbsorberBefore s)).ncard +
      (Set.range (absorberAW ∘ cycleAbsorberBefore s)).ncard +
      (Set.range (absorberBW ∘ cycleAbsorberBefore s)).ncard = 9 * Fintype.card I := by
  obtain ⟨hab,haw,hbw⟩ := cycleAbsorberBefore_injective s
  rw [Set.ncard_range_of_injective hab, Set.ncard_range_of_injective haw,
    Set.ncard_range_of_injective hbw, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
  omega

/-- An absorber edge has a new endpoint: a right summand in one
of the first two classes, or the auxiliary color `none`. -/
theorem cycleAbsorber_edges_touch_auxiliary (s : Equiv.Perm I) :
    (∀ i j : I, (Sum.inl i, Sum.inl j) ∉ Set.range (absorberAB ∘ cycleAbsorberBefore s)) ∧
    (∀ i j : I, (Sum.inl i, some j) ∉ Set.range (absorberAW ∘ cycleAbsorberBefore s)) ∧
    (∀ i j : I, (Sum.inl i, some j) ∉ Set.range (absorberBW ∘ cycleAbsorberBefore s)) := by
  refine ⟨?_,?_,?_⟩ <;> rintro i j ⟨⟨row,w⟩,h⟩ <;> fin_cases row <;>
    simp [absorberAB, absorberAW, absorberBW, cycleAbsorberBefore] at h

end OverfullWork.ChenShan
