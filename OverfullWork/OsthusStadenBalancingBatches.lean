module

public import OverfullWork.OsthusStadenBalancingArcs

@[expose] public section


/-! Use every H2 reserve pair for all layers, within a common
incoming-degree budget, with no repeated physical arc. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

def digraphOfArcs {V : Type*} (S : Finset (V × V)) : Digraph V :=
  ⟨fun x y => (x,y) ∈ S⟩

theorem digraphOfArcs_inDegree {V : Type*} [Fintype V] (S : Finset (V × V)) (v : V) :
    inDegree (digraphOfArcs S) v = (S.filter (fun e => e.2 = v)).card := by
  let e : V ↪ V × V := ⟨fun x => (x,v),fun _ _ h => congrArg Prod.fst h⟩
  have h : (((univ : Finset V).filter (fun x => (x,v) ∈ S)).map e) =
      S.filter (fun a => a.2 = v) := by
    ext a
    constructor
    · intro ha
      obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
      exact mem_filter.mpr ⟨(mem_filter.mp hx).2,rfl⟩
    · intro ha
      rcases a with ⟨x,y⟩
      obtain ⟨he,rfl⟩ := mem_filter.mp ha
      exact mem_map.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,he⟩,rfl⟩
  rw [←h,card_map]
  unfold inDegree inNeighbours
  congr 1
  ext x
  simp only [mem_filter]
  exact Iff.rfl

theorem digraphOfArcs_outDegree {V : Type*} [Fintype V] (S : Finset (V × V)) (v : V) :
    outDegree (digraphOfArcs S) v = (S.filter (fun e => e.1 = v)).card := by
  let e : V ↪ V × V := ⟨fun x => (v,x),fun _ _ h => congrArg Prod.snd h⟩
  have h : (((univ : Finset V).filter (fun x => (v,x) ∈ S)).map e) =
      S.filter (fun a => a.1 = v) := by
    ext a
    constructor
    · intro ha
      obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
      exact mem_filter.mpr ⟨(mem_filter.mp hx).2,rfl⟩
    · intro ha
      rcases a with ⟨y,x⟩
      obtain ⟨he,rfl⟩ := mem_filter.mp ha
      exact mem_map.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,he⟩,rfl⟩
  rw [←h,card_map]
  unfold outDegree
  congr 1
  ext x
  simp only [mem_filter]
  exact Iff.rfl

/-- Realize all layers on one base H2 pair. At step `j`, the union of
the previously chosen arcs has per-vertex incoming degree at most the
number of earlier layers times `cap`. -/
theorem exists_balancing_batches {V I : Type*} [Fintype V] [Fintype I]
    (D : Digraph V) (A B : Finset V) (A' B' : I → Finset V) (ε d : ℝ)
    (q : I → ℕ) (cap loss a b L : ℕ)
    (hR : DirectedRegularPairs.IsUniform D ε A B)
    (hD : d ≤ DirectedRegularPairs.density D A B)
    (hA : ∀ i, A' i ⊆ A) (hB : ∀ i, B' i ⊆ B)
    (ha : 0 < a) (hb : 0 < b) (hcap : 0 < cap) (hLoss : ∀ i, q i ≤ cap*loss)
    (hSizeA : ∀ i, a+loss ≤ (A' i).card) (hSizeB : ∀ i, b+loss ≤ (B' i).card)
    (hLargeA : (A.card:ℝ)*ε ≤ a) (hLargeB : (B.card:ℝ)*ε ≤ b)
    (hUsed : (Fintype.card I-1)*cap ≤ L)
    (hCoeff : 0 ≤ d-ε) (hSlack : 0 ≤ (d-ε)*(a:ℝ)-(L:ℝ))
    (hNeed : ∀ i, (q i:ℝ) ≤ ((d-ε)*(a:ℝ)-(L:ℝ))*(b:ℝ)) :
    ∃ C : I → Finset (V × V),
      (∀ i, C i ⊆ arcRectangle D (A' i) (B' i) ∧ (C i).card = q i ∧
        (∀ x, ((C i).filter (fun e => e.1 = x)).card ≤ cap) ∧
        ∀ y, ((C i).filter (fun e => e.2 = y)).card ≤ cap) ∧
      ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
  suffices h : ∀ T : Finset I, ∃ C : I → Finset (V × V),
      (∀ i ∈ T, C i ⊆ arcRectangle D (A' i) (B' i) ∧ (C i).card = q i ∧
        (∀ x, ((C i).filter (fun e => e.1 = x)).card ≤ cap) ∧
        ∀ y, ((C i).filter (fun e => e.2 = y)).card ≤ cap) ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (C i) (C j) by
    obtain ⟨C,hC,hDis⟩ := h univ
    exact ⟨C,fun i => hC i (mem_univ _),fun i j => hDis i (mem_univ _) j (mem_univ _)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅,by simp,by simp⟩
  | @insert i T hi ih =>
    obtain ⟨C,hC,hDis⟩ := ih
    let used := digraphOfArcs (T.biUnion C)
    have hT : T.card ≤ Fintype.card I-1 := by
      have h := card_le_univ (insert i T)
      rw [card_insert_of_notMem hi] at h
      omega
    have hBound (v : V) : inDegree used v ≤ L := by
      unfold used
      rw [digraphOfArcs_inDegree,filter_biUnion]
      calc
        _ ≤ ∑ j ∈ T,((C j).filter (fun e => e.2 = v)).card := card_biUnion_le
        _ ≤ ∑ _ ∈ T,cap := sum_le_sum (fun j hj => (hC j hj).2.2.2 v)
        _ = T.card*cap := by simp
        _ ≤ L := (Nat.mul_le_mul_right _ hT).trans hUsed
    obtain ⟨E,hE,hCard,hOut,hIn⟩ := exists_sparse_balancing_arcs D used A B (A' i) (B' i) ε d
      (q i) cap loss a b L hR hD (hA i) (hB i) ha hb hcap (hLoss i) (hSizeA i) (hSizeB i)
      hLargeA hLargeB hBound hCoeff hSlack (hNeed i)
    have hEdge (e : V × V) (he : e ∈ E) :
        e.1 ∈ A' i ∧ e.2 ∈ B' i ∧ D.Adj e.1 e.2 ∧ e ∉ T.biUnion C := by
      have h := (mem_arcRectangle _ _ _ _).mp (hE he)
      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩
    have hEd : E ⊆ arcRectangle D (A' i) (B' i) := by
      intro e he
      obtain ⟨ha,hb,hd,_⟩ := hEdge e he
      exact (mem_arcRectangle _ _ _ _).mpr ⟨ha,hb,hd⟩
    have hEdis (j : I) (hj : j ∈ T) : Disjoint E (C j) := by
      rw [disjoint_left]
      intro e he he'
      exact (hEdge e he).2.2.2 (mem_biUnion.mpr ⟨j,hj,he'⟩)
    refine ⟨Function.update C i E,?_,?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using ⟨hEd,hCard,hOut,hIn⟩
      · have hj' : j ≠ i := fun he => hi (he ▸ hj)
        simpa only [Function.update_of_ne hj'] using hC j hj
    · intro j hj k hk hne
      by_cases hj' : j = i
      · subst j
        have hkT := (mem_insert.mp hk).resolve_left hne.symm
        simpa only [Function.update_self,Function.update_of_ne hne.symm] using hEdis k hkT
      · have hjT := (mem_insert.mp hj).resolve_left hj'
        by_cases hk' : k = i
        · subst k
          simpa only [Function.update_self,Function.update_of_ne hj'] using (hEdis j hjT).symm
        · have hkT := (mem_insert.mp hk).resolve_left hk'
          simpa only [Function.update_of_ne hj',Function.update_of_ne hk'] using hDis j hjT k hkT hne

end OverfullWork.DirectedRobustExpansion
