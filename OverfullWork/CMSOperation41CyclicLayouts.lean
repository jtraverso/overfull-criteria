module

public import OverfullWork.CMSOperation41Invariants
public import OverfullWork.DirectedReserveStitching
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section


/-! The cyclic layout of CMS Operation 4.1 and concatenation of its
individual replacements. Distinct cyclic positions remain distinct
occurrences, including the case of two opposite edges. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset SimpleGraph
open scoped Classical

variable {V : Type*}

noncomputable def cyclicLayout {n : ℕ} (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ V)
    (fixed : Finset (Fin (n+1))) (isolated : Finset V) : Layout V (Fin (n+1)) where
  boundary := univ.image w ∪ isolated
  source := w
  target := fun i => w (finRotate (n+1) i)
  fixed := fixed
  ends := by
    intro i
    refine ⟨mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩),
      mem_union_left _ (mem_image.mpr ⟨_,mem_univ _,rfl⟩),?_⟩
    intro he
    have hi := w.injective he
    have hAll := support_finRotate_of_le hn
    have hMem : i ∈ (finRotate (n+1)).support := by rw [hAll]; exact mem_univ _
    exact (Equiv.Perm.mem_support.mp hMem) hi.symm

theorem cyclicLayout_boundary_card_le {n : ℕ} (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ V)
    (fixed : Finset (Fin (n+1))) (isolated : Finset V) :
    (cyclicLayout hn w fixed isolated).boundary.card ≤ (n+1)+isolated.card := by
  exact (card_union_le _ _).trans (by rw [card_image_of_injective _ w.injective,card_univ,Fintype.card_fin])

/-- The successive boundary vertices with each chosen interior inserted. -/
def openCycleWord {n : ℕ} (w : Fin (n+1) → V) (body : Fin (n+1) → List V) : List V :=
  (List.ofFn (id : Fin (n+1) → Fin (n+1))).flatMap (fun i => w i :: body i)

theorem openCycleWord_length {n : ℕ} (w : Fin (n+1) → V) (body : Fin (n+1) → List V) :
    (openCycleWord w body).length = n+1+∑ i,(body i).length := by
  rw [openCycleWord,List.length_flatMap,List.map_ofFn,List.sum_ofFn]
  simp [Function.comp_def,sum_add_distrib,Nat.add_comm]

/-- Traverse the cyclic positions in order and insert the specified
interiors. The paths may come from the robust host or from the
original vertices used to replace a prescribed auxiliary edge. -/
theorem open_cycle_word_of_disjoint_interiors (R : V → V → Prop) {n : ℕ} (w : Fin (n+1) ↪ V)
    (body : Fin (n+1) → List V)
    (hPath : ∀ i, (w i :: body i ++ [w (finRotate (n+1) i)]).IsChain R)
    (hSimple : ∀ i, (w i :: body i).Nodup)
    (hOutside : ∀ i x, x ∈ body i → x ∉ Set.range w)
    (hDisjoint : ∀ i j, i ≠ j → List.Disjoint (body i) (body j)) :
    let T := openCycleWord w body
    T.Nodup ∧ T.head? = some (w 0) ∧ (T ++ [w 0]).IsChain R ∧
      ∀ x, x ∈ T ↔ x ∈ Set.range w ∨ ∃ i, x ∈ body i := by
  let A (i : Fin (n+1)) := w i :: body i
  let last (i : Fin (n+1)) := (A i).getLast (by simp [A])
  let order := List.ofFn (id : Fin (n+1) → Fin (n+1))
  let T := order.flatMap A
  let D : Digraph V := ⟨R⟩
  have hA (i : Fin (n+1)) : (A i).head? = some (w i) := rfl
  have hB (i : Fin (n+1)) : (A i).getLast? = some (last i) :=
    List.getLast?_eq_getLast_of_ne_nil (by simp [A])
  have hChain (i : Fin (n+1)) : (A i).IsChain D.Adj := (hPath i).left_of_append
  have hNext (i : Fin (n+1)) : D.Adj (last i) (w (finRotate (n+1) i)) :=
    (hPath i).rel_getLast_head_of_append (by simp) (by simp)
  have hBlockDis (i j : Fin (n+1)) (hij : i ≠ j) : List.Disjoint (A i) (A j) := by
    intro x hx hy
    rcases List.mem_cons.mp hx with rfl|hx
    · rcases List.mem_cons.mp hy with he|hy
      · exact hij (w.injective he)
      · exact (hOutside j _ hy) ⟨i,rfl⟩
    · rcases List.mem_cons.mp hy with rfl|hy
      · exact (hOutside i _ hx) ⟨j,rfl⟩
      · exact hDisjoint i j hij hx hy
  have hN : T.Nodup :=
    List.nodup_flatMap.mpr ⟨fun i _ => hSimple i,
      (List.nodup_ofFn.mpr Function.injective_id).imp (fun h => hBlockDis _ _ h)⟩
  have hHead : T.head? = some (w 0) := by
    have hOrd : order = 0 :: List.ofFn (fun i : Fin n => i.succ) := List.ofFn_succ
    change (order.flatMap A).head? = _
    rw [hOrd,List.flatMap_cons,List.head?_append_of_ne_nil _ (by simp [A])]
    exact hA 0
  have hClose : (T ++ [w 0]).IsChain R :=
    DirectedReserveStitching.chain_of_blocks D A w last hA hB hChain 0 order
      (DirectedRungCycle.rotate_order hNext)
  refine ⟨hN,hHead,hClose,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hi with hi|hi
    · exact Or.inl ⟨i,hi.symm⟩
    · exact Or.inr ⟨i,hi⟩
  · rintro (⟨i,rfl⟩|⟨i,hi⟩)
    · exact List.mem_flatMap.mpr ⟨i,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_cons_self ..⟩
    · exact List.mem_flatMap.mpr ⟨i,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_cons_of_mem _ hi⟩

theorem cyclic_word_of_disjoint_interiors (R : V → V → Prop) {n : ℕ} (w : Fin (n+1) ↪ V)
    (body : Fin (n+1) → List V)
    (hPath : ∀ i, (w i :: body i ++ [w (finRotate (n+1) i)]).IsChain R)
    (hSimple : ∀ i, (w i :: body i).Nodup)
    (hOutside : ∀ i x, x ∈ body i → x ∉ Set.range w)
    (hDisjoint : ∀ i j, i ≠ j → List.Disjoint (body i) (body j)) :
    ∃ T : List V, T.Nodup ∧ T.head? = some (w 0) ∧ (T ++ [w 0]).IsChain R ∧
      ∀ x, x ∈ T ↔ x ∈ Set.range w ∨ ∃ i, x ∈ body i := by
  exact ⟨openCycleWord w body,open_cycle_word_of_disjoint_interiors R w body hPath hSimple hOutside hDisjoint⟩

theorem Realization.open_word_configuration {n : ℕ} (hn : 2 ≤ n+1)
    (w : Fin (n+1) ↪ V) (fixed : Finset (Fin (n+1))) (isolated : Finset V)
    (hIso : ∀ i, w i ∉ isolated) {D : Digraph V}
    (P : Realization D (cyclicLayout hn w fixed isolated)) :
    let T := openCycleWord w P.interior
    T.Nodup ∧ T.head? = some (w 0) ∧
      (T ++ [w 0]).IsChain (fun x y => D.Adj x y ∨ ∃ i ∈ fixed, x = w i ∧ y = w (finRotate (n+1) i)) ∧
      ∀ x, x ∈ T ↔ x ∉ isolated := by
  obtain ⟨hN,hHead,hClose,hMem⟩ := open_cycle_word_of_disjoint_interiors
    (fun x y => D.Adj x y ∨ ∃ i ∈ fixed, x = w i ∧ y = w (finRotate (n+1) i)) w P.interior
    (fun i => by
      by_cases hi : i ∈ fixed
      · rw [P.fixed_empty i hi]
        exact List.isChain_cons_cons.mpr ⟨Or.inr ⟨i,hi,rfl,rfl⟩,.singleton _⟩
      · exact (P.flexible_chain i hi).imp (fun _ _ h => Or.inl h))
    (fun i => (P.simple i).sublist (List.sublist_append_left _ _))
    (fun i x hx h => by
      obtain ⟨j,rfl⟩ := h
      exact P.outside i _ hx (mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)))
    P.unique
  refine ⟨hN,hHead,hClose,?_⟩
  intro x
  rw [hMem]
  constructor
  · rintro (⟨i,rfl⟩|⟨i,hi⟩)
    · exact hIso i
    · exact fun h => P.outside i _ hi (mem_union_right _ h)
  · intro hx
    by_cases hIn : x ∈ Set.range w
    · exact Or.inl hIn
    · right
      apply P.spans x
      change x ∉ (univ : Finset (Fin (n+1))).image w ∪ isolated
      simp only [mem_union,mem_image,mem_univ,true_and,not_or]
      exact ⟨hIn,hx⟩

theorem Realization.cyclic_configuration {n : ℕ} (hn : 2 ≤ n+1)
    (w : Fin (n+1) ↪ V) (fixed : Finset (Fin (n+1))) (isolated : Finset V)
    (hIso : ∀ i,w i ∉ isolated) {D : Digraph V}
    (P : Realization D (cyclicLayout hn w fixed isolated)) :
    ∃ T : List V,T.Nodup ∧ T.head? = some (w 0) ∧
      (T ++ [w 0]).IsChain (fun x y => D.Adj x y ∨ ∃ i ∈ fixed,x = w i ∧ y = w (finRotate (n+1) i)) ∧
      ∀ x,x ∈ T ↔ x ∉ isolated :=
  ⟨openCycleWord w P.interior,P.open_word_configuration hn w fixed isolated hIso⟩

theorem Realization.cyclic_core_word_length [Fintype V]
    {n : ℕ} (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ V) (fixed : Finset (Fin (n+1)))
    (isolated : Finset V) (hIso : ∀ i,w i ∉ isolated) {D : Digraph V}
    (P : Realization D (cyclicLayout hn w fixed isolated)) :
    n+1+∑ i,(P.interior i).length = Fintype.card V-isolated.card := by
  obtain ⟨hNd,_,_,hMem⟩ := P.open_word_configuration hn w fixed isolated hIso
  let T := openCycleWord w P.interior
  have hSet : T.toFinset = isolatedᶜ := by
    ext v
    rw [List.mem_toFinset,mem_compl]
    exact hMem v
  rw [←openCycleWord_length w P.interior,←List.toFinset_card_of_nodup hNd]
  change T.toFinset.card = _
  rw [hSet,card_compl]

end OverfullWork.DirectedSpanningConfiguration
