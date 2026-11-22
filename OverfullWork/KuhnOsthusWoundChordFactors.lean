module

public import OverfullWork.KuhnOsthusChordExceptionalIntervals
public import OverfullWork.KuhnOsthusWindingExceptionalDegrees

@[expose] public section


/-! Group the original exceptional factors into the rounds of Lemma 9.7. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V J : Type*} [Fintype V] [Fintype J]

set_option maxHeartbeats 600000 in
/-- The exceptional systems used in all chord rounds are the original
arcs of the winding factors. Their supports, balance and disjointness
follow from the same physical cells and boundary slots. -/
theorem wound_chord_factor_round_data {G : Digraph V} {r t f n m : ℕ}
    (Z : Finset V) (C : J × Fin (f*(n+1)) → Finset V) (c : ↥Zᶜ → Fin (f*(n+1)))
    (hf : 2 ≤ f) (hSize : ∀ j, (C j).card = m) (hOrd : ∀ j, Disjoint (C j) Z)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hCover : ∀ x ∉ Z, ∃ j, x ∈ C j)
    (hLabel : ∀ j (v : ↥Zᶜ), v.val ∈ C j → c v = j.2) :
    let U (j : J × Fin f) := univ.biUnion (fun i : Fin (n+1) => C (j.1,intervalPosition j.2 i))
    let S (j : J × Fin f) := C (j.1,intervalPosition j.2 (0 : Fin (n+1)))
    let next := (Equiv.refl J).prodCongr (finRotate f)
    ∀ F : Fin (r*t) → ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
    Pairwise (fun a b => Disjoint (⨆ j, (F a j).digraph) (⨆ j, (F b j).digraph)) →
    let cells (j : Fin f × J) := (U (j.2,j.1)).subtype (· ∈ Zᶜ)
    let D (a : Fin r) (i : Fin f × (J × Fin t)) := (F (finProdFinEquiv (a,i.2.2)) (i.2.1,i.1)).digraph
    (⨆ i : Fin r × (Fin f × (J × Fin t)), D i.1 i.2) = ⨆ a, ⨆ j, (F a j).digraph ∧
    Pairwise (fun i j : Fin r × (Fin f × (J × Fin t)) => Disjoint (D i.1 i.2) (D j.1 j.2)) ∧
    (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
    ∀ a i,
      IsDirectedPathSystem (D a i) ∧ CoversExceptional (D a i) Z ∧
      (∀ x y, (D a i).Adj x y → x ∈ Z → y ∉ Z) ∧
      let P := basicExceptionalPathSystem (D a i) Z
      finiteSatisfying (IncidentTo P) ⊆ cells (i.1,i.2.1) ∪ cells (finRotate f i.1,i.2.1) ∧
      (∀ j, (finiteSatisfying (fun v => c v = j ∧ IncidentTo P v)).card ≤ m) ∧
      ∀ j, (∑ p : Arc P, if c p.val.1 = j then (1:ℕ) else 0) =
        ∑ p : Arc P, if c p.val.2 = finRotate (f*(n+1)) j then (1:ℕ) else 0 := by
  classical
  intro U S next F hF cells D
  let : DecidableEq ↥Zᶜ := Classical.decEq _
  let : DecidableEq (Fin (f*(n+1))) := Classical.decEq _
  let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
  let X (j : J × Fin (f*(n+1))) := (C j).subtype (· ∈ Zᶜ)
  have hMap (j : J × Fin (f*(n+1))) : (X j).map e = C j :=
    subtype_map_of_mem (fun _ hx => mem_compl.mpr (fun hz => disjoint_left.mp (hOrd j) hx hz))
  have hSize' (j : J × Fin (f*(n+1))) : (X j).card = m := by rw [←card_map e,hMap,hSize]
  have hU (j : J × Fin f) :
      ((univ : Finset (Fin (n+1))).biUnion (fun i => X (j.1,intervalPosition j.2 i))).map e = U j := by
    ext v
    simp only [U,mem_map,mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ⟨x,⟨i,hi⟩,rfl⟩
      exact ⟨i,mem_subtype.mp hi⟩
    · rintro ⟨i,hi⟩
      obtain ⟨x,hx,hEq⟩ := mem_map.mp ((hMap (j.1,intervalPosition j.2 i)).symm ▸ hi)
      exact ⟨x,⟨i,hx⟩,hEq⟩
  have hCells (j : Fin f × J) : cells j = univ.biUnion (fun i : Fin (n+1) => X (j.2,intervalPosition j.1 i)) := by
    ext x
    simp only [cells,U,X,mem_subtype,mem_biUnion,mem_univ,true_and]
  have hApart (a : Fin (r*t)) : Pairwise (fun i j => Disjoint (F a i).digraph (F a j).digraph) :=
    (winding_interval_factor_exact_semidegrees C (by omega) hf m hSize hDis hCover (F a)).1
  obtain ⟨_,hUApart,_⟩ := winding_styled_interval_partition C hf (by omega) m hDis hSize
  refine ⟨?_,?_,?_,?_⟩
  · ext x y
    constructor
    · intro h
      obtain ⟨⟨a,i⟩,hi⟩ := Digraph.iSup_adj.mp h
      exact Digraph.iSup_adj.mpr ⟨_,Digraph.iSup_adj.mpr ⟨(i.2.1,i.1),hi⟩⟩
    · intro h
      obtain ⟨a,ha⟩ := Digraph.iSup_adj.mp h
      obtain ⟨⟨j,i⟩,hi⟩ := Digraph.iSup_adj.mp ha
      obtain ⟨⟨b,k⟩,rfl⟩ := (finProdFinEquiv : Fin r × Fin t ≃ Fin (r*t)).surjective a
      exact Digraph.iSup_adj.mpr ⟨(b,i,j,k),hi⟩
  · rintro ⟨a,i,j,k⟩ ⟨b,i',j',k'⟩ hne
    change Disjoint (F (finProdFinEquiv (a,k)) (j,i)).digraph (F (finProdFinEquiv (b,k')) (j',i')).digraph
    by_cases hEq : (a,k) = (b,k')
    · rw [hEq]
      apply hApart
      intro he
      have ha : a = b := congrArg Prod.fst hEq
      have hk : k = k' := congrArg Prod.snd hEq
      have hj : j = j' := congrArg Prod.fst he
      have hi : i = i' := congrArg Prod.snd he
      exact hne (Prod.ext ha (Prod.ext hi (Prod.ext hj hk)))
    · exact (hF (finProdFinEquiv.injective.ne hEq)).mono
        (le_iSup (fun w => (F (finProdFinEquiv (a,k)) w).digraph) (j,i))
        (le_iSup (fun w => (F (finProdFinEquiv (b,k')) w).digraph) (j',i'))
  · intro i j hne
    apply disjoint_left.mpr
    intro x hi hj
    exact disjoint_left.mp (hUApart (i.2,i.1) (j.2,j.1) (Prod.swap_injective.ne hne))
      (mem_subtype.mp hi) (mem_subtype.mp hj)
  · rintro a ⟨i,j,k⟩
    let P := F (finProdFinEquiv (a,k)) (j,i)
    refine ⟨P.path_system,P.cover,(fun _ _ => P.no_internal),?_⟩
    have hA : U (j,i) ∪ S (next (j,i)) =
        ((univ : Finset (Fin (n+1))).biUnion (fun l => X (j,intervalPosition i l))).map e ∪
        (X (j,intervalPosition (finRotate f i) (0 : Fin (n+1)))).map e :=
      congrArg₂ (· ∪ ·) (hU (j,i)).symm (hMap _).symm
    have hT : S (next (j,i)) = (X (j,intervalPosition (finRotate f i) (0 : Fin (n+1)))).map e :=
      (hMap (j,intervalPosition (finRotate f i) 0)).symm
    let Q := P.castSets hA (hMap (j,intervalPosition i 0)).symm hT
    have hQ : Q.digraph = D a (i,j,k) := OriginalInterval.castSets_digraph _ _ _ _
    have hData := winding_exceptional_interval_chord_bounds Z (fun l => X (j,l)) c hf
      (fun l x hx => hLabel (j,l) x (mem_subtype.mp hx)) (fun l => hSize' (j,l)) i Q
    rw [hQ] at hData
    rw [hCells (i,j),hCells (finRotate f i,j)]
    refine ⟨fun _ hv => ?_,hData.2.1,fun z => ?_⟩
    · simpa only [mem_union,Prod.fst,Prod.snd] using hData.1 hv
    · convert hData.2.2 z using 1 <;> apply sum_congr rfl <;> intro p _ <;> split_ifs <;> rfl

end OverfullWork.DirectedRobustExpansion
