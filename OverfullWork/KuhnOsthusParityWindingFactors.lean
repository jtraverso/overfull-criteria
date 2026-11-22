module

public import OverfullWork.KuhnOsthusParityPacketProjection
public import OverfullWork.KuhnOsthusWindingExceptionalDegrees

@[expose] public section


/-! Make the parity packets directly from the unrefined original
intervals constructed by Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- A one-style refinement returns the original cell at each
position. This identifies the output of Lemma 7.6 with the input
of the unrefined parity construction. -/
theorem unrefined_winding_cells {V I : Type*}
    (C : Fin 1 × I → Finset V) (X : I → Finset V)
    (hCover : ∀ i, (univ : Finset (Fin 1)).biUnion (fun j => C (j,i)) = X i) :
    C = fun j => X j.2 := by
  funext j
  rw [←hCover j.2]
  ext x
  constructor
  · exact fun h => mem_biUnion.mpr ⟨j.1,mem_univ _,h⟩
  · intro h
    obtain ⟨l,_,hl⟩ := mem_biUnion.mp h
    rw [Subsingleton.elim l j.1] at hl
    exact hl

/-- The same original winding factors provide the prescribed parity
arcs and their degree certificate. No separate family of packets or
degree witness has to be chosen. -/
theorem parity_packets_of_original_winding_factors {V : Type*} [Fintype V]
    {G : Digraph V} {q r m : ℕ} (Z : Finset V) [Nonempty ↥Zᶜ]
    (X : Fin (14*q) → Finset ↥Zᶜ) (hq : 0 < q)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hApart : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = m) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let emb : ↥Zᶜ ↪ V := Function.Embedding.subtype _
    let idx : Fin (7*(2*q)) ≃ Fin (14*q) := finCongr (by omega)
    let C (i : Fin 1 × Fin (7*(2*q))) := (X (idx i.2)).map emb
    let U (j : Fin 1 × Fin 7) := univ.biUnion (fun i : Fin (2*q) => C (j.1,intervalPosition j.2 i))
    let S (j : Fin 1 × Fin 7) := C (j.1,intervalPosition j.2 ⟨0,by omega⟩)
    let next := (Equiv.refl (Fin 1)).prodCongr (finRotate 7)
    let e := (exceptionalCoordinates Z).toEmbedding
    ∀ F : Fin r → ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
      let E (i : Fin r) := ⨆ j, (F i j).digraph
      Pairwise (fun i j => Disjoint (E i) (E j)) →
      ∃ P : Fin r → ParityExceptionalPacket (pullDirectedPair e e G) A q,
        (⨆ i, (P i).original) = pullDirectedPair e e (⨆ i, E i) ∧
        Pairwise (fun i j => Disjoint (P i).original (P j).original) ∧
        ∀ x : ↥Zᶜ ⊕ ↥Z, let d := match x with | .inl _ => r | .inr _ => 7*r
          inDegree (⨆ i, (P i).original) x = d ∧ outDegree (⨆ i, (P i).original) x = d := by
  intro hk A emb idx C U S next e F E hF
  have hCSize (j : Fin 1 × Fin (7*(2*q))) : (C j).card = m := by simp only [C,card_map,hSize]
  have hDis (i j : Fin 1 × Fin (7*(2*q))) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    apply disjoint_left.mpr
    intro v hi hj
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hi
    obtain ⟨y,hy,he⟩ := mem_map.mp hj
    have hne : idx i.2 ≠ idx j.2 := fun h => hij (Prod.ext (Subsingleton.elim _ _) (idx.injective h))
    exact disjoint_left.mp (hApart _ _ hne) hx (emb.injective he ▸ hy)
  have hCCover (v : V) (hv : v ∉ Z) : ∃ i, v ∈ C i := by
    obtain ⟨i,hi⟩ := hCover ⟨v,mem_compl.mpr hv⟩
    exact ⟨(0,idx.symm i),mem_map.mpr ⟨⟨v,mem_compl.mpr hv⟩,by simpa only [idx.apply_symm_apply] using hi,rfl⟩⟩
  have hDegree (v : V) := winding_exceptional_reserve_exact_semidegrees C
    (by omega : 0 < 2*q) (by decide : 2 ≤ 7) m hCSize hDis hCCover F hF v
  have hDegree' (v : V) : let d := if v ∈ Z then 7*r else r
      inDegree (⨆ i, E i) v = d ∧ outDegree (⨆ i, E i) v = d := by
    simpa only [Fintype.card_fin,one_mul] using hDegree v
  obtain ⟨P,hP,hDisjoint,hCount⟩ := project_wound_interval_family_to_parity_packets Z X hq F hF hDegree'
  refine ⟨P,?_,hDisjoint,hCount⟩
  ext x y
  change (⨆ i, (P i).original).Adj x y ↔ (⨆ i, E i).Adj (e x) (e y)
  rw [Digraph.iSup_adj,Digraph.iSup_adj]
  simp only [hP]
  rfl

end OverfullWork.DirectedRobustExpansion
