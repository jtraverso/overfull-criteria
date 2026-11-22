module

public import OverfullWork.KuhnOsthusExceptionalFactorAssembly

@[expose] public section


/-! The degree and deletion argument of Lemma 7.6 for an arbitrary
number of styles. Keep the actual interval covers in the output. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedSpanningConfiguration
open scoped Classical
variable {V : Type*} [Fintype V]

/-- A family of complete intervals owns each ordinary slot once and
each exceptional slot once per interval. -/
theorem original_interval_family_semidegrees {I : Type*} [Fintype I]
    (G : Digraph V) (Z : Finset V) (next : Equiv.Perm I) (U S : I → Finset V)
    (hNext : ∀ i, next i ≠ i) (hSub : ∀ i, S i ⊆ U i)
    (hDis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ U i)
    (P : ∀ i, OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i))) :
    ∀ x, inDegree (⨆ i, (P i).digraph) x = (if x ∈ Z then Fintype.card I else 1) ∧
      outDegree (⨆ i, (P i).digraph) x = (if x ∈ Z then Fintype.card I else 1) := by
  obtain ⟨hSlots,hIn⟩ := exceptional_interval_slot_owners next U S hNext hSub hDis
  have hOut' (x : V) (hx : x ∉ Z) : ∃! i, ∃ y, (P i).digraph.Adj x y := by
    obtain ⟨i,hi⟩ := hCover x hx
    have hAt (j : I) : (∃ y, (P j).digraph.Adj x y) ↔ x ∈ U j := by rw [((P j).slots x hx).1,hSlots]
    exact ⟨i,(hAt i).mpr hi,fun j hj => by
      by_contra h
      exact disjoint_left.mp (hDis j i h) ((hAt j).mp hj) hi⟩
  have hIn' (x : V) (hx : x ∉ Z) : ∃! i, ∃ y, (P i).digraph.Adj y x := by
    obtain ⟨i,hi,hUnique⟩ := hIn x (hCover x hx)
    exact ⟨i,((P i).slots x hx).2.mpr hi,fun j hj => hUnique j (((P j).slots x hx).2.mp hj)⟩
  have hApart : Pairwise (fun i j => Disjoint (P i).digraph (P j).digraph) := by
    intro i j hij
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hi,hj⟩
    by_cases hx : x ∈ Z
    · obtain ⟨k,_,hk⟩ := hIn' y ((P i).no_internal hi hx)
      exact hij ((hk i ⟨x,hi⟩).trans (hk j ⟨x,hj⟩).symm)
    · obtain ⟨k,_,hk⟩ := hOut' x hx
      exact hij ((hk i ⟨y,hi⟩).trans (hk j ⟨y,hj⟩).symm)
  intro x
  rw [inDegree_iSup_of_disjoint _ hApart,outDegree_iSup_of_disjoint _ hApart]
  by_cases hx : x ∈ Z
  · have hO (i : I) : outDegree (P i).digraph x = 1 := by
      rw [(path_system_degree_slots _ (P i).path_system x).1,if_pos ((P i).cover x hx).1]
    have hI (i : I) : inDegree (P i).digraph x = 1 := by
      rw [(path_system_degree_slots _ (P i).path_system x).2,if_pos ((P i).cover x hx).2]
    simp [hx,hO,hI]
  · obtain ⟨u,hu,hu'⟩ := hOut' x hx
    obtain ⟨v,hv,hv'⟩ := hIn' x hx
    simp only [if_neg hx]
    constructor
    · rw [sum_eq_single v]
      · rw [(path_system_degree_slots _ (P v).path_system x).2,if_pos hv]
      · intro i _ hi
        rw [(path_system_degree_slots _ (P i).path_system x).2,if_neg]
        exact fun hi' => hi (hv' i hi')
      · simp
    · rw [sum_eq_single u]
      · rw [(path_system_degree_slots _ (P u).path_system x).1,if_pos hu]
      · intro i _ hi
        rw [(path_system_degree_slots _ (P i).path_system x).1,if_neg]
        exact fun hi' => hi (hu' i hi')
      · simp

/-- Iterate actual interval families in their physical residual,
retaining their exact unions and individual path projections. -/
theorem pack_original_interval_families
    (G : Digraph V) (Z : Finset V) (r K l : ℕ)
    (next : Equiv.Perm (Fin K × Fin l)) (U S : Fin K × Fin l → Finset V)
    (hNext : ∀ i, next i ≠ i) (hSub : ∀ i, S i ⊆ U i)
    (hDis : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hCover : ∀ x ∉ Z, ∃ i, x ∈ U i)
    (hLocal : ∀ t < r, ∀ H : Digraph V, H ≤ G →
      (∀ v, inDegree H v ≤ t*(if v ∈ Z then K*l else 1) ∧
        outDegree H v ≤ t*(if v ∈ Z then K*l else 1)) →
      ∀ i, Nonempty (OriginalInterval (G \ H) Z (U i ∪ S (next i)) (S i) (S (next i)))) :
    ∃ P : Fin r → ∀ i, OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i)),
      let F (j : Fin r) := ⨆ i, (P j i).digraph
      Pairwise (fun j k => Disjoint (F j) (F k)) ∧
      ∀ x, inDegree (⨆ j, F j) x ≤ r*(if x ∈ Z then K*l else 1) ∧
        outDegree (⨆ j, F j) x ≤ r*(if x ∈ Z then K*l else 1) := by
  let Cert (D : Digraph V) := ∃ P : ∀ i, OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i)),
    (⨆ i, (P i).digraph) = D
  have hPick (t : ℕ) (ht : t < r) (H : Digraph V) (hH : H ≤ G)
      (hBudget : ∀ v, inDegree H v ≤ t*(if v ∈ Z then K*l else 1) ∧
        outDegree H v ≤ t*(if v ∈ Z then K*l else 1)) :
      ∃ D : Digraph V, D ≤ G \ H ∧ Cert D ∧
        ∀ v, inDegree D v ≤ (if v ∈ Z then K*l else 1) ∧
          outDegree D v ≤ (if v ∈ Z then K*l else 1) := by
    let P i := Classical.choice (hLocal t ht H hH hBudget i)
    let P' (i : Fin K × Fin l) : OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i)) :=
      { P i with le := (P i).le.trans (fun _ _ h => h.1) }
    refine ⟨⨆ i, (P i).digraph,iSup_le (fun i => (P i).le),⟨P',rfl⟩,?_⟩
    intro v
    have h := original_interval_family_semidegrees (G \ H) Z next U S hNext hSub hDis hCover P v
    simp only [Fintype.card_prod,Fintype.card_fin] at h
    exact ⟨h.1.le,h.2.le⟩
  obtain ⟨F,hF,hApart,hLoss⟩ := exists_disjoint_exceptional_factor_packing G Z r K l Cert hPick
  choose P hP using fun i => (hF i).2
  refine ⟨P,?_,?_⟩
  · intro i j hij
    change Disjoint (⨆ a, (P i a).digraph) (⨆ a, (P j a).digraph)
    rw [hP,hP]
    exact hApart hij
  · simpa only [hP] using hLoss

end OverfullWork.DirectedRobustExpansion
