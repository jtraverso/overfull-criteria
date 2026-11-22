module

public import OverfullWork.KuhnOsthusChordOriginalSystems

@[expose] public section


/-! The sources of the arcs allocated in one chord round are the
ordinary factor, its walk bank, and its original exceptional paths. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V W J : Type*}

private theorem exact_arc_owners_of_disjoint_sup (A B : Digraph V) (D C : J → Digraph V)
    (hDis : Disjoint A B)
    (hA : ∀ i, D i ≤ A) (hB : ∀ i, C i ≤ B)
    (hDA : ∀ x y, A.Adj x y → ∃! i, (D i).Adj x y)
    (hCB : ∀ x y, B.Adj x y → ∃! i, (C i).Adj x y) :
    (∀ i, D i ⊔ C i ≤ A ⊔ B) ∧ ∀ x y, (A ⊔ B).Adj x y → ∃! i, (D i ⊔ C i).Adj x y := by
  refine ⟨fun i => sup_le_sup (hA i) (hB i),?_⟩
  intro x y h
  rcases h with ha | hb
  · obtain ⟨i,hi,hOwner⟩ := hDA x y ha
    refine ⟨i,Or.inl hi,?_⟩
    rintro j (hj | hj)
    · exact hOwner j hj
    · exact (disjoint_iff_inf_le.mp hDis ⟨ha,hB _ hj⟩).elim
  · obtain ⟨i,hi,hOwner⟩ := hCB x y hb
    refine ⟨i,Or.inr hi,?_⟩
    rintro j (hj | hj)
    · exact (disjoint_iff_inf_le.mp hDis ⟨hA _ hj,hb⟩).elim
    · exact hOwner j hj

private theorem lifted_arc_owners (e : W ↪ V) (A : Digraph W) (D : J → Digraph W)
    (h : ∀ x y, A.Adj x y → ∃! i, (D i).Adj x y) :
    ∀ x y, (liftDirectedPair e e A).Adj x y → ∃! i, (liftDirectedPair e e (D i)).Adj x y := by
  rintro x y ⟨a,b,rfl,rfl,ha⟩
  obtain ⟨i,hi,hOwner⟩ := h a b ha
  exact ⟨i,(liftDirectedPair_adj e e (D i) a b).mpr hi,
    fun j hj => hOwner j ((liftDirectedPair_adj e e (D j) a b).mp hj)⟩

variable [Fintype V]

/-- In the original graph every arc of one chord round is assigned
to exactly one prescribed path system. The round data in the basic
graph are the contractions of the resulting original systems. -/
theorem assemble_original_chord_round (Z : Finset V) (H U : Digraph ↥Zᶜ) (E : Digraph V)
    (M D : J → Digraph ↥Zᶜ) (C : J → Digraph V)
    (hDU : ∀ i, D i ≤ U) (hMH : ∀ i, M i ≤ H) (hCE : ∀ i, C i ≤ E)
    (hU : ∀ x y, U.Adj x y → ∃! i, (D i).Adj x y)
    (hH : ∀ x y, H.Adj x y → ∃! i, (M i).Adj x y)
    (hE : ∀ x y, E.Adj x y → ∃! i, (C i).Adj x y)
    (hUH : Disjoint U H)
    (hD : ∀ i, IsDirectedPathSystem (D i)) (hM : ∀ i, IsDirectedPathSystem (M i))
    (hC : ∀ i, IsDirectedPathSystem (C i) ∧ CoversExceptional (C i) Z)
    (hNo : ∀ i x y, (C i).Adj x y → x ∈ Z → y ∉ Z)
    (hApartD : ∀ i x, IncidentTo (D i) x → ¬ IncidentTo (M i ⊔ basicExceptionalPathSystem (C i) Z) x)
    (hApartM : ∀ i x, IncidentTo (M i) x → ¬ IncidentTo (basicExceptionalPathSystem (C i) Z) x) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let P := liftDirectedPair e e (U ⊔ H) ⊔ E
    Disjoint (liftDirectedPair e e (U ⊔ H)) E →
    ∃ T : J → Digraph V,
      (∀ i, T i ≤ P) ∧ (∀ x y, P.Adj x y → ∃! i, (T i).Adj x y) ∧
      (∀ i, IsDirectedPathSystem (T i) ∧ CoversExceptional (T i) Z) ∧
      (∀ i x y, (T i).Adj x y → x ∈ Z → y ∉ Z) ∧
      ∀ i, basicExceptionalPathSystem (T i) Z = D i ⊔ (M i ⊔ basicExceptionalPathSystem (C i) Z) := by
  intro e P hDis
  let L (i : J) := liftDirectedPair e e (D i ⊔ M i)
  let T (i : J) := L i ⊔ C i
  have hUHM := exact_arc_owners_of_disjoint_sup U H D M hUH hDU hMH hU hH
  have hPart := exact_arc_owners_of_disjoint_sup _ E L C hDis
    (fun i => liftDirectedPair_mono e e (hUHM.1 i)) hCE
    (lifted_arc_owners e _ _ hUHM.2) hE
  have hSystem (i : J) := chord_original_system_of_ordinary Z (D i ⊔ M i) (C i)
    ((hD i).sup_of_disjoint_vertices (hM i) fun x hx hm => by
      rcases hm with ⟨y,hy⟩ | ⟨y,hy⟩
      · exact hApartD i x hx (Or.inl ⟨y,Or.inl hy⟩)
      · exact hApartD i x hx (Or.inr ⟨y,Or.inl hy⟩))
    (hC i).1 (hC i).2 (hNo i) (fun x hx he => by
      rcases hx with ⟨y,hd | hm⟩ | ⟨y,hd | hm⟩
      · apply hApartD i x (Or.inl ⟨y,hd⟩)
        exact he.imp (fun ⟨a,ha⟩ => ⟨a,Or.inr ha⟩) (fun ⟨a,ha⟩ => ⟨a,Or.inr ha⟩)
      · exact hApartM i x (Or.inl ⟨y,hm⟩) he
      · apply hApartD i x (Or.inr ⟨y,hd⟩)
        exact he.imp (fun ⟨a,ha⟩ => ⟨a,Or.inr ha⟩) (fun ⟨a,ha⟩ => ⟨a,Or.inr ha⟩)
      · exact hApartM i x (Or.inr ⟨y,hm⟩) he)
  refine ⟨T,hPart.1,hPart.2,fun i => ⟨(hSystem i).1,(hSystem i).2.1⟩,
    fun i => (hSystem i).2.2.1,?_⟩
  intro i
  exact (hSystem i).2.2.2.trans (sup_assoc ..)

end OverfullWork.DirectedRobustExpansion
