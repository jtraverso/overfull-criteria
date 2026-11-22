module

public import OverfullWork.KuhnOsthusSparsePathExtender
public import OverfullWork.KuhnOsthusPreprocessingResidue
public import OverfullWork.KuhnOsthusSparseReserveDeletion

@[expose] public section


/-! The iteration in Lemma 8.4. The local extender is applied only
to the reserve remaining after the cycles already chosen. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem inDegree_mono_reserve {A B : Digraph V} (h : A ≤ B) (v : V) :
    inDegree A v ≤ inDegree B v := by
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hx).2⟩

private theorem outDegree_mono_reserve {A B : Digraph V} (h : A ≤ B) (v : V) :
    outDegree A v ≤ outDegree B v := by
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hx).2⟩

/-- The used arcs of the extender have both degrees bounded by the
number of cycles already chosen. A local extender valid for every
such deletion can be iterated over all prescribed systems. -/
theorem exists_iterated_path_extensions (R : Digraph V) {k : ℕ}
    (Q : Fin k → Digraph V)
    (hDis : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hReserve : ∀ i, Disjoint (Q i) R)
    (hExtend : ∀ i (H : Digraph V), H ≤ R →
      (∀ v, inDegree H v ≤ i.val ∧ outDegree H v ≤ i.val) →
      ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, (Q i).Adj x y → ρ x = y) ∧
        ∀ x, (Q i ⊔ (R \ H)).Adj x (ρ x)) :
    ∃ F : Fin k → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
      (∀ i x y, (Q i).Adj x y → F i x = y) ∧
      (∀ i x, (Q i ⊔ R).Adj x (F i x)) ∧
      (∀ i j, i ≠ j → ∀ x, F i x ≠ F j x) ∧
      (⨆ i, Q i) ≤ matchingUnion F := by
  have hPrefix (t : ℕ) (ht : t ≤ k) :
      ∃ F : Fin t → Equiv.Perm V,
        (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
        (∀ i x y, (Q (Fin.castLE ht i)).Adj x y → F i x = y) ∧
        (∀ i x, (Q (Fin.castLE ht i) ⊔ R).Adj x (F i x)) ∧
        ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x := by
    induction t with
    | zero => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
    | succ t ih =>
      have ht' : t ≤ k := Nat.le_of_succ_le ht
      obtain ⟨F,hCycle,hKeep,hEdge,hApart⟩ := ih ht'
      let H := R ⊓ matchingUnion F
      let i : Fin k := Fin.castLE ht (Fin.last t)
      have hH (v : V) : inDegree H v ≤ i.val ∧ outDegree H v ≤ i.val := by
        obtain ⟨hIn,hOut⟩ := matchingUnion_semidegrees F v
        exact ⟨(inDegree_mono_reserve inf_le_right v).trans hIn,
          (outDegree_mono_reserve inf_le_right v).trans hOut⟩
      obtain ⟨ρ,hC,hK,hE⟩ := hExtend i H inf_le_left hH
      have hRest : R \ H ≤ R := fun _ _ h => h.1
      have hNew (x : V) : (Q i ⊔ R).Adj x (ρ x) :=
        sup_le_sup_left hRest _ (hE x)
      have hD (j : Fin t) (x : V) : F j x ≠ ρ x := by
        intro h
        have hi : i ≠ Fin.castLE ht' j := by
          intro he
          have hVal := congrArg Fin.val he
          change t = j.val at hVal
          omega
        rcases (Digraph.sup_adj _ _ _ _).mp (hE x) with h1 | h1
        · rcases (Digraph.sup_adj _ _ _ _).mp (hEdge j x) with h2 | h2
          · exact (disjoint_iff_inf_le.mp (hDis i _ hi)) ⟨h1,h ▸ h2⟩
          · exact (disjoint_iff_inf_le.mp (hReserve i)) ⟨h1,h ▸ h2⟩
        · exact h1.2 ⟨h1.1,j,h⟩
      have hCast (j : Fin t) : Fin.castLE ht j.castSucc = Fin.castLE ht' j := Fin.ext rfl
      refine ⟨Fin.snoc F ρ,?_,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun a => ?_) j
        · simpa only [Fin.snoc_last] using hC
        · simpa only [Fin.snoc_castSucc] using hCycle a
      · intro j
        refine Fin.lastCases ?_ (fun a => ?_) j
        · simpa only [Fin.snoc_last] using hK
        · simpa only [Fin.snoc_castSucc,hCast] using hKeep a
      · intro j
        refine Fin.lastCases ?_ (fun a => ?_) j
        · simpa only [Fin.snoc_last] using hNew
        · simpa only [Fin.snoc_castSucc,hCast] using hEdge a
      · intro a b
        refine Fin.lastCases ?_ (fun a' => ?_) a
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun b' _ => ?_) b
          simpa only [Fin.snoc_last,Fin.snoc_castSucc] using fun x => (hD b' x).symm
        · refine Fin.lastCases (fun _ => ?_) (fun b' hab => ?_) b
          · simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hD a'
          · simpa only [Fin.snoc_castSucc] using hApart a' b'
              (fun h => hab (congrArg Fin.castSucc h))
  obtain ⟨F,hC,hK,hE,hD⟩ := hPrefix k le_rfl
  have he (i : Fin k) : Fin.castLE le_rfl i = i := rfl
  simp only [he] at hK hE
  refine ⟨F,hC,hK,hE,hD,?_⟩
  intro x y h
  obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp h
  exact ⟨i,hK i x y hi⟩

/-- The terminal implication of preprocessing. If the prescribed
systems cover the approximate residue, a valid local extension under
the prefix deletion budgets yields the regular nonexceptional factor
of Corollary 8.5. -/
theorem preprocessing_factor_of_iterated_extensions
    (P H R : Digraph V) (Z : Finset V) (r k t : ℕ) (Q : Fin k → Digraph V)
    (hDis : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hReserve : ∀ i, Disjoint (Q i) R)
    (hSupport : ∀ i, Q i ⊔ R ≤ P ⊔ H)
    (hCover : H ≤ ⨆ i, Q i)
    (hDisPH : Disjoint P H)
    (hRegH : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hRegP : ∀ v, let a := if v ∈ Z then k else k+t
      inDegree P v+r = a ∧ outDegree P v+r = a)
    (hExtend : ∀ i (L : Digraph V), L ≤ R →
      (∀ v, inDegree L v ≤ i.val ∧ outDegree L v ≤ i.val) →
      ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, (Q i).Adj x y → ρ x = y) ∧
        ∀ x, (Q i ⊔ (R \ L)).Adj x (ρ x)) :
    ∃ F : Fin k → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
      (∀ i j, i ≠ j → ∀ x, F i x ≠ F j x) ∧
      (∀ i x, (P ⊔ H).Adj x (F i x)) ∧
      H ≤ matchingUnion F ∧
      let D := (P ⊔ H) \ matchingUnion F
      (∀ x y, D.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
      ∀ v : ↥Zᶜ, inDegree (InducedDigraphSampling.induced D Zᶜ) v = t ∧
        outDegree (InducedDigraphSampling.induced D Zᶜ) v = t := by
  obtain ⟨F,hC,_,hEdge,hApart,hAll⟩ :=
    exists_iterated_path_extensions R Q hDis hReserve hExtend
  have hArcs (i : Fin k) (v : V) : (P ⊔ H).Adj v (F i v) := hSupport i (hEdge i v)
  have hH := hCover.trans hAll
  obtain ⟨hEq,hDegrees,hFree⟩ :=
    preprocessing_residue_degrees P H Z r k t F hDisPH hRegH hRegP hArcs hApart hH
  refine ⟨F,hC,hApart,hArcs,hH,?_⟩
  dsimp only
  rw [←hEq]
  exact ⟨hFree,preprocessing_complement_factor _ Z t hFree (fun v hv => by simpa [hv] using hDegrees v)⟩

end OverfullWork.DirectedRobustExpansion
