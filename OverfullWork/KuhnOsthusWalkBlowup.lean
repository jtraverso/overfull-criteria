module

public import OverfullWork.KuhnOsthusSubclusterWalk
public import OverfullWork.KuhnOsthusWalkPairMatchings
public import OverfullWork.KuhnOsthusWalkQuarters

@[expose] public section


/-! The regular walk component (CA2) of the chord absorber.
The physical quarters are disjoint and the fine successor is a permutation,
so each vertex has a unique source and target coordinate. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V J : Type*}

/-- Physical arcs of the matchings between successor cells. -/
def successorCellMatchingUnion {k : ℕ} (A : J → Finset V) (s : Equiv.Perm J)
    (M : ∀ i, Fin k → A i ≃ A (s i)) : Digraph V :=
  ⟨fun x y => ∃ (i : J) (b : Fin k) (a : A i), a.val = x ∧ (M i b a).val = y⟩

private theorem eq_of_shared_cell (A : J → Finset V)
    (hDis : ∀ i j, i ≠ j → Disjoint (A i) (A j)) {i j : J} {v : V}
    (hi : v ∈ A i) (hj : v ∈ A j) : i = j := by
  by_contra hn
  exact Finset.disjoint_left.mp (hDis i j hn) hi hj

variable [Fintype V]

/-- The walk blow-up has degree precisely the number of matchings
on every participating vertex in both directions. -/
theorem successor_cell_matching_union_degrees {k : ℕ}
    (A : J → Finset V) (s : Equiv.Perm J) (M : ∀ i, Fin k → A i ≃ A (s i))
    (hDis : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hArc : ∀ i b c, b ≠ c → ∀ a, M i b a ≠ M i c a)
    (i : J) (x : A i) :
    let U := successorCellMatchingUnion A s M
    inDegree U x = k ∧ outDegree U x = k := by
  intro U
  have hOut (j : J) (a : A j) :
      outDegree U a = k := by
    let f (b : Fin k) := (M j b a).val
    have hInject : Function.Injective f := by
      intro b c he
      by_contra hne
      exact hArc j b c hne a (Subtype.ext he)
    have hEq : (univ : Finset V).filter (U.Adj a) = univ.image f := by
      ext y
      simp only [mem_filter,mem_univ,true_and,mem_image]
      constructor
      · rintro ⟨l,b,w,hw,hy⟩
        have hl : l = j := eq_of_shared_cell A hDis (hw ▸ w.prop) a.prop
        subst l
        have he : w = a := Subtype.ext hw
        refine ⟨b,?_⟩
        change (M j b a).val = y
        rwa [he] at hy
      · rintro ⟨b,hb⟩
        exact ⟨j,b,a,rfl,hb⟩
    rw [outDegree,hEq,card_image_of_injective _ hInject,card_univ,Fintype.card_fin]
  have hIn (j : J) (a : A (s j)) :
      inDegree U a = k := by
    let f (b : Fin k) := ((M j b).symm a).val
    have hInject : Function.Injective f := by
      intro b c he
      by_contra hne
      have he' : (M j b).symm a = (M j c).symm a := Subtype.ext he
      have hb := (M j b).apply_symm_apply a
      have hc := (M j c).apply_symm_apply a
      exact hArc j b c hne ((M j b).symm a) (hb.trans (he'.symm ▸ hc).symm)
    have hEq : (univ : Finset V).filter (fun y => U.Adj y a) = univ.image f := by
      ext y
      simp only [mem_filter,mem_univ,true_and,mem_image]
      constructor
      · rintro ⟨l,b,w,hy,hw⟩
        have hl : l = j := s.injective
          (eq_of_shared_cell A hDis (hw ▸ (M l b w).prop) a.prop)
        subst l
        have he : M j b w = a := Subtype.ext hw
        exact ⟨b,congrArg Subtype.val ((M j b).symm_apply_eq.mpr he.symm) |>.trans hy⟩
      · rintro ⟨b,hb⟩
        exact ⟨j,b,(M j b).symm a,hb,congrArg Subtype.val ((M j b).apply_symm_apply a)⟩
    rw [inDegree,inNeighbours,hEq,card_image_of_injective _ hInject,card_univ,Fintype.card_fin]
  refine ⟨?_,hOut i x⟩
  have hx : x.val ∈ A (s (s.symm i)) := by simpa only [Equiv.apply_symm_apply] using x.prop
  exact hIn (s.symm i) ⟨x.val,hx⟩

/-- The rescaled version of Kühn–Osthus Lemma 9.3(ii) once the
quarters and their lower-superregular pairs are available.
The input host may already exclude the base-cycle and exceptional reserves. -/
theorem exists_universal_walk_blowup_of_quarters {I : Type*} (G : Digraph V)
    (s : Equiv.Perm I) (Q : I × Fin 4 → Finset V) (m k r : ℕ)
    (ε d : ℝ) (hSize : ∀ i, (Q i).card = m)
    (hDis : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) (hr : 0 < r)
    (hCut : (m:ℝ)*ε ≤ r) (hBudget : (k:ℝ) < (d-2*ε)*r)
    (hDegrees : ((r+k : ℕ):ℝ) ≤ (d-ε)*(m:ℝ))
    (hPairs : ∀ i j, IsLowerSuperregularPair G ε d (Q (i,j)) (Q (s i,j))) :
    let t := s.prodCongr (Equiv.refl (Fin 4))
    ∃ M : ∀ i, Fin k → Q i ≃ Q (t i),
      let U := successorCellMatchingUnion Q t M
      U ≤ G ∧
      (∀ i b c, b ≠ c → ∀ a, M i b a ≠ M i c a) ∧
      (∀ i (a : Q i), inDegree U a = k ∧ outDegree U a = k) ∧
      ∀ x y, U.Adj x y → ∃ i, x ∈ Q i ∧ y ∈ Q (t i) := by
  intro t
  obtain ⟨M,hM,hApart⟩ := exists_universal_walk_quarter_matchings G s
    (fun i j => Q (i,j)) m k r ε d (fun i j => hSize (i,j)) hr hCut hBudget hDegrees hPairs
  let N (i : I × Fin 4) (b : Fin k) : Q i ≃ Q (t i) := M i.1 i.2 b
  refine ⟨N,?_,fun i => hApart i.1 i.2,?_,?_⟩
  · rintro x y ⟨i,b,a,rfl,rfl⟩
    exact hM i.1 i.2 b a
  · exact successor_cell_matching_union_degrees Q t N hDis (fun i => hApart i.1 i.2)
  · rintro x y ⟨i,b,a,rfl,rfl⟩
    exact ⟨i,a.prop,(N i b a).prop⟩

/-- The walk part of Lemma 9.3, including the uniform split into
quarters after accounting for allocated arcs. This gives the
matchings and exact semidegrees required in (CA2). -/
theorem kuhn_osthus_lemma_9_3_walk_component (C ε η d a : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (ha : 0 ≤ a) (hFloor : 2*ε ≤ d) (hTol : 2*(4*ε+a) ≤ η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type*} (G H : Digraph V) (_hHG : H ≤ G)
      (s : Equiv.Perm I) (A : I → Finset V) (m loss k r : ℕ), 0 < m →
      (∀ i, N ≤ (A i).card) → (∀ i, (A i).card = 4*m) →
      (2*(Fintype.card V:ℝ) ≤ C*(4*m:ℕ)) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      ((loss:ℝ) ≤ a*((m:ℝ)*η)) →
      (∀ i x, x ∈ A i → inDegree H x ≤ loss ∧ outDegree H x ≤ loss) →
      (∀ i, IsLowerSuperregularPair G ε d (A i) (A (s i))) →
      0 < r → (m:ℝ)*η ≤ r → (k:ℝ) < (d-2*η)*r →
      ((r+k : ℕ):ℝ) ≤ (d-η)*(m:ℝ) →
      let t := s.prodCongr (Equiv.refl (Fin 4))
      ∃ Q : I × Fin 4 → Finset V,
        (∀ i, (univ : Finset (Fin 4)).biUnion (fun j => Q (i,j)) = A i) ∧
        (∀ i, (Q i).card = m) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
        ∃ M : ∀ i, Fin k → Q i ≃ Q (t i),
          let U := successorCellMatchingUnion Q t M
          U ≤ G \ H ∧
          (∀ i b c, b ≠ c → ∀ x, M i b x ≠ M i c x) ∧
          (∀ i (x : Q i), inDegree U x = k ∧ outDegree U x = k) ∧
          ∀ x y, U.Adj x y → ∃ i, x ∈ Q i ∧ y ∈ Q (t i) := by
  obtain ⟨N,hN⟩ := exists_universal_walk_quarters.{u} C ε η d a hC hε hη hη1 ha hFloor hTol
  refine ⟨N,?_⟩
  intro W _ I G H hHG s A m loss k r hm hLarge hSize hProfiles hDis hBudget hLoss hPairs
     hr hCut hDemand hDegrees t
  obtain ⟨Q,hCover,hQsize,hQdis,hQpair⟩ :=
    hN G H hHG s A m loss hm hLarge hSize hProfiles hDis hBudget hLoss hPairs
  exact ⟨Q,hCover,hQsize,hQdis,exists_universal_walk_blowup_of_quarters (G \ H) s Q m k r
    η d hQsize hQdis hr hCut hDemand hDegrees hQpair⟩

end OverfullWork.DirectedRobustExpansion
