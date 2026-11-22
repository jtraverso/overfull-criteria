module

public import OverfullWork.OsthusStadenPrimaryNestedRefinement
public import OverfullWork.OsthusStadenPreparedSlices

@[expose] public section


/-! Align the refinements of all adapted primary factors to one base refinement. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical
universe u v w

/-- The retained sizes and the subsets of the base partition determine
a common error bound for every adaptation. -/
theorem exists_aligned_primary_refinements (C ε τ : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (hSmall : ε ≤ τ/4) (hτ : 0 < τ) (hτ₁ : τ ≤ 1)
    (s p : ℕ) (hs : 0 < s) (hp : 0 < p) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {J : Type w} [Fintype J] {r : ℕ}
      (profiles : J → Finset V) (f : V → Option I) (g : Fin r → V → Option I) (m₀ m : ℕ),
      N ≤ m₀ → m ≤ m₀ →
      (∀ i, (cluster f i).card = s*(p*(2*m₀))) →
      (∀ t i, (cluster (g t) i).card = s*(p*(2*m)) ∧ cluster (g t) i ⊆ cluster f i) →
      (Fintype.card J:ℝ) ≤ C*(m₀:ℝ) →
      let D := s*(p*(2*m₀))-s*(p*(2*m))
      4*(D:ℝ) ≤ (τ^2/16)*(m:ℝ) →
      ∃ R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m₀ ε ε ε,
      ∃ S : ∀ t i, PrimaryNestedRefinement profiles (cluster (g t) i) s p m τ τ τ,
        (∀ t i j, max ((R i).first.cells j \ (S t i).first.cells j).card
          ((S t i).first.cells j \ (R i).first.cells j).card ≤ 2*D) ∧
        (∀ t i j k, max (((R i).second j).cells k \ ((S t i).second j).cells k).card
          (((S t i).second j).cells k \ ((R i).second j).cells k).card ≤ 3*D) ∧
        ∀ t i j k h, max (((R i).halves j k).cells h \ ((S t i).halves j k).cells h).card
          (((S t i).halves j k).cells h \ ((R i).halves j k).cells h).card ≤ 4*D := by
  obtain ⟨N,hN⟩ := exists_primary_nested_refinement.{u,w} C ε hC hε s p hs hp
  refine ⟨N,?_⟩
  intro V _ I _ J _ r profiles f g m₀ m hm₀ hm hBase hAdapt hProfile D hLoss
  let R (i : I) := Classical.choice (hN profiles (cluster f i) m₀ hm₀ (hBase i) hProfile)
  have hD₁ : p*(2*m₀)-p*(2*m) ≤ D := by
    dsimp only [D]
    rw [←Nat.mul_sub s (p*(2*m₀)) (p*(2*m))]
    simpa only [one_mul] using
      Nat.mul_le_mul_right (p*(2*m₀)-p*(2*m)) (show 1 ≤ s from hs)
  have hD₂ : 2*m₀-2*m ≤ p*(2*m₀)-p*(2*m) := by
    rw [←Nat.mul_sub p (2*m₀) (2*m)]
    simpa only [one_mul] using Nat.mul_le_mul_right (2*m₀-2*m) (show 1 ≤ p from hp)
  have hD₃ : m₀-m ≤ 2*m₀-2*m := by omega
  have hCost : ((D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m):ℕ):ℝ) ≤ (τ^2/16)*(m:ℝ) :=
    (show (↑(D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m)):ℝ) ≤ 4*(D:ℝ) by
      exact_mod_cast (show D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m) ≤ 4*D by omega)).trans hLoss
  have hClose (t : Fin r) (i : I) :
      max (cluster f i \ cluster (g t) i).card (cluster (g t) i \ cluster f i).card ≤ D := by
    rw [card_sdiff_of_subset (hAdapt t i).2,sdiff_eq_empty_iff_subset.mpr (hAdapt t i).2,card_empty,
      hBase i,(hAdapt t i).1]
    exact max_le le_rfl (Nat.zero_le _)
  choose S hS₁ hS₂ hS₃ using fun t i => (R i).exists_adapted_of_small_changes hs hp hm
    (hAdapt t i).1 (hClose t i) hε.le hSmall hτ hτ₁ hCost
  exact ⟨R,S,fun t i j => (hS₁ t i j).trans (by omega),
    fun t i j k => (hS₂ t i j k).trans (by omega),fun t i j k h => (hS₃ t i j k h).trans (by omega)⟩

theorem PrimaryNestedRefinement.disjoint_p_cells {V J : Type*}
    {profiles : J → Finset V} {P : Finset V} {s p m : ℕ} {ε₁ ε₂ ε₃ : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m ε₁ ε₂ ε₃)
    (a b : Fin s × Fin p) (h : a ≠ b) :
    Disjoint ((R.second a.1).cells a.2) ((R.second b.1).cells b.2) := by
  rcases a with ⟨i,j⟩
  rcases b with ⟨k,l⟩
  by_cases hi : i = k
  · subst k
    exact (R.second i).disjoint j l (fun h' => h (Prod.ext rfl h'))
  · exact (R.first.disjoint i k hi).mono ((R.second i).subset j) ((R.second k).subset l)

theorem PrimaryNestedRefinement.mem_p_cell_of_mem_parent {V J : Type*}
    {profiles : J → Finset V} {P : Finset V} {s p m : ℕ} {ε₁ ε₂ ε₃ : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m ε₁ ε₂ ε₃) {x : V} (hx : x ∈ P) :
    ∃ i j, x ∈ (R.second i).cells j := by
  rw [←R.first.cover] at hx
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
  rw [←(R.second i).cover] at hi
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp hi
  exact ⟨i,j,hj⟩

/-- Recover the unique refined label of each ordinary vertex. Exceptional
vertices have no label. -/
theorem exists_p_cell_labels {V : Type*} [Fintype V] {I : Type*} [Fintype I] {J : Type*}
    {profiles : J → Finset V} (f : V → Option I) {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃) :
    let cell := fun a : RefinedVertex I s p =>
      ((R a.1.1).second ((ZMod.finEquiv s).symm a.1.2)).cells ((ZMod.finEquiv p).symm a.2)
    ∃ label : V → Option (RefinedVertex I s p),
      (∀ x a, label x = some a ↔ x ∈ cell a) ∧ ∀ x, label x = none ↔ f x = none := by
  intro cell
  have hSub (a : RefinedVertex I s p) : cell a ⊆ cluster f a.1.1 :=
    (((R a.1.1).second ((ZMod.finEquiv s).symm a.1.2)).subset _).trans ((R a.1.1).first.subset _)
  have hUnique (a b : RefinedVertex I s p) (x : V) (ha : x ∈ cell a) (hb : x ∈ cell b) : a = b := by
    rcases a with ⟨⟨i,j⟩,k⟩
    rcases b with ⟨⟨i',j'⟩,k'⟩
    have hii := Option.some.inj (((mem_cluster f i x).mp (hSub _ ha)).symm.trans
      ((mem_cluster f i' x).mp (hSub _ hb)))
    subst i'
    have hPair : ((ZMod.finEquiv s).symm j,(ZMod.finEquiv p).symm k) =
        ((ZMod.finEquiv s).symm j',(ZMod.finEquiv p).symm k') := by
      by_contra hn
      exact disjoint_left.mp ((R i).disjoint_p_cells _ _ hn) ha hb
    have hj := (ZMod.finEquiv s).symm.injective (congrArg Prod.fst hPair)
    have hk := (ZMod.finEquiv p).symm.injective (congrArg Prod.snd hPair)
    exact Prod.ext (Prod.ext rfl hj) hk
  let label (x : V) := if h : ∃ a,x ∈ cell a then some h.choose else none
  have hLabel (x : V) (a : RefinedVertex I s p) : label x = some a ↔ x ∈ cell a := by
    dsimp only [label]
    by_cases he : ∃ a,x ∈ cell a
    · rw [dif_pos he]
      exact ⟨fun h => Option.some.inj h ▸ he.choose_spec,
        fun ha => congrArg some (hUnique _ _ x he.choose_spec ha)⟩
    · rw [dif_neg he]
      exact ⟨by simp,fun ha => (he ⟨a,ha⟩).elim⟩
  refine ⟨label,hLabel,?_⟩
  intro x
  constructor
  · intro hl
    cases hf : f x with
    | none => rfl
    | some i =>
        obtain ⟨j,k,hjk⟩ := (R i).mem_p_cell_of_mem_parent ((mem_cluster f i x).mpr hf)
        let a : RefinedVertex I s p := ((i,ZMod.finEquiv s j),ZMod.finEquiv p k)
        have hc : x ∈ cell a := by
          dsimp only [cell,a]
          rw [(ZMod.finEquiv s).symm_apply_apply,(ZMod.finEquiv p).symm_apply_apply]
          exact hjk
        have h := (hLabel x a).mpr hc
        rw [hl] at h
        cases h
  · intro hf
    dsimp only [label]
    rw [dif_neg]
    rintro ⟨a,ha⟩
    have h := (mem_cluster f a.1.1 x).mp (hSub a ha)
    rw [hf] at h
    cases h

end OverfullWork.DirectedRobustExpansion
