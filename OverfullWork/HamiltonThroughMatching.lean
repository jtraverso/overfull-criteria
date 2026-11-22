module

public import OverfullWork.MergePathExpansion
public import OverfullWork.MergeReservePacking
public import OverfullWork.PairedEndpointContraction
public import OverfullWork.DirectedBatchResidual

@[expose] public section


/-! The simultaneous matching contraction in Kühn–Osthus Lemma 11.1. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset DirectedEndpointContraction DirectedAbsorbingLadder
open scoped Classical
universe u

theorem exists_hamilton_through_matching (ν τ α : ℝ) (hν : 0 < ν) (hνHalf : ν ≤ 1/2)
    (hντ : ν ≤ τ) (hτα : 64*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∀ (p : ℕ), (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      ∀ (a b : Fin p → V), Function.Injective a → Function.Injective b →
        (∀ i j, a i ≠ b j) → (∀ i,D.Adj (b i) (a i)) →
      ∃ σ : Equiv.Perm V, (∀ v,D.Adj v (σ v)) ∧ (∀ i, σ (b i) = a i) ∧
        HasSpanningCycle (fun x y => σ x = y) := by
  obtain ⟨N₀,hHam⟩ := exists_hamilton_threshold.{u} (ν/2) (2*τ) (α/2)
    (by positivity) (by linarith only [hν,hντ]) (by linarith only [hτα]) (by linarith only [hα])
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (16/ν)
  refine ⟨max (2*N₀) N₁,?_⟩
  intro V _ D hn hR hIn hOut p hp a b ha hb hab hEdges
  let W := Outside (pairedSet a b) ⊕ Fin p
  let next := Equiv.refl (Fin p)
  let H := pairedContraction D a b ha hb next
  have hLarge : 16 ≤ ν*(Fintype.card V:ℝ) := by
    have hCast : (N₁:ℝ) ≤ Fintype.card V := by exact_mod_cast (show N₁ ≤ Fintype.card V by omega)
    rw [mul_comm]
    exact (div_le_iff₀ hν).mp (hN₁.trans hCast)
  have hOrder : 2 ≤ τ*(Fintype.card V:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hντ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
    linarith only [hLarge,h]
  have hRob := paired_contraction_robust D a b ha hb hab next ν τ
    hν hνHalf (hν.trans_le hντ) hLarge hOrder hp hR
  obtain ⟨hi,ho⟩ := paired_contraction_semidegrees D a b ha hb hab next ν α
    hν hνHalf (by linarith only [hν,hντ,hτα]) hLarge hp hIn hOut
  have hCard : Fintype.card W + p = Fintype.card V := paired_carrier_card a b ha hb hab
  have hp' : 2*p ≤ Fintype.card V := by
    have h := card_le_univ (pairedSet a b)
    rw [pairedSet_card a b ha hb hab] at h
    exact h
  obtain ⟨T,z,hND,hAll,hHead,hChain⟩ := hHam H (by change N₀ ≤ Fintype.card W; omega) hRob hi ho
  let K : Digraph V := ⟨fun v w => D.Adj v w ∧ ∀ i, v = b i → w = a i⟩
  let P : W → PathRequest K := fun w =>
    match w with
    | .inl v => ⟨v.val,v.val,[],⟨.singleton _,rfl⟩,by simp⟩
    | .inr i =>
      ⟨b i,a i,[a i],
        ⟨List.IsChain.cons_cons ⟨hEdges i,fun j h => congrArg a (hb h)⟩ (.singleton _),rfl⟩,
        by simp [Ne.symm (hab i i)]⟩
  have hSource (w : W) : (P w).source = incomingRepresentative a b hb w := by cases w <;> rfl
  have hTarget (w : W) : (P w).target = outgoingRepresentative a b ha next w := by cases w <;> rfl
  have hTargetOff (w : W) (i : Fin p) : (P w).target ≠ b i := by
    cases w with
    | inl v =>
      intro h
      exact v.prop (by rw [show v.val = b i from h]; exact mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
    | inr j => exact hab j i
  have hCh : (T ++ [z]).IsChain (fun x y => K.Adj (P x).target (P y).source) := by
    apply hChain.imp
    intro x y h
    refine ⟨?_,fun i hi => (hTargetOff x i hi).elim⟩
    rw [hSource,hTarget]
    exact h.2
  have hDis (x y : W) (hxy : x ≠ y) : List.Disjoint (P x).vertices (P y).vertices := by
    intro v hv hv'
    cases x with
    | inl x =>
      have hx : v = x.val := List.mem_singleton.mp hv
      subst v
      cases y with
      | inl y =>
        exact hxy (congrArg Sum.inl (Subtype.ext (List.mem_singleton.mp hv')))
      | inr j =>
        change x.val ∈ [b j,a j] at hv'
        rcases List.mem_cons.mp hv' with h | h
        · exact x.prop (h.symm ▸ mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩))
        · exact x.prop ((List.mem_singleton.mp h).symm ▸ mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩))
    | inr i =>
      cases y with
      | inl y =>
        have hy : v = y.val := List.mem_singleton.mp hv'
        subst v
        rcases List.mem_cons.mp (show y.val ∈ [b i,a i] from hv) with h | h
        · exact y.prop (h.symm ▸ mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
        · exact y.prop ((List.mem_singleton.mp h).symm ▸ mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
      | inr j =>
        have hv₁ : v = b i ∨ v = a i := by simpa [P,PathRequest.vertices] using hv
        have hv₂ : v = b j ∨ v = a j := by simpa [P,PathRequest.vertices] using hv'
        rcases hv₁ with h|h <;> rcases hv₂ with h'|h'
        · exact hxy (congrArg Sum.inr (hb (h.symm.trans h')))
        · exact hab j i (h'.symm.trans h)
        · exact hab i j (h.symm.trans h')
        · exact hxy (congrArg Sum.inr (ha (h.symm.trans h')))
  have hCover (v : V) : ∃ w, v ∈ (P w).vertices := by
    by_cases h : v ∈ pairedSet a b
    · rcases mem_union.mp h with h | h
      · obtain ⟨i,_,rfl⟩ := mem_image.mp h
        exact ⟨Sum.inr i,by simp [P,PathRequest.vertices]⟩
      · obtain ⟨i,_,rfl⟩ := mem_image.mp h
        exact ⟨Sum.inr i,by simp [P,PathRequest.vertices]⟩
    · exact ⟨Sum.inl ⟨v,h⟩,by simp [P,PathRequest.vertices]⟩
  obtain ⟨σ,hσ,hC⟩ := exists_spanning_successor
    (expand_auxiliary_merge_cycle_spanning K P hDis hCover ⟨T,z,hND,hAll,hHead,hCh⟩)
  exact ⟨σ,fun v => (hσ v).1,fun i => (hσ (b i)).2 i rfl,hC⟩

end OverfullWork.DirectedRobustExpansion
