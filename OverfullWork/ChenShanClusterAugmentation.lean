module

public import OverfullWork.ChenShanClusterCycleDemands
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

private theorem card_occupied_cluster_le
    {E I J V : Type*} [DecidableEq V]
    (T : Finset E) (L : I → Finset V) (R : J → Finset V) (i : I)
    (src : E → I) (dst : E → J) (f g : E → V) (blocked : Finset V)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hCross : ∀ i j, Disjoint (L i) (R j))
    (hf : ∀ e ∈ T, f e ∈ L (src e)) (hg : ∀ e ∈ T, g e ∈ R (dst e)) :
    (L i ∩ (blocked ∪ (T.image f ∪ T.image g))).card ≤
      (L i ∩ blocked).card + (T.filter (fun e => src e = i)).card := by
  calc
    _ ≤ ((L i ∩ blocked) ∪ (T.filter (fun e => src e = i)).image f).card := by
      apply card_le_card
      intro x hx
      obtain ⟨hxi, hUsed⟩ := mem_inter.mp hx
      rcases mem_union.mp hUsed with hBlocked | hImage
      · exact mem_union_left _ (mem_inter.mpr ⟨hxi, hBlocked⟩)
      rcases mem_union.mp hImage with hLeft | hRight
      · obtain ⟨e, he, rfl⟩ := mem_image.mp hLeft
        have hEq : src e = i := by
          by_contra hNe
          exact disjoint_left.mp (hL hNe) (hf e he) hxi
        exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨he, hEq⟩))
      · obtain ⟨e, he, rfl⟩ := mem_image.mp hRight
        exact (disjoint_left.mp (hCross i (dst e)) hxi (hg e he)).elim
    _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)

private theorem card_filter_lt_of_fresh
    {E : Type*} (Q T : Finset E) (e : E) (heQ : e ∈ Q) (heT : e ∉ T) (hT : T ⊆ Q)
    (P : E → Prop) [DecidablePred P] (he : P e) :
    (T.filter P).card < (Q.filter P).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset_filter _ hT, fun h => ?_⟩
  exact heT (mem_filter.mp (h ▸ mem_filter.mpr ⟨heQ, he⟩)).1

/-- Realize a finite collection of augmentation requests using
different vertices at both ends, while avoiding the vertices
already covered by the exceptional matching. The right-hand
degree bound accounts for every request ending in its cluster. -/
theorem exists_cluster_augmentation_matching
    {E I J V : Type*} [DecidableEq V] [Nonempty V]
    (adj : V → V → Prop) [DecidableRel adj]
    (Q : Finset E) (L : I → Finset V) (R : J → Finset V)
    (src : E → I) (dst : E → J) (blocked : Finset V)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCross : ∀ i j, Disjoint (L i) (R j))
    (hLeft : ∀ i, (L i ∩ blocked).card + (Q.filter (fun e => src e = i)).card ≤ (L i).card)
    (hRight : ∀ e ∈ Q, ∀ u ∈ L (src e), u ∉ blocked →
      (R (dst e) ∩ blocked).card + (Q.filter (fun d => dst d = dst e)).card ≤
        ((R (dst e)).filter (adj u)).card) :
    ∃ f g : E → V, Set.InjOn f (Q : Set E) ∧ Set.InjOn g (Q : Set E) ∧
      ∀ e ∈ Q, f e ∈ L (src e) ∧ g e ∈ R (dst e) ∧
        f e ∉ blocked ∧ g e ∉ blocked ∧ adj (f e) (g e) := by
  classical
  have hPartial : ∀ T ⊆ Q, ∃ f g : E → V,
      Set.InjOn f (T : Set E) ∧ Set.InjOn g (T : Set E) ∧
      ∀ e ∈ T, f e ∈ L (src e) ∧ g e ∈ R (dst e) ∧
        f e ∉ blocked ∧ g e ∉ blocked ∧ adj (f e) (g e) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      let w : V := Classical.choice ‹Nonempty V›
      exact ⟨fun _ => w, fun _ => w, by simp, by simp, by simp⟩
    | @insert e T heT ih =>
      intro hSubset
      have heQ := hSubset (mem_insert_self e T)
      have hTQ := (subset_insert e T).trans hSubset
      obtain ⟨f, g, hfi, hgi, hfg⟩ := ih hTQ
      let used := blocked ∪ (T.image f ∪ T.image g)
      have hLeft' : (L (src e) ∩ used).card < (L (src e)).card := by
        apply (card_occupied_cluster_le T L R (src e) src dst f g blocked hL hCross
          (fun t ht => (hfg t ht).1) (fun t ht => (hfg t ht).2.1)).trans_lt
        have hStrict := card_filter_lt_of_fresh Q T e heQ heT hTQ (fun t => src t = src e) rfl
        exact (Nat.add_lt_add_left hStrict _).trans_le (hLeft (src e))
      have hRight' : ∀ u ∈ L (src e), u ∉ used →
          (R (dst e) ∩ used).card < ((R (dst e)).filter (adj u)).card := by
        intro u hu huFree
        have hCount := card_occupied_cluster_le T R L (dst e) dst src g f blocked hR
          (fun j i => (hCross i j).symm) (fun t ht => (hfg t ht).2.1)
          (fun t ht => (hfg t ht).1)
        have hCount' : (R (dst e) ∩ used).card ≤
            (R (dst e) ∩ blocked).card + (T.filter (fun t => dst t = dst e)).card := by
          simpa only [used, union_comm (T.image f) (T.image g)] using hCount
        have hStrict := card_filter_lt_of_fresh Q T e heQ heT hTQ (fun t => dst t = dst e) rfl
        exact hCount'.trans_lt ((Nat.add_lt_add_left hStrict _).trans_le
          (hRight e heQ u hu (fun hb => huFree (mem_union_left _ hb))))
      obtain ⟨u, hu, v, hv, huFree, hvFree, huv⟩ :=
        exists_cluster_augmentation_edge adj (L (src e)) (R (dst e)) used hLeft' hRight'
      have hUpdate (h : E → V) (w : V) (hinj : Set.InjOn h (T : Set E))
          (hw : w ∉ T.image h) :
          Set.InjOn (Function.update h e w) (↑(insert e T) : Set E) := by
        rw [coe_insert, Set.injOn_insert (show e ∉ (T : Set E) from heT)]
        constructor
        · intro x hx y hy hxy
          have hx' : x ≠ e := fun hEq => heT (hEq ▸ hx)
          have hy' : y ≠ e := fun hEq => heT (hEq ▸ hy)
          exact hinj hx hy (by simpa [Function.update_of_ne hx', Function.update_of_ne hy'] using hxy)
        · rintro ⟨x, hx, hEq⟩
          have hx' : x ≠ e := fun hEq => heT (hEq ▸ hx)
          have hxw : h x = w := by simpa [Function.update_of_ne hx'] using hEq
          exact hw (hxw ▸ mem_image_of_mem h hx)
      refine ⟨Function.update f e u, Function.update g e v,
        hUpdate f u hfi (fun h => huFree (mem_union_right _ (mem_union_left _ h))),
        hUpdate g v hgi (fun h => hvFree (mem_union_right _ (mem_union_right _ h))), ?_⟩
      intro t ht
      by_cases hEq : t = e
      · subst t
        simpa using And.intro hu (And.intro hv (And.intro
          (show u ∉ blocked from fun h => huFree (mem_union_left _ h))
          (And.intro (show v ∉ blocked from fun h => hvFree (mem_union_left _ h)) huv)))
      · simpa [Function.update_of_ne hEq] using hfg t ((mem_insert.mp ht).resolve_left hEq)
  exact hPartial Q Subset.rfl

/-- One request for each unit of the integral cluster assignment. -/
abbrev ClusterAugmentationRequest {I : Type*} (H : I → I → ℕ) :=
  Σ i : I, Σ j : I, Fin (H i j)

private theorem card_requests_from {I : Type*} [Fintype I] (H : I → I → ℕ) (i : I) :
    ((univ : Finset (ClusterAugmentationRequest H)).filter (fun e => e.1 = i)).card = ∑ j, H i j := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  rw [sum_eq_single i]
  · simp [Fintype.card_sigma]
  · intro x _ h
    simp [h]
  · simp

private theorem card_requests_to {I : Type*} [Fintype I] (H : I → I → ℕ) (j : I) :
    ((univ : Finset (ClusterAugmentationRequest H)).filter (fun e => e.2.1 = j)).card = ∑ i, H i j := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  rw [Fintype.sum_sigma, sum_eq_single j]
  · simp
  · intro x _ h
    simp [h]
  · simp

private theorem card_cluster_after_augmentation {E I V : Type*} [Fintype E] [DecidableEq V]
    (C : I → Finset V) (label : E → I) (f : E → V) (blocked : Finset V) (i : I)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hf : Function.Injective f) (hMem : ∀ e, f e ∈ C (label e))
    (hFree : ∀ e, f e ∉ blocked) :
    (C i ∩ (blocked ∪ univ.image f)).card =
      (C i ∩ blocked).card + (univ.filter (fun e => label e = i)).card := by
  let S := (univ : Finset E).filter (fun e => label e = i)
  have hEq : C i ∩ univ.image f = S.image f := by
    ext v
    constructor
    · intro hv
      obtain ⟨hCiv, hImage⟩ := mem_inter.mp hv
      obtain ⟨e, _, rfl⟩ := mem_image.mp hImage
      have hLabel : label e = i := by
        by_contra hn
        exact disjoint_left.mp (hC hn) (hMem e) hCiv
      exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hLabel⟩)
    · intro hv
      obtain ⟨e, he, rfl⟩ := mem_image.mp hv
      exact mem_inter.mpr ⟨(mem_filter.mp he).2 ▸ hMem e, mem_image_of_mem _ (mem_univ _)⟩
  have hDisj : Disjoint (C i ∩ blocked) (S.image f) := by
    apply disjoint_left.mpr
    intro v hv hImage
    obtain ⟨e, _, rfl⟩ := mem_image.mp hImage
    exact hFree e (mem_inter.mp hv).2
  rw [inter_union_distrib_left, hEq, card_union_of_disjoint hDisj, card_image_of_injective _ hf]

/-- The augmentation in §5.1.5. Realize the loads on the cluster
cycle with an actual matching. Each cluster ends up with exactly
the target number of covered vertices. -/
theorem exists_clusterCycle_augmentation_matching
    {I V : Type*} [Fintype I] [DecidableEq V] [Nonempty V]
    (next : Equiv.Perm I) (hCycle : ∀ i j, next.SameCycle i j)
    (adj : V → V → Prop) [DecidableRel adj]
    (L R : I → Finset V) (blocked : Finset V) (b z : ℕ)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCross : ∀ i j, Disjoint (L i) (R j))
    (hz : z ≤ b) (hBudget : Fintype.card I*z ≤ b)
    (hA : ∀ i, (L i ∩ blocked).card ≤ z) (hB : ∀ i, (R i ∩ blocked).card ≤ z)
    (hBalance : (∑ i, (L i ∩ blocked).card) = ∑ i, (R i ∩ blocked).card)
    (hLeft : ∀ i, b ≤ (L i).card)
    (hDegree : ∀ i j, (j = i ∨ j = next i) → ∀ u ∈ L i, u ∉ blocked →
      b ≤ ((R j).filter (adj u)).card) :
    ∃ (H : I → I → ℕ) (f g : ClusterAugmentationRequest H → V),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ e, (e.2.1 = e.1 ∨ e.2.1 = next e.1) ∧
        f e ∈ L e.1 ∧ g e ∈ R e.2.1 ∧ f e ∉ blocked ∧ g e ∉ blocked ∧ adj (f e) (g e)) ∧
      (∀ i, (L i ∩ (blocked ∪ univ.image f)).card = b) ∧
      (∀ j, (R j ∩ (blocked ∪ univ.image g)).card = b) := by
  classical
  obtain ⟨H, hSupport, hRow, hCol⟩ := exists_clusterCycle_augmentation_loads next hCycle
    (fun i => (L i ∩ blocked).card) (fun j => (R j ∩ blocked).card) b z hz hBudget hA hB hBalance
  let E := ClusterAugmentationRequest H
  let src (e : E) := e.1
  let dst (e : E) := e.2.1
  have hAllowed (e : E) : dst e = src e ∨ dst e = next (src e) := by
    by_contra hn
    exact (Nat.ne_of_gt (Nat.zero_lt_of_lt e.2.2.isLt)) (hSupport _ _ (fun h => hn (Or.inl h))
      (fun h => hn (Or.inr h)))
  have hCL (i : I) : ((univ : Finset E).filter (fun e => src e = i)).card = ∑ j, H i j :=
    card_requests_from H i
  have hCR (j : I) : ((univ : Finset E).filter (fun e => dst e = j)).card = ∑ i, H i j :=
    card_requests_to H j
  obtain ⟨f, g, hfi, hgi, hMem⟩ := exists_cluster_augmentation_matching adj
    (univ : Finset E) L R src dst blocked hL hR hCross
    (fun i => by rw [hCL, hRow]; exact hLeft i)
    (fun e _ u hu hFree => by rw [hCR, hCol]; exact hDegree _ _ (hAllowed e) u hu hFree)
  have hInjectF : Function.Injective f := by simpa using hfi
  have hInjectG : Function.Injective g := by simpa using hgi
  have hE (e : E) := hMem e (mem_univ e)
  refine ⟨H, f, g, hInjectF, hInjectG, fun e => ⟨hAllowed e, hE e⟩, ?_, ?_⟩
  · intro i
    rw [card_cluster_after_augmentation L src f blocked i hL hInjectF
      (fun e => (hE e).1) (fun e => (hE e).2.2.1)]
    exact (congrArg ((L i ∩ blocked).card + ·) (card_requests_from H i)).trans (hRow i)
  · intro j
    rw [card_cluster_after_augmentation R dst g blocked j hR hInjectG
      (fun e => (hE e).2.1) (fun e => (hE e).2.2.2.1)]
    exact (congrArg ((R j ∩ blocked).card + ·) (card_requests_to H j)).trans (hCol j)


/-- A previously chosen matching rules out at most one neighbor of
each fixed left endpoint. Other vertices covered by that matching
can be used in the second augmentation. -/
theorem augmentation_neighbour_loss_le_one
    {E V : Type*} [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (f g : E → V) (hf : Function.Injective f) (R : Finset V) (u : V) :
    (R.filter (adj u)).card ≤
      (R.filter (fun v => adj u v ∧ ¬ ∃ e, f e = u ∧ g e = v)).card + 1 := by
  let old (v : V) := ∃ e, f e = u ∧ g e = v
  have hOne : ((R.filter (adj u)).filter old).card ≤ 1 := by
    apply card_le_one.mpr
    intro v hv w hw
    obtain ⟨e, he, hv'⟩ := (mem_filter.mp hv).2
    obtain ⟨d, hd, hw'⟩ := (mem_filter.mp hw).2
    have h := hf (he.trans hd.symm)
    exact hv'.symm.trans (h ▸ hw')
  have hSum := card_filter_add_card_filter_not (s := R.filter (adj u)) old
  simp only [filter_filter] at hSum hOne
  change (R.filter (adj u)).card ≤ (R.filter (fun v => adj u v ∧ ¬old v)).card + 1
  omega

/-- Run the augmentation on a second cycle after forbidding the
real edges chosen for the first one. A one-neighbor margin suffices. -/
theorem exists_clusterCycle_augmentation_matching_avoiding
    {E I V : Type*} [Fintype I] [DecidableEq V] [Nonempty V]
    (next : Equiv.Perm I) (hCycle : ∀ i j, next.SameCycle i j)
    (adj : V → V → Prop) [DecidableRel adj]
    (f₀ g₀ : E → V) (hf₀ : Function.Injective f₀)
    (L R : I → Finset V) (blocked : Finset V) (b z : ℕ)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCross : ∀ i j, Disjoint (L i) (R j))
    (hz : z ≤ b) (hBudget : Fintype.card I*z ≤ b)
    (hA : ∀ i, (L i ∩ blocked).card ≤ z) (hB : ∀ i, (R i ∩ blocked).card ≤ z)
    (hBalance : (∑ i, (L i ∩ blocked).card) = ∑ i, (R i ∩ blocked).card)
    (hLeft : ∀ i, b ≤ (L i).card)
    (hDegree : ∀ i j, (j = i ∨ j = next i) → ∀ u ∈ L i, u ∉ blocked →
      b+1 ≤ ((R j).filter (adj u)).card) :
    ∃ (H : I → I → ℕ) (f g : ClusterAugmentationRequest H → V),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ e, (e.2.1 = e.1 ∨ e.2.1 = next e.1) ∧
        f e ∈ L e.1 ∧ g e ∈ R e.2.1 ∧ f e ∉ blocked ∧ g e ∉ blocked ∧
        adj (f e) (g e) ∧ ¬ (∃ d, f₀ d = f e ∧ g₀ d = g e)) ∧
      (∀ i, (L i ∩ (blocked ∪ univ.image f)).card = b) ∧
      (∀ j, (R j ∩ (blocked ∪ univ.image g)).card = b) := by
  classical
  let remaining : V → V → Prop := fun u v => adj u v ∧ ¬ ∃ d, f₀ d = u ∧ g₀ d = v
  have hRemaining (i j : I) (hPair : j = i ∨ j = next i) (u : V)
      (hu : u ∈ L i) (hFree : u ∉ blocked) :
      b ≤ ((R j).filter (remaining u)).card := by
    have hLoss : ((R j).filter (adj u)).card ≤ ((R j).filter (remaining u)).card + 1 :=
      augmentation_neighbour_loss_le_one adj f₀ g₀ hf₀ (R j) u
    exact Nat.le_of_add_le_add_right ((hDegree i j hPair u hu hFree).trans hLoss)
  exact exists_clusterCycle_augmentation_matching next hCycle remaining L R blocked b z
    hL hR hCross hz hBudget hA hB hBalance hLeft hRemaining

end OverfullWork.ChenShan
