module

public import OverfullWork.InducedDigraphSampling
public import OverfullWork.RobustClusterQuotient

@[expose] public section


/-! Induced robust expansion under changes of vertex set and arc deletions.
This supplies the two block updates (I) in GGKLO Lemma 7.3(i). -/
namespace OverfullWork.InducedDigraphSampling

open Finset DirectedRobustExpansion RobustClusterQuotient
open scoped Classical
variable {V : Type*} [Fintype V]

omit [Fintype V] in
private theorem count_subtype_filter (A S : Finset V) (h : S ⊆ A) (P : V → Prop) :
    ((S.subtype (· ∈ A)).filter (fun w => P w.val)).card = (S.filter P).card := by
  apply card_bij (fun w _ => w.val)
  · intro w hw
    exact mem_filter.mpr ⟨mem_subtype.mp (mem_filter.mp hw).1,(mem_filter.mp hw).2⟩
  · intro w _ z _ he
    exact Subtype.ext he
  · intro w hw
    obtain ⟨hs,hp⟩ := mem_filter.mp hw
    exact ⟨⟨w,h hs⟩,mem_filter.mpr ⟨mem_subtype.mpr hs,hp⟩,rfl⟩

omit [Fintype V] in
private theorem count_subtype (A S : Finset V) (h : S ⊆ A) :
    (S.subtype (· ∈ A)).card = S.card := by
  simpa using count_subtype_filter A S h (fun _ => True)

omit [Fintype V] in
private theorem image_subtype (A : Finset V) (T : Finset A) :
    (T.map (Function.Embedding.subtype (· ∈ A))).subtype (· ∈ A) = T := by
  ext w
  exact ⟨fun h => (Function.Embedding.subtype (· ∈ A)).injective
      (mem_map.mp (mem_subtype.mp h)).choose_spec.2 ▸
        (mem_map.mp (mem_subtype.mp h)).choose_spec.1,
    fun h => mem_subtype.mpr (mem_map.mpr ⟨w,h,rfl⟩)⟩

omit [Fintype V] in
private theorem block_count_eq (D : Digraph V) (A S : Finset V) (hS : S ⊆ A)
    (ν : ℝ) :
    (realNeighbourhood (induced D A) ν (S.subtype (· ∈ A))).card =
    (A.filter (fun v => ν*(A.card:ℝ) ≤ (inNeighbours D S v:ℝ))).card := by
  have hN (v : A) : inNeighbours (induced D A) (S.subtype (· ∈ A)) v =
      inNeighbours D S v.val := count_subtype_filter A S hS (fun w => D.Adj w v.val)
  unfold realNeighbourhood
  have hU : (univ : Finset A) = A.subtype (· ∈ A) := by
    ext w
    exact ⟨fun _ => mem_subtype.mpr w.prop,fun _ => mem_univ _⟩
  rw [hU]
  refine Eq.trans ?_ (count_subtype_filter A A Subset.rfl _)
  congr 1
  ext w
  simp only [mem_filter,hN,Fintype.card_coe]

omit [Fintype V] in
/-- Ambient vertex-set characterization of the robust expansion of an
induced subdigraph. Degrees are still evaluated against the test set. -/
theorem induced_real_robust_iff (D : Digraph V) (A : Finset V) (ν τ : ℝ) :
    IsRealRobust (induced D A) ν τ ↔
      ∀ S : Finset V, S ⊆ A → τ*(A.card:ℝ) ≤ (S.card:ℝ) →
        (S.card:ℝ) ≤ (1-τ)*(A.card:ℝ) →
        (S.card:ℝ)+ν*(A.card:ℝ) ≤
          ((A.filter (fun v => ν*(A.card:ℝ) ≤ (inNeighbours D S v:ℝ))).card:ℝ) := by
  constructor
  · intro h S hS hlo hhi
    have hCard := count_subtype A S hS
    have hh := h (S.subtype (· ∈ A)) (by simpa only [Fintype.card_coe,hCard] using hlo)
      (by simpa only [Fintype.card_coe,hCard] using hhi)
    simpa only [Fintype.card_coe,hCard,block_count_eq D A S hS ν] using hh
  · intro h T hlo hhi
    let S := T.map (Function.Embedding.subtype (· ∈ A))
    have hS : S ⊆ A := fun _ hv => property_of_mem_map_subtype T hv
    have hCard : S.card = T.card := card_map _
    have hh := h S hS (by simpa only [Fintype.card_coe,hCard] using hlo)
      (by simpa only [Fintype.card_coe,hCard] using hhi)
    rw [← block_count_eq D A S hS ν,image_subtype A T] at hh
    simpa only [Fintype.card_coe,hCard] using hh

/-- Replace the inducing set and delete arcs at the same time. The lower
interval pays for the new vertices in the test set. Growth pays for
vertices on both sides of the symmetric difference and for arc loss. -/
theorem induced_real_robust_of_perturbation (D H : Digraph V) (A B : Finset V)
    (ν τ μ σ : ℝ) (g : ℕ)
    (hD : IsRealRobust (induced D A) ν τ)
    (hLe : H ≤ D) (hLoss : ∀ v, inDegree (D \ H) v ≤ g)
    (hLow : τ*(A.card:ℝ)+((B \ A).card:ℝ) ≤ σ*(B.card:ℝ))
    (hHigh : (1-σ)*(B.card:ℝ) ≤ (1-τ)*(A.card:ℝ))
    (hBudget : μ*(B.card:ℝ)+((A \ B).card:ℝ)+((B \ A).card:ℝ)+(g:ℝ) ≤
      ν*(A.card:ℝ)) :
    IsRealRobust (induced H B) μ σ := by
  rw [induced_real_robust_iff] at hD ⊢
  intro S hS hlo hhi
  let T := S ∩ A
  have hInter (X Y : Finset V) : X.card ≤ (X ∩ Y).card+(X \ Y).card := by
    have he : X.filter (fun v => v ∉ Y) = X \ Y := by
      ext v
      exact mem_filter.trans mem_sdiff.symm
    simpa only [filter_mem_eq_inter,he] using
      (card_filter_add_card_filter_not (s := X) (p := fun v => v ∈ Y)).ge
  have hNew : (S \ A).card ≤ (B \ A).card :=
    card_le_card (sdiff_subset_sdiff_left _ hS)
  have hTlo : (S.card:ℝ) ≤ (T.card:ℝ)+((B \ A).card:ℝ) := by
    exact_mod_cast (hInter S A).trans (Nat.add_le_add_left hNew _)
  have hThi : (T.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card inter_subset_left
  let N := A.filter (fun v => ν*(A.card:ℝ) ≤ (inNeighbours D T v:ℝ))
  have hGrow : (T.card:ℝ)+ν*(A.card:ℝ) ≤ (N.card:ℝ) :=
    hD T inter_subset_right (by linarith only [hLow,hlo,hTlo]) (hThi.trans (hhi.trans hHigh))
  let Q := B.filter (fun v => μ*(B.card:ℝ) ≤ (inNeighbours H S v:ℝ))
  have hSub : N ∩ B ⊆ Q := by
    intro v hv
    obtain ⟨hn,hb⟩ := mem_inter.mp hv
    have hDn := (mem_filter.mp hn).2
    have hg : (inNeighbours D T v:ℝ) ≤ (inNeighbours H T v:ℝ)+(g:ℝ) := by
      exact_mod_cast neighbour_loss_of_deleted_indegree D H hLe g hLoss T v
    have hMono : (inNeighbours H T v:ℝ) ≤ inNeighbours H S v := by
      exact_mod_cast inNeighbours_mono H (show T ⊆ S from inter_subset_left) v
    have hNonneg : 0 ≤ ((A \ B).card:ℝ) ∧ 0 ≤ ((B \ A).card:ℝ) :=
      ⟨Nat.cast_nonneg _,Nat.cast_nonneg _⟩
    exact mem_filter.mpr ⟨hb,by linarith only [hDn,hg,hMono,hBudget,hNonneg.1,hNonneg.2]⟩
  have hOld : (N \ B).card ≤ (A \ B).card :=
    card_le_card (sdiff_subset_sdiff_left _ (filter_subset _ _))
  have hVol : (N.card:ℝ) ≤ (Q.card:ℝ)+((A \ B).card:ℝ) := by
    exact_mod_cast (hInter N B).trans (Nat.add_le_add (card_le_card hSub) hOld)
  have hg : 0 ≤ (g:ℝ) := Nat.cast_nonneg _
  linarith only [hGrow,hVol,hTlo,hBudget,hg]

/-- Trim or enlarge a sampled block by a small set. Both parts of a
partition can therefore use the same expansion margins after trimming. -/
theorem induced_robust_after_small_vertex_changes (D : Digraph V) (A B : Finset V)
    (ν τ : ℝ) (z : ℕ) (hν : 0 ≤ ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/2)
    (hD : IsRealRobust (induced D A) ν τ)
    (hLost : (A \ B).card ≤ z) (hAdded : (B \ A).card ≤ z)
    (hBudgetν : 8*(z:ℝ) ≤ ν*(A.card:ℝ)) (hBudgetτ : 4*(z:ℝ) ≤ τ*(A.card:ℝ)) :
    IsRealRobust (induced D B) (ν/2) (2*τ) := by
  have hLost' : ((A \ B).card:ℝ) ≤ (z:ℝ) := by exact_mod_cast hLost
  have hAdd' : ((B \ A).card:ℝ) ≤ (z:ℝ) := by exact_mod_cast hAdded
  have hLow : (A.card:ℝ) ≤ (B.card:ℝ)+(z:ℝ) := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := A) (t := B)).trans (by omega)
  have hHigh : (B.card:ℝ) ≤ (A.card:ℝ)+(z:ℝ) := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := B) (t := A)).trans (by omega)
  have hz : 0 ≤ (z:ℝ) := Nat.cast_nonneg _
  apply induced_real_robust_of_perturbation D D A B ν τ (ν/2) (2*τ) 0 hD le_rfl
  · intro x
    simp [sdiff_self,inDegree,inNeighbours,Digraph.bot_adj]
  · have h₁ := mul_le_mul_of_nonneg_left hLow (show 0 ≤ 2*τ by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (show 2*τ ≤ 1 by linarith) hz
    nlinarith only [h₁,h₂,hBudgetτ,hAdd',hz]
  · have h₁ := mul_le_mul_of_nonneg_left hHigh (show 0 ≤ 1-2*τ by linarith)
    have h₂ := mul_le_mul_of_nonneg_right (show 1-2*τ ≤ 1 by linarith) hz
    nlinarith only [h₁,h₂,hBudgetτ,hz]
  · have h₁ := mul_le_mul_of_nonneg_left hHigh (show 0 ≤ ν/2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (show ν/2 ≤ 1/2 by linarith) hz
    push_cast
    nlinarith only [h₁,h₂,hBudgetν,hAdd',hLost',hz]

end OverfullWork.InducedDigraphSampling
