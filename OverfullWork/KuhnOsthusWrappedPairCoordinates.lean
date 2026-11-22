module

public import OverfullWork.KuhnOsthusExceptionalIntervalSplit
public import OverfullWork.OsthusStadenTrimmedCopies

@[expose] public section


/-! Pull physical regular pairs back to the identified interval.
For the pair entering the boundary, the target embedding uses the
terminal cell instead of its identified initial copy. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {W V : Type*}

/-- Exact pullback of regularity along the two physical embeddings. -/
theorem uniform_pullDirectedPair [Fintype W] [Fintype V]
    (G : Digraph V) (a b : W ↪ V) (X Y : Finset W) (ε : ℝ)
    (h : IsUniform G ε (X.map a) (Y.map b)) :
    IsUniform (pullDirectedPair a b G) ε X Y := by
  intro S hS T hT hs ht
  rw [density_pullDirectedPair,density_pullDirectedPair]
  exact h (S.map a) (map_subset_map.mpr hS) (T.map b) (map_subset_map.mpr hT)
    (by simpa only [card_map] using hs) (by simpa only [card_map] using ht)

/-- A coordinate change preserves the size of a restricted neighbourhood. -/
theorem profile_pull_embedding [Fintype W] [Fintype V]
    (e : W ↪ V) (A : Finset W) (p : V → Prop) :
    profileCount A (univ.filter (fun x => p (e x))) =
      profileCount (A.map e) (univ.filter p) := by
  have he : (A ∩ univ.filter (fun x => p (e x))).map e =
      A.map e ∩ univ.filter p := by
    ext y
    simp only [mem_map,mem_inter,mem_filter,mem_univ,true_and]
    exact ⟨fun ⟨x,⟨hA,hp⟩,he⟩ => ⟨⟨x,hA,he⟩,he ▸ hp⟩,
      fun ⟨⟨x,hA,he⟩,hp⟩ => ⟨x,⟨hA,he.symm ▸ hp⟩,he⟩⟩
  rw [profileCount,profileCount,←he,card_map]

/-- Both minimum-degree conditions and the density of a physical
successor pair are preserved in its pullback. -/
theorem superregular_pullDirectedPair [Fintype W] [Fintype V]
    (G : Digraph V) (a b : W ↪ V) (X Y : Finset W) (ε d : ℝ)
    (h : IsSuperregularPair G ε d (X.map a) (Y.map b)) :
    IsSuperregularPair (pullDirectedPair a b G) ε d X Y := by
  refine ⟨uniform_pullDirectedPair G a b X Y ε h.1,?_,?_,?_⟩
  · rw [density_pullDirectedPair]
    exact h.2.1
  · intro x hx
    change |profileCount Y (univ.filter (fun y => G.Adj (a x) (b y)))-d*(Y.card:ℝ)| ≤ ε*(Y.card:ℝ)
    rw [profile_pull_embedding b Y (G.Adj (a x))]
    have hx' : a x ∈ X.map a := mem_map.mpr ⟨x,hx,rfl⟩
    simpa only [outProfile,card_map] using h.2.2.1 (a x) hx'
  · intro y hy
    change |profileCount X (univ.filter (fun x => G.Adj (a x) (b y)))-d*(X.card:ℝ)| ≤ ε*(X.card:ℝ)
    rw [profile_pull_embedding a X (fun x => G.Adj x (b y))]
    have hy' : b y ∈ Y.map b := mem_map.mpr ⟨y,hy,rfl⟩
    simpa only [inProfile,card_map] using h.2.2.2 (b y) hy'

/-- Read superregularity in the physical graph from a pair in
common coordinates. Every physical test set pulls back inside its
corresponding side. -/
theorem superregular_of_pullDirectedPair [Fintype W] [Fintype V]
    (G : Digraph V) (a b : W ↪ V) (X Y : Finset W) (ε d : ℝ)
    (h : IsSuperregularPair (pullDirectedPair a b G) ε d X Y) :
    IsSuperregularPair G ε d (X.map a) (Y.map b) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · have hMap (e : W ↪ V) (A : Finset W) (B : Finset V) (hB : B ⊆ A.map e) :
        (A.filter (fun x => e x ∈ B)).map e = B := by
      ext y
      constructor
      · rintro hy
        obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
        exact (mem_filter.mp hx).2
      · intro hy
        obtain ⟨x,hx,rfl⟩ := mem_map.mp (hB hy)
        exact mem_map.mpr ⟨x,mem_filter.mpr ⟨hx,hy⟩,rfl⟩
    intro S hS T hT hSizeS hSizeT
    let S' := X.filter (fun x => a x ∈ S)
    let T' := Y.filter (fun y => b y ∈ T)
    have hS' : S'.map a = S := hMap a X S hS
    have hT' : T'.map b = T := hMap b Y T hT
    have hSizeS' : (X.card:ℝ)*ε ≤ (S'.card:ℝ) := by
      simpa only [←hS',card_map] using hSizeS
    have hSizeT' : (Y.card:ℝ)*ε ≤ (T'.card:ℝ) := by
      simpa only [←hT',card_map] using hSizeT
    have hReg := h.1 S' (filter_subset _ _) T' (filter_subset _ _) hSizeS' hSizeT'
    simpa only [density_pullDirectedPair,hS',hT'] using hReg
  · rw [←density_pullDirectedPair]
    exact h.2.1
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    have hh := h.2.2.1 x hx
    change |profileCount Y (univ.filter (fun y => G.Adj (a x) (b y)))-d*(Y.card:ℝ)| ≤
      ε*(Y.card:ℝ) at hh
    rw [profile_pull_embedding b Y (G.Adj (a x))] at hh
    simpa only [outProfile,card_map] using hh
  · intro v hv
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
    have hh := h.2.2.2 y hy
    change |profileCount X (univ.filter (fun x => G.Adj (a x) (b y)))-d*(X.card:ℝ)| ≤
      ε*(X.card:ℝ) at hh
    rw [profile_pull_embedding a X (fun x => G.Adj x (b y))] at hh
    simpa only [inProfile,card_map] using hh

/-- Select the terminal copy for a target in the identified cluster. -/
noncomputable def wrappedTargetEmbedding (B : Finset W) : W ↪ W ⊕ B where
  toFun x := if h : x ∈ B then Sum.inr ⟨x,h⟩ else Sum.inl x
  inj' := by
    intro x y h
    have hLeft (x : W) : Sum.elim id (fun b : B => b.val)
        (if h : x ∈ B then Sum.inr ⟨x,h⟩ else Sum.inl x) = x := by
      split <;> rfl
    exact (hLeft x).symm.trans ((congrArg (Sum.elim id (fun b : B => b.val)) h).trans (hLeft y))

theorem wrappedTargetEmbedding_inside (B : Finset W) (b : B) :
    wrappedTargetEmbedding B b.val = Sum.inr b := by
  change (if h : b.val ∈ B then (Sum.inr (⟨b.val,h⟩ : ↥B) : W ⊕ ↥B)
    else Sum.inl b.val) = Sum.inr b
  rw [dif_pos b.prop]

theorem wrappedTargetEmbedding_outside (B : Finset W) (y : W) (hy : y ∉ B) :
    wrappedTargetEmbedding B y = Sum.inl y := by
  change (if h : y ∈ B then (Sum.inr (⟨y,h⟩ : ↥B) : W ⊕ ↥B)
    else Sum.inl y) = Sum.inl y
  rw [dif_neg hy]

/-- Every reopened arc of the pullback is an actual physical arc. -/
theorem split_wrapped_pair_lifts (G : Digraph V) (B : Finset W) (f : W ⊕ B ↪ V) :
    let H := pullDirectedPair (Function.Embedding.inl.trans f) ((wrappedTargetEmbedding B).trans f) G
    ∀ x y, (splitIntervalDigraph H B).Adj x y → G.Adj (f x) (f y) := by
  dsimp only
  rintro (x|x) (y|y) h
  · obtain ⟨hy,h⟩ := h
    change G.Adj (f (Sum.inl x)) (f (wrappedTargetEmbedding B y)) at h
    rwa [wrappedTargetEmbedding_outside B y hy] at h
  · change G.Adj (f (Sum.inl x)) (f (wrappedTargetEmbedding B y.val)) at h
    rwa [wrappedTargetEmbedding_inside B y] at h
  · exact h.elim
  · exact h.elim

/-- The target side outside the boundary uses its ordinary physical
coordinates. -/
theorem map_wrapped_target_outside (B S : Finset W) (f : W ⊕ B ↪ V) (h : Disjoint S B) :
    S.map ((wrappedTargetEmbedding B).trans f) = S.map (Function.Embedding.inl.trans f) := by
  ext v
  simp only [mem_map,Function.Embedding.trans_apply]
  have he (x : W) (hx : x ∈ S) :
      wrappedTargetEmbedding B x = Sum.inl x :=
    wrappedTargetEmbedding_outside B x (fun hy => disjoint_left.mp h hx hy)
  exact ⟨fun ⟨x,hx,hv⟩ => ⟨x,hx,(congrArg f (he x hx)).symm.trans hv⟩,
    fun ⟨x,hx,hv⟩ => ⟨x,hx,(congrArg f (he x hx)).trans hv⟩⟩

/-- The target side at the boundary is precisely the physical
terminal cell. -/
theorem map_wrapped_target_boundary (B : Finset W) (f : W ⊕ B ↪ V) :
    B.map ((wrappedTargetEmbedding B).trans f) =
      (univ : Finset B).map (Function.Embedding.inr.trans f) := by
  ext v
  simp only [mem_map,mem_univ,true_and,Function.Embedding.trans_apply]
  constructor
  · rintro ⟨y,hy,he⟩
    let b : B := ⟨y,hy⟩
    have he' : wrappedTargetEmbedding B y = Sum.inr b :=
      wrappedTargetEmbedding_inside B b
    rw [he'] at he
    exact ⟨b,he⟩
  · rintro ⟨b,he⟩
    exact ⟨b,b.prop,by rw [wrappedTargetEmbedding_inside]; exact he⟩

/-- Pull back all consecutive pairs. Only the pair entering the
identified first cluster uses the physical terminal cell. -/
theorem wrapped_successor_superregularity {I : Type*} [DecidableEq I] [Fintype W] [Fintype V]
    (G : Digraph V) (C : I → Finset W) (s : Equiv.Perm I) (first : I)
    (f : W ⊕ ↥(C first) ↪ V) (ε d : ℝ)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hPair : ∀ i, IsSuperregularPair G ε d ((C i).map (Function.Embedding.inl.trans f))
      (if s i = first then (univ : Finset ↥(C first)).map (Function.Embedding.inr.trans f)
       else (C (s i)).map (Function.Embedding.inl.trans f))) :
    let H := pullDirectedPair (Function.Embedding.inl.trans f)
      ((wrappedTargetEmbedding (C first)).trans f) G
    (∀ i, IsSuperregularPair H ε d (C i) (C (s i))) ∧
      ∀ x y, (splitIntervalDigraph H (C first)).Adj x y → G.Adj (f x) (f y) := by
  dsimp only
  refine ⟨?_,split_wrapped_pair_lifts G (C first) f⟩
  intro i
  apply superregular_pullDirectedPair
  by_cases h : s i = first
  · rw [h,map_wrapped_target_boundary]
    simpa only [if_pos h] using hPair i
  · rw [map_wrapped_target_outside _ _ _ (hDis _ _ h)]
    simpa only [if_neg h] using hPair i

end OverfullWork.DirectedRobustExpansion
