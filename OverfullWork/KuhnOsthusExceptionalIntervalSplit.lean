module

public import OverfullWork.KuhnOsthusExceptionalPairStability
public import OverfullWork.FactorMergeCoarsening
public import OverfullWork.MergeFactorCut

@[expose] public section


/-! Split the identified endpoint clusters in Kühn–Osthus Lemma 7.6.
Incoming arcs at the identified cluster use the final copy, while
outgoing arcs use the initial copy. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedAbsorbingLadder DirectedListRoutes
open scoped Classical
variable {V : Type*}

/-- Undo the identification of the two boundary clusters. Ordinary
vertices and the first cluster keep their labels; the last cluster
gets its own copy. -/
def splitIntervalDigraph (G : Digraph V) (B : Finset V) : Digraph (V ⊕ B) :=
  ⟨fun x y => match x,y with
    | .inl v,.inl w => w ∉ B ∧ G.Adj v w
    | .inl v,.inr w => G.Adj v w
    | .inr _,_ => False⟩

private theorem split_interval_mono {G H : Digraph V} (h : G ≤ H) (B : Finset V) :
    splitIntervalDigraph G B ≤ splitIntervalDigraph H B := by
  rintro (v|v) (w|w) hv
  · exact ⟨hv.1,h hv.2⟩
  · exact h hv
  · exact hv.elim
  · exact hv.elim

/-- Split every arc entering the identified boundary and obtain
one path per final vertex. The paths exhaust the physical vertices. -/
theorem exists_interval_paths_of_wraparound_factor [Fintype V]
    (σ : Equiv.Perm V) (B : Finset V)
    (hHit : ∀ v, ∃ b ∈ B, σ.SameCycle v b) :
    ∃ P : B → PathRequest (splitIntervalDigraph (⟨fun x y => σ x = y⟩ : Digraph V) B),
      ∃ starts : Equiv.Perm B,
        (∀ b, (P b).source = Sum.inl (starts b).val ∧ (P b).target = Sum.inr b) ∧
        (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) ∧
        ∀ v, ∃ i, v ∈ (P i).vertices := by
  classical
  let S := B.image σ.symm
  have hBoundary (v : V) : v ∈ S ↔ σ v ∈ B := by
    constructor
    · intro hv
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
      simpa using hb
    · intro hv
      exact mem_image.mpr ⟨σ v,hv,σ.symm_apply_apply v⟩
  obtain ⟨Q,orig,hQ,hApart,hCover⟩ := exists_cut_factor_paths σ S (fun v => by
    obtain ⟨b,hb,hPath⟩ := hHit v
    exact ⟨σ.symm b,mem_image.mpr ⟨b,hb,rfl⟩,hPath.symm_apply_right⟩)
  let f : S → B := fun i => ⟨σ i,(hBoundary _).mp i.prop⟩
  have hBij : Function.Bijective f :=
    ⟨fun _ _ h => Subtype.ext (σ.injective (congrArg Subtype.val h)),fun b =>
      ⟨⟨σ.symm b,(hBoundary _).mpr (by simp)⟩,Subtype.ext (σ.apply_symm_apply b)⟩⟩
  let e := Equiv.ofBijective f hBij
  let G := splitIntervalDigraph (⟨fun x y => σ x = y⟩ : Digraph V) B
  let emb : V → V ⊕ B := Sum.inl
  have hMiddle (i : S) : Route G (emb (Q i).source) (emb (Q i).target) ((Q i).tail.map emb) := by
    constructor
    · change ((Q i).vertices.map emb).IsChain G.Adj
      apply List.isChain_map_of_isChain emb _ (Q i).route.1
      intro x y h
      change x ∉ S ∧ σ x = y at h
      have hy : y ∉ B := fun hy => h.1 ((hBoundary x).mpr (h.2.symm ▸ hy))
      exact ⟨hy,h.2⟩
    · change ((Q i).vertices.map emb).getLast? = _
      rw [List.getLast?_map]
      change ((Q i).source :: (Q i).tail).getLast?.map emb = _
      rw [(Q i).route.2]
      rfl
  have hFinal (i : S) : G.Adj (emb (Q i).target) (.inr (e i)) := by
    change σ (Q i).target = σ i
    rw [(hQ i).1]
  let P' (i : S) : PathRequest G :=
    ⟨emb (Q i).source,.inr (e i),(Q i).tail.map emb ++ [(Sum.inr (e i) : V ⊕ B)],
      snoc_route G (hMiddle i) (hFinal i),by
        change ((Q i).vertices.map emb ++ [(Sum.inr (e i) : V ⊕ B)]).Nodup
        refine List.nodup_append.mpr ⟨(Q i).simple.map Sum.inl_injective,by simp,?_⟩
        intro x hx y hy
        obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
        obtain rfl := List.mem_singleton.mp hy
        exact Sum.inl_ne_inr⟩
  let P (i : B) := P' (e.symm i)
  refine ⟨P,e.symm.trans (orig.trans e),?_,?_,?_⟩
  · intro b
    change emb (Q (e.symm b)).source = emb (σ (orig (e.symm b)).val) ∧
      (Sum.inr (e (e.symm b)) : V ⊕ B) = Sum.inr b
    rw [(hQ _).2,e.apply_symm_apply]
    exact ⟨rfl,rfl⟩
  · intro i j hij x hxi hxj
    change x ∈ (Q (e.symm i)).vertices.map emb ++ [.inr (e (e.symm i))] at hxi
    change x ∈ (Q (e.symm j)).vertices.map emb ++ [.inr (e (e.symm j))] at hxj
    rw [e.apply_symm_apply] at hxi hxj
    cases x with
    | inl x =>
      have hLeft (b : B) (h : Sum.inl x ∈ (Q (e.symm b)).vertices.map emb ++ [.inr b]) :
          x ∈ (Q (e.symm b)).vertices := by
        rcases List.mem_append.mp h with h | h
        · obtain ⟨v,hv,hvx⟩ := List.mem_map.mp h
          exact Sum.inl.inj hvx ▸ hv
        · simp at h
      exact hApart _ _ (e.symm.injective.ne hij) (hLeft i hxi) (hLeft j hxj)
    | inr x =>
      have hRight (b : B) (h : Sum.inr x ∈ (Q (e.symm b)).vertices.map emb ++ [.inr b]) : x = b := by
        rcases List.mem_append.mp h with h | h
        · obtain ⟨v,_,hv⟩ := List.mem_map.mp h
          exact (Sum.inl_ne_inr hv).elim
        · exact Sum.inr.inj (List.mem_singleton.mp h)
      exact hij ((hRight i hxi).symm.trans (hRight j hxj))
  · intro v
    cases v with
    | inl v =>
      obtain ⟨i,hi⟩ := hCover v
      refine ⟨e i,?_⟩
      change Sum.inl v ∈ (Q (e.symm (e i))).vertices.map emb ++ [.inr (e (e.symm (e i)))]
      rw [e.symm_apply_apply]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨v,hi,rfl⟩)
    | inr b =>
      refine ⟨b,?_⟩
      change Sum.inr b ∈ (Q (e.symm b)).vertices.map emb ++ [.inr (e (e.symm b))]
      simp

private theorem pair_occurs_in_path {W : Type*} {D : Digraph W} (P : PathRequest D)
    {x y : W} (hx : x ∈ P.vertices) (hEnd : x ≠ P.target)
    (hNext : ∀ z, D.Adj x z → z = y) : [x,y] <:+: P.vertices := by
  obtain ⟨before,after,he⟩ := List.append_of_mem hx
  cases after with
  | nil =>
    have hh : P.vertices.getLast? = some P.target := P.route.2
    rw [he,List.getLast?_append_of_ne_nil _ (by simp)] at hh
    exact (hEnd (Option.some.inj hh)).elim
  | cons z after =>
    have hChain : P.vertices.IsChain D.Adj := P.route.1
    rw [he] at hChain
    have hz : D.Adj x z := hChain.right_of_append.rel
    have hz' := hNext z hz
    subst z
    exact ⟨before,after,by rw [List.append_assoc]; exact he.symm⟩

/-- Reopen a Hamilton cycle of the wrapped interval. All prescribed
interior arcs occur in the resulting paths, and every split vertex
occurs on exactly one path. -/
theorem exists_interval_paths_after_merge [Fintype V]
    (D R : Digraph V) (σ : Equiv.Perm V) (B : Finset V) (hB : B.Nonempty)
    (hSpan : HasSpanningCycle (fun x y => σ x = y))
    (hKeep : ∀ x y, D.Adj x y → σ x = y) (hUse : ∀ x, (D ⊔ R).Adj x (σ x))
    (hInside : ∀ x y, D.Adj x y → y ∉ B) :
    ∃ P : B → PathRequest (splitIntervalDigraph (D ⊔ R) B), ∃ starts : Equiv.Perm B,
      (∀ b, (P b).source = Sum.inl (starts b).val ∧ (P b).target = Sum.inr b) ∧
      (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) ∧
      (∀ v, ∃ i, v ∈ (P i).vertices) ∧
      ∀ x y, D.Adj x y → ∃ i, [(Sum.inl x : V ⊕ B),Sum.inl y] <:+: (P i).vertices := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨L,a,_,hAll,_,hChain⟩ := hSpan
  have hHit (v : V) : ∃ c ∈ B, σ.SameCycle v c :=
    ⟨b,hb,sameCycle_of_successor_chain σ hChain
      (List.mem_append_left _ (hAll v)) (List.mem_append_left _ (hAll b))⟩
  obtain ⟨Q,starts,hEnds,hDis,hCover⟩ := exists_interval_paths_of_wraparound_factor σ B hHit
  have hLe : (⟨fun x y => σ x = y⟩ : Digraph V) ≤ D ⊔ R := by
    intro x y h
    change σ x = y at h
    rw [←h]
    exact hUse x
  let P (i : B) : PathRequest (splitIntervalDigraph (D ⊔ R) B) :=
    ⟨(Q i).source,(Q i).target,(Q i).tail,
      ⟨(Q i).route.1.imp (fun _ _ h => split_interval_mono hLe B h),(Q i).route.2⟩,(Q i).simple⟩
  refine ⟨P,starts,hEnds,hDis,hCover,?_⟩
  intro x y hxy
  obtain ⟨i,hi⟩ := hCover (Sum.inl x)
  refine ⟨i,pair_occurs_in_path (Q i) hi (by rw [(hEnds i).2]; exact Sum.inl_ne_inr) ?_⟩
  intro z hz
  cases z with
  | inl z =>
    have hz' : z ∉ B ∧ σ x = z := hz
    exact congrArg Sum.inl (hz'.2.symm.trans (hKeep x y hxy))
  | inr z =>
    have hz' : σ x = z.val := hz
    exact ((hInside x y hxy) ((hz'.symm.trans (hKeep x y hxy)) ▸ z.prop)).elim

universe u

/-- The completion step of Lemma 7.6 on the identified interval.
Balance and superregularity on the free pairs give the merged
cycle, which is reopened at the identified boundary. -/
theorem exists_exceptional_interval_completion_of_superregular_pairs
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ} (D R : Digraph W)
      (cluster : W → Fin (n+1)) (r : Fin (n+1) → ℕ),
      let s := finRotate (n+1)
      let S := freeOut D cluster
      let T i := freeIn D cluster (s i)
      let B := (univ : Finset W).filter (fun x => cluster x = 0)
      IsDirectedPathSystem D →
      (∀ x y, D.Adj x y → y ∉ B) →
      (∀ i, (S i).card = (T i).card) →
      (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ S i) →
      (∀ i, N ≤ (S i).card) →
      (∀ i, 0 < r i ∧ ε*((S i).card:ℝ) ≤ (r i:ℝ) ∧ (r i:ℝ) ≤ (d-2*ε)*((S i).card:ℝ)) →
      (∀ i, IsSuperregularPair R ε d (S i) (T i)) →
      ∃ P : B → PathRequest (splitIntervalDigraph (D ⊔ R) B), ∃ starts : Equiv.Perm B,
        (∀ b, (P b).source = Sum.inl (starts b).val ∧ (P b).target = Sum.inr b) ∧
        (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) ∧
        (∀ v, ∃ i, v ∈ (P i).vertices) ∧
        ∀ x y, D.Adj x y → ∃ i, [(Sum.inl x : W ⊕ B),Sum.inl y] <:+: (P i).vertices := by
  obtain ⟨N,hN⟩ := exists_hamilton_completion_of_physical_successor_pairs.{u}
    (d-2*ε) ε ν τ γ hν hWidth hε hτγ hγ (sub_pos.mpr hd) hCost hDegrees
  refine ⟨N,?_⟩
  intro W _ n D R cluster r s S T B hPath hInside hBal hOverlap hSize hr hPair
  have hLow (i : Fin (n+1)) := IsSuperregularPair.physical_lower_bounds R (S i) (T i) d ε (hPair i)
  have hB : B.Nonempty := by
    obtain ⟨x,_,hx⟩ := hOverlap 0
    exact ⟨x,mem_filter.mpr ⟨mem_univ _,(mem_freeOut.mp hx).1⟩⟩
  have hScale (i : Fin (n+1)) : (d-2*ε)*((S i).card:ℝ) ≤ (d-ε)*((S i).card:ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith only [hε]) (Nat.cast_nonneg _)
  have hRect : ∀ i, ∀ X ⊆ S i, ∀ Y ⊆ T i,
      ε*((S i).card:ℝ) ≤ (X.card:ℝ) → ε*((S i).card:ℝ) ≤ (Y.card:ℝ) →
      (d-2*ε)*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences R X Y:ℝ) := by
    intro i X hX Y hY hx hy
    apply (hLow i).2.2 X hX Y hY
    · rwa [mul_comm]
    · rwa [←hBal i,mul_comm]
  obtain ⟨σ,hSpan,hKeep,hUse⟩ := hN D R cluster r hPath hBal hOverlap hSize hr hRect
    (fun i y hy => (hScale i).trans ((hLow i).2.1 y hy)) (by
      intro i x hx
      have h := (hLow i).1 x hx
      rw [←hBal i] at h
      exact (hScale i).trans h)
  exact exists_interval_paths_after_merge D R σ B hB hSpan hKeep hUse hInside

/-- The completion step of Lemma 7.6 on the identified interval.
Balance and superregularity on the free pairs give the merged
cycle, which is reopened at the identified boundary. The density
may vary between the free pairs. -/
theorem exists_exceptional_interval_completion_of_lower_superregular_pairs
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ} (D R : Digraph W)
      (cluster : W → Fin (n+1)) (r : Fin (n+1) → ℕ),
      let s := finRotate (n+1)
      let S := freeOut D cluster
      let T i := freeIn D cluster (s i)
      let B := (univ : Finset W).filter (fun x => cluster x = 0)
      IsDirectedPathSystem D →
      (∀ x y, D.Adj x y → y ∉ B) →
      (∀ i, (S i).card = (T i).card) →
      (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ S i) →
      (∀ i, N ≤ (S i).card) →
      (∀ i, 0 < r i ∧ ε*((S i).card:ℝ) ≤ (r i:ℝ) ∧ (r i:ℝ) ≤ (d-2*ε)*((S i).card:ℝ)) →
      (∀ i, IsLowerSuperregularPair R ε d (S i) (T i)) →
      ∃ P : B → PathRequest (splitIntervalDigraph (D ⊔ R) B), ∃ starts : Equiv.Perm B,
        (∀ b, (P b).source = Sum.inl (starts b).val ∧ (P b).target = Sum.inr b) ∧
        (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) ∧
        (∀ v, ∃ i, v ∈ (P i).vertices) ∧
        ∀ x y, D.Adj x y → ∃ i, [(Sum.inl x : W ⊕ B),Sum.inl y] <:+: (P i).vertices := by
  obtain ⟨N,hN⟩ := exists_hamilton_completion_of_physical_successor_pairs.{u}
    (d-2*ε) ε ν τ γ hν hWidth hε hτγ hγ (sub_pos.mpr hd) hCost hDegrees
  refine ⟨N,?_⟩
  intro W _ n D R cluster r s S T B hPath hInside hBal hOverlap hSize hr hPair
  have hLow (i : Fin (n+1)) := IsLowerSuperregularPair.physical_lower_bounds R (S i) (T i) d ε (hPair i)
  have hB : B.Nonempty := by
    obtain ⟨x,_,hx⟩ := hOverlap 0
    exact ⟨x,mem_filter.mpr ⟨mem_univ _,(mem_freeOut.mp hx).1⟩⟩
  have hScale (i : Fin (n+1)) : (d-2*ε)*((S i).card:ℝ) ≤ (d-ε)*((S i).card:ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith only [hε]) (Nat.cast_nonneg _)
  have hRect : ∀ i, ∀ X ⊆ S i, ∀ Y ⊆ T i,
      ε*((S i).card:ℝ) ≤ (X.card:ℝ) → ε*((S i).card:ℝ) ≤ (Y.card:ℝ) →
      (d-2*ε)*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences R X Y:ℝ) := by
    intro i X hX Y hY hx hy
    apply (hLow i).2.2 X hX Y hY
    · rwa [mul_comm]
    · rwa [←hBal i,mul_comm]
  obtain ⟨σ,hSpan,hKeep,hUse⟩ := hN D R cluster r hPath hBal hOverlap hSize hr hRect
    (fun i y hy => (hScale i).trans ((hLow i).2.1 y hy)) (by
      intro i x hx
      have h := (hLow i).1 x hx
      rw [←hBal i] at h
      exact (hScale i).trans h)
  exact exists_interval_paths_after_merge D R σ B hB hSpan hKeep hUse hInside

end OverfullWork.DirectedRobustExpansion
