module

public import OverfullWork.OsthusStadenPhysicalBalance
public import OverfullWork.OsthusStadenH3Split
public import OverfullWork.ClusterFactorCompletion

@[expose] public section


/-! Connect the physical balance equation to the dense successor-pair
completion and the edge-disjoint factors in Osthus–Staden §5.10. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {E I W : Type*}

abbrev SliceVertex (E I W : Type*) := E ⊕ (I × W)

def sliceLabel : SliceVertex E I W → Option I
  | .inl _ => none
  | .inr (i,_) => some i

noncomputable def arcMultiplicity {V : Type*} (A : Finset (V × V)) (x y : V) : ℕ :=
  if (x,y) ∈ A then 1 else 0

theorem arcMultiplicity_row {V : Type*} [Fintype V] (A : Finset (V × V)) (x : V) :
    (∑ y : V, arcMultiplicity A x y) = outDegree (digraphOfArcs A) x := by
  let P := fun y : V => (x,y) ∈ A
  calc
    _ = ∑ y : V, if P y then 1 else 0 := by
      apply sum_congr rfl
      intro y _
      by_cases h : (x,y) ∈ A <;> simp [P,arcMultiplicity,h]
    _ = ((univ : Finset V).filter P).card := (card_filter _ _).symm
    _ = _ := by
      unfold outDegree
      congr 1
      ext y
      simp only [P,mem_filter,mem_univ,true_and]
      rfl

theorem arcMultiplicity_col {V : Type*} [Fintype V] (A : Finset (V × V)) (y : V) :
    (∑ x : V, arcMultiplicity A x y) = inDegree (digraphOfArcs A) y := by
  let P := fun x : V => (x,y) ∈ A
  calc
    _ = ∑ x : V, if P x then 1 else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases h : (x,y) ∈ A <;> simp [P,arcMultiplicity,h]
    _ = ((univ : Finset V).filter P).card := (card_filter _ _).symm
    _ = _ := by
      unfold inDegree inNeighbours
      congr 1
      ext x
      simp only [P,mem_filter,mem_univ,true_and]
      rfl

variable [Fintype E] [Fintype I] [Fintype W]

private theorem labelled_cluster_vertices (i : I) :
    ((univ : Finset (SliceVertex E I W)).filter (fun x => sliceLabel x = some i)) =
      (univ : Finset W).map ⟨fun w => .inr (i,w),fun _ _ h => (Prod.mk.inj (Sum.inr.inj h)).2⟩ := by
  ext x
  simp only [mem_filter,mem_univ,true_and,mem_map]
  constructor
  · intro h
    rcases x with e | ⟨j,w⟩
    · cases h
    · have hj : j = i := Option.some.inj h
      subst j
      exact ⟨w,rfl⟩
  · rintro ⟨w,rfl⟩
    rfl

/-- The balance totals computed on the physical arc sets agree with
the degree sums used by the capacity theorem for the successor pairs. -/
theorem clusterArcMass_eq_degree_sum (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (i : I) :
    clusterArcMass sliceLabel A true i =
      (∑ w : W,outDegree (digraphOfArcs A) (.inr (i,w))) ∧
    clusterArcMass sliceLabel A false i =
      (∑ w : W,inDegree (digraphOfArcs A) (.inr (i,w))) := by
  constructor
  · have h := sum_card_fiberwise_eq_card_filter A
      (univ.filter (fun x : SliceVertex E I W => sliceLabel x = some i)) Prod.fst
    simp only [mem_filter,mem_univ,true_and] at h
    change (∑ x ∈ univ.filter (fun x => sliceLabel x = some i),
      (A.filter (fun e => e.1 = x)).card) = clusterArcMass sliceLabel A true i at h
    rw [←h]
    rw [labelled_cluster_vertices,sum_map]
    simp only [digraphOfArcs_outDegree]
    apply sum_congr rfl
    intro x _
    congr 1
    ext e
    simp only [mem_filter]
    rfl
  · have h := sum_card_fiberwise_eq_card_filter A
      (univ.filter (fun x : SliceVertex E I W => sliceLabel x = some i)) Prod.snd
    simp only [mem_filter,mem_univ,true_and] at h
    change (∑ x ∈ univ.filter (fun x => sliceLabel x = some i),
      (A.filter (fun e => e.2 = x)).card) = clusterArcMass sliceLabel A false i at h
    rw [←h]
    rw [labelled_cluster_vertices,sum_map]
    simp only [digraphOfArcs_inDegree]
    apply sum_congr rfl
    intro x _
    congr 1
    ext e
    simp only [mem_filter]
    rfl

omit [Fintype E] [Fintype I] [Fintype W] in
/-- The physical mass of the disjoint exceptional and balancing arcs
adds exactly. Thus equation (41) is the input balance for completion. -/
theorem balanced_physical_arc_union
    (σ : Equiv.Perm I) (T B : Finset (SliceVertex E I W × SliceVertex E I W))
    (hDis : Disjoint T B)
    (hBalance : ∀ i, clusterArcMass sliceLabel T true i + clusterArcMass sliceLabel B true i =
      clusterArcMass sliceLabel T false (σ i) + clusterArcMass sliceLabel B false (σ i)) :
    ∀ i, clusterArcMass sliceLabel (T ∪ B) true i =
      clusterArcMass sliceLabel (T ∪ B) false (σ i) := by
  have hMass (s : Bool) (i : I) :
      clusterArcMass sliceLabel (T ∪ B) s i =
        clusterArcMass sliceLabel T s i + clusterArcMass sliceLabel B s i := by
    unfold clusterArcMass
    rw [filter_union,card_union_of_disjoint (hDis.mono (filter_subset _ _) (filter_subset _ _))]
  intro i
  rw [hMass,hMass]
  exact hBalance i

/-- The supported indicator of a balanced physical red set yields
actual edge-disjoint factors. The pair margins include the cutoff for
large rectangles, the available degrees, and the interval of demands. -/
theorem exists_factors_of_balanced_physical_arcs (σ : Equiv.Perm I)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (D : I → Digraph W) (κ t L : ℕ) (ε d : ℝ)
    (hBalance : ∀ i, clusterArcMass sliceLabel A true i = clusterArcMass sliceLabel A false (σ i))
    (hEx : ∀ e : E, inDegree (digraphOfArcs A) (.inl e) = κ ∧ outDegree (digraphOfArcs A) (.inl e) = κ)
    (hCap : ∀ i w, inDegree (digraphOfArcs A) (.inr (i,w)) ≤ κ-L ∧
      outDegree (digraphOfArcs A) (.inr (i,w)) ≤ κ-L)
    (hPairs : ∀ i, IsCentredSuperregular (D i) ε d)
    (hDis : ∀ i x y, (D i).Adj x y → (Sum.inr (i,x),Sum.inr (σ i,y)) ∉ A)
    (ht : 0 < t)
    (hWidth : (Fintype.card W:ℝ)*ε ≤ t)
    (hAvail : (κ:ℝ)+2*(t:ℝ) ≤ (d-ε)*(Fintype.card W:ℝ))
    (hβ : 0 ≤ d-2*ε) (hLκ : L ≤ κ) (hTwo : κ ≤ 2*L)
    (hL : 2*(d-2*ε)*(Fintype.card W:ℝ) ≤ 3*(L:ℝ))
    (hU : (κ:ℝ) ≤ (d-2*ε)*(Fintype.card W:ℝ))
    (hSlack : (d-2*ε)*(Fintype.card W:ℝ)-(L:ℝ) ≤
      2*((d-2*ε)*(Fintype.card W:ℝ)-(κ:ℝ))) :
    ∃ F : Fin κ → Equiv.Perm (SliceVertex E I W), ∃ H : I → Digraph W,
      (∀ i, H i ≤ D i) ∧
      (∀ x y, ((univ : Finset (Fin κ)).filter (fun j => F j x = y)).card =
        arcMultiplicity A x y + DirectedMultigraphFactors.successorPairArcs σ H x y) ∧
      ∀ f g, f ≠ g → ∀ x, F f x ≠ F g x := by
  have hRedOut (i : I) (w : W) :
      (∑ y,arcMultiplicity A (Sum.inr (i,w)) y) ≤ κ-L := by
    rw [arcMultiplicity_row]
    exact (hCap i w).2
  have hRedIn (i : I) (w : W) :
      (∑ x,arcMultiplicity A x (Sum.inr (i,w))) ≤ κ-L := by
    rw [arcMultiplicity_col]
    exact (hCap i w).1
  have hRow (x : SliceVertex E I W) : (∑ y,arcMultiplicity A x y) ≤ κ := by
    cases x with
    | inl e => rw [arcMultiplicity_row,(hEx e).2]
    | inr u => exact (hRedOut u.1 u.2).trans (Nat.sub_le _ _)
  have hCol (y : SliceVertex E I W) : (∑ x,arcMultiplicity A x y) ≤ κ := by
    cases y with
    | inl e => rw [arcMultiplicity_col,(hEx e).1]
    | inr u => exact (hRedIn u.1 u.2).trans (Nat.sub_le _ _)
  have hB (i : I) : (∑ w : W,∑ y,arcMultiplicity A (Sum.inr (i,w)) y) =
      ∑ w : W,∑ x,arcMultiplicity A x (Sum.inr (σ i,w)) := by
    simp_rw [arcMultiplicity_row,arcMultiplicity_col]
    rw [←(clusterArcMass_eq_degree_sum A i).1,←(clusterArcMass_eq_degree_sum A (σ i)).2]
    exact hBalance i
  have hMin (i : I) (w : W) : κ+2*t ≤ outDegree (D i) w ∧ κ+2*t ≤ inDegree (D i) w := by
    have ho := (abs_le.mp ((hPairs i).2 w).2).1
    have hi := (abs_le.mp ((hPairs i).2 w).1).1
    have ho' : (κ:ℝ)+2*(t:ℝ) ≤ (outDegree (D i) w:ℝ) := by linarith only [ho,hAvail]
    have hi' : (κ:ℝ)+2*(t:ℝ) ≤ (inDegree (D i) w:ℝ) := by linarith only [hi,hAvail]
    exact ⟨by exact_mod_cast ho',by exact_mod_cast hi'⟩
  have hRect i (X Y : Finset W) (hx : t ≤ X.card) (hy : t ≤ Y.card) :
      (d-2*ε)*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences (D i) X Y:ℝ) := by
    have hDen := (abs_le.mp (hPairs i).1.2).1
    have h := uniform_incidences_lower (D i) (hPairs i).1.1
      (show d-ε ≤ density (D i) univ univ by linarith only [hDen])
      (subset_univ X) (subset_univ Y)
      (by rw [card_univ]; exact hWidth.trans (by exact_mod_cast hx))
      (by rw [card_univ]; exact hWidth.trans (by exact_mod_cast hy))
      (card_pos.mp (ht.trans_le hx)) (card_pos.mp (ht.trans_le hy))
    rw [show d-ε-ε = d-2*ε by ring] at h
    exact h.le
  obtain ⟨F,H,hH,hMult⟩ := DirectedMultigraphFactors.exists_dense_cluster_factorization
    σ (arcMultiplicity A) D κ t L (d-2*ε) hRow hCol
    (fun e => (arcMultiplicity_row _ _).trans (hEx e).2)
    (fun e => (arcMultiplicity_col _ _).trans (hEx e).1)
    hB hRedOut hRedIn hLκ hβ hTwo hL hU hSlack
    (fun i w => (hMin i w).1) (fun i w => (hMin i w).2) hRect
  refine ⟨F,H,hH,hMult,?_⟩
  intro f g hfg x he
  let y := F f x
  let S := (univ : Finset (Fin κ)).filter (fun j => F j x = y)
  have hf : f ∈ S := mem_filter.mpr ⟨mem_univ _,rfl⟩
  have hg : g ∈ S := mem_filter.mpr ⟨mem_univ _,he.symm⟩
  have hSize : 1 < S.card := one_lt_card.mpr ⟨f,hf,g,hg,hfg⟩
  have hAt : S.card = arcMultiplicity A x y + DirectedMultigraphFactors.successorPairArcs σ H x y := hMult x y
  have hBound : arcMultiplicity A x y + DirectedMultigraphFactors.successorPairArcs σ H x y ≤ 1 := by
    rcases x with x | ⟨i,v⟩ <;> rcases y with y | ⟨j,w⟩
    · simp [DirectedMultigraphFactors.successorPairArcs,arcMultiplicity]; split <;> decide
    · simp [DirectedMultigraphFactors.successorPairArcs,arcMultiplicity]; split <;> decide
    · simp [DirectedMultigraphFactors.successorPairArcs,arcMultiplicity]; split <;> decide
    · by_cases h : j = σ i ∧ (H i).Adj v w
      · obtain ⟨rfl,hEdge⟩ := h
        have hNo := hDis i v w (hH i hEdge)
        simp [DirectedMultigraphFactors.successorPairArcs,arcMultiplicity,hEdge,hNo]
      · simp [DirectedMultigraphFactors.successorPairArcs,arcMultiplicity,h]; split <;> decide
  omega

end OverfullWork.DirectedRobustExpansion
