module

public import OverfullWork.KuhnOsthusExceptionalPairStability
public import OverfullWork.KuhnOsthusCodegreeCount

@[expose] public section


/-! Extend the prescribed switch edges to spanning matchings, as in
Kühn–Osthus Lemma 10.5. Keep the deletion budget on the two free sides
explicit so the same criterion applies after earlier factors are removed. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

omit [Fintype V] in
private theorem card_filter_le_free_add_removed (A S : Finset V) (p : V → Prop) :
    (A.filter p).card ≤ ((A \ S).filter p).card + S.card := by
  have hSub : A.filter p ⊆ (A \ S).filter p ∪ S := by
    intro x hx
    obtain ⟨hA,hp⟩ := mem_filter.mp hx
    by_cases hs : x ∈ S
    · exact mem_union_right _ hs
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hA,hs⟩,hp⟩)
  exact (card_le_card hSub).trans (card_union_le _ _)

/-- Equal small deletions from a lower-superregular pair leave a
perfect matching on the remaining vertices. -/
theorem IsLowerSuperregularPair.exists_matching_on_free_vertices
    (G : Digraph V) (A B A₀ B₀ : Finset V) (d ε : ℝ) (r : ℕ)
    (hPair : IsLowerSuperregularPair G ε d A B)
    (hA : A₀ ⊆ A) (hB : B₀ ⊆ B) (hBal : A.card = B.card) (hBal₀ : A₀.card = B₀.card)
    (hGap : 2*ε < d) (hr : 0 < r) (hCut : (A.card:ℝ)*ε ≤ (r:ℝ))
    (hMargin : (r:ℝ)+(A₀.card:ℝ) ≤ (d-ε)*(A.card:ℝ)) :
    ∃ g : ↥(A \ A₀) ≃ ↥(B \ B₀), ∀ a : ↥(A \ A₀), G.Adj a (g a) := by
  let A' := A \ A₀
  let B' := B \ B₀
  have hFree : A'.card = B'.card := by simp only [A',B',card_sdiff_of_subset hA,card_sdiff_of_subset hB,hBal,hBal₀]
  obtain ⟨hOut,hIn,hRect⟩ := IsLowerSuperregularPair.physical_lower_bounds G A B d ε hPair
  have hCutB : (B.card:ℝ)*ε ≤ (r:ℝ) := hBal ▸ hCut
  apply exists_matching_on_of_rectangle_threshold G A' B' r hFree
  · intro x hx
    have h₁ := hOut x (mem_sdiff.mp hx).1
    rw [←hBal] at h₁
    have h₂ : r + A₀.card ≤ (B.filter (G.Adj x)).card := by exact_mod_cast hMargin.trans h₁
    have h₃ := card_filter_le_free_add_removed B B₀ (G.Adj x)
    change r ≤ (B'.filter (G.Adj x)).card
    dsimp [B']
    omega
  · intro y hy
    have h₁ := hIn y (mem_sdiff.mp hy).1
    have h₂ : r + A₀.card ≤ inNeighbours G A y := by exact_mod_cast hMargin.trans h₁
    have h₃ := card_filter_le_free_add_removed A A₀ (fun x => G.Adj x y)
    change r ≤ (A'.filter (fun x => G.Adj x y)).card
    change r + A₀.card ≤ (A.filter (fun x => G.Adj x y)).card at h₂
    dsimp [A']
    omega
  · intro X hX Y hY hx hy
    have hx' : (r:ℝ) ≤ X.card := by exact_mod_cast hx
    have hy' : (r:ℝ) ≤ Y.card := by exact_mod_cast hy
    have hr' : (0:ℝ) < r := by exact_mod_cast hr
    have h := hRect X (hX.trans sdiff_subset) Y (hY.trans sdiff_subset)
      (hCut.trans hx') (hCutB.trans hy')
    exact_mod_cast (mul_pos (mul_pos (sub_pos.mpr hGap) (hr'.trans_le hx'))
      (hr'.trans_le hy')).trans_le h

/-- Complete a matching already fixed on (A₀,B₀). The remaining
vertices are paired by Hall, while the prescribed edges keep their
original endpoints. -/
theorem IsLowerSuperregularPair.extend_prescribed_matching (G : Digraph V) (A B A₀ B₀ : Finset V)
    (d ε : ℝ) (r : ℕ)
    (hPair : IsLowerSuperregularPair G ε d A B)
    (hA : A₀ ⊆ A) (hB : B₀ ⊆ B) (hBal : A.card = B.card)
    (f : A₀ ≃ B₀) (hFixed : ∀ a : A₀, G.Adj a (f a))
    (hGap : 2*ε < d) (hr : 0 < r) (hCut : (A.card:ℝ)*ε ≤ (r:ℝ))
    (hMargin : (r:ℝ)+(A₀.card:ℝ) ≤ (d-ε)*(A.card:ℝ)) :
    ∃ e : A ≃ B, (∀ a : A, G.Adj a (e a)) ∧
      ∀ a : A₀, (e ⟨a.val,hA a.prop⟩).val = (f a).val := by
  have hBal₀ : A₀.card = B₀.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr f
  let A' := A \ A₀
  let B' := B \ B₀
  obtain ⟨g,hg⟩ := IsLowerSuperregularPair.exists_matching_on_free_vertices
    G A B A₀ B₀ d ε r hPair hA hB hBal hBal₀ hGap hr hCut hMargin
  let e (x : A) : B :=
    if hx : x.val ∈ A₀ then ⟨(f ⟨x.val,hx⟩).val,hB (f ⟨x.val,hx⟩).prop⟩
    else ⟨(g ⟨x.val,mem_sdiff.mpr ⟨x.prop,hx⟩⟩).val,
      (mem_sdiff.mp (g ⟨x.val,mem_sdiff.mpr ⟨x.prop,hx⟩⟩).prop).1⟩
  have hInject : Function.Injective e := by
    intro x y hxy
    by_cases hx : x.val ∈ A₀ <;> by_cases hy : y.val ∈ A₀
    · have h : f ⟨x.val,hx⟩ = f ⟨y.val,hy⟩ := Subtype.ext (by
        simpa only [e,dif_pos hx,dif_pos hy] using congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg (fun a : A₀ => a.val) (f.injective h))
    · have h : (f ⟨x.val,hx⟩).val = (g ⟨y.val,mem_sdiff.mpr ⟨y.prop,hy⟩⟩).val := by
        simpa only [e,dif_pos hx,dif_neg hy] using congrArg Subtype.val hxy
      exact ((mem_sdiff.mp (g ⟨y.val,mem_sdiff.mpr ⟨y.prop,hy⟩⟩).prop).2
        (h ▸ (f ⟨x.val,hx⟩).prop)).elim
    · have h : (g ⟨x.val,mem_sdiff.mpr ⟨x.prop,hx⟩⟩).val = (f ⟨y.val,hy⟩).val := by
        simpa only [e,dif_neg hx,dif_pos hy] using congrArg Subtype.val hxy
      exact ((mem_sdiff.mp (g ⟨x.val,mem_sdiff.mpr ⟨x.prop,hx⟩⟩).prop).2
        (h.symm ▸ (f ⟨y.val,hy⟩).prop)).elim
    · have h : g ⟨x.val,mem_sdiff.mpr ⟨x.prop,hx⟩⟩ = g ⟨y.val,mem_sdiff.mpr ⟨y.prop,hy⟩⟩ :=
        Subtype.ext (by simpa only [e,dif_neg hx,dif_neg hy] using congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg (fun a : A' => a.val) (g.injective h))
  let E := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr
    ⟨hInject, by simpa only [Fintype.card_coe] using hBal⟩)
  refine ⟨E,?_,?_⟩
  · intro a
    change G.Adj a (e a)
    by_cases ha : a.val ∈ A₀
    · simpa only [e,dif_pos ha] using hFixed ⟨a.val,ha⟩
    · simpa only [e,dif_neg ha] using hg ⟨a.val,mem_sdiff.mpr ⟨a.prop,ha⟩⟩
  · intro a
    change (e ⟨a.val,hA a.prop⟩).val = (f a).val
    simp only [e,dif_pos a.prop]

/-- Find the two sources and the common target set for a potential
switch. The cases q = 2 and q = 3 give the copies used in Lemma 10.5. -/
theorem IsLowerSuperregularPair.exists_common_switch_targets (G : Digraph V) (A B : Finset V)
    (d ε : ℝ) (q : ℕ) (hPair : IsLowerSuperregularPair G ε d A B)
    (hGap : 2*ε < d) (hSize : 2 ≤ A.card)
    (hCutA : (A.card:ℝ)*ε ≤ ((A.card-1 : ℕ):ℝ))
    (hCutB : (B.card:ℝ)*ε ≤ (d-ε)*(B.card:ℝ))
    (hBudget : (q:ℝ) ≤ (d-2*ε)*((d-ε)*(B.card:ℝ))) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ∃ S ⊆ B, S.card = q ∧ ∀ z ∈ S, G.Adj x z ∧ G.Adj y z := by
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < A.card)
  let X := A.erase x
  let Y := B.filter (G.Adj x)
  have hX : X.card = A.card-1 := card_erase_of_mem hx
  obtain ⟨w,hw⟩ := card_pos.mp (by omega : 0 < X.card)
  obtain ⟨hOut,_,hRect⟩ := IsLowerSuperregularPair.physical_lower_bounds G A B d ε hPair
  have hY : (d-ε)*(B.card:ℝ) ≤ (Y.card:ℝ) := hOut x hx
  have hLarge : (q:ℝ) ≤ (d-2*ε)*(Y.card:ℝ) :=
    hBudget.trans (mul_le_mul_of_nonneg_left hY (by linarith))
  have hRect' := hRect X (erase_subset x A) Y (filter_subset _ _)
    (by rwa [hX]) (hCutB.trans hY)
  have hEnough : ∃ y ∈ X, q ≤ outTo G Y y := by
    by_contra! h
    have hSum : (incidences G X Y:ℝ) < (X.card:ℝ)*(q:ℝ) := by
      rw [incidences_eq_sum_outTo, ← nsmul_eq_mul, ← sum_const]
      apply sum_lt_sum
      · intro y hy
        exact_mod_cast (h y hy).le
      · exact ⟨w,hw,by exact_mod_cast h w hw⟩
    have hLower : (X.card:ℝ)*(q:ℝ) ≤ (incidences G X Y:ℝ) := by
      calc
        _ ≤ (X.card:ℝ)*((d-2*ε)*(Y.card:ℝ)) := mul_le_mul_of_nonneg_left hLarge (by positivity)
        _ = (d-2*ε)*(X.card:ℝ)*(Y.card:ℝ) := by ring
        _ ≤ _ := hRect'
    exact (not_lt_of_ge hLower) hSum
  obtain ⟨y,hy,hq⟩ := hEnough
  obtain ⟨S,hSub,hCard⟩ := exists_subset_card_eq hq
  refine ⟨x,hx,y,mem_of_mem_erase hy,((mem_erase.mp hy).1).symm,S,
    hSub.trans ((filter_subset _ _).trans (filter_subset _ _)),hCard,?_⟩
  intro z hz
  have hm : z ∈ Y.filter (G.Adj y) := hSub hz
  exact ⟨(mem_filter.mp (mem_filter.mp hm).1).2,(mem_filter.mp hm).2⟩

end OverfullWork.DirectedRobustExpansion
