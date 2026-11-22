module

public import OverfullWork.KuhnOsthusCodegreeCount

@[expose] public section


/-! Embed a bounded pattern by intersecting the candidate sets of
later vertices. Only the rectangle bound for each required pair is
used, so the candidates may be indices of already packed pieces. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V W : Type*} [Fintype V]

/-- A target set above the rectangle threshold has fewer than r rows
whose degree falls below the density lower bound. -/
theorem card_bad_rows_of_rectangle (D : Digraph V) (A B Y : Finset V)
    (r : ℕ) (η : ℝ) (hr : 0 < r) (hY : Y ⊆ B) (hSize : r ≤ Y.card)
    (hRect : ∀ X ⊆ A, ∀ T ⊆ B, r ≤ X.card → r ≤ T.card →
      η*(X.card:ℝ)*(T.card:ℝ) ≤ (incidences D X T:ℝ)) :
    (A.filter (fun x => (outTo D Y x:ℝ) < η*(Y.card:ℝ))).card < r := by
  let X := A.filter (fun x => (outTo D Y x:ℝ) < η*(Y.card:ℝ))
  by_contra! hx
  obtain ⟨w,hw⟩ := card_pos.mp (hr.trans_le hx)
  have hLT : (incidences D X Y:ℝ) < (X.card:ℝ)*(η*(Y.card:ℝ)) := by
    rw [incidences_eq_sum_outTo, ←nsmul_eq_mul, ←sum_const]
    exact sum_lt_sum (fun x hx => (mem_filter.mp hx).2.le) ⟨w,hw,(mem_filter.mp hw).2⟩
  have hGE := hRect X (filter_subset _ _) Y hY hx hSize
  linarith only [hGE,hLT,mul_comm η (X.card:ℝ)]

/-- Transport the bound for bad rows through two injective
enumerations of subsets. -/
theorem card_bad_index_rows_of_rectangle (D : Digraph V) (A B : Finset V)
    (U Y : Finset W) (f g : W → V) (hf : Set.InjOn f U) (hg : Set.InjOn g Y)
    (hfA : ∀ x ∈ U, f x ∈ A) (hgB : ∀ y ∈ Y, g y ∈ B)
    (r : ℕ) (η : ℝ) (hr : 0 < r) (hY : r ≤ Y.card)
    (hRect : ∀ X ⊆ A, ∀ T ⊆ B, r ≤ X.card → r ≤ T.card →
      η*(X.card:ℝ)*(T.card:ℝ) ≤ (incidences D X T:ℝ)) :
    (U.filter (fun x => ((Y.filter (fun y => D.Adj (f x) (g y))).card:ℝ) <
      η*(Y.card:ℝ))).card ≤ r := by
  let bad := U.filter (fun x => ((Y.filter (fun y => D.Adj (f x) (g y))).card:ℝ) < η*(Y.card:ℝ))
  have hyCard : (Y.image g).card = Y.card := card_image_iff.mpr hg
  have hB : Y.image g ⊆ B := by
    rintro z hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    exact hgB y hy
  have hSmall := card_bad_rows_of_rectangle D A B (Y.image g) r η hr hB (by rwa [hyCard]) hRect
  have hSub : bad.image f ⊆ A.filter (fun x => (outTo D (Y.image g) x:ℝ) < η*((Y.image g).card:ℝ)) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    have hCount : outTo D (Y.image g) (f x) = (Y.filter (fun y => D.Adj (f x) (g y))).card := by
      unfold outTo
      rw [filter_image,card_image_iff.mpr (fun a ha b hb => hg (mem_filter.mp ha).1 (mem_filter.mp hb).1)]
    exact mem_filter.mpr ⟨hfA x (mem_filter.mp hx).1,by
      rw [hCount,hyCard]
      exact (mem_filter.mp hx).2⟩
  have hCard : (bad.image f).card = bad.card :=
    card_image_iff.mpr (fun _ h₁ _ h₂ => hf (mem_filter.mp h₁).1 (mem_filter.mp h₂).1)
  have h := (card_le_card hSub).trans hSmall.le
  rwa [hCard] at h

omit [Fintype V] in
/-- Greedy embedding with explicit room for distinctness and for
the union of the bad rows of every later candidate set. -/
theorem exists_injective_greedy_embedding {m : ℕ}
    (C : Fin m → Finset W) (Q : Fin m → Fin m → W → W → Prop)
    (r : ℕ) (η : ℝ) (L : ℕ → ℝ) (hη : 0 ≤ η)
    (hInit : ∀ i, L 0 ≤ ((C i).card:ℝ))
    (hRoom : ∀ n ≤ m, ((m*r+m : ℕ):ℝ) < L n)
    (hProgress : ∀ n < m, L (n+1) ≤ η*L n)
    (hBad : ∀ i j, i < j → ∀ Y ⊆ C j, r ≤ Y.card →
      ((C i).filter (fun x => ((Y.filter (Q i j x)).card:ℝ) < η*(Y.card:ℝ))).card ≤ r)
    :
    ∃ f : Fin m → W, Injective f ∧ (∀ i, f i ∈ C i) ∧ ∀ i j, i < j → Q i j (f i) (f j) := by
  by_cases hm : m = 0
  · subst m
    exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
  let first : Fin m := ⟨0,Nat.pos_of_ne_zero hm⟩
  have hC : 0 < (C first).card := by
    have hn := (hRoom 0 (Nat.zero_le m)).trans_le (hInit first)
    exact_mod_cast (show (0:ℝ) < ((C first).card:ℝ) from
      (Nat.cast_nonneg (m*r+m)).trans_lt hn)
  obtain ⟨w,-⟩ := card_pos.mp hC
  let cand (f : Fin m → W) (n : ℕ) (j : Fin m) : Finset W :=
    (C j).filter (fun v => ∀ i : Fin m, i.val < n → Q i j (f i) v)
  have hStep (n : ℕ) (hn : n ≤ m) :
      ∃ f : Fin m → W,
        (∀ i j : Fin m, i.val < n → j.val < n → f i = f j → i = j) ∧
        (∀ i : Fin m, i.val < n → f i ∈ C i) ∧
        (∀ i j : Fin m, i < j → j.val < n → Q i j (f i) (f j)) ∧
        ∀ j : Fin m, n ≤ j.val → L n ≤ ((cand f n j).card:ℝ) := by
    induction n with
    | zero =>
      refine ⟨fun _ => w,fun _ _ h => (Nat.not_lt_zero _ h).elim,
        fun _ h => (Nat.not_lt_zero _ h).elim,fun _ _ _ h => (Nat.not_lt_zero _ h).elim,?_⟩
      intro j _
      simpa [cand] using hInit j
    | succ n ih =>
      have hnM : n < m := by omega
      obtain ⟨f,hInj,hMem,hQ,hCand⟩ := ih (by omega)
      let a : Fin m := ⟨n,hnM⟩
      let bad (j : Fin m) :=
        if a < j then (C a).filter (fun x =>
          (((cand f n j).filter (Q a j x)).card:ℝ) < η*((cand f n j).card:ℝ)) else ∅
      have hSize (j : Fin m) (hj : n ≤ j.val) : r ≤ (cand f n j).card := by
        have h₁ : r ≤ m*r+m := by
          have hm₁ : 1 ≤ m := by omega
          exact (by simpa using Nat.mul_le_mul_right r hm₁ : r ≤ m*r) |>.trans (Nat.le_add_right _ _)
        have h₂ : (m*r+m : ℝ) < ((cand f n j).card:ℝ) := by
          exact_mod_cast (hRoom n (by omega)).trans_le (hCand j hj)
        exact_mod_cast (show (r:ℝ) ≤ ((cand f n j).card:ℝ) by
          have hcast : (r:ℝ) ≤ (m*r+m : ℝ) := by exact_mod_cast h₁
          exact hcast.trans h₂.le)
      have hBadSize (j : Fin m) : (bad j).card ≤ r := by
        by_cases hj : a < j
        · have hj' : n ≤ j.val := Nat.le_of_lt hj
          simpa only [bad,if_pos hj] using hBad a j hj (cand f n j) (filter_subset _ _) (hSize j hj')
        · simp [bad,hj]
      let used := ((univ : Finset (Fin m)).filter (fun i => i.val < n)).image f
      let forbidden := ((univ : Finset (Fin m)).biUnion bad) ∪ used
      have hUsed : used.card ≤ m := by
        unfold used
        exact card_image_le.trans (by
          simpa using card_filter_le (univ : Finset (Fin m)) (fun i => i.val < n))
      have hAllBad : ((univ : Finset (Fin m)).biUnion bad).card ≤ m*r := by
        exact card_biUnion_le.trans ((sum_le_sum (fun j _ => hBadSize j)).trans_eq
          (by simp))
      have hForbidden : forbidden.card ≤ m*r+m :=
        (card_union_le _ _).trans (Nat.add_le_add hAllBad hUsed)
      have hEnough : forbidden.card < (cand f n a).card := hForbidden.trans_lt (by
        exact_mod_cast (hRoom n (by omega)).trans_le (hCand a le_rfl))
      obtain ⟨v,hv,hvFree⟩ := exists_mem_notMem_of_card_lt_card hEnough
      obtain ⟨hvC,hvQ⟩ := mem_filter.mp hv
      have hNotUsed (i : Fin m) (hi : i.val < n) : f i ≠ v := by
        intro h
        exact hvFree (mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,h⟩))
      have hvGood (j : Fin m) (hj : a < j) :
          η*((cand f n j).card:ℝ) ≤ (((cand f n j).filter (Q a j v)).card:ℝ) := by
        by_contra! h
        apply hvFree
        exact mem_union_left _ (mem_biUnion.mpr ⟨j,mem_univ _,by
          simpa only [bad,if_pos hj,mem_filter] using And.intro hvC h⟩)
      let f' := update f a v
      have hOld (i : Fin m) (hi : i.val < n) : f' i = f i :=
        update_of_ne (fun h => by
          have he := congrArg Fin.val h
          change i.val = n at he
          omega) _ _
      have hNew : f' a = v := update_self _ _ _
      have hIndex (i : Fin m) (hi : i.val < n+1) (hh : ¬ i.val < n) : i = a := Fin.ext (by
        change i.val = n
        omega)
      refine ⟨f',?_,?_,?_,?_⟩
      · intro i j hi hj he
        by_cases hii : i.val < n <;> by_cases hjj : j.val < n
        · exact hInj i j hii hjj (by rwa [hOld i hii,hOld j hjj] at he)
        · have hja := hIndex j hj hjj
          rw [hja,hOld i hii,hNew] at he
          exact (hNotUsed i hii he).elim
        · have hia := hIndex i hi hii
          rw [hia,hOld j hjj,hNew] at he
          exact (hNotUsed j hjj he.symm).elim
        · exact (hIndex i hi hii).trans (hIndex j hj hjj).symm
      · intro i hi
        by_cases hii : i.val < n
        · rw [hOld i hii]
          exact hMem i hii
        · rw [hIndex i hi hii,hNew]
          exact hvC
      · intro i j hij hj
        have hi : i.val < n := by have h := show i.val < j.val from hij; omega
        by_cases hjj : j.val < n
        · rw [hOld i hi,hOld j hjj]
          exact hQ i j hij hjj
        · rw [hIndex j hj hjj,hOld i hi,hNew]
          exact hvQ i hi
      · intro j hj
        have hAj : a < j := by change n < j.val; omega
        have hSub : (cand f n j).filter (Q a j v) ⊆ cand f' (n+1) j := by
          intro z hz
          obtain ⟨hzC,hzNew⟩ := mem_filter.mp hz
          obtain ⟨hzMem,hzOld⟩ := mem_filter.mp hzC
          refine mem_filter.mpr ⟨hzMem,?_⟩
          intro i hi
          by_cases hii : i.val < n
          · rw [hOld i hii]
            exact hzOld i hii
          · rw [hIndex i hi hii,hNew]
            exact hzNew
        have hGain := hvGood j hAj
        exact (hProgress n hnM).trans ((mul_le_mul_of_nonneg_left (hCand j (by omega)) hη).trans
          (hGain.trans (by exact_mod_cast card_le_card hSub)))
  obtain ⟨f,hi,hc,hq,_⟩ := hStep m le_rfl
  exact ⟨f,fun i j => hi i j i.isLt j.isLt,fun i => hc i i.isLt,
    fun i j h => hq i j h j.isLt⟩

end OverfullWork.DirectedRobustExpansion
