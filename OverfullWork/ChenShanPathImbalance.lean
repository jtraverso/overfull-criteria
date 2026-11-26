module

public import OverfullWork.ChenShanTrianglePackingLeave

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

/-- Out-degree minus in-degree in a finite directed edge set. -/
noncomputable def arcDivergence (G : Finset (V × V)) (v : V) : ℤ :=
  ((G.filter (fun e => e.1 = v)).card : ℤ) - (G.filter (fun e => e.2 = v)).card

noncomputable def positiveImbalance [Fintype V] (G : Finset (V × V)) : ℕ :=
  ∑ v, (arcDivergence G v).toNat

theorem arcDivergence_sdiff {G C : Finset (V × V)} (hC : C ⊆ G) (v : V) :
    arcDivergence (G \ C) v = arcDivergence G v - arcDivergence C v := by
  have hFilter (p : V × V → Prop) [DecidablePred p] :
      (G \ C).filter p = G.filter p \ C.filter p := by
    ext e
    simp only [mem_filter,mem_sdiff]
    tauto
  unfold arcDivergence
  rw [hFilter,hFilter,card_sdiff_of_subset (filter_subset_filter _ hC),
    card_sdiff_of_subset (filter_subset_filter _ hC),
    Nat.cast_sub (card_le_card (filter_subset_filter _ hC)),
    Nat.cast_sub (card_le_card (filter_subset_filter _ hC))]
  ring

theorem sum_arcDivergence [Fintype V] (G : Finset (V × V)) :
    (∑ v, arcDivergence G v) = 0 := by
  have hCount (f : V × V → V) :
      (∑ v, ((G.filter (fun e => f e = v)).card : ℤ)) = G.card := by
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [sum_comm]
    simp
  simp only [arcDivergence,sum_sub_distrib,hCount,sub_self]

theorem exists_opposite_arcDivergence [Fintype V] (G : Finset (V × V))
    (h : 0 < positiveImbalance G) :
    ∃ u v, 0 < arcDivergence G u ∧ arcDivergence G v < 0 := by
  have hP : ∃ u, 0 < arcDivergence G u := by
    by_contra! hn
    have hZero (u : V) : (arcDivergence G u).toNat = 0 := by have := hn u; omega
    simp [positiveImbalance,hZero] at h
  obtain ⟨u,hu⟩ := hP
  have hN : ∃ v, arcDivergence G v < 0 := by
    by_contra! hn
    have hSum := single_le_sum (s := (univ : Finset V)) (f := arcDivergence G)
      (fun v _ => hn v) (mem_univ u)
    rw [sum_arcDivergence] at hSum
    omega
  obtain ⟨v,hv⟩ := hN
  exact ⟨u,v,hu,hv⟩

theorem arcBalanced_iff_positiveImbalance_eq_zero [Fintype V] (G : Finset (V × V)) :
    ArcBalanced G ↔ positiveImbalance G = 0 := by
  constructor
  · intro h
    have hZero (v : V) : arcDivergence G v = 0 := by
      unfold arcDivergence
      rw [h v,sub_self]
    simp [positiveImbalance,hZero]
  · intro h v
    have hNonpos (x : V) : arcDivergence G x ≤ 0 := by
      have hx := single_le_sum (s := (univ : Finset V))
        (f := fun y => (arcDivergence G y).toNat) (fun _ _ => Nat.zero_le _) (mem_univ x)
      change (arcDivergence G x).toNat ≤ positiveImbalance G at hx
      omega
    have hSum := single_le_sum (s := (univ : Finset V)) (f := fun x => -arcDivergence G x)
      (fun x _ => neg_nonneg.mpr (hNonpos x)) (mem_univ v)
    rw [sum_neg_distrib,sum_arcDivergence,neg_zero] at hSum
    have hv : arcDivergence G v = 0 := by have := hNonpos v; omega
    unfold arcDivergence at hv
    exact_mod_cast (sub_eq_zero.mp hv)

/-- The starting value of the decreasing measure bounds the number of
paths that can be deleted. It is at most the number of vertices times
the pointwise imbalance budget. -/
theorem positiveImbalance_le_card_mul [Fintype V] (G : Finset (V × V)) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ v, (arcDivergence G v : ℝ) ≤ M) :
    (positiveImbalance G : ℝ) ≤ (Fintype.card V : ℝ) * M := by
  rw [positiveImbalance,Nat.cast_sum]
  calc
    _ ≤ ∑ _v : V, M := by
      apply sum_le_sum
      intro v _
      by_cases hv : 0 ≤ arcDivergence G v
      · have hx : ((arcDivergence G v).toNat : ℤ) = arcDivergence G v :=
          Int.toNat_of_nonneg hv
        have hcast := congrArg (fun x : ℤ => (x : ℝ)) hx
        rw [Int.cast_natCast] at hcast
        rw [hcast]
        exact h v
      · have hx : (arcDivergence G v).toNat = 0 := by omega
        simpa [hx] using hM
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

/-- The consecutive arcs of a simple directed path of length l. -/
noncomputable def directedPathArcs (l : ℕ) (f : Fin (l+1) ↪ V) : Finset (V × V) :=
  (univ : Finset (Fin l)).map ⟨fun i => (f i.castSucc,f i.succ),fun _ _ h =>
    Fin.castSucc_injective _ (f.injective (congrArg Prod.fst h))⟩

theorem arcDivergence_directedPathArcs (l : ℕ) (f : Fin (l+1) ↪ V) (v : V) :
    arcDivergence (directedPathArcs l f) v =
      (if f 0 = v then (1 : ℤ) else 0) - (if f (Fin.last l) = v then 1 else 0) := by
  unfold arcDivergence directedPathArcs
  rw [filter_map,filter_map,card_map,card_map]
  simp only [Function.comp_def,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  let g : Fin (l+1) → ℤ := fun i => if f i = v then 1 else 0
  change (∑ i : Fin l, g i.castSucc) - (∑ i : Fin l, g i.succ) = g 0-g (Fin.last l)
  have hl := Fin.sum_univ_castSucc g
  have hr := Fin.sum_univ_succ g
  linarith only [hl,hr]

/-- A simple directed path uses two incident edges at each internal
vertex and one at either endpoint when the path is nonempty. -/
theorem incidentDegree_directedPathArcs (l : ℕ) (f : Fin (l+1) ↪ V) (v : V) :
    incidentDegree (directedPathArcs l f) v +
      ((if f 0 = v then 1 else 0) + (if f (Fin.last l) = v then 1 else 0)) =
      2 * (if ∃ i, f i = v then 1 else 0) := by
  unfold incidentDegree directedPathArcs
  rw [filter_map,card_map,card_filter]
  simp only [Function.comp_def]
  let g : Fin (l+1) → ℕ := fun i => if f i = v then 1 else 0
  have hSplit (i : Fin l) : (if f i.castSucc = v ∨ f i.succ = v then 1 else 0) =
      g i.castSucc+g i.succ := by
    have hNe : f i.castSucc ≠ f i.succ := by
      intro h
      have hh := congrArg Fin.val (f.injective h)
      simp at hh
    by_cases h₁ : f i.castSucc = v <;> by_cases h₂ : f i.succ = v <;> simp [g,h₁,h₂]
    exact hNe (h₁.trans h₂.symm)
  change (∑ i : Fin l, if f i.castSucc = v ∨ f i.succ = v then (1 : ℕ) else 0) + _ = _
  simp_rw [hSplit,sum_add_distrib]
  change (∑ i : Fin l, g i.castSucc) + (∑ i : Fin l, g i.succ) +
    (g 0 + g (Fin.last l)) = 2 * _
  have hSum : (∑ i : Fin (l+1), g i) = if ∃ i, f i = v then 1 else 0 := by
    by_cases h : ∃ i, f i = v
    · obtain ⟨i,rfl⟩ := h
      simp [g,f.injective.eq_iff]
    · have hg (i : Fin (l+1)) : g i = 0 := by simp [g,show f i ≠ v from fun hi => h ⟨i,hi⟩]
      simp [h,hg]
  have hLeft := Fin.sum_univ_castSucc g
  have hRight := Fin.sum_univ_succ g
  omega

/-- A path from a positive vertex to a negative vertex reduces the total
positive imbalance by one, as in the repair procedure of Lemma 4.13. -/
theorem positiveImbalance_delete_directedPath [Fintype V] {l : ℕ}
    (G : Finset (V × V)) (f : Fin (l+1) ↪ V) (hf : directedPathArcs l f ⊆ G)
    (hStart : 0 < arcDivergence G (f 0)) (hEnd : arcDivergence G (f (Fin.last l)) < 0) :
    positiveImbalance (G \ directedPathArcs l f) + 1 = positiveImbalance G := by
  have hne : f 0 ≠ f (Fin.last l) := by
    intro h
    rw [h] at hStart
    omega
  let H := G \ directedPathArcs l f
  let ind (v : V) : ℕ := if f 0 = v then 1 else 0
  have hInd : (∑ v, ind v) = 1 := by simp [ind]
  have hPoint (v : V) : (arcDivergence H v).toNat + ind v = (arcDivergence G v).toNat := by
    dsimp only [H,ind]
    rw [arcDivergence_sdiff hf,arcDivergence_directedPathArcs]
    by_cases h₁ : f 0 = v
    · subst v
      have hne' : f (Fin.last l) ≠ f 0 := Ne.symm hne
      simp only [ite_true,hne',ite_false,sub_zero]
      omega
    by_cases h₂ : f (Fin.last l) = v
    · subst v
      simp only [hne,ite_false,ite_true,add_zero]
      omega
    · simp [h₁,h₂]
  unfold positiveImbalance
  change (∑ v, (arcDivergence H v).toNat) + 1 = _
  rw [← hInd,← sum_add_distrib]
  exact sum_congr rfl (fun v _ => hPoint v)

end OverfullWork.ChenShan
