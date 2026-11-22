module

public import OverfullWork.DirectedPathCoverAbsorption
public import OverfullWork.DirectedRobustExpansion

@[expose] public section


/-! A deterministic weighted selection for the covering-pairs step
of Lo–Patel Lemma 4.8. The weights of covered targets halve. -/
namespace OverfullWork.DirectedCoveringPairs

open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

def Covers (D : Digraph V) (p x : V × V) : Prop := D.Adj p.1 x.1 ∧ D.Adj x.2 p.2

noncomputable def used (S : Finset (V × V)) : Finset V := S.image Prod.fst ∪ S.image Prod.snd

def DisjointPairs (S : Finset (V × V)) : Prop :=
  (∀ p ∈ S, p.1 ≠ p.2) ∧
    (S : Set (V × V)).Pairwise fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

private noncomputable def available (S : Finset (V × V)) : Finset (V × V) :=
  univ.filter fun p => p.1 ≠ p.2 ∧ p.1 ∉ used S ∧ p.2 ∉ used S

omit [Fintype V] in
private theorem used_le (S : Finset (V × V)) : (used S).card ≤ 2*S.card := by
  exact (card_union_le _ _).trans (by simpa [two_mul] using Nat.add_le_add card_image_le card_image_le)

private theorem outside_of_available {S : Finset (V × V)} {p : V × V} (h : p ∈ available S) :
    p ∉ S := by
  intro hp
  exact (mem_filter.mp h).2.2.1 (mem_union_left _ (mem_image_of_mem _ hp))

private theorem disjoint_insert {S : Finset (V × V)} {p : V × V} (h : p ∈ available S)
    (hS : DisjointPairs S) : DisjointPairs (insert p S) := by
  obtain ⟨hne, hleft, hright⟩ := (mem_filter.mp h).2
  have hNew : ∀ q ∈ S, p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
    intro q hq
    have h₁ : q.1 ∈ used S := mem_union_left _ (mem_image_of_mem _ hq)
    have h₂ : q.2 ∈ used S := mem_union_right _ (mem_image_of_mem _ hq)
    exact ⟨fun he => hleft (he.symm ▸ h₁), fun he => hleft (he.symm ▸ h₂),
      fun he => hright (he.symm ▸ h₁), fun he => hright (he.symm ▸ h₂)⟩
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases mem_insert.mp hq with rfl|hq
    · exact hne
    · exact hS.1 q hq
  · intro q hq x hx hqx
    rcases mem_insert.mp hq with rfl|hqS
    · exact hNew _ (mem_of_mem_insert_of_ne hx hqx.symm)
    · rcases mem_insert.mp hx with rfl|hxS
      · obtain ⟨h₁, h₂, h₃, h₄⟩ := hNew _ hqS
        exact ⟨h₁.symm, h₃.symm, h₂.symm, h₄.symm⟩
      · exact hS.2 hqS hxS hqx

private theorem available_cover_count (D : Digraph V) (S : Finset (V × V)) (x : V × V) (g : ℕ)
    (hIn : (used S).card+g ≤ inDegree D x.1) (hOut : (used S).card+g ≤ outDegree D x.2) :
    g*(g-1) ≤ ((available S).filter fun p => Covers D p x).card := by
  let A := (univ.filter fun u => D.Adj u x.1) \ used S
  let B := (univ.filter fun v => D.Adj x.2 v) \ used S
  have hA : g ≤ A.card := by
    have h := card_le_card_sdiff_add_card
      (s := univ.filter fun u => D.Adj u x.1) (t := used S)
    change inDegree D x.1 ≤ A.card+(used S).card at h
    omega
  have hB : g ≤ B.card := by
    have h := card_le_card_sdiff_add_card
      (s := univ.filter fun v => D.Adj x.2 v) (t := used S)
    change outDegree D x.2 ≤ B.card+(used S).card at h
    omega
  let rows := fun u => (B.erase u).image (Prod.mk u)
  have hRows : ((A : Set V)).PairwiseDisjoint rows := by
    intro u _ v _ huv
    refine Finset.disjoint_left.mpr ?_
    intro p hu hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hu
    obtain ⟨b, _, hb⟩ := mem_image.mp hv
    exact huv (congrArg Prod.fst hb).symm
  have hEach : ∀ u ∈ A, g-1 ≤ (rows u).card := by
    intro u _
    rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
    have h := (pred_card_le_card_erase (s := B) (a := u))
    omega
  have hSub : A.biUnion rows ⊆ (available S).filter (fun p => Covers D p x) := by
    intro p hp
    obtain ⟨u, hu, hp⟩ := mem_biUnion.mp hp
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hp
    obtain ⟨hvu, hvB⟩ := mem_erase.mp hv
    obtain ⟨huD, huS⟩ := mem_sdiff.mp hu
    obtain ⟨hvD, hvS⟩ := mem_sdiff.mp hvB
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hvu.symm, huS, hvS⟩,
      (mem_filter.mp huD).2, (mem_filter.mp hvD).2⟩
  apply le_trans _ (card_le_card hSub)
  rw [card_biUnion hRows]
  have hSum : A.card*(g-1) ≤ ∑ u ∈ A, (rows u).card := by
    simpa using (sum_le_sum hEach :
      (∑ _u ∈ A, (g-1)) ≤ ∑ u ∈ A, (rows u).card)
  exact (Nat.mul_le_mul_right _ hA).trans hSum

private noncomputable def weight (D : Digraph V) (S : Finset (V × V)) (x : V × V) : ℝ :=
  (1/2:ℝ)^((S.filter fun p => Covers D p x).card)

private noncomputable def total (D : Digraph V) (S : Finset (V × V)) : ℝ :=
  ∑ x : V × V, weight D S x

private noncomputable def gain (D : Digraph V) (S : Finset (V × V)) (p : V × V) : ℝ :=
  ∑ x : V × V, if Covers D p x then weight D S x else 0

private theorem choose_pair [Nonempty V] (D : Digraph V) (S : Finset (V × V)) (g : ℕ) (δ : ℝ)
    (hg : 2 ≤ g) (hδ : 0 ≤ δ)
    (hDensity : δ*(Fintype.card V:ℝ)^2 ≤ (g:ℝ)*(g-1))
    (hIn : ∀ x, (used S).card+g ≤ inDegree D x)
    (hOut : ∀ x, (used S).card+g ≤ outDegree D x) :
    ∃ p ∈ available S, δ*total D S ≤ gain D S p := by
  let A := available S
  have hCount : ∀ x : V × V, g*(g-1) ≤ (A.filter (fun p => Covers D p x)).card :=
    fun x => available_cover_count D S x g (hIn x.1) (hOut x.2)
  have hA : A.Nonempty := by
    let x : V := Classical.choice ‹Nonempty V›
    have h := hCount (x,x)
    have hp : 0 < g*(g-1) := Nat.mul_pos (by omega) (by omega)
    exact (card_pos.mp (hp.trans_le h)).mono (filter_subset _ _)
  have hTotal : 0 ≤ total D S := sum_nonneg (fun _ _ => by unfold weight; positivity)
  have hCard : (A.card:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    have h := card_le_univ A
    rw [Fintype.card_prod] at h
    exact_mod_cast (show A.card ≤ (Fintype.card V)^2 by simpa [pow_two] using h)
  have hBound : δ*(A.card:ℝ) ≤ (g:ℝ)*(g-1) :=
    (mul_le_mul_of_nonneg_left hCard hδ).trans hDensity
  have hSum : (A.card:ℝ)*(δ*total D S) ≤ ∑ p ∈ A, gain D S p := by
    unfold gain
    rw [sum_comm]
    calc
      _ = ∑ x : V × V, (δ*(A.card:ℝ))*weight D S x := by
        rw [← mul_sum]
        unfold total
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro x _
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have hCounts : (g:ℝ)*(g-1) ≤ ((A.filter (fun p => Covers D p x)).card:ℝ) := by
          have hg' : 1 ≤ g := by omega
          exact_mod_cast (hCount x : g*(g-1) ≤ _)
        exact mul_le_mul_of_nonneg_right (hBound.trans hCounts) (by unfold weight; positivity)
  by_contra h
  push Not at h
  have hlt := sum_lt_sum_of_nonempty hA (fun p hp => h p hp)
  simp only [sum_const, nsmul_eq_mul] at hlt
  exact (not_lt_of_ge hSum) hlt

private theorem total_insert (D : Digraph V) (S : Finset (V × V)) (p : V × V) (hp : p ∉ S) :
    total D (insert p S) = total D S - gain D S p/2 := by
  have hWeight : ∀ x : V × V, weight D (insert p S) x =
      weight D S x - (if Covers D p x then weight D S x else 0)/2 := by
    intro x
    by_cases h : Covers D p x
    · have hn : p ∉ S.filter (fun q => Covers D q x) := fun h => hp (mem_filter.mp h).1
      simp only [weight, filter_insert, if_pos h, card_insert_of_notMem hn, pow_succ]
      ring
    · simp [weight, filter_insert, h]
  unfold total gain
  simp only [div_eq_mul_inv]
  rw [sum_mul, ← sum_sub_distrib]
  exact sum_congr rfl (fun x _ => by simpa only [div_eq_mul_inv] using hWeight x)

/-- Select disjoint covering pairs with a geometric bound on the residual
weight. All hypotheses are finite inequalities on the host parameters. -/
theorem exists_disjoint_cover [Nonempty V] (D : Digraph V) (m d g : ℕ) (δ : ℝ)
    (hg : 2 ≤ g) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hDensity : δ*(Fintype.card V:ℝ)^2 ≤ (g:ℝ)*(g-1))
    (hIn : ∀ v, 2*m+g ≤ inDegree D v) (hOut : ∀ v, 2*m+g ≤ outDegree D v)
    (hSmall : (Fintype.card V:ℝ)^2*(1-δ/2)^m < (1/2:ℝ)^d) :
    ∃ S : Finset (V × V), S.card = m ∧ DisjointPairs S ∧
      ∀ x : V × V, d ≤ (S.filter fun p => Covers D p x).card := by
  have hNonneg : 0 ≤ 1-δ/2 := by linarith
  have hMain : ∀ k ≤ m, ∃ S : Finset (V × V), S.card = k ∧ DisjointPairs S ∧
      total D S ≤ (Fintype.card V:ℝ)^2*(1-δ/2)^k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, rfl, by simp [DisjointPairs], by simp [total, weight, Fintype.card_prod, pow_two]⟩
    | succ k ih =>
      intro hk
      obtain ⟨S, hCard, hDisj, hTotal⟩ := ih (by omega)
      have hUsed := used_le S
      obtain ⟨p, hp, hGain⟩ := choose_pair D S g δ hg hδ hDensity
        (fun v => by have := hIn v; omega) (fun v => by have := hOut v; omega)
      have hNo := outside_of_available hp
      refine ⟨insert p S, by rw [card_insert_of_notMem hNo, hCard], disjoint_insert hp hDisj, ?_⟩
      rw [total_insert D S p hNo, pow_succ (1-δ/2) k, ← mul_assoc]
      calc
        total D S - gain D S p/2 ≤ total D S*(1-δ/2) := by linarith only [hGain]
        _ ≤ _ := mul_le_mul_of_nonneg_right hTotal hNonneg
  obtain ⟨S, hCard, hDisj, hTotal⟩ := hMain m le_rfl
  refine ⟨S, hCard, hDisj, fun x => ?_⟩
  by_contra h
  have hPow : (1/2:ℝ)^d ≤ weight D S x := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hw : weight D S x ≤ total D S :=
    single_le_sum (f := weight D S) (fun _ _ => by unfold weight; positivity) (mem_univ x)
  exact (not_lt_of_ge (hPow.trans (hw.trans hTotal))) hSmall

end OverfullWork.DirectedCoveringPairs
