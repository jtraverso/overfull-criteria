module

public import OverfullWork.ChenShanConditionalPermutation

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real UniformSubsetSampling
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The degree test for one vertex and one target prefix. -/
noncomputable def sampledDegreeError (E : A → B → Prop) (v : A) (T : Finset B) : ℝ :=
  |(((univ.filter (E v)) ∩ T).card : ℝ) -
    ((T.card : ℝ)/Fintype.card B) * (univ.filter (E v)).card|

/-- A bad event for one ordered pair of classes, including membership
of the vertex in the source prefix and a target at most two levels on. -/
def failsDegreeSample (E : A → B → Prop) (S : ℕ → Finset A) (T : ℕ → Finset B)
    (m : ℕ → ℕ) (l : ℕ) (ξ : ℝ) (permA : Equiv.Perm A) (permB : Equiv.Perm B) : Prop :=
  ∃ i : Fin (l+1), ∃ r : Fin 3, (i.val+r.val ≤ l) ∧
    ∃ v, v ∈ permutationImage (S i) permA ∧
      ξ * m (i.val+r.val) < sampledDegreeError E v (permutationImage (T (i.val+r.val)) permB)

/-- The source membership probability cancels the ambient population
size when summing the tests at a level. -/
theorem failsDegreeSample_card_le
    (E : A → B → Prop) (S : ℕ → Finset A) (T : ℕ → Finset B)
    (m : ℕ → ℕ) (l : ℕ) (ξ : ℝ) (bound : ℕ → ℝ)
    (hn : 0 < Fintype.card A) (hBound : ∀ i, 0 ≤ bound i)
    (hTail : ∀ i ≤ l, ∀ r ≤ 2, i+r ≤ l → ∀ v : A,
      probability (T (i+r)).card (fun X => ξ*m (i+r) < sampledDegreeError E v X) ≤ bound i) :
    (((univ : Finset (Equiv.Perm A × Equiv.Perm B)).filter (fun z =>
      failsDegreeSample E S T m l ξ z.1 z.2)).card : ℝ) ≤
      (∑ i : Fin (l+1), 3*(S i).card*bound i) *
        ((Fintype.card (Equiv.Perm A) : ℝ)*Fintype.card (Equiv.Perm B)) := by
  let Ω := Equiv.Perm A × Equiv.Perm B
  let I := Fin (l+1) × Fin 3 × A
  let event (i : I) (z : Ω) : Prop :=
    i.1.val+i.2.1.val ≤ l ∧ i.2.2 ∈ permutationImage (S i.1) z.1 ∧
      ξ*m (i.1.val+i.2.1.val) < sampledDegreeError E i.2.2
        (permutationImage (T (i.1.val+i.2.1.val)) z.2)
  let bad (i : I) := (univ : Finset Ω).filter (event i)
  let n := (Fintype.card A : ℝ)
  let N := (Fintype.card (Equiv.Perm A) : ℝ)*Fintype.card (Equiv.Perm B)
  have hnR : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hSub : (univ.filter (fun z : Ω => failsDegreeSample E S T m l ξ z.1 z.2)) ⊆
      (univ : Finset I).biUnion bad := by
    intro z hz
    obtain ⟨i,r,hj,v,hv,hFail⟩ := (mem_filter.mp hz).2
    exact mem_biUnion.mpr ⟨(i,r,v),mem_univ _,mem_filter.mpr ⟨mem_univ _,hj,hv,hFail⟩⟩
  have hTest (i : I) : ((bad i).card : ℝ) ≤ ((S i.1).card/n)*bound i.1*N := by
    let badTarget (X : Finset B) := ξ*m (i.1.val+i.2.1.val) < sampledDegreeError E i.2.2 X
    by_cases hi : i.1.val+i.2.1.val ≤ l
    · have hE : bad i = univ.filter (fun z : Ω =>
          i.2.2 ∈ permutationImage (S i.1) z.1 ∧
            badTarget (permutationImage (T (i.1.val+i.2.1.val)) z.2)) := by
        ext z
        simp only [bad,mem_filter,event,hi,true_and,badTarget]
      rw [hE,permutation_pair_bad_event_card]
      have h := hTail i.1 (by omega) i.2.1 (by omega) hi i.2.2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by positivity)) hN
    · have hEmpty : bad i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hi (mem_filter.mp hz).2.1
      rw [hEmpty,card_empty,Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (hBound _)) hN
  have hCount : (((univ : Finset Ω).filter (fun z =>
      failsDegreeSample E S T m l ξ z.1 z.2)).card : ℝ) ≤ ∑ i : I, ((bad i).card : ℝ) := by
    exact_mod_cast (card_le_card hSub).trans (card_biUnion_le (s := univ) (t := bad))
  calc
    _ ≤ _ := hCount
    _ ≤ ∑ i : I, ((S i.1).card/n)*bound i.1*N := sum_le_sum fun i _ => hTest i
    _ = _ := by
      rw [← sum_mul]
      congr 1
      dsimp only [I]
      simp only [Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul]
      apply sum_congr rfl
      intro i _
      simp only [Fintype.card_prod,Nat.cast_mul,Fintype.card_fin,Nat.cast_ofNat]
      change 3*n*((S i).card/n*bound i) = 3*(S i).card*bound i
      field_simp [hnR.ne']

end OverfullWork.ChenShan
