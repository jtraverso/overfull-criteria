module

public import OverfullWork.DirectedConfigurationDegrees
public import OverfullWork.DirectedReserveUsage
public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Residual degree and expansion estimates for GGKLO Lemma 7.3(ii)–(iii).
The original reserve is charged only for its own arcs. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage
open scoped Classical
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]

/-- Flexible occurrences incident to the given vertex, in the indicated
direction. This counts repeated ordered endpoint pairs with multiplicity. -/
noncomputable def Layout.endpointLoad (L : Layout V I) (incoming : Bool) (v : V) : ℕ :=
  ∑ i : {i // i ∉ L.fixed}, if v = (if incoming then L.target i.val else L.source i.val)
    then 1 else 0

/-- The total host use is one in-arc and one out-arc per round, up to the
number of boundary appearances and the sum of flexible endpoint loads. -/
theorem semidegrees_batch_used (D : Digraph V) (L : J → Layout V I)
    (R : ∀ i, Realization D (L i))
    (hDis : Pairwise (fun i j => Disjoint (R i).used (R j).used)) (v : V)
    (a b : ℕ) (hAppearance : visits (fun i => (L i).boundary) v ≤ a)
    (hLoad : ∀ s, (∑ i, (L i).endpointLoad s v) ≤ b) :
    let U := ⨆ i, (R i).used
    Fintype.card J ≤ inDegree U v+a ∧ inDegree U v ≤ Fintype.card J+b ∧
      Fintype.card J ≤ outDegree U v+a ∧ outDegree U v ≤ Fintype.card J+b := by
  dsimp only
  rw [inDegree_iSup_of_disjoint _ hDis,outDegree_iSup_of_disjoint _ hDis]
  have hAtLeast (f : J → ℕ) (hf : ∀ i, v ∉ (L i).boundary → f i = 1) :
      Fintype.card J ≤ (∑ i, f i)+a := by
    have hmin : ∑ i : J, (if v ∈ (L i).boundary then 0 else 1) ≤ ∑ i, f i := by
      apply sum_le_sum
      intro i _
      by_cases hi : v ∈ (L i).boundary
      · simp [hi]
      · simp [hi,hf i hi]
    have he : ∑ i : J, (if v ∈ (L i).boundary then 0 else 1) =
        ((univ : Finset J).filter (fun i => v ∉ (L i).boundary)).card := by
      rw [card_filter]
      apply sum_congr rfl
      intro i _
      by_cases hi : v ∈ (L i).boundary <;> simp [hi]
    have hcard := card_filter_add_card_filter_not (s := (univ : Finset J))
      (p := fun i => v ∈ (L i).boundary)
    rw [he] at hmin
    change ((univ : Finset J).filter (fun i => v ∈ (L i).boundary)).card ≤ a at hAppearance
    rw [card_univ] at hcard
    omega
  have hAtMost (f : J → ℕ) (s : Bool)
      (hf : ∀ i, f i = if v ∈ (L i).boundary then (L i).endpointLoad s v else 1) :
      (∑ i, f i) ≤ Fintype.card J+b := by
    calc
      _ ≤ ∑ i, (1+(L i).endpointLoad s v) := by
        apply sum_le_sum
        intro i _
        rw [hf i]
        split <;> omega
      _ = Fintype.card J+∑ i, (L i).endpointLoad s v := by simp [sum_add_distrib]
      _ ≤ _ := Nat.add_le_add_left (hLoad s) _
  have hIn (i : J) : inDegree (R i).used v =
      if v ∈ (L i).boundary then (L i).endpointLoad true v else 1 :=
    (R i).semidegrees_used v |>.1
  have hOut (i : J) : outDegree (R i).used v =
      if v ∈ (L i).boundary then (L i).endpointLoad false v else 1 :=
    (R i).semidegrees_used v |>.2
  exact ⟨hAtLeast _ (fun i hi => by rw [hIn,if_neg hi]),hAtMost _ true hIn,
    hAtLeast _ (fun i hi => by rw [hOut,if_neg hi]),hAtMost _ false hOut⟩

omit [Fintype I] [Fintype J] in
private theorem degree_split (D Γ U : Digraph V) (hDΓ : Disjoint D Γ) (hU : U ≤ D ⊔ Γ)
    (v : V) :
    inDegree U v = inDegree (U ⊓ D) v+inDegree (U ⊓ Γ) v ∧
    outDegree U v = outDegree (U ⊓ D) v+outDegree (U ⊓ Γ) v := by
  let H : Bool → Digraph V := fun b => if b then U ⊓ Γ else U ⊓ D
  have hEq : (⨆ b, H b) = U := by
    ext x y
    rw [Digraph.iSup_adj]
    constructor
    · rintro ⟨b,h⟩
      cases b <;> exact h.1
    · intro h
      exact (hU h).elim (fun hD => ⟨false,h,hD⟩) (fun hΓ => ⟨true,h,hΓ⟩)
  have hDis : Pairwise (fun i j => Disjoint (H i) (H j)) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hDΓ.mono inf_le_right inf_le_right
    · exact hDΓ.symm.mono inf_le_right inf_le_right
    · exact (hij rfl).elim
  have hIn := inDegree_iSup_of_disjoint H hDis v
  have hOut := outDegree_iSup_of_disjoint H hDis v
  rw [hEq] at hIn hOut
  exact ⟨by simpa [H,Nat.add_comm] using hIn,by simpa [H,Nat.add_comm] using hOut⟩

omit [Fintype I] [Fintype J] in
/-- The residual dense graph has lost about one arc in each direction per
round. The lower estimate pays for layout incidences, and the upper
estimate pays for boundary appearances and arcs taken from the reserve. -/
theorem dense_semidegrees_after_batch (D Γ U : Digraph V)
    (hDΓ : Disjoint D Γ) (hU : U ≤ D ⊔ Γ) (v : V) (m a b g : ℕ)
    (hIn : m ≤ inDegree U v+a ∧ inDegree U v ≤ m+b)
    (hOut : m ≤ outDegree U v+a ∧ outDegree U v ≤ m+b)
    (hReserveIn : inDegree (U ⊓ Γ) v ≤ g) (hReserveOut : outDegree (U ⊓ Γ) v ≤ g) :
    inDegree D v ≤ inDegree (D \ U) v+m+b ∧
    inDegree (D \ U) v+m ≤ inDegree D v+a+g ∧
    outDegree D v ≤ outDegree (D \ U) v+m+b ∧
    outDegree (D \ U) v+m ≤ outDegree D v+a+g := by
  have hDiff : D \ (U ⊓ D) = D \ U := by
    ext x y
    simp only [Digraph.sdiff_adj,Digraph.inf_adj]
    tauto
  obtain ⟨hi,ho⟩ := degree_split D Γ U hDΓ hU v
  have hDi := inDegree_sdiff_add_of_le D (U ⊓ D) inf_le_right v
  have hDo := outDegree_sdiff_add_of_le D (U ⊓ D) inf_le_right v
  rw [hDiff] at hDi hDo
  omega

omit [Fintype I] [Fintype J] in
theorem real_robust_after_reserve_use (Γ U : Digraph V) (ν τ ν' : ℝ) (g : ℕ)
    (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (hR : IsRealRobust Γ ν τ)
    (hUse : ∀ v, inDegree U v ≤ g)
    (hBudget : ν'*(Fintype.card V:ℝ)+(g:ℝ) ≤ ν*(Fintype.card V:ℝ)) :
    IsRealRobust (Γ \ U) ν' τ := by
  apply real_of_integer_at_ceil_interval _ (⌈ν*(Fintype.card V:ℝ)⌉₊-g) _ _ hτ
    (robust_after_reserve_use Γ U _ _ g (integer_of_real Γ ν τ hν hR) hUse)
  have hCeil := Nat.le_ceil (ν*(Fintype.card V:ℝ))
  by_cases hLe : g ≤ ⌈ν*(Fintype.card V:ℝ)⌉₊
  · rw [Nat.cast_sub hLe]
    linarith
  · have hGt : (⌈ν*(Fintype.card V:ℝ)⌉₊:ℝ) ≤ (g:ℝ) := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hLe)
    exact (show ν'*(Fintype.card V:ℝ) ≤ 0 by linarith).trans (Nat.cast_nonneg _)

end OverfullWork.DirectedSpanningConfiguration
