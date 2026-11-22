module

public import OverfullWork.CMSTwoCentreStopColouring
public import OverfullWork.SecondLowRegularImage
public import OverfullWork.CleanedSourceVAL

@[expose] public section


/-! Apply the paper's two-identification regularization to the actual
second-low stopping data. The cleanup certificate supplies weak VAL
at all vertices in the two parts. -/
namespace OverfullWork.NormalizedClassTwoStep

open Finset SimpleGraph TwoIndependentIdentifications RobustExpansion
open scoped Classical
universe u

set_option maxHeartbeats 1400000 in
theorem cms_no_clean_second_low_terminal (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ} {s : State V B K}
          (p : SecondLowData s),
          let m := Fintype.card (Vertices p.exceptional)
          N ≤ m → α*(m:ℝ) ≤ (s.graph.maxDegree:ℝ) →
          (K+1:ℕ) ≤ 2*η^2*(m:ℝ) → (B:ℝ) ≤ 5*η*(m:ℝ) →
          CleanedSourceVAL.IsReady s.graph p.exceptional →
          IsRealRobust s.graph ν σ → False := by
  obtain ⟨σ,hσ,hUse⟩ := cms_colourable_of_two_centre_stop.{u} α hα hα₁
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨ηMax,hηMax,hUse'⟩ := hUse ν hν hνσ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse' η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ B K s p m hSize hDensity hK hB hClean hRob
  obtain ⟨q⟩ := p.exists_partition
  have hEven := even_card_vertices p.exceptional p.even_complement
  have hAtLeastTwo : 2 ≤ p.exceptional.card := by
    have hA := card_pos.mpr q.left_nonempty
    have hB := card_pos.mpr q.right_nonempty
    have hC := card_sdiff_add_card_eq_card q.subset
    omega
  have hCard : (p.exceptional.card:ℝ) ≤ 2*η^2*(m:ℝ) := by
    exact (by exact_mod_cast p.card_bound : (p.exceptional.card:ℝ) ≤ (K+1:ℕ)).trans hK
  have hSmall (j : Bool) : (q.image.degree (Sum.inl j):ℝ) ≤ 10*η*(m:ℝ) := by
    have h := q.profile.2.2.1
    have hN : q.image.degree (Sum.inl j) ≤ 2*B := by cases j <;> omega
    have hR : (q.image.degree (Sum.inl j):ℝ) ≤ 2*(B:ℝ) := by exact_mod_cast hN
    linarith only [hR,hB]
  have hF : (∑ x : Outside p.exceptional, (s.graph.maxDegree-s.graph.degree x.val)) =
      TwoCentreRegularCompletion.ordinaryDeficit q.image s.graph.maxDegree := by
    unfold TwoCentreRegularCompletion.ordinaryDeficit
    simp only [SecondLowData.Partition.image,degree_inr]
  have hFBound : ((∑ x : Outside p.exceptional, (s.graph.maxDegree-s.graph.degree x.val)):ℕ) ≤ B := by
    rw [hF]
    exact q.profile.2.2.2
  have hDef : ((∑ x : Outside p.exceptional, (s.graph.maxDegree-s.graph.degree x.val)):ℕ) ≤
      6*η*(m:ℝ) := by
    have hh : ((∑ x : Outside p.exceptional, (s.graph.maxDegree-s.graph.degree x.val)):ℕ) ≤ (B:ℝ) := by
      exact_mod_cast hFBound
    linarith only [hh,hB,mul_nonneg hη (Nat.cast_nonneg (α := ℝ) m)]
  have hBalance : q.image.degree (Sum.inl true) ≤ q.image.degree (Sum.inl false)+
      ∑ x : Outside p.exceptional, (s.graph.maxDegree-s.graph.degree x.val) := by
    rw [hF]
    exact q.profile.2.1
  have hHigh (x : Outside p.exceptional) :
      (s.graph.maxDegree:ℝ)-5*η*(m:ℝ) ≤ s.graph.degree x.val := by
    have hx : s.graph.maxDegree-s.graph.degree x.val ≤
        ∑ y : Outside p.exceptional, (s.graph.maxDegree-s.graph.degree y.val) :=
      single_le_sum (f := fun y => s.graph.maxDegree-s.graph.degree y.val)
        (fun _ _ => Nat.zero_le _) (mem_univ x)
    have hD := s.graph.degree_le_maxDegree x.val
    have hR : (s.graph.maxDegree:ℝ) ≤ (s.graph.degree x.val:ℝ)+(B:ℝ) := by
      exact_mod_cast (show s.graph.maxDegree ≤ s.graph.degree x.val+B by omega)
    linarith only [hR,hB]
  have hColour := hN s.graph p.exceptional q.left q.subset p.independent hSize hDensity hEven
    hAtLeastTwo hCard hSmall q.profile.1 hBalance hDef hHigh
    (CleanedSourceVAL.weak_VAL s.graph p.exceptional hClean) s.no_overfull hRob
  exact s.uncolourable hColour

end OverfullWork.NormalizedClassTwoStep
