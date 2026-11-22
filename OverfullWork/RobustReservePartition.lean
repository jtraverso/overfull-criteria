module

public import OverfullWork.UniformProfilePartitions
public import OverfullWork.RobustVertexSamplingTheorem

@[expose] public section


/-! The initial reserve blocks for GGKLO Lemma 7.3(i). One partition
controls specified neighbourhood profiles and retains robust expansion
in each block and in each complementary block. -/
namespace OverfullWork.UniformSubsetSampling

open Finset DirectedRobustExpansion InducedDigraphSampling
open scoped Classical
universe u v w
set_option maxHeartbeats 4000000

theorem probability_complement {V : Type u} [Fintype V] (k : ℕ)
    (hk : k ≤ Fintype.card V) (bad : Finset V → Prop) :
    probability k (fun X => bad Xᶜ) = probability (Fintype.card V-k) bad := by
  classical
  unfold probability
  rw [Nat.choose_symm hk]
  congr 1
  apply congrArg (fun x : ℕ => (x:ℝ))
  apply card_bij (fun X _ => Xᶜ)
  · intro X hX
    obtain ⟨hX,hBad⟩ := mem_filter.mp hX
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      by rw [card_compl, (mem_powersetCard.mp hX).2]⟩,hBad⟩
  · intro X _ Y _ he
    exact compl_injective he
  · intro Y hY
    obtain ⟨hY,hBad⟩ := mem_filter.mp hY
    have hCard : (Yᶜ : Finset V).card = k := by
      rw [card_compl,(mem_powersetCard.mp hY).2]
      omega
    exact ⟨Yᶜ, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hCard⟩,
      by simpa only [compl_compl] using hBad⟩,compl_compl _⟩

/-- Simultaneously sample all parts and their complements from the
reserve. The profiles may include both in- and out-neighbours from
any of the digraphs on the common vertex set. -/
theorem exists_robust_profile_partition (ν τ c C η : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/8)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hC : 0 < C) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {J : Type w} [Fintype J] (Γ : Digraph V) (profiles : J → Finset V) (size : I → ℕ),
      N ≤ Fintype.card V → IsRealRobust Γ ν τ →
      (∑ i,size i) = Fintype.card V → (Fintype.card J:ℝ) ≤ C*(Fintype.card V:ℝ) →
      3*Fintype.card I < Fintype.card V^2 →
      (∀ i, c*(Fintype.card V:ℝ) ≤ (size i:ℝ) ∧
        c*(Fintype.card V:ℝ) ≤ ((Fintype.card V-size i:ℕ):ℝ)) →
      ∃ rank : V → I, ∀ i, (slice rank i).card = size i ∧
        IsRealRobust (induced Γ (slice rank i)) (ν^6/(2:ℝ)^60) (4*τ) ∧
        IsRealRobust (induced Γ (slice rank i)ᶜ) (ν^6/(2:ℝ)^60) (4*τ) ∧
        ∀ j, |((slice rank i ∩ profiles j).card:ℝ)-
          ((size i:ℝ)/(Fintype.card V:ℝ))*(profiles j).card| < η*(Fintype.card V:ℝ) := by
  obtain ⟨N₀,hSample⟩ := BipartiteRegularitySource.robust_vertex_sampling_explicit.{u}
    ν τ hν hντ (hν.trans_le hντ) hτ c hc hc₁
  obtain ⟨N₁,hProfile⟩ := exists_uniform_profile_threshold.{u,w} C η hC hη
  refine ⟨max N₀ (max N₁ 2), ?_⟩
  intro V _ I _ J _ Γ profiles size hn hR hSize hProfiles hI hSmall
  let n := Fintype.card V
  let ν' := ν^6/(2:ℝ)^60
  let f (X : Finset V) := ¬IsRealRobust (induced Γ X) ν' (4*τ)
  let g (i : I) (X : Finset V) : Prop := ∃ j, η*(n:ℝ) ≤
    |((X ∩ profiles j).card:ℝ)-((size i:ℝ)/(n:ℝ))*(profiles j).card|
  let events (i : I) (t : Fin 3) : Finset V → Prop :=
    if t = 0 then f else if t = 1 then (fun X => f Xᶜ) else g i
  let bad (i : I) (X : Finset V) : Prop := ∃ t, events i t X
  have hSamp := (hSample Γ (by omega) hR).2
  have hQ : ∀ i, probability (size i) (bad i) ≤ 3/(n:ℝ)^2 := by
    intro i
    have hi : size i ≤ n := by
      change size i ≤ Fintype.card V
      rw [← hSize]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    have hB := hSamp (size i) hi (hSmall i).1
    have hBC := hSamp (n-size i) (Nat.sub_le _ _) (hSmall i).2
    have hG := hProfile profiles (size i) (by omega) hi hProfiles
    apply (probability_union_bound _ _).trans
    have hEvent : ∀ t, probability (size i) (events i t) ≤ 1/(n:ℝ)^2 := by
      intro t
      have ht : t = 0 ∨ t = 1 ∨ t = 2 := by
        fin_cases t <;> decide
      rcases ht with rfl|rfl|rfl
      · simpa [events, f, ν', n] using hB
      · have he : events i 1 = fun X => f Xᶜ := by simp [events]
        rw [he,probability_complement _ hi]
        exact hBC
      · have he : events i 2 = g i := by simp [events]
        rw [he]
        exact hG
    have hSum : (∑ t : Fin 3, probability (size i) (events i t)) ≤ ∑ _t : Fin 3, 1/(n:ℝ)^2 :=
      sum_le_sum (fun t _ => hEvent t)
    exact hSum.trans (by simp [nsmul_eq_mul, div_eq_mul_inv])
  have hlt : (∑ i,probability (size i) (bad i)) < 1 := by
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hi : 3*(Fintype.card I:ℝ) < (n:ℝ)^2 := by exact_mod_cast hI
    calc
      _ ≤ ∑ _i : I, 3/(n:ℝ)^2 := sum_le_sum (fun i _ => hQ i)
      _ = (3*(Fintype.card I:ℝ))/(n:ℝ)^2 := by simp [mul_div_assoc, mul_comm]
      _ < _ := (div_lt_one (pow_pos hnR _)).mpr hi
  obtain ⟨rank,hResult⟩ := exists_partition_avoiding size hSize bad hlt
  refine ⟨rank, fun i => ⟨(hResult i).1, ?_, ?_, ?_⟩⟩
  · by_contra h
    exact (hResult i).2 ⟨0, by simpa [events] using h⟩
  · by_contra h
    exact (hResult i).2 ⟨1, by simpa [events] using h⟩
  · intro j
    apply not_le.mp
    intro h
    exact (hResult i).2 ⟨2, by simpa [events] using (show g i (slice rank i) from ⟨j,h⟩)⟩

end OverfullWork.UniformSubsetSampling
