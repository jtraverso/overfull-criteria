module

public import OverfullWork.UniformProfilePartitions

@[expose] public section


/-! Uniform refinement for a cluster, simultaneously for every profile in
Osthus–Staden's (URef). The profiles may contain both orientations and
all the reserve digraphs. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset UniformSubsetSampling
open scoped Classical
universe u v

theorem exists_uniform_profile_refinement (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {J : Type v} [Fintype J]
      (profiles : J → Finset V) (m : ℕ),
      N ≤ Fintype.card V → Fintype.card V = ℓ*m →
      (Fintype.card J : ℝ) ≤ C*(Fintype.card V : ℝ) →
      ∃ rank : V → Fin ℓ, ∀ i,
        (slice rank i).card = m ∧ ∀ j,
          ε*(Fintype.card V : ℝ) ≤ (profiles j).card →
          |((slice rank i ∩ profiles j).card : ℝ)-(profiles j).card/(ℓ : ℝ)| ≤
            ε*((profiles j).card/(ℓ : ℝ)) := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hTol : 0 < ε*ε/(ℓ : ℝ) := div_pos (mul_pos hε hε) hℓR
  obtain ⟨N,hN⟩ := exists_partition_profile_threshold.{u,0,v} C (ε*ε/(ℓ : ℝ)) hC hTol
  refine ⟨max N (ℓ+1), ?_⟩
  intro V _ J _ profiles m hSize hCard hProfiles
  have hLarge : ℓ+1 ≤ Fintype.card V := le_trans (le_max_right _ _) hSize
  have hn : 0 < Fintype.card V := by omega
  have hm : 0 < m := by
    by_contra! h
    simp [show m=0 by omega] at hCard
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : (∑ _i : Fin ℓ, m) = Fintype.card V := by simp [hCard]
  have hIndex : Fintype.card (Fin ℓ) < Fintype.card V^2 := by
    simp only [Fintype.card_fin]
    exact (show ℓ < Fintype.card V by omega).trans_le (Nat.le_self_pow (by decide) _)
  obtain ⟨rank,hRank⟩ := hN profiles (fun _ : Fin ℓ => m) ((le_max_left _ _).trans hSize)
    hsum hProfiles hIndex
  refine ⟨rank,fun i => ⟨(hRank i).1,?_⟩⟩
  intro j hj
  have hc : (Fintype.card V : ℝ) = (ℓ : ℝ)*m := by exact_mod_cast hCard
  have hFrac : (m : ℝ)/(Fintype.card V : ℝ) = 1/(ℓ : ℝ) := by
    rw [hc]
    field_simp
  have h := (hRank i).2 j
  rw [hFrac,one_div,mul_comm ((ℓ : ℝ)⁻¹),←div_eq_mul_inv] at h
  apply le_trans h.le
  have hh := (mul_le_mul_of_nonneg_left hj hε.le)
  calc
    ε*ε/(ℓ : ℝ)*(Fintype.card V : ℝ) =
        (ε*(ε*(Fintype.card V : ℝ)))/(ℓ : ℝ) := by ring
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hh hℓR.le

end OverfullWork.DirectedRobustExpansion
