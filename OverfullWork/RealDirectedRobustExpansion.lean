module

public import OverfullWork.DirectedRobustSplit

@[expose] public section


/-! Published real normalized robust out-expansion, with exact ceiling
bridges. Upward rounding in the constructed split recovers precisely
p*nu/2 and (1-p)*nu/2, without an unproved rounding convention. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

noncomputable def realNeighbourhood (D : Digraph V) (ν : ℝ) (S : Finset V) : Finset V :=
  univ.filter fun v => ν*(Fintype.card V:ℝ) ≤ (inNeighbours D S v:ℝ)

def IsRealRobust (D : Digraph V) (ν τ : ℝ) : Prop :=
  ∀ S : Finset V,τ*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
    (S.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) →
    (S.card:ℝ)+ν*(Fintype.card V:ℝ) ≤ ((realNeighbourhood D ν S).card:ℝ)

theorem realNeighbourhood_eq_integer (D : Digraph V) (ν : ℝ) (S : Finset V) :
    realNeighbourhood D ν S=neighbourhood D ⌈ν*(Fintype.card V:ℝ)⌉₊ S := by
  ext v
  simp only [realNeighbourhood,neighbourhood,mem_filter,mem_univ,true_and,Nat.ceil_le]

theorem integer_of_real (D : Digraph V) (ν τ : ℝ) (hν : 0 ≤ ν)
    (hRobust : IsRealRobust D ν τ) :
    IsRobustAt D ⌈ν*(Fintype.card V:ℝ)⌉₊ ⌈τ*(Fintype.card V:ℝ)⌉₊ := by
  intro S hlo hhi
  have hLo : τ*(Fintype.card V:ℝ) ≤ (S.card:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlo)
  have hHi : (S.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) := by
    have hh : (S.card:ℝ)+(⌈τ*(Fintype.card V:ℝ)⌉₊:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hhi
    have hτ := Nat.le_ceil (τ*(Fintype.card V:ℝ))
    nlinarith only [hh,hτ]
  have hGrow := hRobust S hLo hHi
  rw [realNeighbourhood_eq_integer] at hGrow
  have hCeil := Nat.ceil_le.mpr hGrow
  rw [add_comm, Nat.ceil_add_natCast (mul_nonneg hν (Nat.cast_nonneg _))] at hCeil
  omega

theorem real_of_integer_at_ceil_interval (D : Digraph V) (r : ℕ) (ν τ : ℝ)
    (hτ : 0 ≤ τ) (hRobust : IsRobustAt D r ⌈τ*(Fintype.card V:ℝ)⌉₊)
    (hν : ν*(Fintype.card V:ℝ) ≤ (r:ℝ)) : IsRealRobust D ν τ := by
  intro S hlo hhi
  have hLo : ⌈τ*(Fintype.card V:ℝ)⌉₊ ≤ S.card := Nat.ceil_le.mpr hlo
  have hCombined : τ*(Fintype.card V:ℝ)+(S.card:ℝ) ≤ (Fintype.card V:ℝ) := by nlinarith only [hhi]
  have hCeil := Nat.ceil_le.mpr hCombined
  rw [Nat.ceil_add_natCast (mul_nonneg hτ (Nat.cast_nonneg _))] at hCeil
  have hHi : S.card+⌈τ*(Fintype.card V:ℝ)⌉₊ ≤ Fintype.card V := by omega
  have hGrow := hRobust S hLo hHi
  have hSub : neighbourhood D r S ⊆ realNeighbourhood D ν S := by
    intro v hv
    have hCount : (r:ℝ) ≤ (inNeighbours D S v:ℝ) := by exact_mod_cast (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _,hν.trans hCount⟩
  have hh : (S.card:ℝ)+(r:ℝ) ≤ ((realNeighbourhood D ν S).card:ℝ) := by
    exact_mod_cast hGrow.trans (card_le_card hSub)
  linarith only [hh,hν]

end OverfullWork.DirectedRobustExpansion

namespace OverfullWork.DirectedRobustSplit
open Finset DirectedRobustExpansion
open scoped Classical
universe u
set_option maxHeartbeats 18000000

/-- Gao--Shan Lemma 2.9 in its real normalized convention, with degree
control for both actual parts. The threshold precedes the host digraph. -/
theorem exists_real_relative_split (p ν τ α η : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hν : 0 < ν) (hτ : 0 ≤ τ) (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (D : Digraph V),N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ H : Digraph V,H ≤ D ∧
        (∀ v,|(inDegree H v:ℝ)-p*(inDegree D v:ℝ)| < η*p*(inDegree D v:ℝ)) ∧
        (∀ v,|(outDegree H v:ℝ)-p*(outDegree D v:ℝ)| < η*p*(outDegree D v:ℝ)) ∧
        (∀ v,|(inDegree (D\H) v:ℝ)-(1-p)*(inDegree D v:ℝ)| < η*(1-p)*(inDegree D v:ℝ)) ∧
        (∀ v,|(outDegree (D\H) v:ℝ)-(1-p)*(outDegree D v:ℝ)| < η*(1-p)*(outDegree D v:ℝ)) ∧
        IsRealRobust H (p*ν/2) τ ∧ IsRealRobust (D\H) ((1-p)*ν/2) τ := by
  obtain ⟨N,hN⟩ := exists_relative_split.{u} p ν α η hp hp1 hν hα hη
  refine ⟨N,?_⟩
  intro V _ _ D hn hRobust hIn hOut
  let r := ⌈ν*(Fintype.card V:ℝ)⌉₊
  let t := ⌈τ*(Fintype.card V:ℝ)⌉₊
  obtain ⟨H,hLe,hHI,hHO,hBI,hBO,_,hH,_,hB⟩ := hN D r t hn
    (integer_of_real D ν τ hν.le hRobust) (Nat.le_ceil _) hIn hOut
  refine ⟨H,hLe,hHI,hHO,hBI,hBO,?_,?_⟩
  · apply real_of_integer_at_ceil_interval H _ (p*ν/2) τ hτ hH
    have h₁ := mul_le_mul_of_nonneg_left (Nat.le_ceil (ν*(Fintype.card V:ℝ))) hp.le
    have h₂ := Nat.le_ceil (p*(r:ℝ)/2)
    change p*(ν*(Fintype.card V:ℝ)) ≤ p*(r:ℝ) at h₁
    nlinarith only [h₁,h₂]
  · apply real_of_integer_at_ceil_interval (D\H) _ ((1-p)*ν/2) τ hτ hB
    have h₁ := mul_le_mul_of_nonneg_left (Nat.le_ceil (ν*(Fintype.card V:ℝ)))
      (show 0 ≤ 1-p by linarith only [hp1])
    have h₂ := Nat.le_ceil ((1-p)*(r:ℝ)/2)
    change (1-p)*(ν*(Fintype.card V:ℝ)) ≤ (1-p)*(r:ℝ) at h₁
    nlinarith only [h₁,h₂]

end OverfullWork.DirectedRobustSplit
