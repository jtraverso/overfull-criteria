module

public import OverfullWork.ChenShanHypergeometricTail
public import OverfullWork.UniformPartitionSampling
public import OverfullWork.ChenShanNestedSamplingBudget
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real UniformSubsetSampling
open scoped Classical

variable {W I V : Type*} [Fintype W] [Fintype I] [Fintype V]

/-- Realize the palette sizes as disjoint subsets of the allowed colors. -/
theorem exists_disjoint_palette_seeds (s : I → ℕ) (hs : (∑ i, s i) ≤ Fintype.card W) :
    ∃ B : I → Finset W, (∀ i, (B i).card = s i) ∧ Pairwise (fun i j => Disjoint (B i) (B j)) := by
  let J := Σ i : I, Fin (s i)
  have hJ : Fintype.card J ≤ Fintype.card W := by
    simpa only [J,Fintype.card_sigma,Fintype.card_fin] using hs
  let e : J ↪ W := (Fintype.equivFin J).toEmbedding.trans
    ((Fin.castLEEmb hJ).trans (Fintype.equivFin W).symm.toEmbedding)
  let f (i : I) : Fin (s i) ↪ W :=
    (⟨fun j => ⟨i,j⟩,fun j j' h => by cases h; rfl⟩ : Fin (s i) ↪ J).trans e
  let B (i : I) := univ.map (f i)
  refine ⟨B,fun i => by simp [B],?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro w hi hj
  obtain ⟨a,_,ha⟩ := mem_map.mp hi
  obtain ⟨b,_,hb⟩ := mem_map.mp hj
  exact hij (congrArg Sigma.fst (e.injective (ha.trans hb.symm)))

/-- Equation (5.3) for a simultaneous family of disjoint palettes. The
input sum is a finite bound on the probability of any failed test.
The same permutation avoids any extra tests whose probabilities fit
in the remaining budget. A lists the allowed core colors at each
active vertex. -/
theorem exists_disjoint_palettes_with_incidence_and_tests {J : Type*} [Fintype J]
    (s : I → ℕ) (hs : (∑ i, s i) ≤ Fintype.card W)
    (k : ℕ) (hk : 0 < k) (θ : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hWlo : (511/512 : ℝ)*k ≤ Fintype.card W) (hWhi : Fintype.card W ≤ k)
    (c : V → ℕ) (A : V → Finset W)
    (hActive : ∀ v, θ*k ≤ (c v:ℝ))
    (hAvailable : ∀ v, (511/512 : ℝ)*(c v:ℝ) ≤ (A v).card)
    (hTotal : ∀ v, (A v).card ≤ c v)
    (label : J → I) (extra : J → Finset W → Prop)
    (hRisk : (∑ p : I × V, 2*exp (-((θ/32)^2*(s p.1:ℝ))/4)) +
      (∑ j, probability (s (label j)) (extra j)) < 1) :
    ∃ P : I → Finset W, (∀ i, (P i).card = s i) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (∀ j, ¬extra j (P (label j))) ∧
      ∀ i v, (15/16 : ℝ)*((s i:ℝ)/k)*c v ≤ ((A v ∩ P i).card:ℝ) ∧
        ((A v ∩ P i).card:ℝ) ≤ 2*((s i:ℝ)/k)*c v := by
  obtain ⟨B,hB,hDisj⟩ := exists_disjoint_palette_seeds s hs
  let n := Fintype.card W
  let bad (p : I × V) (T : Finset W) : Prop :=
    θ/32*(s p.1:ℝ) ≤ |((A p.2 ∩ T).card:ℝ)-((s p.1:ℝ)/n)*(A p.2).card|
  have hTail (p : I × V) :
      probability (B p.1).card (bad p) ≤ 2*exp (-((θ/32)^2*(s p.1:ℝ))/4) := by
    rw [hB]
    have hpn : s p.1 ≤ Fintype.card W := (hB p.1).symm ▸ card_le_univ (B p.1)
    have hh := fixed_size_intersection_two_sided hpn (A p.2) (θ/32)
      (by positivity) (by linarith only [hθ₁])
    exact hh
  let blocks : (I × V) ⊕ J → Finset W :=
    Sum.elim (fun p => B p.1) (fun j => B (label j))
  let tests : (I × V) ⊕ J → Finset W → Prop := Sum.elim bad extra
  have hSum : (∑ t, probability (blocks t).card (tests t)) < 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ p : I × V, probability (B p.1).card (bad p)) +
      (∑ j, probability (B (label j)).card (extra j)) < 1
    simp_rw [hB] at hTail ⊢
    exact (add_le_add_left (sum_le_sum (fun p _ => hTail p)) _).trans_lt hRisk
  obtain ⟨perm,hperm⟩ := exists_permutation_avoiding blocks tests hSum
  let P (i : I) := (B i).map perm.toEmbedding
  refine ⟨P,fun i => by simp only [P,card_map,hB],
    fun i j hij => (disjoint_map _).mpr (hDisj hij),fun j => hperm (.inr j),?_⟩
  intro i v
  have hnk : (n:ℝ) ≤ k := by exact_mod_cast hWhi
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hn : 0 < (n:ℝ) := (show 0 < (511/512:ℝ)*(k:ℝ) by positivity).trans_le hWlo
  let fraction : ℝ := (s i:ℝ)/k
  let allowedFraction : ℝ := (s i:ℝ)/n
  have hfraction : 0 ≤ fraction := by dsimp [fraction]; positivity
  have hallowedFraction : 0 ≤ allowedFraction := by dsimp [allowedFraction]; positivity
  have hScale₀ : fraction ≤ allowedFraction := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn hnk
  have hScale₁ : allowedFraction ≤ (512/511 : ℝ)*fraction := by
    have hf := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) (s i))
      (show 0 < (511/512:ℝ)*(k:ℝ) by positivity) hWlo
    dsimp [fraction,allowedFraction]
    calc
      (s i:ℝ)/n ≤ (s i:ℝ)/((511/512:ℝ)*(k:ℝ)) := hf
      _ = _ := by ring
  have hμlo : (511/512 : ℝ)*fraction*c v ≤ allowedFraction*(A v).card := by
    have h₁ := mul_le_mul_of_nonneg_left (hAvailable v) hfraction
    have h₂ := mul_le_mul_of_nonneg_right hScale₀ (Nat.cast_nonneg (α := ℝ) (A v).card)
    nlinarith only [h₁,h₂]
  have hμhi : allowedFraction*(A v).card ≤ (512/511 : ℝ)*fraction*c v := by
    have h₁ := mul_le_mul_of_nonneg_left
      (show ((A v).card:ℝ) ≤ c v by exact_mod_cast hTotal v) hallowedFraction
    exact h₁.trans (mul_le_mul_of_nonneg_right hScale₁ (Nat.cast_nonneg _))
  have hErr : θ/32*(s i:ℝ) ≤ fraction*c v/32 := by
    have h := mul_le_mul_of_nonneg_left (hActive v) hfraction
    have hFractionEq : fraction*(k:ℝ) = s i := div_mul_cancel₀ _ hkR.ne'
    nlinarith only [h,congrArg (fun x : ℝ => θ*x) hFractionEq]
  have hGood : |((A v ∩ P i).card:ℝ)-allowedFraction*(A v).card| < θ/32*(s i:ℝ) :=
    lt_of_not_ge (hperm (.inl (i,v)))
  obtain ⟨hLo,hHi⟩ := abs_lt.mp hGood
  have hNonneg := mul_nonneg hfraction (Nat.cast_nonneg (α := ℝ) (c v))
  change (15/16:ℝ)*fraction*c v ≤ ((A v ∩ P i).card:ℝ) ∧
    ((A v ∩ P i).card:ℝ) ≤ 2*fraction*c v
  constructor <;>
    nlinarith only [hLo,hHi,hμlo,hμhi,hErr,hNonneg]


/-- Simultaneous incidence bounds (5.3) with no additional bad events. -/
theorem exists_disjoint_palettes_with_incidence
    (s : I → ℕ) (hs : (∑ i, s i) ≤ Fintype.card W)
    (k : ℕ) (hk : 0 < k) (θ : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hWlo : (511/512 : ℝ)*k ≤ Fintype.card W) (hWhi : Fintype.card W ≤ k)
    (c : V → ℕ) (A : V → Finset W)
    (hActive : ∀ v, θ*k ≤ (c v:ℝ))
    (hAvailable : ∀ v, (511/512 : ℝ)*(c v:ℝ) ≤ (A v).card)
    (hTotal : ∀ v, (A v).card ≤ c v)
    (hRisk : (∑ p : I × V, 2*exp (-((θ/32)^2*(s p.1:ℝ))/4)) < 1) :
    ∃ P : I → Finset W, (∀ i, (P i).card = s i) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      ∀ i v, (15/16 : ℝ)*((s i:ℝ)/k)*c v ≤ ((A v ∩ P i).card:ℝ) ∧
        ((A v ∩ P i).card:ℝ) ≤ 2*((s i:ℝ)/k)*c v := by
  obtain ⟨P,hCard,hDisj,_,hInc⟩ := exists_disjoint_palettes_with_incidence_and_tests
    s hs k hk θ hθ hθ₁ hWlo hWhi c A hActive hAvailable hTotal
    (fun j : Empty => j.elim) (fun j _ => j.elim) (by simpa using hRisk)
  exact ⟨P,hCard,hDisj,hInc⟩

universe u

/-- For fixed positive incidence and palette fractions, an arbitrary
positive part of the failure budget can be reserved for these tests. -/
theorem exists_palette_incidence_risk_threshold (p : ℕ) (C θ δ ε : ℝ)
    (hC : 0 ≤ C) (hθ : 0 < θ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
    ∀ {I V : Type u} [Fintype I] [Fintype V],
      Fintype.card I ≤ p → (Fintype.card V:ℝ) ≤ C*k →
      ∀ s : I → ℕ, (∀ i, δ*k ≤ (s i:ℝ)) →
      (∑ i : I × V, 2*exp (-((θ/32)^2*(s i.1:ℝ))/4)) < ε := by
  let γ : ℝ := (θ/32)^2*δ/4
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨N,hN⟩ := exists_nested_sampling_budget (2*(p:ℝ)*C) γ ε (by positivity) hγ hε
  refine ⟨N,?_⟩
  intro k hk I V _ _ hI hV s hFrac
  have hMain : (2*(p:ℝ)*C)*(k:ℝ)*exp (-γ*k) < ε := by
    simpa only [sum_singleton] using hN {k} (by
      intro n hn
      rw [mem_singleton.mp hn]
      exact hk)
  have hCard : (Fintype.card (I × V):ℝ) ≤ (p:ℝ)*C*k := by
    rw [Fintype.card_prod,Nat.cast_mul,mul_assoc]
    exact mul_le_mul (by exact_mod_cast hI) hV (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply lt_of_le_of_lt _ hMain
  calc
    _ ≤ ∑ _i : I × V, 2*exp (-γ*k) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (hFrac i.1)
        (show 0 ≤ (θ/32)^2 by positivity)
      dsimp only [γ]
      nlinarith only [h]
    _ = (Fintype.card (I × V):ℝ)*(2*exp (-γ*k)) := by simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hCard (show 0 ≤ 2*exp (-γ*k) by positivity)
      nlinarith only [h]

/-- Uniform-order form of (5.3). The numbers of palettes and active
vertices may be bounded by a constant and a linear function of k.
The minimum palette fraction and the active threshold determine the
exponential decay uniformly before the color and vertex sets are chosen. -/
theorem exists_palette_incidence_threshold (p : ℕ) (C θ δ : ℝ)
    (hC : 0 ≤ C) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
    ∀ {W I V : Type u} [Fintype W] [Fintype I] [Fintype V],
    Fintype.card I ≤ p → (Fintype.card V:ℝ) ≤ C*k →
    (511/512 : ℝ)*k ≤ Fintype.card W → Fintype.card W ≤ k →
    ∀ (s : I → ℕ) (c : V → ℕ) (A : V → Finset W),
      (∑ i, s i) ≤ Fintype.card W →
      (∀ i, δ*k ≤ (s i:ℝ)) →
      (∀ v, θ*k ≤ (c v:ℝ)) →
      (∀ v, (511/512 : ℝ)*(c v:ℝ) ≤ (A v).card) →
      (∀ v, (A v).card ≤ c v) →
      ∃ P : I → Finset W, (∀ i, (P i).card = s i) ∧
        Pairwise (fun i j => Disjoint (P i) (P j)) ∧
        ∀ i v, (15/16 : ℝ)*((s i:ℝ)/k)*c v ≤ ((A v ∩ P i).card:ℝ) ∧
          ((A v ∩ P i).card:ℝ) ≤ 2*((s i:ℝ)/k)*c v := by
  obtain ⟨N,hN⟩ := exists_palette_incidence_risk_threshold.{u} p C θ δ 1
    hC hθ hδ (by norm_num)
  refine ⟨max N 1,?_⟩
  intro k hk W I V _ _ _ hI hV hWlo hWhi s c A hSlots hFrac hActive hAvailable hTotal
  have hk₀ : 0 < k := (le_max_right N 1).trans hk
  exact exists_disjoint_palettes_with_incidence s hSlots k hk₀ θ hθ hθ₁ hWlo hWhi
    c A hActive hAvailable hTotal (hN k ((le_max_left N 1).trans hk) hI hV s hFrac)

end OverfullWork.ChenShan
