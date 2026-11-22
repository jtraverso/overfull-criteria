module

public import OverfullWork.KuhnOsthusDivisibleClusters
public import OverfullWork.KuhnOsthusWoundSetup

@[expose] public section


/-! Round the two coarse partition dimensions and put the resulting
clusters in the cyclic order used in the proof of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs DirectedClusterQuotient InducedDigraphSampling
open scoped Classical
universe u v

set_option maxHeartbeats 850000 in
/-- A coarse reduced graph produced by the degree form of regularity
can be rounded and ordered before refining the clusters. Surviving
reduced edges still represent pairs in the original graph. -/
theorem exists_kuhn_osthus_ordered_coarse_partition (ν τ α : ℝ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ) (hτα : 16*(2*τ) ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} {I : Type v} [Fintype V] [Fintype I]
      (G : Digraph V) (D : Digraph I) (f : V → Option I) (b ℓ m d : ℕ) (ε ρ : ℝ),
      0 < b → 0 < ℓ → 2*(ℓ-1) ≤ m → N+b ≤ Fintype.card I →
      (∀ i, (cluster f i).card = m) → 0 ≤ ε → ε ≤ 1/2 →
      IsRealRobust D ν τ → (∀ i, ¬ D.Adj i i) →
      8*((b-1:ℕ):ℝ) ≤ ν*(Fintype.card I:ℝ) →
      4*((b-1:ℕ):ℝ) ≤ τ*(Fintype.card I:ℝ) →
      α*(Fintype.card I:ℝ)+((b-1:ℕ):ℝ) ≤ (d:ℝ) →
      (∀ i, d ≤ inDegree D i ∧ d ≤ outDegree D i) →
      (∀ i j, D.Adj i j → IsUniform G ε (cluster f i) (cluster f j) ∧
        ρ+ε ≤ density G (cluster f i) (cluster f j)) →
      ∃ (k : ℕ) (Z₀ : Finset V) (P : Fin k → Finset V) (R₀ : Digraph (Fin k)),
        N ≤ k ∧ k = (Fintype.card I/b)*b ∧ b ∣ k ∧
        (∀ i, (P i).card = ℓ*(m/ℓ)) ∧ (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, Disjoint (P i) Z₀) ∧ (∀ x, x ∉ Z₀ → x ∈ univ.biUnion P) ∧
        Z₀.card = (exceptional f).card+m*(Fintype.card I%b)+(m%ℓ)*k ∧
        (∀ i, ¬ R₀.Adj i i) ∧ (∀ i, R₀.Adj i (finRotate k i)) ∧
        IsRealRobust R₀ (ν/2) (2*τ) ∧
        (∀ i, α*(k:ℝ) ≤ (inDegree R₀ i:ℝ)) ∧ (∀ i, α*(k:ℝ) ≤ (outDegree R₀ i:ℝ)) ∧
        ∀ i j, R₀.Adj i j → IsUniform G (2*ε) (P i) (P j) ∧ ρ ≤ density G (P i) (P j) := by
  have hτpos : 0 < τ := hν.trans_le hντ
  have hτHalf : τ ≤ 1/2 := by linarith only [hτα,hα]
  have hαpos : 0 ≤ α := by linarith only [hτα,hτpos]
  obtain ⟨N,hN⟩ := exists_kuhn_osthus_ordered_reduced_cycle.{v} (ν/2) (2*τ) α
    (by linarith only [hν]) (by linarith only [hντ,hτpos]) hτα hα
  refine ⟨N,?_⟩
  intro V I _ _ G D f b ℓ m d ε ρ hb hℓ hRoom hLarge hSize hε hε₁ hRob hLoop hBudgetν hBudgetτ
    hBudgetDegree hDeg hPairs
  obtain ⟨B,g,hB,hDiv,hG,hExc,hRobB,hDegreeB,hPairsB⟩ :=
    kuhn_osthus_coarse_partition_for_refinement G D f b ℓ m d ν τ ε ρ hb hℓ hRoom hSize
      hν.le hν₁ hτpos.le hτHalf hε hε₁ hRob hBudgetν hBudgetτ hDeg hPairs
  let k := Fintype.card B
  have hkB : k = B.card := Fintype.card_coe B
  have hkI : k ≤ Fintype.card I := hkB ▸ card_le_univ B
  have hRem : Fintype.card I%b ≤ b-1 := Nat.le_pred_of_lt (Nat.mod_lt _ hb)
  have hOrder : Fintype.card I%b+k = Fintype.card I := by
    rw [hkB,hB,Nat.mul_comm (Fintype.card I/b)]
    exact Nat.mod_add_div _ _
  have hNk : N ≤ k := by omega
  have hRemR : ((Fintype.card I%b:ℕ):ℝ) ≤ ((b-1:ℕ):ℝ) := by exact_mod_cast hRem
  have hDrop : Fintype.card I%b ≤ d := by
    have h := mul_nonneg hαpos (Nat.cast_nonneg (Fintype.card I))
    exact_mod_cast (show ((Fintype.card I%b:ℕ):ℝ) ≤ (d:ℝ) by linarith only [h,hRemR,hBudgetDegree])
  have hBase : α*(k:ℝ) ≤ ((d-Fintype.card I%b:ℕ):ℝ) := by
    rw [Nat.cast_sub hDrop]
    have hK : (k:ℝ) ≤ Fintype.card I := by exact_mod_cast hkI
    linarith only [hRemR,hBudgetDegree,mul_le_mul_of_nonneg_left hK hαpos]
  obtain ⟨e,hCycle,hR,hSemidegree⟩ := hN (induced D B) hNk hRobB
    (fun i => hBase.trans (by exact_mod_cast (hDegreeB i).1))
    (fun i => hBase.trans (by exact_mod_cast (hDegreeB i).2))
  let P (i : Fin k) := cluster g (e i)
  let R₀ := fibrePullback (induced D B) e e
  refine ⟨k,exceptional g,P,R₀,hNk,hkB.trans hB,hkB ▸ hDiv,(fun i => (hG (e i)).2),
    (fun _ _ h => clusters_disjoint g (e.injective.ne h)),?_,?_,?_,(fun i => hLoop (e i).val),hCycle,hR,?_,?_,?_⟩
  · intro i
    refine disjoint_left.mpr (fun x hx hg => ?_)
    have h : (none : Option B) = some (e i) :=
      ((mem_exceptional g x).mp hg).symm.trans ((mem_cluster g (e i) x).mp hx)
    cases h
  · intro x hx
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp (fun h => hx ((mem_exceptional g x).mpr h))
    obtain ⟨j,rfl⟩ := e.surjective i
    exact mem_biUnion.mpr ⟨j,mem_univ _,(mem_cluster g (e j) x).mpr hi⟩
  · rw [hExc,hkB]
  · intro i
    rw [(hSemidegree i).1]
    exact hBase.trans (by exact_mod_cast (hDegreeB (e i)).1)
  · intro i
    rw [(hSemidegree i).2]
    exact hBase.trans (by exact_mod_cast (hDegreeB (e i)).2)
  · intro i j h
    exact hPairsB (e i) (e j) h

end OverfullWork.DirectedRobustExpansion
