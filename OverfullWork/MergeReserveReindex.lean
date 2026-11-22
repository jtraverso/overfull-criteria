module

public import OverfullWork.SuperregularMergeReserve
public import OverfullWork.RobustHamiltonDecomposition

@[expose] public section


/-! Identifying the initial and terminal vertices of each path is an
independent relabeling of the rows of the reserve's bipartite matrix. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

def reindexSources (D : Digraph V) (e : Equiv.Perm V) : Digraph V :=
  ⟨fun v w => D.Adj (e v) w⟩

theorem reindexSources_incidences (D : Digraph V) (e : Equiv.Perm V) (S T : Finset V) :
    incidences (reindexSources D e) S T = incidences D (S.image e) T := by
  simp only [←Nat.cast_inj (R := ℝ),incidences_eq_sum,reindexSources]
  apply sum_congr rfl
  intro w _
  rw [sum_image (fun _ _ _ _ he => e.injective he)]

private theorem reindexSources_image_univ (e : Equiv.Perm V) : (univ : Finset V).image e = univ := by
  ext v
  exact ⟨fun _ => mem_univ _,fun _ => mem_image.mpr ⟨e.symm v,mem_univ _,e.apply_symm_apply v⟩⟩

theorem reindexSources_semidegrees (D : Digraph V) (e : Equiv.Perm V) (v : V) :
    inDegree (reindexSources D e) v = inDegree D v ∧ outDegree (reindexSources D e) v = outDegree D (e v) := by
  constructor
  · simpa only [incidences_degree,reindexSources_image_univ] using
      reindexSources_incidences D e univ {v}
  · rfl

/-- After any endpoint identification, the surviving reserve supplies
a Hamilton cycle in the auxiliary digraph. -/
theorem exists_auxiliary_merge_cycle (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D H : Digraph W) (e : Equiv.Perm W) (k : ℕ),
      N ≤ Fintype.card W → H ≤ D →
      (k:ℝ)+ν*(Fintype.card W:ℝ) ≤ d*τ*(Fintype.card W:ℝ) →
      γ*(Fintype.card W:ℝ)+(k:ℝ) ≤ d*(Fintype.card W:ℝ) →
      (∀ S T : Finset W, ε*(Fintype.card W:ℝ) ≤ (S.card:ℝ) →
        ε*(Fintype.card W:ℝ) ≤ (T.card:ℝ) →
        d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences D S T:ℝ)) →
      (∀ v, d*(Fintype.card W:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, d*(Fintype.card W:ℝ) ≤ (outDegree D v:ℝ)) →
      (∀ v, inDegree H v ≤ k ∧ outDegree H v ≤ k) →
      HasSpanningCycle (reindexSources (D \ H) e).Adj := by
  have hντ : ν ≤ τ := by linarith only [hWidth,hε]
  obtain ⟨N,hN⟩ := DirectedAbsorbingLadder.exists_hamilton_threshold.{u} ν τ γ hν hντ hτγ hγ
  refine ⟨max N 1,?_⟩
  intro W _ D H e k hn hHD hCost hDeg hRect hIn hOut hRemoved
  have hOrder := (le_max_right N 1).trans hn
  have hResI (v : W) : γ*(Fintype.card W:ℝ) ≤ (inDegree (D \ H) v:ℝ) := by
    have hPay : (inDegree (D \ H) v:ℝ)+(inDegree H v:ℝ) = (inDegree D v:ℝ) := by
      exact_mod_cast (residual_semidegrees D H hHD v).1
    have hL : (inDegree H v:ℝ) ≤ k := by exact_mod_cast (hRemoved v).1
    linarith only [hPay,hL,hIn v,hDeg]
  have hResO (v : W) : γ*(Fintype.card W:ℝ) ≤ (outDegree (D \ H) v:ℝ) := by
    have hPay : (outDegree (D \ H) v:ℝ)+(outDegree H v:ℝ) = (outDegree D v:ℝ) := by
      exact_mod_cast (residual_semidegrees D H hHD v).2
    have hL : (outDegree H v:ℝ) ≤ k := by exact_mod_cast (hRemoved v).2
    linarith only [hPay,hL,hOut v,hDeg]
  let A := reindexSources D e
  let B := reindexSources H e
  have hAB : B ≤ A := fun _ _ h => hHD h
  have hRectA (S T : Finset W) (hs : ε*(Fintype.card W:ℝ) ≤ (S.card:ℝ))
      (ht : ε*(Fintype.card W:ℝ) ≤ (T.card:ℝ)) :
      d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences A S T:ℝ) := by
    simpa only [A,reindexSources_incidences,card_image_of_injective _ e.injective] using
      hRect (S.image e) T (by rwa [card_image_of_injective _ e.injective]) ht
  have hR := real_robust_of_rectangles_after_deletion A B k hAB d ε ν τ hd hε hν.le
    hWidth hCost hOrder hRectA (fun v => by
      simpa only [B,(reindexSources_semidegrees H e v).1] using (hRemoved v).1)
  have hs : reindexSources (D \ H) e = A \ B := by
    ext x y
    rfl
  have h1 := hN (reindexSources (D \ H) e) ((le_max_left _ _).trans hn) (hs ▸ hR)
    (fun v => by rw [(reindexSources_semidegrees (D \ H) e v).1]; exact hResI v)
    (fun v => by rw [(reindexSources_semidegrees (D \ H) e v).2]; exact hResO (e v))
  exact h1

end OverfullWork.DirectedRobustExpansion
