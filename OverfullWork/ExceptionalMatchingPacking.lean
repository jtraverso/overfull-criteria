module

public import OverfullWork.HamiltonThroughMatching

@[expose] public section


/-! Cover scheduled exceptional matchings by pairwise arc-disjoint
Hamilton cycles, preserving the arcs of matchings still to be used. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u}

structure DirectedMatching (V : Type u) where
  size : ℕ
  target : Fin size → V
  source : Fin size → V
  target_inj : Function.Injective target
  source_inj : Function.Injective source
  separate : ∀ i j, target i ≠ source j

def DirectedMatching.toDigraph (M : DirectedMatching V) : Digraph V :=
  ⟨fun v w => ∃ i, M.source i = v ∧ M.target i = w⟩

def futureMatchings {k : ℕ} (M : Fin k → DirectedMatching V) (t : ℕ) : Digraph V :=
  ⟨fun v w => ∃ j : Fin k, t ≤ j.val ∧ (M j).toDigraph.Adj v w⟩

private theorem union_filter_bound [Fintype V] {k : ℕ} (P : Fin k → V → Prop) (T : Finset V)
    (hP : ∀ v ∈ T, ∃ i, P i v) (hUnique : ∀ i v w, P i v → P i w → v = w) :
    T.card ≤ k := by
  let A := fun i => (univ : Finset V).filter (P i)
  have hSub : T ⊆ (univ : Finset (Fin k)).biUnion A := by
    intro v hv
    obtain ⟨i,hi⟩ := hP v hv
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  calc
    _ ≤ ((univ : Finset (Fin k)).biUnion A).card := card_le_card hSub
    _ ≤ ∑ i,(A i).card := card_biUnion_le
    _ ≤ ∑ _ : Fin k,1 := by
      apply sum_le_sum
      intro i _
      exact card_le_one.mpr (fun v hv w hw => hUnique i v w (mem_filter.mp hv).2 (mem_filter.mp hw).2)
    _ = _ := by simp

theorem futureMatchings_semidegrees [Fintype V] {k : ℕ} (M : Fin k → DirectedMatching V)
    (t : ℕ) (v : V) :
    inDegree (futureMatchings M t) v ≤ k ∧ outDegree (futureMatchings M t) v ≤ k := by
  constructor
  · let F := fun w => (futureMatchings M t).Adj w v
    change (@Finset.filter V F (Classical.decPred _) univ).card ≤ k
    letI : DecidablePred F := Classical.decPred _
    apply union_filter_bound (fun i w => t ≤ i.val ∧ (M i).toDigraph.Adj w v)
    · exact fun _ h => (mem_filter.mp h).2
    · rintro i a b ⟨_,j,hja,hjv⟩ ⟨_,l,hlb,hlv⟩
      have he := (M i).target_inj (hjv.trans hlv.symm)
      cases he
      exact hja.symm.trans hlb
  · let F := fun w => (futureMatchings M t).Adj v w
    change (@Finset.filter V F (Classical.decPred _) univ).card ≤ k
    letI : DecidablePred F := Classical.decPred _
    apply union_filter_bound (fun i w => t ≤ i.val ∧ (M i).toDigraph.Adj v w)
    · exact fun _ h => (mem_filter.mp h).2
    · rintro i a b ⟨_,j,hjv,hja⟩ ⟨_,l,hlv,hlb⟩
      have he := (M i).source_inj (hjv.trans hlv.symm)
      cases he
      exact hja.symm.trans hlb

/-- The covering stage of Kühn–Osthus Lemma 11.1, given the matching classes.
The bound includes the arcs of later matchings as well as spent cycles. -/
theorem exists_hamilton_pack_covering_matchings (ν τ α : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hντ : ν ≤ τ) (hτα : 128*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D : Digraph W) {k : ℕ}
      (M : Fin k → DirectedMatching W), N ≤ Fintype.card W →
      IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (outDegree D v:ℝ)) →
      2*(k:ℝ) ≤ ν*(Fintype.card W:ℝ)/2 →
      (∀ j, ((M j).size:ℝ) ≤ (ν/2)^4*(Fintype.card W:ℝ)) →
      (∀ j, (M j).toDigraph ≤ D) →
      (∀ i j, i ≠ j → ∀ v w, ¬((M i).toDigraph.Adj v w ∧ (M j).toDigraph.Adj v w)) →
      ∃ σ : Fin k → Equiv.Perm W,
        (∀ j v,D.Adj v (σ j v)) ∧ (∀ j,HasSpanningCycle (fun x y => σ j x = y)) ∧
        (∀ i j, i ≠ j → ∀ v, σ i v ≠ σ j v) ∧
        ∀ j i, σ j ((M j).source i) = (M j).target i := by
  obtain ⟨N,hN⟩ := exists_hamilton_through_matching.{u} (ν/2) τ (α/2)
    (by positivity) (by linarith only [hν1]) (by linarith only [hν,hντ])
    (by linarith only [hτα]) (by linarith only [hα])
  refine ⟨N,?_⟩
  intro W _ D k M hn hD hIn hOut hK hSize hLe hMDis
  have hInd (t : ℕ) (ht : t ≤ k) :
      ∃ σ : Fin t → Equiv.Perm W,
        (∀ j v,D.Adj v (σ j v)) ∧ (∀ j,HasSpanningCycle (fun x y => σ j x = y)) ∧
        (∀ i j, i ≠ j → ∀ v, σ i v ≠ σ j v) ∧
        (∀ (j : Fin t) (i : Fin ((M (j.castLE ht)).size)),
          σ j ((M (j.castLE ht)).source i) = (M (j.castLE ht)).target i) ∧
        ∀ j v, ¬(futureMatchings M t).Adj v (σ j v) := by
    induction t with
    | zero => exact ⟨Fin.elim0,fun j => j.elim0,fun j => j.elim0,fun j => j.elim0,
        fun j => j.elim0,fun j => j.elim0⟩
    | succ t ih =>
      obtain ⟨σ,hσ,hCycle,hDis,hReq,hAvoid⟩ := ih (Nat.le_of_succ_le ht)
      let j : Fin k := ⟨t,by omega⟩
      let U := matchingUnion σ
      let F := futureMatchings M (t+1)
      let H := U ⊔ F
      have hU : U ≤ D := by rintro v w ⟨i,rfl⟩; exact hσ i v
      have hF : F ≤ D := by rintro v w ⟨i,_,h⟩; exact hLe i h
      have hFDis (v w : W) : ¬(U.Adj v w ∧ F.Adj v w) := by
        rintro ⟨⟨i,rfl⟩,⟨l,hl,h⟩⟩
        exact hAvoid i v ⟨l,by omega,h⟩
      have hHU : H ≤ D := sup_le hU hF
      have hLost (v : W) : inDegree H v ≤ 2*k ∧ outDegree H v ≤ 2*k := by
        obtain ⟨hi,ho⟩ := matchingUnion_semidegrees σ v
        obtain ⟨hfi,hfo⟩ := futureMatchings_semidegrees M (t+1) v
        obtain ⟨heO,heI⟩ := degrees_sup_of_disjoint U F hFDis v
        change inDegree (U ⊔ F) v ≤ 2*k ∧ outDegree (U ⊔ F) v ≤ 2*k
        rw [heI,heO]
        change inDegree U v ≤ t at hi
        change outDegree U v ≤ t at ho
        change inDegree F v ≤ k at hfi
        change outDegree F v ≤ k at hfo
        omega
      have hBudget : (ν/2)*(Fintype.card W:ℝ)+((2*k:ℕ):ℝ) ≤ ν*(Fintype.card W:ℝ) := by
        push_cast
        linarith only [hK]
      have hR := DirectedSpanningConfiguration.real_robust_after_reserve_use D H ν τ (ν/2) (2*k)
        hν.le (hν.le.trans hντ) hD (fun v => (hLost v).1) hBudget
      have hαn : (ν/2)*(Fintype.card W:ℝ) ≤ (α/2)*(Fintype.card W:ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hν,hντ,hτα]) (Nat.cast_nonneg _)
      have hi (v : W) : (α/2)*(Fintype.card W:ℝ) ≤ (inDegree (D \ H) v:ℝ) := by
        have hPay : (inDegree (D \ H) v:ℝ)+(inDegree H v:ℝ) = (inDegree D v:ℝ) := by
          exact_mod_cast (residual_semidegrees D H hHU v).1
        have hLoss : (inDegree H v:ℝ) ≤ 2*(k:ℝ) := by exact_mod_cast (hLost v).1
        linarith only [hPay,hLoss,hK,hαn,hIn v]
      have ho (v : W) : (α/2)*(Fintype.card W:ℝ) ≤ (outDegree (D \ H) v:ℝ) := by
        have hPay : (outDegree (D \ H) v:ℝ)+(outDegree H v:ℝ) = (outDegree D v:ℝ) := by
          exact_mod_cast (residual_semidegrees D H hHU v).2
        have hLoss : (outDegree H v:ℝ) ≤ 2*(k:ℝ) := by exact_mod_cast (hLost v).2
        linarith only [hPay,hLoss,hK,hαn,hOut v]
      have hAvail (l : Fin ((M j).size)) : (D \ H).Adj ((M j).source l) ((M j).target l) := by
        have hm : (M j).toDigraph.Adj ((M j).source l) ((M j).target l) := ⟨l,rfl,rfl⟩
        refine ⟨hLe j hm,?_⟩
        rintro (⟨i,he⟩ | ⟨i,hi,he⟩)
        · exact hAvoid i _ ⟨j,le_rfl,by rw [he]; exact hm⟩
        · exact hMDis j i (fun he => by have := congrArg Fin.val he; dsimp [j] at this; omega) _ _ ⟨hm,he⟩
      obtain ⟨ρ,hρ,hForce,hC⟩ := hN (D \ H) hn hR hi ho (M j).size (hSize j)
        (M j).target (M j).source (M j).target_inj (M j).source_inj (M j).separate hAvail
      refine ⟨Fin.snoc σ ρ,?_,?_,?_,?_,?_⟩
      · intro i
        refine Fin.lastCases (by simpa using fun v => (hρ v).1) (fun l => by simpa using hσ l) i
      · intro i
        refine Fin.lastCases (by simpa using hC) (fun l => by simpa using hCycle l) i
      · intro a b
        refine Fin.lastCases ?_ (fun a => ?_) a
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun l _ v h => ?_) b
          exact (hρ v).2 (Or.inl ⟨l,by simpa using h.symm⟩)
        · refine Fin.lastCases (fun _ v h => ?_) (fun l h v => ?_) b
          · exact (hρ v).2 (Or.inl ⟨a,by simpa using h⟩)
          · simpa using hDis a l (fun he => h (congrArg Fin.castSucc he)) v
      · intro i
        refine Fin.lastCases ?_ (fun l => ?_) i
        · change ∀ i : Fin ((M j).size),
            (@Fin.snoc t (fun _ => Equiv.Perm W) σ ρ) (Fin.last t) ((M j).source i) = (M j).target i
          simpa only [Fin.snoc_last] using hForce
        · simpa using hReq l
      · intro i
        refine Fin.lastCases ?_ (fun l => ?_) i
        · intro v h
          exact (hρ v).2 (Or.inr (by simpa using h))
        · intro v h
          obtain ⟨a,ha,he⟩ := h
          exact hAvoid l v ⟨a,by omega,by simpa using he⟩
  obtain ⟨σ,hσ,hC,hDis,hReq,_⟩ := hInd k le_rfl
  exact ⟨σ,hσ,hC,hDis,hReq⟩

end OverfullWork.DirectedRobustExpansion
