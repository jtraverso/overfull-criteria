module

public import OverfullWork.MergeReserveReindex
public import Mathlib.GroupTheory.Perm.List

@[expose] public section


/-! The matching budget in Osthus–Staden Claim 5.7. Each matching
uses one arc per endpoint, and subsequent contractions can use arbitrary
bijections of the surviving reserve's endpoints. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u}

theorem exists_spanning_successor {R : V → V → Prop} (h : HasSpanningCycle R) :
    ∃ σ : Equiv.Perm V, (∀ v,R v (σ v)) ∧ HasSpanningCycle (fun v w => σ v = w) := by
  classical
  obtain ⟨T,x,hND,hAll,hHead,hChain⟩ := h
  cases T with
  | nil => simp at hHead
  | cons a L =>
    have hEq : a = x := by simpa using hHead
    subst x
    let T := a :: L
    have hStep (i : ℕ) (hi : i+1 < (T++[a]).length) :
        T.formPerm (T++[a])[i] = (T++[a])[i+1] := by
      have hi' : i < T.length := by simp only [List.length_append,List.length_singleton] at hi; omega
      rw [List.getElem_append_left hi']
      by_cases hlt : i+1 < T.length
      · rw [List.getElem_append_left hlt, List.formPerm_apply_lt_getElem _ hND _ hlt]
      · have he : i+1 = T.length := by omega
        rw [List.getElem_append_right (by omega)]
        have hDiff : i+1-T.length = 0 := by omega
        have hiL : i = L.length := by simp [T] at he; omega
        subst i
        rw [List.formPerm_apply_getElem_length]
        simp
    refine ⟨T.formPerm,?_,T,a,hND,hAll,hHead,List.isChain_iff_getElem.mpr hStep⟩
    intro v
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp (hAll v)
    have hh : i+1 < (T++[a]).length := by
      change i < T.length at hi
      simp only [List.length_append,List.length_singleton]
      omega
    have hEdge := (List.isChain_iff_getElem.mp hChain) i hh
    change R (T++[a])[i] (T++[a])[i+1] at hEdge
    rw [←hStep i hh,List.getElem_append_left hi] at hEdge
    exact hEdge

def matchingUnion {t : ℕ} (M : Fin t → Equiv.Perm V) : Digraph V :=
  ⟨fun v w => ∃ j, M j v = w⟩

theorem matchingUnion_semidegrees [Fintype V] {t : ℕ} (M : Fin t → Equiv.Perm V) (v : V) :
    inDegree (matchingUnion M) v ≤ t ∧ outDegree (matchingUnion M) v ≤ t := by
  have hSize (g : Fin t → V) : ((univ : Finset (Fin t)).image g).card ≤ t :=
    (card_image_le (f := g)).trans_eq (by simp)
  constructor
  · apply le_trans (b := ((univ : Finset (Fin t)).image (fun i => (M i).symm v)).card) _ (hSize _)
    apply card_le_card
    intro w hw
    obtain ⟨j,hj⟩ := (mem_filter.mp hw).2
    exact mem_image.mpr ⟨j,mem_univ _,(M j).eq_symm_apply.mpr hj |>.symm⟩
  · apply le_trans (b := ((univ : Finset (Fin t)).image (fun i => M i v)).card) _ (hSize _)
    apply card_le_card
    intro w hw
    obtain ⟨j,hj⟩ := (mem_filter.mp hw).2
    exact mem_image.mpr ⟨j,mem_univ _,hj⟩

/-- At most k consecutive replacements of the same selected pair can be
made. Each supplies a new matching and induces one cycle on the path labels
for the endpoint identification of its own round. -/
theorem exists_disjoint_merge_matchings (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D : Digraph W) (k : ℕ)
      (e : Fin k → Equiv.Perm W), N ≤ Fintype.card W →
      (k:ℝ)+ν*(Fintype.card W:ℝ) ≤ d*τ*(Fintype.card W:ℝ) →
      γ*(Fintype.card W:ℝ)+(k:ℝ) ≤ d*(Fintype.card W:ℝ) →
      (∀ S T : Finset W, ε*(Fintype.card W:ℝ) ≤ (S.card:ℝ) →
        ε*(Fintype.card W:ℝ) ≤ (T.card:ℝ) →
        d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences D S T:ℝ)) →
      (∀ v, d*(Fintype.card W:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, d*(Fintype.card W:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ M : Fin k → Equiv.Perm W, (∀ j v,D.Adj v (M j v)) ∧
        (∀ j, HasSpanningCycle (fun x y => M j (e j x) = y)) ∧
        ∀ i j, i ≠ j → ∀ v, M i v ≠ M j v := by
  obtain ⟨N,hN⟩ := exists_auxiliary_merge_cycle.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ D k e hn hCost hDeg hRect hIn hOut
  have hInd (t : ℕ) (ht : t ≤ k) (f : Fin t → Equiv.Perm W) :
      ∃ M : Fin t → Equiv.Perm W, (∀ j v,D.Adj v (M j v)) ∧
        (∀ j, HasSpanningCycle (fun x y => M j (f j x) = y)) ∧
        ∀ i j, i ≠ j → ∀ v, M i v ≠ M j v := by
    induction t with
    | zero => exact ⟨Fin.elim0,fun j => j.elim0,fun j => j.elim0,fun j => j.elim0⟩
    | succ t ih =>
      obtain ⟨M,hM,hC,hDis⟩ := ih (Nat.le_of_succ_le ht) (fun j => f j.castSucc)
      have hMD : matchingUnion M ≤ D := by
        intro v w h
        obtain ⟨j,rfl⟩ := h
        exact hM j v
      have hBudget : (t:ℝ) ≤ k := by exact_mod_cast (Nat.le_of_succ_le ht)
      have hAux := hN D (matchingUnion M) (f (Fin.last t)) t hn hMD
        (by linarith only [hBudget,hCost]) (by linarith only [hBudget,hDeg])
        hRect hIn hOut (matchingUnion_semidegrees M)
      obtain ⟨σ,hσ,hCycle⟩ := exists_spanning_successor hAux
      let m := (f (Fin.last t)).symm.trans σ
      have hEdge (v : W) : (D \ matchingUnion M).Adj v (m v) := by
        simpa [m,reindexSources] using hσ ((f (Fin.last t)).symm v)
      have hNewCycle : HasSpanningCycle (fun x y => m (f (Fin.last t) x) = y) := by
        simpa [m] using hCycle
      refine ⟨Fin.snoc M m,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using fun v => (hEdge v).1
        · simpa using hM i
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using hNewCycle
        · simpa using hC i
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun j' _ v => ?_) j
          exact fun h => (hEdge v).2 ⟨j',by simpa using h.symm⟩
        · refine Fin.lastCases (fun _ v => ?_) (fun j' h v => ?_) j
          · exact fun h => (hEdge v).2 ⟨i',by simpa using h⟩
          · simpa using hDis i' j' (fun h' => h (congrArg Fin.castSucc h')) v
  obtain ⟨M,hM,hC,hDis⟩ := hInd k le_rfl e
  exact ⟨M,hM,hC,hDis⟩

end OverfullWork.DirectedRobustExpansion
