module

public import OverfullWork.TouchedFactorPaths
public import OverfullWork.MergeReservePacking

@[expose] public section


/-! Replace one selected perfect matching in a factor. The selected
pair must meet each orbit of the factor. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset DirectedAbsorbingLadder
open scoped Classical
universe u

def replaceCutMatching {V : Type u} (σ : Equiv.Perm V) (S : Finset V)
    (M : Equiv.Perm (↑S)) : Digraph V :=
  cutFactor σ S ⊔ ⟨fun x y => ∃ a : S, x = a.val ∧ y = σ (M a).val⟩

noncomputable def replacedSuccessor {V : Type u} (σ : Equiv.Perm V) (S : Finset V)
    (M : Equiv.Perm (↑S)) : Equiv.Perm V :=
  (Equiv.Perm.ofSubtype M).trans σ

theorem replaceCutMatching_adj_iff {V : Type u} (σ : Equiv.Perm V) (S : Finset V)
    (M : Equiv.Perm (↑S)) (x y : V) :
    (replaceCutMatching σ S M).Adj x y ↔ replacedSuccessor σ S M x = y := by
  change (x ∉ S ∧ σ x = y) ∨ (∃ a : S, x = a.val ∧ y = σ (M a).val) ↔ _
  by_cases hx : x ∈ S
  · rw [replacedSuccessor,Equiv.trans_apply,Equiv.Perm.ofSubtype_apply_of_mem M hx]
    constructor
    · rintro (h | ⟨a,ha,hy⟩)
      · exact (h.1 hx).elim
      · have he : a = ⟨x,hx⟩ := Subtype.ext ha.symm
        simpa only [he] using hy.symm
    · exact fun h => Or.inr ⟨⟨x,hx⟩,rfl,h.symm⟩
  · rw [replacedSuccessor,Equiv.trans_apply,Equiv.Perm.ofSubtype_apply_of_not_mem M hx]
    constructor
    · rintro (h | ⟨a,ha,_⟩)
      · exact h.2
      · exact (hx (ha.symm ▸ a.prop)).elim
    · exact fun h => Or.inl ⟨hx,h⟩

theorem replacement_cycle_of_path_order (σ : Equiv.Perm V) (S : Finset V)
    (P : S → PathRequest (cutFactor σ S)) (e M : Equiv.Perm (↑S))
    (hEnds : ∀ i, (P i).target = i.val ∧ (P i).source = σ (e i).val)
    (hDis : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices)
    (hCover : ∀ v, (∃ i, v ∈ (P i).vertices) ↔ touchesCut σ S v)
    (hCycle : HasSpanningCycle (fun i j => M (e.symm i) = j)) :
    ∃ T : List V, ∃ z : V, T.Nodup ∧ T.head? = some z ∧
      (T ++ [z]).IsChain (replaceCutMatching σ S M).Adj ∧
      ∀ v, v ∈ T ↔ touchesCut σ S v := by
  let K := replaceCutMatching σ S M
  let Q (j : S) : PathRequest K :=
    ⟨(P (e.symm j)).source,(P (e.symm j)).target,(P (e.symm j)).tail,
      ⟨(P (e.symm j)).route.1.imp (fun _ _ h => Or.inl h),(P (e.symm j)).route.2⟩,
      (P (e.symm j)).simple⟩
  have hQDis (i j : S) (hne : i ≠ j) : List.Disjoint (Q i).vertices (Q j).vertices :=
    hDis _ _ (fun h => hne (e.symm.injective h))
  have hQCover (v : V) : (∃ i : S, v ∈ (Q i).vertices) ↔ touchesCut σ S v := by
    rw [←hCover v]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨e i,by simpa [Q,PathRequest.vertices] using hi⟩
  obtain ⟨order,z,hND,hAll,hHead,hChain⟩ := hCycle
  have hClosed : HasSpanningCycle (fun i j => K.Adj (Q i).target (Q j).source) := by
    refine ⟨order,z,hND,hAll,hHead,hChain.imp ?_⟩
    intro i j h
    apply Or.inr
    refine ⟨e.symm i,(hEnds _).1,?_⟩
    change (P (e.symm j)).source = σ (M (e.symm i)).val
    rw [(hEnds _).2,e.apply_symm_apply,h]
  obtain ⟨T,z,hND,hHead,hChainT,hMem,_⟩ := expand_auxiliary_merge_cycle K Q hQDis hClosed
  exact ⟨T,z,hND,hHead,hChainT,fun v => (hMem v).trans (hQCover v)⟩

theorem exists_touched_cycle_merge (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (σ : Equiv.Perm V) (S : Finset V)
      (D H : Digraph (↑S)) (k : ℕ), N ≤ S.card → H ≤ D →
      (k:ℝ)+ν*(S.card:ℝ) ≤ d*τ*(S.card:ℝ) →
      γ*(S.card:ℝ)+(k:ℝ) ≤ d*(S.card:ℝ) →
      (∀ A B : Finset (↑S), ε*(S.card:ℝ) ≤ (A.card:ℝ) →
        ε*(S.card:ℝ) ≤ (B.card:ℝ) →
        d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences D A B:ℝ)) →
      (∀ v, d*(S.card:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, d*(S.card:ℝ) ≤ (outDegree D v:ℝ)) →
      (∀ v, inDegree H v ≤ k ∧ outDegree H v ≤ k) →
      ∃ M : Equiv.Perm (↑S), (∀ i, (D \ H).Adj i (M i)) ∧
        ∃ T : List V, ∃ z : V, T.Nodup ∧ T.head? = some z ∧
          (T ++ [z]).IsChain (replaceCutMatching σ S M).Adj ∧
          ∀ v, v ∈ T ↔ touchesCut σ S v := by
  obtain ⟨N,hN⟩ := exists_auxiliary_merge_cycle.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro V _ σ S D H k hn hHD hCost hDegree hRect hIn hOut hLoss
  obtain ⟨P,e,hEnds,hDis,hCover⟩ := exists_cut_paths_on_touched_cycles σ S
  have hAux := hN D H e.symm k (by simpa using hn) hHD (by simpa using hCost)
    (by simpa using hDegree) (by simpa using hRect) (by simpa using hIn) (by simpa using hOut) hLoss
  obtain ⟨g,hg,hCycle⟩ := exists_spanning_successor hAux
  let M := e.trans g
  have hM (i : S) : (D \ H).Adj i (M i) := by
    simpa [reindexSources,M] using hg (e i)
  have hOrder : HasSpanningCycle (fun i j => M (e.symm i) = j) := by
    simpa [M] using hCycle
  exact ⟨M,hM,replacement_cycle_of_path_order σ S P e M hEnds hDis hCover hOrder⟩

theorem exists_single_pair_factor_merge (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (σ : Equiv.Perm V) (S : Finset V)
      (D H : Digraph (↑S)) (k : ℕ), N ≤ S.card → H ≤ D →
      (∀ v, ∃ w ∈ S, σ.SameCycle v w) →
      (k:ℝ)+ν*(S.card:ℝ) ≤ d*τ*(S.card:ℝ) →
      γ*(S.card:ℝ)+(k:ℝ) ≤ d*(S.card:ℝ) →
      (∀ A B : Finset (↑S), ε*(S.card:ℝ) ≤ (A.card:ℝ) →
        ε*(S.card:ℝ) ≤ (B.card:ℝ) →
        d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences D A B:ℝ)) →
      (∀ v, d*(S.card:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, d*(S.card:ℝ) ≤ (outDegree D v:ℝ)) →
      (∀ v, inDegree H v ≤ k ∧ outDegree H v ≤ k) →
      ∃ M : Equiv.Perm (↑S), (∀ i, (D \ H).Adj i (M i)) ∧
        HasSpanningCycle (replaceCutMatching σ S M).Adj := by
  obtain ⟨N,hN⟩ := exists_touched_cycle_merge.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro V _ σ S D H k hn hHD hHit hCost hDegree hRect hIn hOut hLoss
  obtain ⟨M,hM,T,z,hT,hHead,hChain,hSupport⟩ := hN σ S D H k hn hHD
    hCost hDegree hRect hIn hOut hLoss
  exact ⟨M,hM,T,z,hT,fun v => (hSupport v).mpr (hHit v),hHead,hChain⟩

end OverfullWork.DirectedRobustExpansion
