module

public import OverfullWork.DirectedConfigurationDegrees

@[expose] public section


/-! The outer deletion induction in Kühn–Osthus Lemma 7.6.
Each original exceptional factor has a separate degree budget at
ordinary and exceptional vertices. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedSpanningConfiguration
open scoped Classical
variable {V : Type*} [Fintype V]

/-- A construction valid after all prefix losses yields pairwise
arc-disjoint factors. The deletion subgraph is exactly the union of
the factors chosen at that prefix. -/
theorem exists_disjoint_exceptional_factor_packing (G : Digraph V)
    (Z : Finset V) (r K L : ℕ) (IsFactor : Digraph V → Prop)
    (hPick : ∀ t < r, ∀ H : Digraph V, H ≤ G →
      (∀ v, inDegree H v ≤ t*(if v ∈ Z then K*L else 1) ∧
        outDegree H v ≤ t*(if v ∈ Z then K*L else 1)) →
      ∃ F : Digraph V, F ≤ G \ H ∧ IsFactor F ∧
        ∀ v, inDegree F v ≤ (if v ∈ Z then K*L else 1) ∧
          outDegree F v ≤ (if v ∈ Z then K*L else 1)) :
    ∃ F : Fin r → Digraph V, (∀ i, F i ≤ G ∧ IsFactor (F i)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      ∀ v, inDegree (⨆ i, F i) v ≤ r*(if v ∈ Z then K*L else 1) ∧
        outDegree (⨆ i, F i) v ≤ r*(if v ∈ Z then K*L else 1) := by
  classical
  let b (v : V) := if v ∈ Z then K*L else 1
  have hLoss {t : ℕ} (F : Fin t → Digraph V)
      (hDis : Pairwise (fun i j => Disjoint (F i) (F j)))
      (hDegree : ∀ i v, inDegree (F i) v ≤ b v ∧ outDegree (F i) v ≤ b v) (v : V) :
      inDegree (⨆ i, F i) v ≤ t*b v ∧ outDegree (⨆ i, F i) v ≤ t*b v := by
    rw [inDegree_iSup_of_disjoint F hDis,outDegree_iSup_of_disjoint F hDis]
    have h₁ := sum_le_sum (s := (univ : Finset (Fin t))) (fun i _ => (hDegree i v).1)
    have h₂ := sum_le_sum (s := (univ : Finset (Fin t))) (fun i _ => (hDegree i v).2)
    simpa only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] using And.intro h₁ h₂
  have hPrefix (t : ℕ) (ht : t ≤ r) :
      ∃ F : Fin t → Digraph V, (∀ i, F i ≤ G ∧ IsFactor (F i)) ∧
        Pairwise (fun i j => Disjoint (F i) (F j)) ∧
        ∀ i v, inDegree (F i) v ≤ b v ∧ outDegree (F i) v ≤ b v := by
    induction t with
    | zero => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
    | succ t ih =>
      obtain ⟨F,hF,hDis,hDeg⟩ := ih (Nat.le_of_succ_le ht)
      let H := ⨆ i, F i
      have hHG : H ≤ G := iSup_le (fun i => (hF i).1)
      obtain ⟨E,hEH,hE,hEDeg⟩ := hPick t (by omega) H hHG (hLoss F hDis hDeg)
      have hEG : E ≤ G := hEH.trans (fun _ _ h => h.1)
      have hFresh (i : Fin t) : Disjoint (F i) E := by
        rw [disjoint_iff_inf_le]
        intro x y h
        exact (hEH h.2).2 (Digraph.iSup_adj.mpr ⟨i,h.1⟩)
      refine ⟨Fin.snoc F E,?_,?_,?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using And.intro hEG hE
        · simpa only [Fin.snoc_castSucc] using hF j
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · refine Fin.lastCases (fun h => (h rfl).elim) (fun j' _ => ?_) j
          simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hFresh j').symm
        · refine Fin.lastCases (fun _ => ?_) (fun j' h => ?_) j
          · simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hFresh i'
          · simpa only [Fin.snoc_castSucc] using hDis (fun h' => h (congrArg Fin.castSucc h'))
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hEDeg
        · simpa only [Fin.snoc_castSucc] using hDeg j
  obtain ⟨F,hF,hDis,hDeg⟩ := hPrefix r le_rfl
  exact ⟨F,hF,hDis,hLoss F hDis hDeg⟩

end OverfullWork.DirectedRobustExpansion
