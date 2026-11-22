module

public import OverfullWork.EquitableRecolouring

@[expose] public section


/-! # Aligning two equitable palettes by a proved permutation -/

namespace OverfullWork.PaletteAlignment

open Finset
open scoped Classical

theorem equitable_vectors_permutation {I : Type*} [Fintype I] [DecidableEq I]
    (f g : I → ℕ) (hf : ∀ i j, f i≤f j+1) (hg : ∀ i j, g i≤g j+1)
    (hsum : (∑ i,f i)=∑ i,g i) : ∃ σ : Equiv.Perm I, ∀ i, f i=g (σ i) := by
  cases isEmpty_or_nonempty I with
  | inl he =>
    letI := he
    exact ⟨Equiv.refl _,fun i => isEmptyElim i⟩
  | inr hn =>
    letI := hn
    obtain ⟨i,_,hi⟩ := exists_min_image (univ : Finset I) f univ_nonempty
    obtain ⟨j,_,hj⟩ := exists_min_image (univ : Finset I) g univ_nonempty
    have hmin : f i=g j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt|hgt
      · have hle : ∀ z, f z≤g z := fun z => by have h₁:=hf z i; have h₂:=hj z (mem_univ z); omega
        have hstrict : f i<g i := by have h:=hj i (mem_univ i); omega
        have h := sum_lt_sum (fun z _ => hle z) ⟨i,mem_univ i,hstrict⟩
        omega
      · have hle : ∀ z, g z≤f z := fun z => by have h₁:=hg z j; have h₂:=hi z (mem_univ z); omega
        have hstrict : g j<f j := by have h:=hi j (mem_univ j); omega
        have h := sum_lt_sum (fun z _ => hle z) ⟨j,mem_univ j,hstrict⟩
        omega
    let q := f i
    have hfq : ∀ z, q≤f z ∧ f z≤q+1 := fun z => ⟨hi z (mem_univ z),hf z i⟩
    have hgq : ∀ z, q≤g z ∧ g z≤q+1 := by
      intro z
      dsimp [q]
      rw [hmin]
      exact ⟨hj z (mem_univ z),hg z j⟩
    let A := univ.filter (fun z => f z=q+1)
    let B := univ.filter (fun z => g z=q+1)
    have hledger (h : I → ℕ) (hh : ∀ z, q≤h z ∧ h z≤q+1) :
        (∑ z,h z)=Fintype.card I*q+(univ.filter (fun z => h z=q+1)).card := by
      calc
        _ = ∑ z, (q + if h z=q+1 then 1 else 0) := by
          apply sum_congr rfl
          intro z _
          have h:=hh z
          split_ifs <;> omega
        _ = _ := by simp [sum_add_distrib,sum_boole]
    have hA:=hledger f hfq
    have hB:=hledger g hgq
    have hcard : A.card=B.card := by dsimp [A,B]; omega
    obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq A B hcard
    refine ⟨σ,fun z => ?_⟩
    have hmem : σ z∈B ↔ z∈A := by rw [←hσ]; simp
    have hm : g (σ z)=q+1 ↔ f z=q+1 := by simpa only [A,B,mem_filter,mem_univ,true_and] using hmem
    have h₁:=hfq z
    have h₂:=hgq (σ z)
    omega

end OverfullWork.PaletteAlignment

namespace SimpleGraph.MultiGraph.EdgeColoring

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M N : MultiGraph V} {k : ℕ}

def relabel (C : M.EdgeColoring k) (σ : Equiv.Perm (Fin k)) : M.EdgeColoring k where
  col e i := C.col e (σ i)
  sum_col e := (Fintype.sum_equiv σ _ _ (fun _ => rfl)).trans (C.sum_col e)
  proper v i := C.proper v (σ i)

theorem colourMass_relabel (C : M.EdgeColoring k) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (C.relabel σ).colourMass i=C.colourMass (σ i) := rfl

theorem sum_colourMass (C : M.EdgeColoring k) : (∑ i,C.colourMass i)=M.edgeCount := by
  simp only [colourMass,colourGraph,edgeCount]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  exact C.sum_col e

/-- Both equitable colourings and the aligning permutation are constructed
from arbitrary proper colourings with equal total edge count. -/
theorem exists_aligned_equitable_pair (C : M.EdgeColoring k) (B : N.EdgeColoring k)
    (he : M.edgeCount=N.edgeCount) :
    ∃ (C' : M.EdgeColoring k) (B' : N.EdgeColoring k),
      C'.IsEquitable ∧ B'.IsEquitable ∧ ∀ i, C'.colourMass i=B'.colourMass i := by
  obtain ⟨C',hC⟩:=C.exists_equitable
  obtain ⟨B',hB⟩:=B.exists_equitable
  have hs : (∑ i,C'.colourMass i)=∑ i,B'.colourMass i := by rw [sum_colourMass,sum_colourMass,he]
  obtain ⟨σ,hσ⟩ := OverfullWork.PaletteAlignment.equitable_vectors_permutation
    C'.colourMass B'.colourMass hC hB hs
  refine ⟨C',B'.relabel σ,hC,?_,?_⟩
  · intro i j
    exact hB (σ i) (σ j)
  · exact hσ

end SimpleGraph.MultiGraph.EdgeColoring
