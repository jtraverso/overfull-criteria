module

public import OverfullWork.CMSCaseTwoInitialCopies
public import OverfullWork.CanonicalTriangleComponent

@[expose] public section


/-! Lemma 4.1 of Chen–McDonald–Shan for the constructed canonical
completion, with explicit integer allowances for the two row errors. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph CanonicalPairTriangle
open scoped Classical

variable {m Δ : ℕ} {D : MultiGraph (Fin (m+1) × Bool)}

private theorem weighted_pair_mult_ge {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (e : (Fin k × Bool) ↪ V) (f : Fin k → ℕ) (i : Fin k) :
    f i ≤ (weightedPairs e f).mult s(e (i,false),e (i,true)) := by
  have hh := single_le_sum
    (s := (univ : Finset (Fin k)))
    (f := fun j => (copiesOn (e (j,false)) (e (j,true))
      (fun h => by have hb := congrArg Prod.snd (e.injective h); cases hb) (f j)).mult
        s(e (i,false),e (i,true)))
    (fun _ _ => Nat.zero_le _) (mem_univ i)
  simpa only [weightedPairs,sumCopies,copiesOn,scaledCopies,MultiGraph.unitEdge,if_pos rfl,if_true,Nat.mul_one]
    using hh

theorem Completion.first_bundle_lower (C : Completion D Δ) :
    Δ-D.degree (0,true)-C.q ≤ C.N.mult s((0,false),(0,true)) := by
  let i : Fin C.k := ⟨0,C.positive⟩
  let e := prefixEmbedding C.cut_le
  have hI : pairResidue D Δ C.cut_le i = Δ-D.degree (0,true) := rfl
  by_cases hFull : C.k = m+1
  · rw [C.canonical_N.1 hFull,C.paired_q_zero hFull,Nat.sub_zero]
    exact hI ▸ weighted_pair_mult_ge e (pairResidue D Δ C.cut_le) i
  · have hkm : C.k < m+1 := by have hh := C.cut_le; omega
    obtain ⟨hw,hN⟩ := C.canonical_N.2 hkm
    rw [hN]
    let j : Fin C.k := ⟨C.k-1,by have hh := C.positive; omega⟩
    let f := fun z : Fin C.k => pairResidue D Δ C.cut_le z-(if z=j then C.q else 0)
    have hh := weighted_pair_mult_ge e f i
    have hSub : Δ-D.degree (0,true)-C.q ≤ f i := by
      dsimp only [f]
      rw [hI]
      split_ifs <;> omega
    exact (hSub.trans hh).trans (by
      change (weightedPairs e f).mult s((0,false),(0,true)) ≤
        (weightedPairs e f).mult s((0,false),(0,true))+_
      omega)

/-- A first pair outside the final triangle receives the full
second-vertex deficit. -/
theorem Completion.first_bundle_lower_of_prefix_two (C : Completion D Δ) (hK : 2 ≤ C.k) :
    Δ-D.degree (0,true) ≤ C.N.mult s((0,false),(0,true)) := by
  let i : Fin C.k := ⟨0,C.positive⟩
  let e := prefixEmbedding C.cut_le
  have hI : pairResidue D Δ C.cut_le i = Δ-D.degree (0,true) := rfl
  by_cases hFull : C.k = m+1
  · rw [C.canonical_N.1 hFull]
    exact hI ▸ weighted_pair_mult_ge e (pairResidue D Δ C.cut_le) i
  · have hkm : C.k < m+1 := by have hh := C.cut_le; omega
    obtain ⟨hw,hN⟩ := C.canonical_N.2 hkm
    rw [hN]
    let j : Fin C.k := ⟨C.k-1,by have hh := C.positive; omega⟩
    let f := fun z : Fin C.k => pairResidue D Δ C.cut_le z-(if z=j then C.q else 0)
    have hne : i ≠ j := by
      intro h
      have hh := congrArg Fin.val h
      change 0 = C.k-1 at hh
      omega
    have hh := weighted_pair_mult_ge e f i
    have hf : f i = Δ-D.degree (0,true) := by simp only [f,hI,if_neg hne,Nat.sub_zero]
    rw [hf] at hh
    exact hh.trans (by
      change (weightedPairs e f).mult s((0,false),(0,true)) ≤
        (weightedPairs e f).mult s((0,false),(0,true))+_
      omega)

set_option maxHeartbeats 1400000 in
theorem Completion.bundle_comparison_of_support (C : Completion D Δ) (E Y : ℕ)
    (hOrder : ∀ v, v ≠ (0,false) → D.degree (0,true) ≤ D.degree v)
    (hBase : ∀ v, v ≠ (0,false) → v ≠ (0,true) → D.mult s((0,false),v) ≤ Y) :
    let M := (D.addCopies C.L).addCopies C.N
    (∀ v, v ≠ (0,false) → Δ ≤ M.supportGraph.degree v+M.mult s((0,false),v)+E) →
    ∀ v, v ≠ (0,false) →
      M.mult s((0,false),v) ≤ M.mult s((0,false),(0,true))+(E+Y+2) := by
  intro M hProfile v hva
  by_cases hvb : v = (0,true)
  · subst v
    omega
  have hq : C.q ≤ E+2 := by
    by_cases hFull : C.k = m+1
    · rw [C.paired_q_zero hFull]; omega
    have hkm : C.k < m+1 := by have hh := C.cut_le; omega
    let x := C.middleVertex hkm
    let y := C.lastTrue
    have hxa : x ≠ (0,false) := by
      intro h
      have hh := congrArg (fun u : Fin (m+1) × Bool => u.1.val) h
      change C.k = 0 at hh
      have hc := C.positive
      omega
    have hya : y ≠ (0,false) := by
      intro h
      have hh := congrArg Prod.snd h
      cases hh
    have hEx := CMSBalancedCut.off_centre_excess_le_of_support_degree M (0,false) x Δ E
      C.regular (hProfile x hxa)
    have hOne : M.mult s(x,y)-1 ≤ ∑ z ∈ (univ : Finset (Fin (m+1) × Bool)).erase (0,false),
        (M.mult s(x,z)-1) :=
      single_le_sum (f := fun z => M.mult s(x,z)-1) (fun _ _ => Nat.zero_le _)
        (mem_erase.mpr ⟨hya,mem_univ y⟩)
    have hMid : C.N.mult s(x,y) = C.q := C.N_middle_bundle hkm y (Or.inr rfl)
    have hN : C.N.mult s(x,y) ≤ M.mult s(x,y) := by
      change C.N.mult s(x,y) ≤ D.mult s(x,y)+C.L.mult s(x,y)+C.N.mult s(x,y)
      omega
    omega
  have hBase' := hBase v hva hvb
  have hOrder' := hOrder v hva
  have hDay := C.regular v
  rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hDay
  have hL := C.L.mult_pair_le_degree v (0,false)
  have hN := C.N.mult_pair_le_degree v (0,false)
  rw [Sym2.eq_swap] at hL hN
  have hFirst := C.first_bundle_lower
  change D.mult s((0,false),v)+C.L.mult s((0,false),v)+C.N.mult s((0,false),v) ≤
    D.mult s((0,false),(0,true))+C.L.mult s((0,false),(0,true))+C.N.mult s((0,false),(0,true))+(E+Y+2)
  omega

end OverfullWork.CanonicalRegularization
