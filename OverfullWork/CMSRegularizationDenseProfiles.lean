module

public import OverfullWork.CMSRegularizationSimpleSecond

@[expose] public section


/-! The support profiles of CMS Claim 4.3 when the ordinary base
vertices already have high simple degree. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph
open scoped Classical

variable {m d : ℕ} {D : MultiGraph (Fin (m+1) × Bool)}

theorem Completion.support_degree_mono (C : Completion D d) (v : Fin (m+1) × Bool) :
    D.supportGraph.degree v ≤ ((D.addCopies C.L).addCopies C.N).supportGraph.degree v := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  apply card_le_card
  intro u hu
  exact (mem_neighborFinset _ _ _).mpr (C.support_le ((mem_neighborFinset _ _ _).mp hu))

theorem Completion.q_bound_of_ordinary_support (C : Completion D d) (E : ℝ) (hE : 0 ≤ E)
    (hOrd : ∀ v : Fin (m+1) × Bool, v ≠ (0,false) → v ≠ (0,true) →
      (d:ℝ)-E ≤ (D.supportGraph.degree v:ℝ)) :
    2*(C.q:ℝ) ≤ E := by
  by_cases hFull : C.k = m+1
  · rw [C.paired_q_zero hFull,Nat.cast_zero,mul_zero]
    exact hE
  have hkm : C.k < m+1 := by have hh := C.cut_le; omega
  let x := C.middleVertex hkm
  have hxa : x ≠ (0,false) := by
    intro h
    have hh := congrArg (fun v : Fin (m+1) × Bool => v.1.val) h
    change C.k = 0 at hh
    have hk := C.positive
    omega
  have hxb : x ≠ (0,true) := by
    intro h
    have hh := congrArg Prod.snd h
    cases hh
  have hMiddle : C.L.degree x+2*C.q = d-D.degree x := C.middle_degrees ⟨C.k,hkm⟩ rfl
  have hD : D.degree x ≤ d := by
    have hh := C.regular x
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
    omega
  have hMidR : (C.L.degree x:ℝ)+2*(C.q:ℝ) = (d:ℝ)-(D.degree x:ℝ) := by
    rw [←Nat.cast_sub hD]
    exact_mod_cast hMiddle
  have hSupportR : (D.supportGraph.degree x:ℝ) ≤ D.degree x := by
    exact_mod_cast D.support_degree_le_degree x
  linarith only [hOrd x hxa hxb,hMidR,hSupportR,Nat.cast_nonneg (α := ℝ) (C.L.degree x)]

/-- The second anchor has at most the base row loss plus half the
ordinary deficiency tolerance, even when it is far below maximum degree. -/
theorem Completion.second_anchor_profile_of_dense_base (C : Completion D d) (E K : ℝ)
    (hE : 0 ≤ E)
    (hOrd : ∀ v : Fin (m+1) × Bool, v ≠ (0,false) → v ≠ (0,true) →
      (d:ℝ)-E ≤ (D.supportGraph.degree v:ℝ))
    (hb : (D.degree (0,true):ℝ) ≤ (D.supportGraph.degree (0,true):ℝ)+K) :
    let M := (D.addCopies C.L).addCopies C.N
    (d:ℝ)-(M.mult s((0,false),(0,true)):ℝ)-(K+E/2) ≤ M.supportGraph.degree (0,true) := by
  intro M
  let b : Fin (m+1) × Bool := (0,true)
  have hQ := C.q_bound_of_ordinary_support E hE hOrd
  have hBd := C.first_bundle_lower
  have hLe : C.N.mult s((0,false),b) ≤ M.mult s((0,false),b) := by
    change C.N.mult _ ≤ D.mult _+C.L.mult _+C.N.mult _
    omega
  have hNat : d ≤ D.degree b+C.q+M.mult s((0,false),b) := by
    change d-D.degree b-C.q ≤ C.N.mult s((0,false),b) at hBd
    omega
  have hNatR : (d:ℝ) ≤ (D.degree b:ℝ)+(C.q:ℝ)+(M.mult s((0,false),b):ℝ) := by
    exact_mod_cast hNat
  have hMono : (D.supportGraph.degree b:ℝ) ≤ M.supportGraph.degree b := by
    exact_mod_cast C.support_degree_mono b
  change (d:ℝ)-(M.mult s((0,false),b):ℝ)-(K+E/2) ≤ M.supportGraph.degree b
  change (D.degree b:ℝ) ≤ (D.supportGraph.degree b:ℝ)+K at hb
  linarith only [hQ,hNatR,hMono,hb]

end OverfullWork.CanonicalRegularization
