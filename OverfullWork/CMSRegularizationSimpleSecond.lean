module

public import OverfullWork.CMSRegularizationThreeDeficits
public import OverfullWork.CanonicalOnePairPreservation

@[expose] public section


/-! The exceptional triples in CMS Claim 4.3 when the second anchor
is simple in the base multigraph. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph CanonicalTripleAddition
open scoped Classical

variable {m d : ℕ} {D : MultiGraph (Fin (m+1) × Bool)}

set_option maxHeartbeats 2000000 in
theorem Completion.simple_second_triples_safe_away_from_first (C : Completion D d)
    (hD : ∀ v, D.degree v ≤ d) (hNo : ¬D.HasOverfullSubset d)
    (hOrder : D.degree (0,false) ≤ D.degree (0,true))
    (hSimple : ∀ v, v ≠ (0,false) → D.mult s((0,true),v) ≤ 1)
    (hLocal : ((D.supportGraph.neighborFinset (0,false)).erase (0,true)).card ≤ 1 →
      (∃ w : Fin (m+1) × Bool, w ≠ (0,false) ∧ w ≠ (0,true) ∧
        D.degree w < d ∧ ∀ v, v ∉ ({(0,false),(0,true),w}:Finset _) → D.degree v = d) ∨
      ∀ v, v ≠ (0,false) → v ≠ (0,true) → d ≤ D.cutSize {(0,false),(0,true),v}) :
    ∀ v, v ≠ (0,false) → v ≠ (0,true) →
      d ≤ ((D.addCopies C.L).addCopies C.N).cutSize {(0,false),(0,true),v} := by
  let W := Fin (m+1) × Bool
  let a : W := (0,false)
  let b : W := (0,true)
  let M := (D.addCopies C.L).addCopies C.N
  have hab : a ≠ b := by
    intro h
    have hh := congrArg Prod.snd h
    change false = true at hh
    cases hh
  have hSub (e : Sym2 W) : D.mult e ≤ M.mult e := by
    change D.mult e ≤ D.mult e+C.L.mult e+C.N.mult e
    omega
  have hEven : Even (Fintype.card W) := by
    refine ⟨m+1,?_⟩
    simp only [W,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] <;> omega
  have hL : C.L.degree b = 0 := (C.prefix_degrees 0 C.positive).2
  have hLzero (v : W) : C.L.mult s(b,v) = 0 := by
    have hh := C.L.mult_pair_le_degree b v
    rw [hL] at hh
    omega
  have hNdeg : C.N.degree b = d-D.degree b := by
    have hh := C.regular b
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies,hL] at hh
    omega
  intro v hva hvb
  change v ≠ a at hva
  change v ≠ b at hvb
  have hNonSpecial :
      d ≤ M.cutSize {a,b,v} ∨ C.N.mult s(b,v) = 0 := by
    by_cases hTwo : 2 ≤ C.k
    · apply Or.inr
      have hPair := C.first_bundle_lower_of_prefix_two hTwo
      have hSum := two_bundles_le_degree C.N b a v hva.symm
      rw [hNdeg,Sym2.eq_swap (a := b) (b := a)] at hSum
      change d-D.degree b ≤ C.N.mult s(a,b) at hPair
      omega
    have hk : C.k = 1 := by have hp := C.positive; omega
    have hkm : C.k < m+1 := by
      by_contra! hn
      have hm : m = 0 := by omega
      subst m
      have hv0 : v.1 = 0 := by
        apply Fin.ext
        have hh := v.1.isLt
        change v.1.val = 0
        omega
      obtain ⟨x,y⟩ := v
      cases y
      · apply hva
        exact Prod.ext hv0 rfl
      · apply hvb
        exact Prod.ext hv0 rfl
    have ha : C.lastFalse = a := by
      apply Prod.ext
      · apply Fin.ext
        change C.k-1 = 0
        omega
      · rfl
    have hb : C.lastTrue = b := by
      apply Prod.ext
      · apply Fin.ext
        change C.k-1 = 0
        omega
      · rfl
    by_cases hm : v = C.middleVertex hkm
    · apply Or.inl
      have hSafe := C.triangle_safe_of_prefix_one hkm hk hD hNo
      simpa only [Completion.triangle,ha,hb,←hm] using hSafe
    · apply Or.inr
      have hv : v ∉ C.triangle hkm := by simp [Completion.triangle,ha,hb,hva,hvb,hm]
      have hbT : b ∈ C.triangle hkm := by simp [Completion.triangle,hb]
      rw [Sym2.eq_swap]
      exact C.N_triangle_boundary_zero hkm v b hv hbT
  rcases hNonSpecial with hSafe | hZero
  · exact hSafe
  have hSimpleM : M.mult s(b,v) ≤ 1 := by
    change D.mult s(b,v)+C.L.mult s(b,v)+C.N.mult s(b,v) ≤ 1
    rw [hLzero,hZero]
    simpa using hSimple v hva
  by_cases hSpare : ∃ w : W, w ≠ b ∧ w ≠ v ∧ 0 < M.mult s(a,w)
  · obtain ⟨w,hwb,hwv,hw⟩ := hSpare
    exact triple_cut_safe_of_spare_copy M d a b v w C.regular hab hva.symm hvb.symm hwb hwv hw hSimpleM
  have hSmall : ((D.supportGraph.neighborFinset a).erase b).card ≤ 1 := by
    have hS : (D.supportGraph.neighborFinset a).erase b ⊆ {v} := by
      intro x hx
      obtain ⟨hxb,hx⟩ := mem_erase.mp hx
      have hDPos : 0 < D.mult s(a,x) := (mem_neighborFinset _ a x).mp hx
      have hMPos := hDPos.trans_le (hSub s(a,x))
      by_contra hn
      exact hSpare ⟨x,hxb,fun he => hn (mem_singleton.mpr he),hMPos⟩
    simpa using card_le_card hS
  rcases hLocal hSmall with ⟨w,hwa,hwb,hW,hOut⟩ | hCuts
  · exact simple_second_triples_safe_of_three_deficits_away_from_first D M d a b w hab hwa.symm hwb.symm hEven
      C.regular hSub hNo hOrder hW hOut hSimple v hva.symm hvb.symm
  · exact (hCuts v hva hvb).trans (StarBudgetOddCuts.cut_mono D M hSub _)

theorem Completion.simple_second_triples_safe (C : Completion D d)
    (hD : ∀ v, D.degree v ≤ d) (hNo : ¬D.HasOverfullSubset d)
    (hOrder : D.degree (0,false) ≤ D.degree (0,true))
    (hSimple : ∀ v, D.mult s((0,true),v) ≤ 1)
    (hLocal : ((D.supportGraph.neighborFinset (0,false)).erase (0,true)).card ≤ 1 →
      (∃ w : Fin (m+1) × Bool, w ≠ (0,false) ∧ w ≠ (0,true) ∧
        D.degree w < d ∧ ∀ v, v ∉ ({(0,false),(0,true),w}:Finset _) → D.degree v = d) ∨
      ∀ v, v ≠ (0,false) → v ≠ (0,true) → d ≤ D.cutSize {(0,false),(0,true),v}) :
    ∀ v, v ≠ (0,false) → v ≠ (0,true) →
      d ≤ ((D.addCopies C.L).addCopies C.N).cutSize {(0,false),(0,true),v} := by
  exact C.simple_second_triples_safe_away_from_first hD hNo hOrder (fun v _ => hSimple v) hLocal

end OverfullWork.CanonicalRegularization
