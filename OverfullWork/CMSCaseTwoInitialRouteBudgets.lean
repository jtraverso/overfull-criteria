module

public import OverfullWork.CMSCaseTwoInitialAnchors
public import OverfullWork.CrossingSupport
public import OverfullWork.CutMassBounds
public import OverfullWork.SecondAnchorCrossingBudget

@[expose] public section


/-! Budget the actual partial colouring passed from the initial
anchor runs to the alternating path stage of CMS. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k : ℕ} {η : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

structure CaseTwoPartition.InitialRouteBudget
    (s : CaseTwoPartition M a b d m L r t η) (R : M.PartialColouring k)
    (w : V) (ξ B : ℝ) : Prop where
  anchors : ∀ i : Fin k, (R.colouring.colourGraph i).degree a = 1 ∧
    (R.colouring.colourGraph i).degree b = 1
  vertex_missing : ∀ v, ((R.colouring.missingPalette v).card:ℝ) < 6*ξ
  colour_missing : ∀ i : Fin k, ((R.colouring.missingSet univ i).card:ℝ) ≤ B+2*ξ
  total_missing : (∑ v, ((R.colouring.missingPalette v).card:ℝ)) ≤
    (Fintype.card V:ℝ)*(6*ξ)
  residue : ((R.available.internalPart s.part).edgeCount:ℝ) < 5*ξ
  centre_residue : (R.available.internalPart s.part).degree a = 0
  protected_residue : (R.available.internalPart s.part).mult s(b,w) = 0
  colour_cut : ∀ i : Fin k, (R.colouring.colourGraph i).cutSize s.part ≤ 2
  ordinary_deleted : ∀ v, v ≠ a → v ≠ b → (R.graph.crossingSupport s.part).degree v ≤ 2

/-- The centre bundles and the second crossing row after initial saturation. -/
structure CaseTwoMiddleCopies.InitialCrossingRows (copies : CaseTwoMiddleCopies s w)
    (R : M.PartialColouring k) (ξ : ℝ) : Prop where
  centre : ∀ v ∈ s.partᶜ, copies.count v ≤ R.graph.mult s(a,v) ∧
    R.graph.mult s(a,v) ≤ copies.count v+⌈ξ⌉₊
  second : (R.graph.crossingSupport s.part).degree b ≤ 1+⌈3*ξ⌉₊

set_option maxHeartbeats 1800000 in
theorem CaseTwoMiddleCopies.exists_initial_route_budget_with_rows (copies : CaseTwoMiddleCopies s w)
    (C : copies.graph.EdgeColoring k) (hw : w ∉ s.part) (hk : k ≤ M.degree a)
    (E : ℕ) (ξ B : ℝ) (hOrder : Fintype.card V = 2*m)
    (hMissing : ∀ v, ((C.missingPalette v).card:ℝ) < ξ)
    (hPerColour : ∀ i : Fin k, ((C.missingSet univ i).card:ℝ) ≤ B)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E)
    (hGap : (M.mult s(a,b):ℝ)+(E:ℝ)+η*(m:ℝ)+6*ξ+4 ≤ (d:ℝ)) :
    ∃ R : M.PartialColouring k, s.InitialRouteBudget R w ξ B ∧ copies.InitialCrossingRows R ξ := by
  obtain ⟨Q,R,u,v,hFirst,hSecond,hu,hv,hSat,hBundle,hCentre,hAway,hFinal,_,hColour⟩ :=
    copies.exists_initial_anchor_runs C hw hk E ξ B hOrder hMissing hPerColour hProfile hGap
  have hResidue := copies.initial_residue_size C hFirst hSecond
  have huR : (u:ℝ) ≤ 2*((C.missingPalette a).card:ℝ) := by exact_mod_cast hu
  have hvR : (v:ℝ) ≤ (Q.colouring.missingPalette b).card := by exact_mod_cast hv
  have hGrow : (Q.colouring.missingPalette b).card ≤ (C.missingPalette b).card+u := by
    split_ifs at hFirst <;> exact hFirst.missingPalette_growth_le b
  have hGrowR : ((Q.colouring.missingPalette b).card:ℝ) ≤
      (C.missingPalette b).card+(u:ℝ) := by exact_mod_cast hGrow
  have hResR : ((R.available.internalPart s.part).edgeCount:ℝ) ≤ (u:ℝ)+(v:ℝ) := by
    exact_mod_cast hResidue
  have hPair : ({a,b} : Finset V).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have hCover (x y : V) (hCross : ¬(x ∈ s.part ↔ y ∈ s.part))
      (hPositive : 0 < R.graph.mult s(x,y)) : x ∈ ({a,b} : Finset V) ∨ y ∈ ({a,b} : Finset V) := by
    by_contra! hn
    have hx : x ≠ a ∧ x ≠ b := by simpa using hn.1
    have hy : y ≠ a ∧ y ≠ b := by simpa using hn.2
    exact (Nat.ne_of_gt hPositive) (hAway x y hx.1 hy.1 hx.2 hy.2 hCross)
  refine ⟨R,{
    anchors := hSat
    vertex_missing := hFinal
    colour_missing := hColour
    total_missing := ?_
    residue := by linarith only [huR,hvR,hGrowR,hResR,hMissing a,hMissing b]
    centre_residue := ?_
    protected_residue := ?_
    colour_cut := ?_
    ordinary_deleted := ?_
  },?_⟩
  · simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum
      (s := (univ : Finset V)) (fun x _ => (hFinal x).le)
  · rw [MultiGraph.degree_internalPart,if_pos s.centre_mem]
    apply sum_eq_zero
    intro x hx
    change M.mult s(a,x)-R.graph.mult s(a,x) = 0
    rw [hCentre x hx,Nat.sub_self]
  · rw [MultiGraph.internalPart_mult,if_pos (by simp [s.second_not_mem,hw])]
    change M.mult s(b,w)-R.graph.mult s(b,w) = 0
    rw [hBundle,Nat.sub_self]
  · intro i
    apply le_trans ((R.colouring.colourGraph i).matching_cut_le_cover
      (R.colouring.colourGraph_degree_le_one i) s.part {a,b} ?_) hPair
    intro x y hne hcol
    have hh := R.colouring.col_le_mult s(x,y) i
    change 0 < R.colouring.col s(x,y) i at hcol
    exact hCover x y hne (by omega)
  · intro x hxa hxb
    exact (R.graph.crossingSupport_degree_le_cover s.part {a,b}
      (fun y z hyz => hCover y z hyz.2 hyz.1) x (by simp [hxa,hxb])).trans hPair

  · have hab : a ≠ b := fun he => s.second_not_mem (he ▸ s.centre_mem)
    have hAtCentre (v : V) : copies.graph.mult s(a,v) ≤ R.graph.mult s(a,v) := by
      rw [hSecond.anchor_bundle hab v]
      split_ifs at hFirst
      · exact (hFirst.bundle_bounds _).1 (by simp)
      · exact hFirst.centre_bundle_mono v
    have hSatA : R.graph.degree a = k := by
      rw [←R.colouring.sum_colour_degree a]
      have hEach := fun i => (hSat i).1
      simp_rw [hEach]
      simp
    refine ⟨?_,?_⟩
    · intro z hz
      have hMiddle : copies.graph.mult s(a,z) = copies.count z :=
        MiddleCopyGraph.crossing_mult M s.part a z copies.count
          (copies.inside_zero _ s.centre_mem) s.centre_mem (mem_compl.mp hz)
      have hAdd := C.missingPalette_card_add_degree a
      have hGrowRow := MultiGraph.bundle_growth_le_degree_growth copies.graph R.graph a z
        (C.missingPalette a).card hAtCentre (by omega)
      have hCeil : (C.missingPalette a).card ≤ ⌈ξ⌉₊ := by
        exact_mod_cast (hMissing a).le.trans (Nat.le_ceil ξ)
      exact ⟨by simpa only [hMiddle] using hAtCentre z,by omega⟩
    · have hNoOff (x y : V) (hxa : x ≠ a) (hya : y ≠ a)
          (hCross : ¬ (x ∈ s.part ↔ y ∈ s.part)) : Q.graph.mult s(x,y) = 0 := by
        have ha : a ∉ s(x,y) := by simp only [Sym2.mem_iff]; tauto
        have hZero := copies.away_crossing_zero x y hxa hya hCross
        have hh : Q.graph.mult s(x,y) ≤ copies.graph.mult s(x,y) := by
          split_ifs at hFirst
          · exact (hFirst.bundle_bounds _).2 ha
          · exact hFirst.away_bundle_le _ ha
        omega
      have hCrossCover (x y : V) (hxy : (Q.graph.crossingSupport s.part).Adj x y) :
          x ∈ ({a} : Finset V) ∨ y ∈ ({a} : Finset V) := by
        by_contra! hn
        have hx : x ≠ a := by simpa using hn.1
        have hy : y ≠ a := by simpa using hn.2
        exact (Nat.ne_of_gt hxy.1) (hNoOff x y hx hy hxy.2)
      have hBefore : (Q.graph.crossingSupport s.part).degree b ≤ 1 := by
        simpa only [card_singleton] using
          Q.graph.crossingSupport_degree_le_cover s.part {a} hCrossCover b (by simp [hab.symm])
      have hGrow := hSecond.crossing_support_degree
      have hQB : ((Q.colouring.missingPalette b).card:ℝ) < 3*ξ :=
        by linarith only [hGrowR,huR,hMissing a,hMissing b]
      have hCeil : (Q.colouring.missingPalette b).card ≤ ⌈3*ξ⌉₊ := by
        exact_mod_cast hQB.le.trans (Nat.le_ceil _)
      omega

theorem CaseTwoMiddleCopies.exists_initial_route_budget (copies : CaseTwoMiddleCopies s w)
    (C : copies.graph.EdgeColoring k) (hw : w ∉ s.part) (hk : k ≤ M.degree a)
    (E : ℕ) (ξ B : ℝ) (hOrder : Fintype.card V = 2*m)
    (hMissing : ∀ v, ((C.missingPalette v).card:ℝ) < ξ)
    (hPerColour : ∀ i : Fin k, ((C.missingSet univ i).card:ℝ) ≤ B)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E)
    (hGap : (M.mult s(a,b):ℝ)+(E:ℝ)+η*(m:ℝ)+6*ξ+4 ≤ (d:ℝ)) :
    ∃ R : M.PartialColouring k, s.InitialRouteBudget R w ξ B := by
  obtain ⟨R,budget,_⟩ := copies.exists_initial_route_budget_with_rows
    C hw hk E ξ B hOrder hMissing hPerColour hProfile hGap
  exact ⟨R,budget⟩

end OverfullWork.CMSBalancedCut
