module

public import OverfullWork.EquitableRecolouring

@[expose] public section


/-! # Weighted contrasts of bichromatic components

Weights are natural vertex weights. Two-colour components have at most
two vertices covered in exactly one colour; no path classification is used.
-/
namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def weightedLoad (C : M.EdgeColoring k) (w : V → ℕ) (i : Fin k) : ℕ :=
  ∑ v,w v*(C.colourGraph i).degree v

noncomputable def componentLoad (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) (i : Fin k) : ℕ :=
  ∑ v∈C.componentSet a b z,w v*(C.colourGraph i).degree v

theorem component_exclusive_card_le_two (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    ((C.componentSet a b z).filter fun v => (C.colourGraph a).degree v≠(C.colourGraph b).degree v).card≤2 := by
  let T:=C.componentSet a b z
  have hpoint : ∀ v∈T,
      (if (C.colourGraph a).degree v≠(C.colourGraph b).degree v then 1 else 0)+
        (C.colourGraph a).degree v+(C.colourGraph b).degree v≤2 := by
    intro v _
    have ha:=C.colourGraph_degree_le_one a v
    have hb:=C.colourGraph_degree_le_one b v
    split_ifs <;> omega
  have hsum:=sum_le_sum hpoint
  rw [sum_add_distrib,sum_add_distrib] at hsum
  have hcard : (∑ v∈T,if (C.colourGraph a).degree v≠(C.colourGraph b).degree v then 1 else 0)=
      (T.filter fun v => (C.colourGraph a).degree v≠(C.colourGraph b).degree v).card := by
    simp only [card_eq_sum_ones,sum_filter]
  rw [hcard] at hsum
  simp only [sum_const,Nat.nsmul_eq_mul] at hsum
  have ha:=(C.colourGraph a).twiceInternal_le_degree_sum T
  have hb:=(C.colourGraph b).twiceInternal_le_degree_sum T
  rw [twiceInternal_eq] at ha hb
  have hs:=C.component_size_bound a b z
  change T.card≤(C.colourGraph a).edgesWithin T+(C.colourGraph b).edgesWithin T+1 at hs
  change (T.filter _).card≤2
  omega

theorem weighted_degree_sum_le (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) (a b : Fin k) (T : Finset V) :
    (∑ v∈T,w v*(C.colourGraph a).degree v)≤
      (∑ v∈T,w v*(C.colourGraph b).degree v)+
        S*(T.filter fun v => (C.colourGraph a).degree v≠(C.colourGraph b).degree v).card := by
  have hpoint : ∀ v∈T,w v*(C.colourGraph a).degree v≤
      w v*(C.colourGraph b).degree v+S*(if (C.colourGraph a).degree v≠(C.colourGraph b).degree v then 1 else 0) := by
    intro v _
    have ha:=C.colourGraph_degree_le_one a v
    have hb:=C.colourGraph_degree_le_one b v
    have hh:=hw v
    by_cases he : (C.colourGraph a).degree v=(C.colourGraph b).degree v
    · simp [he]
    · have hcase : ((C.colourGraph a).degree v=1 ∧ (C.colourGraph b).degree v=0) ∨
          ((C.colourGraph a).degree v=0 ∧ (C.colourGraph b).degree v=1):=by omega
      rcases hcase with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> simp [h₁,h₂] <;> omega
  have hh:=sum_le_sum hpoint
  rw [sum_add_distrib,←mul_sum] at hh
  have hcard : (∑ v∈T,if (C.colourGraph a).degree v≠(C.colourGraph b).degree v then 1 else 0)=
      (T.filter fun v => (C.colourGraph a).degree v≠(C.colourGraph b).degree v).card := by
    simp only [card_eq_sum_ones,sum_filter]
  rwa [hcard] at hh

theorem component_load_le_add (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    C.componentLoad w a b z a≤C.componentLoad w a b z b+2*S := by
  have hh:=C.weighted_degree_sum_le w S hw a b (C.componentSet a b z)
  have hc:=C.component_exclusive_card_le_two a b z
  have hm:=Nat.mul_le_mul_left S hc
  change C.componentLoad w a b z a≤C.componentLoad w a b z b+_ at hh
  omega

/-- A surplus-one colour covers every vertex of its component. -/
theorem component_full_of_surplus (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent)
    (hsurplus : (C.colourGraph a).edgesWithin (C.componentSet a b z)=
      (C.colourGraph b).edgesWithin (C.componentSet a b z)+1) :
    ∀ v∈C.componentSet a b z,(C.colourGraph a).degree v=1 := by
  let T:=C.componentSet a b z
  have ha:=(C.colourGraph a).twiceInternal_le_degree_sum T
  rw [twiceInternal_eq] at ha
  have hs:=C.component_size_bound a b z
  change T.card≤(C.colourGraph a).edgesWithin T+(C.colourGraph b).edgesWithin T+1 at hs
  intro v hv
  by_contra hn
  have hd:=C.colourGraph_degree_le_one a v
  have hzero : (C.colourGraph a).degree v=0:=by omega
  have hsum:=(sum_le_sum (s:=T.erase v) (fun u _ => C.colourGraph_degree_le_one a u))
  simp only [sum_const,Nat.nsmul_eq_mul,Nat.mul_one] at hsum
  have he : (∑ u∈T.erase v,(C.colourGraph a).degree u)+(C.colourGraph a).degree v=
      ∑ u∈T,(C.colourGraph a).degree u:=sum_erase_add T _ hv
  have hc : (T.erase v).card+1=T.card:=card_erase_add_one hv
  rw [hzero] at he
  change (C.colourGraph a).edgesWithin T=(C.colourGraph b).edgesWithin T+1 at hsurplus
  omega

theorem component_load_nonnegative_of_surplus (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent)
    (hsurplus : (C.colourGraph a).edgesWithin (C.componentSet a b z)=
      (C.colourGraph b).edgesWithin (C.componentSet a b z)+1) :
    C.componentLoad w a b z b≤C.componentLoad w a b z a := by
  unfold componentLoad
  apply sum_le_sum
  intro v hv
  rw [C.component_full_of_surplus a b z hsurplus v hv]
  exact Nat.mul_le_mul_left (w v) (C.colourGraph_degree_le_one b v)

/-- A surplus-one colour covers every vertex of its component. -/
theorem component_full_right_of_surplus (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent)
    (hsurplus : (C.colourGraph b).edgesWithin (C.componentSet a b z)=
      (C.colourGraph a).edgesWithin (C.componentSet a b z)+1) :
    ∀ v∈C.componentSet a b z,(C.colourGraph b).degree v=1 := by
  let T:=C.componentSet a b z
  have ha:=(C.colourGraph b).twiceInternal_le_degree_sum T
  rw [twiceInternal_eq] at ha
  have hs:=C.component_size_bound a b z
  change T.card≤(C.colourGraph a).edgesWithin T+(C.colourGraph b).edgesWithin T+1 at hs
  intro v hv
  by_contra hn
  have hd:=C.colourGraph_degree_le_one b v
  have hzero : (C.colourGraph b).degree v=0:=by omega
  have hsum:=(sum_le_sum (s:=T.erase v) (fun u _ => C.colourGraph_degree_le_one b u))
  simp only [sum_const,Nat.nsmul_eq_mul,Nat.mul_one] at hsum
  have he : (∑ u∈T.erase v,(C.colourGraph b).degree u)+(C.colourGraph b).degree v=
      ∑ u∈T,(C.colourGraph b).degree u:=sum_erase_add T _ hv
  have hc : (T.erase v).card+1=T.card:=card_erase_add_one hv
  rw [hzero] at he
  change (C.colourGraph b).edgesWithin T=(C.colourGraph a).edgesWithin T+1 at hsurplus
  omega

theorem component_load_nonpositive_of_surplus (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent)
    (hsurplus : (C.colourGraph b).edgesWithin (C.componentSet a b z)=
      (C.colourGraph a).edgesWithin (C.componentSet a b z)+1) :
    C.componentLoad w a b z a≤C.componentLoad w a b z b := by
  unfold componentLoad
  apply sum_le_sum
  intro v hv
  rw [C.component_full_right_of_surplus a b z hsurplus v hv]
  exact Nat.mul_le_mul_left (w v) (C.colourGraph_degree_le_one a v)

theorem componentLoad_eq_indicator (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) (i : Fin k) :
    C.componentLoad w a b z i=∑ v,if v∈C.componentSet a b z then w v*(C.colourGraph i).degree v else 0 := by
  rw [←sum_filter]
  unfold componentLoad
  congr 1
  ext v
  simp

theorem sum_component_load (C : M.EdgeColoring k) (w : V → ℕ) (a b i : Fin k) :
    (∑ z : (C.twoColourGraph a b).ConnectedComponent,C.componentLoad w a b z i)=C.weightedLoad w i := by
  simp_rw [C.componentLoad_eq_indicator]
  rw [sum_comm]
  unfold weightedLoad
  apply sum_congr rfl
  intro v _
  let z₀:=(C.twoColourGraph a b).connectedComponentMk v
  have hv : v∈C.componentSet a b z₀:=by simp [componentSet,z₀]
  rw [sum_eq_single z₀]
  · simp only [if_pos hv]
  · intro z _ hne
    have hn : v∉C.componentSet a b z := by
      intro hmem
      have he : (C.twoColourGraph a b).connectedComponentMk v=z := by
        simpa only [componentSet,Set.mem_toFinset,ConnectedComponent.mem_supp_iff] using hmem
      exact hne he.symm
    simp [hn]
  · simp

theorem component_load_reverse_le_add (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    C.componentLoad w a b z b≤C.componentLoad w a b z a+2*S := by
  have hh:=C.weighted_degree_sum_le w S hw b a (C.componentSet a b z)
  have hc:=C.component_exclusive_card_le_two a b z
  have he : ((C.componentSet a b z).filter fun v => (C.colourGraph b).degree v≠(C.colourGraph a).degree v)=
      ((C.componentSet a b z).filter fun v => (C.colourGraph a).degree v≠(C.colourGraph b).degree v) := by
    ext v
    simp only [mem_filter]
    tauto
  rw [he] at hh
  have hm:=Nat.mul_le_mul_left S hc
  change C.componentLoad w a b z b≤C.componentLoad w a b z a+_ at hh
  omega

theorem component_real_card_difference (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)-
        ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ) = -1 ∨
    ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)-
        ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ) = 0 ∨
    ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)-
        ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ) = 1 := by
  have hs:=C.component_size_bound a b z
  have ha:=C.twice_colour_edgesWithin_le a (C.componentSet a b z)
  have hb:=C.twice_colour_edgesWithin_le b (C.componentSet a b z)
  have hcases : (C.colourGraph a).edgesWithin (C.componentSet a b z)+1=
      (C.colourGraph b).edgesWithin (C.componentSet a b z) ∨
      (C.colourGraph a).edgesWithin (C.componentSet a b z)=
        (C.colourGraph b).edgesWithin (C.componentSet a b z) ∨
      (C.colourGraph a).edgesWithin (C.componentSet a b z)=
        (C.colourGraph b).edgesWithin (C.componentSet a b z)+1:=by omega
  rcases hcases with h|h|h
  · left
    have hr : ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)+1=
        ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ):=by exact_mod_cast h
    linarith
  · right;left
    rw [h];ring
  · right;right
    have hr : ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)=
        ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ)+1:=by exact_mod_cast h
    linarith

theorem component_real_load_contrast (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    |(C.componentLoad w a b z a:ℝ)-(C.componentLoad w a b z b:ℝ)|≤2*(S:ℝ) := by
  have hl:=C.component_load_le_add w S hw a b z
  have hr:=C.component_load_reverse_le_add w S hw a b z
  have hlR : (C.componentLoad w a b z a:ℝ)≤(C.componentLoad w a b z b:ℝ)+2*(S:ℝ):=by exact_mod_cast hl
  have hrR : (C.componentLoad w a b z b:ℝ)≤(C.componentLoad w a b z a:ℝ)+2*(S:ℝ):=by exact_mod_cast hr
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end SimpleGraph.MultiGraph.EdgeColoring
