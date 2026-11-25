module

public import OverfullWork.CMSTheorem14

@[expose] public section

/-! Theorems 1.3 and 1.4 of Shan, arXiv:2308.16808v4, derived from
Chen–McDonald–Shan, Theorem 1.4. -/
namespace OverfullWork.ShanI

open Finset SimpleGraph
open scoped Classical
universe u

theorem shan_v4_criterion :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      (13/14 : ℝ)*(Fintype.card V : ℝ) ≤ (G.maxDegree : ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬ G.HasOverfullSubgraph) := by
  obtain ⟨N,h⟩ := Gate8J.cms_theorem_1_4.{u} (6/7) (by norm_num)
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hd
  apply h G hn
  convert hd using 1
  ring

theorem shan_v4_theorem_1_3 (ε : ℝ) (_hεpos : 0 < ε) (hε : ε ≤ 1/14) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      (1-ε)*(Fintype.card V : ℝ) ≤ (G.maxDegree : ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬ G.HasOverfullSubgraph) := by
  obtain ⟨N,h⟩ := shan_v4_criterion.{u}
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hd
  exact h G hn ((mul_le_mul_of_nonneg_right (by linarith : (13/14 : ℝ) ≤ 1-ε)
    (Nat.cast_nonneg _)).trans hd)

private theorem twice_internal_le_degree_bound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [dG : DecidableRel G.Adj] (S : Finset V) :
    2*Plantholt.eIn G S ≤ G.maxDegree*S.card := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  rw [Plantholt.two_mul_eIn]
  calc
    _ ≤ ∑ v ∈ S,G.degree v := by
      apply sum_le_sum
      intro v _
      have h := card_le_card (filter_subset (· ∈ S) (G.neighborFinset v))
      simpa only [Plantholt.nbIn,card_neighborFinset_eq_degree] using h
    _ ≤ ∑ _v ∈ S,G.maxDegree := sum_le_sum (fun v _ => G.degree_le_maxDegree v)
    _ = _ := by simp [Nat.mul_comm]

/-- The unique possible overfull support in an edge-critical graph
is the whole vertex set. Its edge count exceeds capacity by one. -/
theorem critical_edge_count_of_overfull {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [dG : DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V)
    (hc : Overfull.IsDeltaCritical G) (ho : G.HasOverfullSubgraph) :
    Odd (Fintype.card V) ∧
      G.edgeFinset.card = G.maxDegree*(Fintype.card V/2)+1 := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨S,hS⟩ := ho
  rw [←MultigraphExtension.eIn_eq_edge_filter G S] at hS
  have hOdd : Odd S.card := by
    rcases Nat.even_or_odd S.card with hEven | hOdd
    · have hHalf : 2*(S.card/2) = S.card := by obtain ⟨k,hk⟩ := hEven; omega
      have hCap := twice_internal_le_degree_bound G S
      rw [←hHalf,Nat.mul_left_comm] at hCap
      omega
    · exact hOdd
  have hAll : S = univ := by
    apply eq_univ_of_forall
    intro v
    by_contra hv
    obtain ⟨w,hw⟩ := G.degree_pos_iff_exists_adj v |>.mp
      (hc.1.preconnected.degree_pos_of_nontrivial v)
    let e := s(v,w)
    let R := G.deleteEdges ({e} : Set (Sym2 V))
    let : DecidableRel R.Adj := fun a b => Classical.propDecidable (R.Adj a b)
    have he : e ∈ G.edgeSet := G.mem_edgeSet.mpr hw
    have hOutside : ¬ e.toFinset ⊆ S := fun h => hv (h (by simp [e]))
    have hEdges : R.edgeFinset = G.edgeFinset \ {e} := by
      ext f
      simp [R,edgeSet_deleteEdges]
    have hInternal : Plantholt.eIn R S = Plantholt.eIn G S := by
      rw [MultigraphExtension.eIn_eq_edge_filter,MultigraphExtension.eIn_eq_edge_filter,hEdges]
      congr 1
      ext f
      simp only [mem_filter,mem_sdiff,mem_singleton]
      constructor
      · rintro ⟨⟨hf,_⟩,hfs⟩
        exact ⟨hf,hfs⟩
      · rintro ⟨hf,hfs⟩
        exact ⟨⟨hf,fun h => hOutside (h ▸ hfs)⟩,hfs⟩
    have hBound := Plantholt.two_mul_eIn_le_of_colorable (G := R) (hc.2.2 e he) hOdd
    rw [hInternal] at hBound
    have hHalf : 2*(S.card/2) = S.card-1 := by obtain ⟨k,hk⟩ := hOdd; omega
    rw [←hHalf,Nat.mul_left_comm] at hBound
    omega
  subst S
  rw [card_univ] at hOdd hS
  rw [Plantholt.eIn_univ] at hS
  refine ⟨hOdd,?_⟩
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨w,hw⟩ := G.degree_pos_iff_exists_adj v |>.mp
    (hc.1.preconnected.degree_pos_of_nontrivial v)
  let e := s(v,w)
  let R := G.deleteEdges ({e} : Set (Sym2 V))
  let : DecidableRel R.Adj := fun a b => Classical.propDecidable (R.Adj a b)
  have he : e ∈ G.edgeSet := G.mem_edgeSet.mpr hw
  have hEdges : R.edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp [R,edgeSet_deleteEdges,and_comm]
  have hBound := Plantholt.two_mul_eIn_le_of_colorable (G := R)
    (S := univ) (hc.2.2 e he) (by simpa using hOdd)
  rw [Plantholt.eIn_univ,card_univ,hEdges,card_erase_of_mem (G.mem_edgeFinset.mpr he)] at hBound
  have hHalf : 2*(Fintype.card V/2) = Fintype.card V-1 := by
    obtain ⟨k,hk⟩ := hOdd
    omega
  rw [←hHalf,Nat.mul_left_comm] at hBound
  omega

theorem critical_average_degree_of_overfull_criterion (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      ((1+ε)/2)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
      Overfull.IsDeltaCritical G →
      (G.maxDegree:ℝ)-1+3/(Fintype.card V:ℝ) ≤
        (2*(G.edgeFinset.card:ℝ))/(Fintype.card V:ℝ) := by
  obtain ⟨N,hN⟩ := Gate8J.cms_theorem_1_4.{u} ε hε
  refine ⟨max N 2,?_⟩
  intro V _ _ G _ hn hd hc
  have h₂ : 2 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hOver : G.HasOverfullSubgraph := by
    by_contra hNo
    exact hc.2.1 ((hN G ((le_max_left _ _).trans hn) hd).mpr hNo)
  obtain ⟨hOdd,hExact⟩ := critical_edge_count_of_overfull G h₂ hc hOver
  have hn0 : 0 < Fintype.card V := by omega
  let : Nonempty V := Fintype.card_pos_iff.mp hn0
  have hDeg := G.maxDegree_lt_card_verts
  have hHalf : 2*(Fintype.card V/2) = Fintype.card V-1 := by
    obtain ⟨k,hk⟩ := hOdd
    omega
  have hprod : 2*G.edgeFinset.card = G.maxDegree*(Fintype.card V-1)+2 := by
    rw [hExact,←hHalf]
    ring
  have hprodR : 2*(G.edgeFinset.card:ℝ) = (G.maxDegree:ℝ)*((Fintype.card V:ℝ)-1)+2 := by
    have hc : (2*(G.edgeFinset.card:ℝ)) =
        (G.maxDegree:ℝ)*((Fintype.card V-1:ℕ):ℝ)+2 := by exact_mod_cast hprod
    simpa only [Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using hc
  have hPos : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hn0
  have hMax : (G.maxDegree:ℝ)+1 ≤ (Fintype.card V:ℝ) := by exact_mod_cast hDeg
  apply (le_div_iff₀ hPos).mpr
  rw [add_mul,div_mul_cancel₀ _ hPos.ne',hprodR]
  nlinarith only [hMax]

theorem shan_v4_theorem_1_4 :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      (13/14 : ℝ)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
      Overfull.IsDeltaCritical G →
      (G.maxDegree:ℝ)-1+3/(Fintype.card V:ℝ) ≤
        (2*(G.edgeFinset.card:ℝ))/(Fintype.card V:ℝ) := by
  obtain ⟨N,hN⟩ := critical_average_degree_of_overfull_criterion.{u} (6/7) (by norm_num)
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hd hc
  apply hN G hn _ hc
  convert hd using 1
  ring

end OverfullWork.ShanI
