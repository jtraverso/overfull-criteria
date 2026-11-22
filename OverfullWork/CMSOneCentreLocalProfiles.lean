module

public import OverfullWork.CriticalCentreTriples
public import OverfullWork.WeakVALIdentificationEdges

@[expose] public section


/-! The local triple test at the first vertex of a one-centre image.
If the centre has only two support neighbours, the weighted degree
sum forces both of them to have maximum degree. -/
namespace OverfullWork.IndependentSetIdentification

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem centre_weighted_degree_sum_of_weak_val (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y : Set V))
    (hWeak : ∀ u ∈ Y,∀ v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (x : Outside Y) :
    (G.maxDegree-(graph G Y hInd).degree (some x)+2)*(graph G Y hInd).mult s(none,some x) ≤
      (graph G Y hInd).degree none := by
  rw [centre_mult_eq_neighbour_count,degree_some,degree_none]
  let T := Y.filter (G.Adj x.val)
  let f := G.maxDegree-G.degree x.val+2
  change f*T.card ≤ _
  calc
    _ = ∑ _y ∈ T,f := by simp [Nat.mul_comm]
    _ ≤ ∑ y ∈ T,G.degree y := by
      apply sum_le_sum
      intro y hy
      obtain ⟨hyY,hxy⟩ := mem_filter.mp hy
      have hh := hWeak y hyY x.val hxy.symm
      have hD := G.degree_le_maxDegree x.val
      dsimp only [f]
      omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

end OverfullWork.IndependentSetIdentification

namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
theorem sparse_first_bundle_triples (M : MultiGraph V) (a b : V) (d h : ℕ)
    (hab : a ≠ b) (hMax : ∀ v,M.degree v ≤ d) (hMin : ∀ v,M.degree a ≤ M.degree v)
    (hPos : 0 < M.degree a) (hSmall : 2*h+2 ≤ d)
    (hMulti : ∀ v,M.mult s(a,v) ≤ h)
    (hSimple : ∀ v,v ≠ a → M.mult s(b,v) ≤ 1)
    (hWeighted : ∀ v,(d-M.degree v+2)*M.mult s(a,v) ≤ M.degree a)
    (hFew : ((M.supportGraph.neighborFinset a).erase b).card ≤ 1) :
    ∀ v,v ≠ a → v ≠ b → d ≤ M.cutSize {a,b,v} := by
  let N : Finset V := univ.filter (fun v => 0 < M.mult s(a,v))
  have hN : N = M.supportGraph.neighborFinset a := by
    ext v
    simp only [N,mem_filter,mem_univ,true_and,mem_neighborFinset]
    rfl
  have hDeg : M.degree a = ∑ v ∈ N,M.mult s(a,v) := by
    rw [M.degree_eq_sum_mult]
    change (∑ v : V,M.mult s(a,v)) =
      ∑ v ∈ univ.filter (fun v => 0 < M.mult s(a,v)),M.mult s(a,v)
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    split_ifs <;> omega
  have hWeight (v : V) : 2*M.mult s(a,v) ≤ M.degree a :=
    (Nat.mul_le_mul_right _ (by omega : 2 ≤ d-M.degree v+2)).trans (hWeighted v)
  have hTwo : 2 ≤ N.card := by
    by_contra! h
    by_cases hz : N.card = 0
    · rw [card_eq_zero.mp hz,sum_empty] at hDeg
      omega
    · obtain ⟨v,hv⟩ := card_eq_one.mp (show N.card = 1 by omega)
      rw [hv,sum_singleton] at hDeg
      have hh := hWeight v
      omega
  have hErase : (N.erase b).card ≤ 1 := by rwa [hN]
  have hb : b ∈ N := by
    by_contra hn
    rw [erase_eq_of_notMem hn] at hErase
    omega
  have hOne : (N.erase b).card = 1 := by
    rw [card_erase_of_mem hb]
    have hCard := card_erase_add_one hb
    omega
  obtain ⟨w,hw⟩ := card_eq_one.mp hOne
  have hbw : b ≠ w := by
    have he : w ∈ N.erase b := by simp [hw]
    exact (mem_erase.mp he).1.symm
  have hPair : N = {b,w} := by rw [←insert_erase hb,hw]
  have hm (v : V) (hv : v ∈ N) : 0 < M.mult s(a,v) := (mem_filter.mp hv).2
  have hMb := hm b hb
  have hMw := hm w (by rw [hPair]; simp)
  rw [hPair,sum_pair hbw] at hDeg
  have hBalB : M.degree a = 2*M.mult s(a,b) := by have h₁ := hWeight b; have h₂ := hWeight w; omega
  have hBalW : M.degree a = 2*M.mult s(a,w) := by have h₁ := hWeight b; have h₂ := hWeight w; omega
  have hFullB : M.degree b = d := by
    have h := hWeighted b
    rw [hBalB] at h
    have h' := Nat.le_of_mul_le_mul_right h hMb
    have hM := hMax b
    omega
  have hFullW : M.degree w = d := by
    have h := hWeighted w
    rw [hBalW] at h
    have h' := Nat.le_of_mul_le_mul_right h hMw
    have hM := hMax w
    omega
  intro v hva hvb
  have hCut := CriticalCentreTriples.triple_cut_identity M a b v hab hva.symm hvb.symm
  have hS := hSimple v hva
  by_cases hwv : v = w
  · subst v
    have hh := hMulti b
    omega
  · have hvN : v ∉ N := by rw [hPair]; simp [hvb,hwv]
    have hZ : M.mult s(a,v) = 0 := by
      by_contra hz
      exact hvN (mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero hz⟩)
    have hD := hMin v
    omega

end OverfullWork.CanonicalRegularization
