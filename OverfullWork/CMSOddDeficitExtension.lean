module

public import OverfullWork.CMSIsolatedStoppingExtension

@[expose] public section


/-! Deficit accounting for the two odd-order extensions in CMS
Subcase 2.1. The budget of the even graph away from its first
vertex is exactly that of the old odd graph. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph OddCutDeficit
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem odd_two_edge_extension_preserves_first_vertex_budget (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (hab : a ≠ b) (hD : 2 ≤ G.maxDegree)
    (ha : G.degree a < G.maxDegree) (hb : G.degree b < G.maxDegree)
    (hMin : ∀ v,2 ≤ G.degree v) :
    let H := OddTwoEdgeExtension.extension G a b
    ∀ p : Option V,(∀ v,H.degree p ≤ H.degree v) →
      (∑ v ∈ univ.erase p,(H.maxDegree-H.degree v))+H.degree p =
        deficitMass G G.maxDegree univ := by
  intro H p hp
  let d := G.maxDegree
  have hMax : H.maxDegree = d := OddTwoEdgeExtension.maxDegree_eq G a b hab hD ha hb
  have hNew : H.degree none = 2 := OddTwoEdgeExtension.degree_new G a b hab
  have hOld (v : V) : H.degree (some v) = G.degree v+(if v=a ∨ v=b then 1 else 0) :=
    OddTwoEdgeExtension.degree_old G a b v
  have hLeast (v : Option V) : 2 ≤ H.degree v := by
    cases v with
    | none => rw [hNew]
    | some v =>
      rw [hOld]
      exact (hMin v).trans (Nat.le_add_right _ _)
  have hp2 : H.degree p = 2 := by have hh := hp none; have hl := hLeast p; omega
  have hRow (v : V) :
      (d-H.degree (some v))+(if v=a ∨ v=b then 1 else 0)=d-G.degree v := by
    have hh := H.degree_le_maxDegree (some v)
    rw [hMax,hOld] at hh
    rw [hOld]
    omega
  have hSelected : (∑ v : V,if v=a ∨ v=b then 1 else 0) = 2 := by
    have hSet : (univ : Finset V).filter (fun v => v=a ∨ v=b) = {a,b} := by ext v; simp
    rw [←sum_filter,hSet,sum_const,card_pair hab]
    rfl
  have hSum := sum_congr (s₁ := (univ : Finset V)) (s₂ := univ) rfl (fun v _ => hRow v)
  rw [sum_add_distrib,hSelected] at hSum
  have hBudget := sum_erase_add (univ : Finset (Option V)) (fun v => d-H.degree v) (mem_univ p)
  rw [Fintype.sum_option,hp2,hNew] at hBudget
  change _ = deficitMass G d univ
  rw [hMax,hp2]
  unfold deficitMass
  omega

theorem isolated_extension_preserves_first_vertex_budget (G : SimpleGraph V)
    [DecidableRel G.Adj] (hPos : ∀ v,0 < G.degree v) :
    let H := isolatedStoppingExtension G
    ∀ p : Option V,(∀ v,H.degree p ≤ H.degree v) →
      (∑ v ∈ univ.erase p,(H.maxDegree-H.degree v))+H.degree p =
        deficitMass G G.maxDegree univ := by
  intro H p hp
  have hNew : H.degree none = 0 := isolated_stopping_extension_degree_new G
  have hOld (v : V) : H.degree (some v) = G.degree v := isolated_stopping_extension_degree_old G v
  have hMax : H.maxDegree = G.maxDegree := isolated_stopping_extension_maxDegree G
  have hNone : p=none := by
    cases p with
    | none => rfl
    | some v =>
      have h := hp none
      rw [hNew,hOld] at h
      exact (not_le_of_gt (hPos v) h).elim
  subst p
  have h := sum_erase_add (univ : Finset (Option V)) (fun v => G.maxDegree-H.degree v) (mem_univ none)
  rw [Fintype.sum_option,hNew] at h
  simp_rw [hOld] at h
  rw [hMax,hNew]
  unfold deficitMass
  omega

theorem one_low_degree_of_global_deficit_budget (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nonempty V] (B t : ℕ)
    (hBudget : deficitMass G G.maxDegree univ ≤ G.maxDegree+B)
    (hGap : B+2*t < G.maxDegree+2) :
    ∃ z : V,∀ v,v ≠ z → t ≤ G.degree v := by
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  refine ⟨z,?_⟩
  intro v hv
  by_contra! hn
  have hMin : G.degree z ≤ G.degree v := hz.symm.trans_le (G.minDegree_le_degree v)
  have hSub : ({v,z}:Finset V) ⊆ univ := subset_univ _
  have hTwo := sum_le_sum_of_subset_of_nonneg hSub
    (f := fun x => G.maxDegree-G.degree x) (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hv] at hTwo
  change _ ≤ deficitMass G G.maxDegree univ at hTwo
  have hV := G.degree_le_maxDegree v
  have hZ := G.degree_le_maxDegree z
  omega

end OverfullWork.CanonicalRegularization
