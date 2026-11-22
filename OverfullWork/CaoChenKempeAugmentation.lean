module

public import OverfullWork.CaoChenForkSelection
public import OverfullWork.CommonMissingColour

@[expose] public section


/-! # The actual Kempe augmentation used in Cao--Chen Claim 5.3 -/
namespace OverfullWork.CaoChenForkSelection
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenForkCounting
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

theorem inA_nonA_swap_off_left (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b w : V} (hcm : IsColMinus c a b)
    {δ γ : Fin G.maxDegree} (hδ : c.IsFree a δ) (hγ : ¬ InA c a b γ)
    (hoff : ¬ (c.kempeGraph δ γ).Reachable w a) (ε : Fin G.maxDegree) :
    InA (c.kempeSwap δ γ w) a b ε ↔ InA c a b ε := by
  have hδb : ¬ c.IsFree b δ := fun hb => (hcm.ab_facts hG).1 δ hδ hb
  have hγb : ¬ c.IsFree b γ := fun hb => hγ (Or.inr hb)
  unfold InA
  rw [isFree_kempeSwap_of_not_reachable c δ γ hoff,
    isFree_kempeSwap_of_neither c δ γ w hδb hγb]

theorem good_kept_by_nonA_swap {c : PEC G (Fin G.maxDegree)} {a b w z t : V}
    {δ γ : Fin G.maxDegree} (hγ : ¬ InA c a b γ)
    (hA : ∀ ε, InA (c.kempeSwap δ γ w) a b ε ↔ InA c a b ε)
    (hgood : Good c a b z t) (hδ : c.col z t ≠ some δ) :
    Good (c.kempeSwap δ γ w) a b z t := by
  obtain ⟨ε, hzt, hε⟩ := hgood
  have hεδ : ε ≠ δ := fun he => hδ (he ▸ hzt)
  have hεγ : ε ≠ γ := fun he => hγ (he ▸ hε)
  exact ⟨ε, kempeSwap_col_of_ne c δ γ w z t hzt hεδ hεγ, (hA ε).mpr hε⟩

/-- Swapping a component disjoint from a promotes one bad leaf while
preserving chosen witnesses of every previously good leaf. -/
theorem promote_good_fork_leaf (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b u w z : V} {d : ℕ}
    (hcm : IsColMinus c a b) {α δ γ : Fin G.maxDegree}
    (hbu : c.col b u = some α) (hα : c.IsFree a α) (hαδ : α ≠ δ)
    (hw : w ∈ goodSecondNeighbours c a b u ∩ smallVertices G d)
    (hbad : w ∉ goodForkLeaves c a b u d) (hz : z ∈ goodNeighbours c a b u)
    (hzw : c.col z w = some γ) (hγ : ¬ InA c a b γ)
    (hδ : c.IsFree a δ) (hoff : ¬ (c.kempeGraph δ γ).Reachable w a)
    (huzδ : c.col u z ≠ some δ)
    (f : V → V)
    (hf : ∀ t ∈ goodForkLeaves c a b u d,
      f t ∈ goodNeighbours c a b u ∧ Good c a b (f t) t)
    (hprotect : ∀ t ∈ goodForkLeaves c a b u d,
      c.col u (f t) ≠ some δ ∧ c.col (f t) t ≠ some δ) :
    ∃ c' : PEC G (Fin G.maxDegree), RootedAdmissible c' a b u ∧
      (goodForkLeaves c a b u d).card < (goodForkLeaves c' a b u d).card := by
  classical
  let c' := c.kempeSwap δ γ w
  have hA : ∀ ε, InA c' a b ε ↔ InA c a b ε :=
    fun ε => inA_nonA_swap_off_left hG hcm hδ hγ hoff ε
  have hαγ : α ≠ γ := fun he => hγ (Or.inl (he ▸ hα))
  have hbu' : c'.col b u = some α := kempeSwap_col_of_ne c δ γ w b u hbu hαδ hαγ
  have hα' : c'.IsFree a α := (isFree_kempeSwap_of_not_reachable c δ γ hoff α).mpr hα
  have hNAkeep : ∀ v ∈ goodNeighbours c a b u, c.col u v ≠ some δ →
      v ∈ goodNeighbours c' a b u := by
    intro v hv hvδ
    obtain ⟨hvN, hvb, hvGood⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨hvN, hvb, good_kept_by_nonA_swap hγ hA hvGood hvδ⟩
  have hLAadd : ∀ t ∈ goodSecondNeighbours c a b u, ∀ v,
      v ∈ goodNeighbours c' a b u → G.Adj v t → t ∈ goodSecondNeighbours c' a b u := by
    intro t ht v hv hvt
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨v, hv, (mem_neighborFinset G v t).mpr hvt⟩,
      (mem_sdiff.mp ht).2⟩
  have hkeep : goodForkLeaves c a b u d ⊆ goodForkLeaves c' a b u d := by
    intro t ht
    have hleaf := (mem_goodForkLeaves c a b u d t).mp ht
    have hft := hf t ht
    have hNA := hNAkeep (f t) hft.1 (hprotect t ht).1
    have hGood := good_kept_by_nonA_swap hγ hA hft.2 (hprotect t ht).2
    have hAdj : G.Adj (f t) t := by
      obtain ⟨ε, he, _⟩ := hft.2
      exact c.col_adj he
    exact (mem_goodForkLeaves c' a b u d t).mpr
      ⟨hLAadd t hleaf.1 (f t) hNA hAdj, hleaf.2.1, f t, hNA, hGood⟩
  have hrz : (c.kempeGraph δ γ).Reachable w z := by
    apply (kempeGraph_adj_of_col (Or.inr (show c.col w z = some γ by rw [c.col_symm]; exact hzw))).reachable
  have hzw' : c'.col z w = some δ := kcol_flip₂ c hzw hrz
  have hδ' : c'.IsFree a δ := (isFree_kempeSwap_of_not_reachable c δ γ hoff δ).mpr hδ
  have hNAz := hNAkeep z hz huzδ
  have hwLA := (mem_inter.mp hw).1
  have hwSmall : G.degree w ≤ d := (mem_filter.mp (mem_inter.mp hw).2).2
  have hw' : w ∈ goodForkLeaves c' a b u d := (mem_goodForkLeaves c' a b u d w).mpr
    ⟨hLAadd w hwLA z hNAz (c.col_adj hzw), hwSmall, z, hNAz, δ, hzw', Or.inl hδ'⟩
  have hsub : insert w (goodForkLeaves c a b u d) ⊆ goodForkLeaves c' a b u d :=
    insert_subset hw' hkeep
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hbad] at hcard
  exact ⟨c', ⟨hcm.kempeSwap δ γ w, α, hbu', hα'⟩, by omega⟩

end OverfullWork.CaoChenForkSelection
