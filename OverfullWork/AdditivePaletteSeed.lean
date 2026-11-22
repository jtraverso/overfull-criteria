module

public import OverfullWork.EfficientSeed

@[expose] public section


/-! # A balanced small-defect seed from an actual additive palette

The input is a supplied proper colouring with explicit lower and upper
palette bounds. Existence of that colouring is a separate obligation.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Equitably align the two internal sides, preserving the palette, and
bound every vertex and colour defect by 64r. -/
theorem exists_balanced_seed_of_additive_palette (M : MultiGraph V) (S : Finset V)
    (m D r μ k : ℕ) (hr : 1≤r) (hμr : μ≤r)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hreg : M.IsRegularOfDegree D) (hdense : m≤D)
    (hdis : ∀ v,|(M.degreeInto S v:ℝ)-(M.degreeInto Sᶜ v:ℝ)|<2*(r:ℝ))
    (A : (M.internalPart S).EdgeColoring k)
    (hklower : D/2+r+1≤k) (hkupper : k≤D/2+r+8*μ) :
    ∃ B : (M.internalPart S).EdgeColoring k,
      k≤D/2+64*r ∧ m≤2*k ∧
      (∀ i,(B.colourGraph i).edgesWithin S=(B.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i j,(B.colourGraph i).edgesWithin S≤(B.colourGraph j).edgesWithin S+1) ∧
      (∀ v,(B.missingPalette v).card≤64*r) ∧
      (∀ i,(B.missingSet S i).card=(B.missingSet Sᶜ i).card) ∧
      ∀ i,(B.missingSet S i).card≤64*r := by
  have hbounds : ∀ v,D<2*(M.internalPart S).degree v+2*r := by
    intro v
    have hs : (M.degreeInto S v:ℝ)+(M.degreeInto Sᶜ v:ℝ)=(D:ℝ) := by
      exact_mod_cast (M.degreeInto_add_compl S v).trans (hreg v)
    obtain ⟨hl,hu⟩:=abs_lt.mp (hdis v)
    have hA : D<2*M.degreeInto S v+2*r := by
      exact_mod_cast (show (D:ℝ)<2*(M.degreeInto S v:ℝ)+2*(r:ℝ) by linarith)
    have hB : D<2*M.degreeInto Sᶜ v+2*r := by
      exact_mod_cast (show (D:ℝ)<2*(M.degreeInto Sᶜ v:ℝ)+2*(r:ℝ) by linarith)
    rw [degree_internalPart]
    split_ifs <;> assumption
  have hA : Nonempty ((M.restrict S).EdgeColoring k) := by
    rw [←M.internalPart_restrict S]
    exact ⟨A.restrictColouring S⟩
  have hB : Nonempty ((M.restrict Sᶜ).EdgeColoring k) := by
    rw [←M.internalPart_restrict_compl S]
    exact ⟨A.restrictColouring Sᶜ⟩
  obtain ⟨B,hbal,heq⟩:=M.exists_balanced_internal_colouring S D k hreg (hS.trans hSc.symm) hA hB
  have hkm : m≤2*k:=by omega
  have hk : 0<k:=by omega
  have hhalf : 2*(D/2)≤D:=by omega
  have hvertex : ∀ v,(B.missingPalette v).card≤16*r := by
    intro v
    have hh:=B.missingPalette_card_add_degree v
    have hd:=hbounds v
    nlinarith only [hh,hd,hkupper,hμr,hhalf]
  refine ⟨B,by omega,hkm,hbal,heq,?_,?_,?_⟩
  · intro v
    have hh:=hvertex v
    omega
  · exact B.missingSet_card_eq_of_internal_balance S (hS.trans hSc.symm) hbal
  · have hh:=B.missingSet_card_le_of_vertex_deficiency S m (16*r) hS hkm hk
      (fun v _ => hvertex v) (fun i => by simpa only [hS] using B.internal_missing_count S i) heq
    intro i
    have hi:=hh i
    omega

end SimpleGraph.MultiGraph
