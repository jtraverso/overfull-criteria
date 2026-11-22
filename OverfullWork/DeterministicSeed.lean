module

public import OverfullWork.DeterministicMulticolouring
public import OverfullWork.AdditivePaletteSeed

@[expose] public section


/-! # Internal seeds from deterministic additive multicolouring

The degree partition may still use a moment. No further moment or
geometric tolerance is needed to colour the internal multigraph.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

theorem exists_deterministic_internal_seed (M : MultiGraph V) (S : Finset V)
    (h m D r : ℕ) (hr : 1≤r) (hS : S.card=m) (hSc : Sᶜ.card=m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4^h)
    (hμr : 4^h≤r) (hdense : m≤D)
    (hdis : ∀ v,|(M.degreeInto S v:ℝ)-(M.degreeInto Sᶜ v:ℝ)|<2*(r:ℝ)) :
    ∃ (k : ℕ) (B : (M.internalPart S).EdgeColoring k),
      k≤D/2+64*r ∧ m≤2*k ∧
      (∀ i,(B.colourGraph i).edgesWithin S=(B.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i j,(B.colourGraph i).edgesWithin S≤(B.colourGraph j).edgesWithin S+1) ∧
      (∀ v,(B.missingPalette v).card≤64*r) ∧
      (∀ i,(B.missingSet S i).card=(B.missingSet Sᶜ i).card) ∧
      ∀ i,(B.missingSet S i).card≤64*r := by
  have hpow : (2:ℕ)^(2*h)=4^h:=by norm_num [pow_mul]
  have hbounds : ∀ v,(M.internalPart S).degree v≤D/2+r := by
    intro v
    have hs : (M.degreeInto S v:ℝ)+(M.degreeInto Sᶜ v:ℝ)=(D:ℝ) := by
      exact_mod_cast (M.degreeInto_add_compl S v).trans (hreg v)
    obtain ⟨hl,hu⟩:=abs_lt.mp (hdis v)
    have hA : 2*M.degreeInto S v<D+2*r := by
      exact_mod_cast (show 2*(M.degreeInto S v:ℝ)<(D:ℝ)+2*(r:ℝ) by linarith)
    have hB : 2*M.degreeInto Sᶜ v<D+2*r := by
      exact_mod_cast (show 2*(M.degreeInto Sᶜ v:ℝ)<(D:ℝ)+2*(r:ℝ) by linarith)
    rw [degree_internalPart]
    split_ifs <;> omega
  have hmuI : ∀ e,(M.internalPart S).mult e≤2^(2*h) := by
    intro e
    rw [hpow]
    exact (M.internalPart_le S e).trans (hmu e)
  obtain ⟨k,hklower,hkupper,⟨A⟩⟩:=exists_deterministic_palette (2*h) (M.internalPart S) (D/2+r)
    hmuI hbounds
  have hkupper' : k≤D/2+r+8*(4^h):=by simpa only [hpow] using hkupper
  obtain ⟨B,hk,hkm,hbal,heq,hv,hmb,hcol⟩:=M.exists_balanced_seed_of_additive_palette S
    m D r (4^h) k hr hμr hS hSc hreg hdense hdis A hklower hkupper'
  exact ⟨k,B,hk,hkm,hbal,heq,hv,hmb,hcol⟩

end SimpleGraph.MultiGraph
