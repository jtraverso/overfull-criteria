module

public import OverfullWork.GeneralApproximateMulticolouring
public import OverfullWork.EfficientSeed

@[expose] public section


/-! # Small-deficiency internal seeds at arbitrary binary depth -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Construct a balanced equitable internal colouring whose palette is
near half the ambient regular degree. Both kinds of missing-colour
bounds are conclusions, not hypotheses about a chosen colouring. -/
theorem exists_efficient_balanced_internal_power_two (M : MultiGraph V) (S : Finset V)
    (j m D r : ℕ) (hr : 1≤r) (hcard : Fintype.card V=2*m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hreg : M.IsRegularOfDegree D)
    (hmu : ∀ e,M.mult e≤2^j) (hdense : m≤D)
    (hdis : ∀ v, |(M.degreeInto S v:ℝ)-(M.degreeInto Sᶜ v:ℝ)|<2*(r:ℝ))
    (hsize : 15*(2*m:ℝ)*(D/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ (k : ℕ) (C : (M.internalPart S).EdgeColoring k),
      k≤D/2+(2*2^j-1)*r+2^j ∧ m≤2*k ∧
      (∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i j,(C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1) ∧
      (∀ v,(C.missingPalette v).card≤(2*2^j)*(r+1)) ∧
      (∀ i,(C.missingSet S i).card=(C.missingSet Sᶜ i).card) ∧
      ∀ i,(C.missingSet S i).card≤2*((2*2^j)*(r+1))+2 := by
  let d:=D/2+r
  let k:=binaryPalette j d r
  have hbounds : ∀ v, D<2*(M.internalPart S).degree v+2*r ∧
      (M.internalPart S).degree v≤d := by
    intro v
    have hs : (M.degreeInto S v:ℝ)+(M.degreeInto Sᶜ v:ℝ)=(D:ℝ) := by
      exact_mod_cast (M.degreeInto_add_compl S v).trans (hreg v)
    obtain ⟨hl,hu⟩:=abs_lt.mp (hdis v)
    have hA : D<2*M.degreeInto S v+2*r ∧ 2*M.degreeInto S v<D+2*r := by
      constructor
      · exact_mod_cast (show (D:ℝ)<2*(M.degreeInto S v:ℝ)+2*(r:ℝ) by linarith)
      · exact_mod_cast (show 2*(M.degreeInto S v:ℝ)<(D:ℝ)+2*(r:ℝ) by linarith)
    have hB : D<2*M.degreeInto Sᶜ v+2*r ∧ 2*M.degreeInto Sᶜ v<D+2*r := by
      constructor
      · exact_mod_cast (show (D:ℝ)<2*(M.degreeInto Sᶜ v:ℝ)+2*(r:ℝ) by linarith)
      · exact_mod_cast (show 2*(M.degreeInto Sᶜ v:ℝ)<(D:ℝ)+2*(r:ℝ) by linarith)
    rw [degree_internalPart]
    by_cases hv : v∈S
    · rw [if_pos hv]; dsimp [d]; omega
    · rw [if_neg hv]; dsimp [d]; omega
  have hmuI : ∀ e,(M.internalPart S).mult e≤2^j :=
    fun e => (M.internalPart_le S e).trans (hmu e)
  have hsize' : 15*(Fintype.card V:ℝ)*(d+j*r+1:ℕ)^3<(2*r:ℝ)^6 := by
    simpa only [hcard,Nat.cast_mul,Nat.cast_ofNat,d] using hsize
  obtain ⟨A⟩ := exists_edgeColoring_power_two_of_moment j (M.internalPart S) d r hmuI
    (fun v => (hbounds v).2) hsize'
  have hA : Nonempty ((M.restrict S).EdgeColoring k) := by
    rw [←M.internalPart_restrict S]
    exact ⟨A.restrictColouring S⟩
  have hB : Nonempty ((M.restrict Sᶜ).EdgeColoring k) := by
    rw [←M.internalPart_restrict_compl S]
    exact ⟨A.restrictColouring Sᶜ⟩
  obtain ⟨C,hbal,heq⟩:=M.exists_balanced_internal_colouring S D k hreg (hS.trans hSc.symm) hA hB
  have hklower : d+1≤k:=binary_palette_ge_degree j d r hr
  have hkm : m≤2*k := by dsimp [d] at hklower; omega
  have hk : 0<k := by omega
  have hkupper : k+2*r≤d+2*r*2^j+2^j:=binary_palette_bound j d r
  have hpow : 1≤2^j:=Nat.one_le_pow j 2 (by omega)
  have hsub : 2*2^j-1+1=2*2^j:=by omega
  have hDhalf : 2*(D/2)≤D:=by omega
  have hvertex : ∀ v,(C.missingPalette v).card≤(2*2^j)*(r+1) := by
    intro v
    have h:=C.missingPalette_card_add_degree v
    have hd:=(hbounds v).1
    dsimp [d] at hkupper
    nlinarith only [h,hd,hkupper,hpow,hDhalf]
  have hpalette : k≤D/2+(2*2^j-1)*r+2^j := by
    dsimp [d] at hkupper
    nlinarith only [hkupper,hsub]
  refine ⟨k,C,hpalette,hkm,hbal,heq,hvertex,?_,?_⟩
  · exact C.missingSet_card_eq_of_internal_balance S (hS.trans hSc.symm) hbal
  · have h:=C.missingSet_card_le_of_vertex_deficiency S m ((2*2^j)*(r+1)) hS hkm hk
      (fun v _ => hvertex v) (fun i => by simpa only [hS] using C.internal_missing_count S i) heq
    intro i
    have hi:=h i
    omega

end SimpleGraph.MultiGraph
