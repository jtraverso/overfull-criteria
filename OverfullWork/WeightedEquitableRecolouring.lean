module

public import OverfullWork.WeightedComponentSwap
public import OverfullWork.CompensatedWeightedBalance

@[expose] public section


/-! # Equitable cardinalities and equitable natural vertex loads

Compensated swaps of at most two bichromatic components preserve every
individual colour-class cardinality and strictly decrease the natural
quadratic load energy whenever two loads differ by more than 2S.
-/
namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def weightedEnergy (C : M.EdgeColoring k) (w : V → ℕ) : ℕ:=∑ i,(C.weightedLoad w i)^2

theorem exists_weighted_energy_drop (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) (heq : C.IsEquitable)
    (hbad : ¬∀ a b,C.weightedLoad w a≤C.weightedLoad w b+2*S) :
    ∃ B : M.EdgeColoring k,(∀ i,B.colourMass i=C.colourMass i) ∧
      B.weightedEnergy w<C.weightedEnergy w := by
  obtain ⟨a,b,hgap⟩ : ∃ a b,C.weightedLoad w b+2*S<C.weightedLoad w a := by
    simpa only [not_forall,not_le] using hbad
  have hab : a≠b:=by intro h;subst b;omega
  let δ : (C.twoColourGraph a b).ConnectedComponent → ℝ:=fun z =>
    ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)-
      ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ)
  let e : (C.twoColourGraph a b).ConnectedComponent → ℝ:=fun z =>
    (C.componentLoad w a b z a:ℝ)-(C.componentLoad w a b z b:ℝ)
  have hδsum : (∑ z,δ z)=(C.colourMass a:ℝ)-(C.colourMass b:ℝ) := by
    dsimp [δ]
    rw [sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,C.sum_component_mass a b a (Or.inl rfl),
      C.sum_component_mass a b b (Or.inr rfl)]
  have hesum : (∑ z,e z)=(C.weightedLoad w a:ℝ)-(C.weightedLoad w b:ℝ) := by
    dsimp [e]
    rw [sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,C.sum_component_load w a b a,C.sum_component_load w a b b]
  have hcounts : |∑ z,δ z|≤1 := by
    rw [hδsum]
    have ha : (C.colourMass a:ℝ)≤(C.colourMass b:ℝ)+1:=by exact_mod_cast heq a b
    have hb : (C.colourMass b:ℝ)≤(C.colourMass a:ℝ)+1:=by exact_mod_cast heq b a
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hδ : ∀ z∈(univ : Finset (C.twoColourGraph a b).ConnectedComponent),δ z=-1 ∨ δ z=0 ∨ δ z=1 := by
    intro z _
    exact C.component_real_card_difference a b z
  have hzero : ∀ z∈(univ : Finset (C.twoColourGraph a b).ConnectedComponent),δ z=0 → |e z|≤2*(S:ℝ) := by
    intro z _ _
    exact C.component_real_load_contrast w S hw a b z
  have hplus : ∀ z∈(univ : Finset (C.twoColourGraph a b).ConnectedComponent),δ z=1 →
      0≤e z ∧ e z≤2*(S:ℝ) := by
    intro z _ hz
    have hreal : ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)=
        ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ)+1:=by dsimp [δ] at hz;linarith
    have hnat : (C.colourGraph a).edgesWithin (C.componentSet a b z)=
        (C.colourGraph b).edgesWithin (C.componentSet a b z)+1:=by exact_mod_cast hreal
    have hl:=C.component_load_nonnegative_of_surplus w a b z hnat
    have hlR : (C.componentLoad w a b z b:ℝ)≤(C.componentLoad w a b z a:ℝ):=by exact_mod_cast hl
    exact ⟨by dsimp [e];linarith,(abs_le.mp (C.component_real_load_contrast w S hw a b z)).2⟩
  have hminus : ∀ z∈(univ : Finset (C.twoColourGraph a b).ConnectedComponent),δ z=-1 →
      -2*(S:ℝ)≤e z ∧ e z≤0 := by
    intro z _ hz
    have hreal : ((C.colourGraph b).edgesWithin (C.componentSet a b z):ℝ)=
        ((C.colourGraph a).edgesWithin (C.componentSet a b z):ℝ)+1:=by dsimp [δ] at hz;linarith
    have hnat : (C.colourGraph b).edgesWithin (C.componentSet a b z)=
        (C.colourGraph a).edgesWithin (C.componentSet a b z)+1:=by exact_mod_cast hreal
    have hl:=C.component_load_nonpositive_of_surplus w a b z hnat
    have hlR : (C.componentLoad w a b z a:ℝ)≤(C.componentLoad w a b z b:ℝ):=by exact_mod_cast hl
    refine ⟨?_,by dsimp [e];linarith⟩
    have hh:=(abs_le.mp (C.component_real_load_contrast w S hw a b z)).1
    dsimp [e]
    linarith only [hh]
  have hgapR : 2*(S:ℝ)<(C.weightedLoad w a:ℝ)-(C.weightedLoad w b:ℝ) := by
    have hh : (C.weightedLoad w b:ℝ)+2*(S:ℝ)<(C.weightedLoad w a:ℝ):=by exact_mod_cast hgap
    linarith
  obtain ⟨T,_,_,hneutral,hpos,hupper⟩:=OverfullWork.CompensatedWeightedBalance.exists_signed_balanced_transfer
    univ δ e (S:ℝ) (by positivity) hδ hcounts hzero hplus hminus (by rw [hesum];exact hgapR)
  let B:=C.swapSelected a b T
  have hmass : ∀ i,B.colourMass i=C.colourMass i := by
    apply C.swapSelected_mass_preserved a b T
    have hr : ((∑ z∈T,(C.colourGraph a).edgesWithin (C.componentSet a b z)):ℝ)=
        ((∑ z∈T,(C.colourGraph b).edgesWithin (C.componentSet a b z)):ℝ) := by
      dsimp [δ] at hneutral
      rw [sum_sub_distrib] at hneutral
      push_cast
      linarith only [hneutral]
    exact_mod_cast hr
  let τ : ℝ:=∑ z∈T,e z
  have hτ : τ=(∑ z∈T,(C.componentLoad w a b z a:ℝ))-(∑ z∈T,(C.componentLoad w a b z b:ℝ)) := by
    dsimp [τ,e]
    rw [sum_sub_distrib]
  have hleft : (B.weightedLoad w a:ℝ)=(C.weightedLoad w a:ℝ)-τ := by
    have hh:=C.swapSelected_load_left w a b T
    have hhR : (B.weightedLoad w a:ℝ)+(∑ z∈T,(C.componentLoad w a b z a:ℝ))=
        (C.weightedLoad w a:ℝ)+(∑ z∈T,(C.componentLoad w a b z b:ℝ)):=by exact_mod_cast hh
    linarith only [hhR,hτ]
  have hright : (B.weightedLoad w b:ℝ)=(C.weightedLoad w b:ℝ)+τ := by
    have hh:=C.swapSelected_load_right w a b T
    have hhR : (B.weightedLoad w b:ℝ)+(∑ z∈T,(C.componentLoad w a b z b:ℝ))=
        (C.weightedLoad w b:ℝ)+(∑ z∈T,(C.componentLoad w a b z a:ℝ)):=by exact_mod_cast hh
    linarith only [hhR,hτ]
  have hdrop : (B.weightedLoad w a)^2+(B.weightedLoad w b)^2<
      (C.weightedLoad w a)^2+(C.weightedLoad w b)^2 := by
    have hh:=OverfullWork.CompensatedWeightedBalance.swap_energy_decreases
      (C.weightedLoad w a:ℝ) (C.weightedLoad w b:ℝ) τ hpos (by linarith only [hupper,hgapR])
    rw [←hleft,←hright] at hh
    exact_mod_cast hh
  have hrest : (∑ i∈(univ.erase a).erase b,(B.weightedLoad w i)^2)=
      ∑ i∈(univ.erase a).erase b,(C.weightedLoad w i)^2 := by
    apply sum_congr rfl
    intro i hi
    have hi':=mem_erase.mp hi
    have hi'':=mem_erase.mp hi'.2
    have hh:=C.swapSelected_load_other w a b T i hi''.1 hi'.1
    rw [show B.weightedLoad w i=C.weightedLoad w i from hh]
  refine ⟨B,hmass,?_⟩
  unfold weightedEnergy
  rw [sum_two_erase _ a b hab,sum_two_erase _ a b hab,hrest]
  omega

/-- Recolour an equitable colouring while preserving the cardinality of
every labelled colour class exactly. -/
theorem exists_weighted_preserving_mass (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) (heq : C.IsEquitable) :
    ∃ B : M.EdgeColoring k,(∀ i,B.colourMass i=C.colourMass i) ∧
      ∀ a b,B.weightedLoad w a≤B.weightedLoad w b+2*S := by
  induction hn : C.weightedEnergy w using Nat.strong_induction_on generalizing C with
  | h n ih =>
    by_cases hgood : ∀ a b,C.weightedLoad w a≤C.weightedLoad w b+2*S
    · exact ⟨C,fun _ => rfl,hgood⟩
    · obtain ⟨B,hmass,hdrop⟩:=C.exists_weighted_energy_drop w S hw heq hgood
      have hBeq : B.IsEquitable := by
        intro a b
        rw [hmass a,hmass b]
        exact heq a b
      obtain ⟨D,hDmass,hDgood⟩:=ih (B.weightedEnergy w) (hn ▸ hdrop) B hBeq rfl
      exact ⟨D,fun i => (hDmass i).trans (hmass i),hDgood⟩

/-- Both unweighted cardinalities and weighted vertex loads can be balanced
on the original palette. The colouring is constructed, not assumed. -/
theorem exists_equitable_weighted (C : M.EdgeColoring k) (w : V → ℕ) (S : ℕ)
    (hw : ∀ v,w v≤S) :
    ∃ B : M.EdgeColoring k,B.IsEquitable ∧
      ∀ a b,B.weightedLoad w a≤B.weightedLoad w b+2*S := by
  obtain ⟨A,hA⟩:=C.exists_equitable
  obtain ⟨B,hmass,hgood⟩:=A.exists_weighted_preserving_mass w S hw hA
  refine ⟨B,?_,hgood⟩
  intro a b
  rw [hmass a,hmass b]
  exact hA a b

end SimpleGraph.MultiGraph.EdgeColoring
