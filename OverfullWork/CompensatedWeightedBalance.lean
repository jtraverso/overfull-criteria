module

public import OverfullWork.VarianceSigningMoments

@[expose] public section


/-! # Small balanced transfers between equitable colour classes

Only the component surplus {-1,0,1} and endpoint load bounds enter this
combinatorial argument. The transfer is exhibited, never assumed.
-/
namespace OverfullWork.CompensatedWeightedBalance
open Finset
open scoped Classical
set_option maxHeartbeats 4000000

/-- An averaged pairing estimate, valid even for nonintegral counts. -/
theorem paired_load_le (p n E F S : ℝ) (hp : 0≤p) (hn : 0≤n) (hS : 0≤S)
    (hcounts : |p-n|≤1) (hE : |E|≤2*S*p) (hF : |F|≤2*S*n)
    (hpairs : n*E+p*F≤0) : E+F≤2*S := by
  have hdiff : |E-F|≤2*S*(p+n) := by
    calc
      _ ≤ |E|+|F|:=abs_sub E F
      _ ≤ _:=by nlinarith only [hE,hF]
  have hcross : (p-n)*(E-F)≤2*S*(p+n) := by
    calc
      _ ≤ |(p-n)*(E-F)|:=le_abs_self _
      _ = |p-n| * |E-F|:=abs_mul _ _
      _ ≤ 1*(2*S*(p+n)):=mul_le_mul hcounts hdiff (abs_nonneg _) (by norm_num)
      _ = _:=by ring
  have hscaled : (p+n)*(E+F)≤2*S*(p+n):=by nlinarith only [hpairs,hcross]
  by_cases hpos : 0<p+n
  · by_contra hh
    have hprod:=mul_pos hpos (show 0<E+F-2*S by linarith)
    nlinarith only [hprod,hscaled]
  · have hp0 : p=0:=by linarith
    have hn0 : n=0:=by linarith
    have he:=(abs_le.mp hE).2
    have hf:=(abs_le.mp hF).2
    simp only [hp0,hn0,mul_zero] at he hf
    linarith

/-- The sum of a finite list of endpoint loads has the expected bound. -/
theorem sum_abs_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ)
    (B : ℝ) (hbound : ∀ i∈s,|e i|≤B) : |∑ i∈s,e i|≤B*s.card := by
  calc
    _ ≤ ∑ i∈s,|e i|:=abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈s,B:=sum_le_sum (fun i hi => hbound i hi)
    _ = _:=by simp only [sum_const,nsmul_eq_mul];ring

/-- If all neutral singles and all opposite-surplus pairs fail to transfer
positive load, at most one unpaired endpoint budget can remain. -/
theorem exists_positive_neutral_piece {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ e : ι → ℝ) (S : ℝ) (hS : 0≤S)
    (hδ : ∀ i∈s,δ i=-1 ∨ δ i=0 ∨ δ i=1)
    (hcounts : |∑ i∈s,δ i|≤1) (hbound : ∀ i∈s,|e i|≤2*S)
    (hgap : 2*S<∑ i∈s,e i) :
    (∃ i∈s,δ i=0 ∧ 0<e i) ∨
      ∃ i∈s,∃ j∈s,δ i=1 ∧ δ j=-1 ∧ 0<e i+e j := by
  classical
  by_contra hn
  push_neg at hn
  have hzero : ∀ i∈s,δ i=0 → e i≤0:=hn.1
  have hpair : ∀ i∈s,∀ j∈s,δ i=1 → δ j=-1 → e i+e j≤0:=hn.2
  let P:=s.filter fun i => δ i=1
  let N:=s.filter fun i => δ i=-1
  have htotalδ : (∑ i∈s,δ i)=(P.card:ℝ)-(N.card:ℝ) := by
    have hi : ∀ i∈s,δ i=(if δ i=1 then 1 else 0)-(if δ i=-1 then 1 else 0) := by
      intro i hi
      rcases hδ i hi with h|h|h <;> norm_num [h]
    calc
      _ = ∑ i∈s,((if δ i=1 then 1 else 0)-(if δ i=-1 then 1 else 0)):=sum_congr rfl hi
      _ = _:=by rw [sum_sub_distrib];simp [P,N]
  have hcounts' : |(P.card:ℝ)-(N.card:ℝ)|≤1:=by rwa [htotalδ] at hcounts
  have hEP : |∑ i∈P,e i|≤2*S*(P.card:ℝ):=
    sum_abs_bound P e (2*S) (fun i hi => hbound i (mem_filter.mp hi).1)
  have hEN : |∑ i∈N,e i|≤2*S*(N.card:ℝ):=
    sum_abs_bound N e (2*S) (fun i hi => hbound i (mem_filter.mp hi).1)
  have hpairs : (N.card:ℝ)*(∑ i∈P,e i)+(P.card:ℝ)*(∑ j∈N,e j)≤0 := by
    have hh : (∑ i∈P,∑ j∈N,(e i+e j))≤0 := by
      apply sum_nonpos
      intro i hi
      apply sum_nonpos
      intro j hj
      exact hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 (mem_filter.mp hi).2 (mem_filter.mp hj).2
    simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] using hh
  have htotal : (∑ i∈s,e i)≤(∑ i∈P,e i)+(∑ i∈N,e i) := by
    calc
      _ ≤ ∑ i∈s,((if δ i=1 then e i else 0)+(if δ i=-1 then e i else 0)) := by
        apply sum_le_sum
        intro i hi
        rcases hδ i hi with h|h|h
        · norm_num [h]
        · simpa [h] using hzero i hi h
        · norm_num [h]
      _ = _:=by rw [sum_add_distrib];simp [P,N,sum_filter]
  have hh:=paired_load_le (P.card:ℝ) (N.card:ℝ) (∑ i∈P,e i) (∑ i∈N,e i) S
    (by positivity) (by positivity) hS hcounts' hEP hEN hpairs
  linarith

/-- Package a positive neutral component or opposite pair as a finite set. -/
theorem transfer_of_piece {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (δ e : ι → ℝ) (B : ℝ)
    (hzero : ∀ i∈s,δ i=0 → e i≤B)
    (hpair : ∀ i∈s,∀ j∈s,δ i=1 → δ j=-1 → e i+e j≤B)
    (hpiece : (∃ i∈s,δ i=0 ∧ 0<e i) ∨
      ∃ i∈s,∃ j∈s,δ i=1 ∧ δ j=-1 ∧ 0<e i+e j) :
    ∃ T : Finset ι,T⊆s ∧ T.card≤2 ∧ (∑ i∈T,δ i)=0 ∧
      0<(∑ i∈T,e i) ∧ (∑ i∈T,e i)≤B := by
  classical
  rcases hpiece with ⟨i,hi,hδi,he⟩|⟨i,hi,j,hj,hδi,hδj,he⟩
  · refine ⟨{i},?_,by simp,?_,?_,?_⟩
    · simpa using hi
    · simpa using hδi
    · simpa using he
    · simpa using hzero i hi hδi
  · have hij : i≠j:=by intro h;subst j;linarith
    refine ⟨{i,j},?_,?_,?_,?_,?_⟩
    · exact insert_subset_iff.mpr ⟨hi,singleton_subset_iff.mpr hj⟩
    · simp [hij]
    · norm_num [hij,hδi,hδj]
    · simpa [hij] using he
    · simpa [hij] using hpair i hi j hj hδi hδj

/-- General endpoint bounds yield a neutral transfer of load at most 4S. -/
theorem exists_balanced_transfer {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ e : ι → ℝ) (S : ℝ) (hS : 0≤S)
    (hδ : ∀ i∈s,δ i=-1 ∨ δ i=0 ∨ δ i=1)
    (hcounts : |∑ i∈s,δ i|≤1) (hbound : ∀ i∈s,|e i|≤2*S)
    (hgap : 2*S<∑ i∈s,e i) :
    ∃ T : Finset ι,T⊆s ∧ T.card≤2 ∧ (∑ i∈T,δ i)=0 ∧
      0<(∑ i∈T,e i) ∧ (∑ i∈T,e i)≤4*S := by
  have hpiece:=exists_positive_neutral_piece s δ e S hS hδ hcounts hbound hgap
  apply transfer_of_piece s δ e (4*S) ?_ ?_ hpiece
  · intro i hi _
    have hh:=(abs_le.mp (hbound i hi)).2
    linarith
  · intro i hi j hj _ _
    have hh:=(abs_le.mp (hbound i hi)).2
    have hh':=(abs_le.mp (hbound j hj)).2
    linarith

/-- Alternating-path signs improve the transfer bound from 4S to 2S.
The colour-class sizes are preserved exactly, not merely up to permutation. -/
theorem exists_signed_balanced_transfer {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ e : ι → ℝ) (S : ℝ) (hS : 0≤S)
    (hδ : ∀ i∈s,δ i=-1 ∨ δ i=0 ∨ δ i=1)
    (hcounts : |∑ i∈s,δ i|≤1)
    (hzero : ∀ i∈s,δ i=0 → |e i|≤2*S)
    (hplus : ∀ i∈s,δ i=1 → 0≤e i ∧ e i≤2*S)
    (hminus : ∀ i∈s,δ i=-1 → -2*S≤e i ∧ e i≤0)
    (hgap : 2*S<∑ i∈s,e i) :
    ∃ T : Finset ι,T⊆s ∧ T.card≤2 ∧ (∑ i∈T,δ i)=0 ∧
      0<(∑ i∈T,e i) ∧ (∑ i∈T,e i)≤2*S := by
  have hbound : ∀ i∈s,|e i|≤2*S := by
    intro i hi
    rcases hδ i hi with h|h|h
    · obtain ⟨hl,hu⟩:=hminus i hi h
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · exact (hzero i hi h).trans (by linarith)
    · obtain ⟨hl,hu⟩:=hplus i hi h
      exact abs_le.mpr ⟨by linarith,hu⟩
  have hpiece:=exists_positive_neutral_piece s δ e S hS hδ hcounts hbound hgap
  apply transfer_of_piece s δ e (2*S) ?_ ?_ hpiece
  · intro i hi h
    have hh:=(abs_le.mp (hzero i hi h)).2
    linarith
  · intro i hi j hj hδi hδj
    have hh:=(hplus i hi hδi).2
    have hh':=(hminus j hj hδj).2
    linarith

/-- Exact compensated load exchange strictly decreases the quadratic energy. -/
theorem swap_energy_decreases (a b τ : ℝ) (hτ : 0<τ) (hgap : τ<a-b) :
    (a-τ)^2+(b+τ)^2<a^2+b^2 := by
  have hp:=mul_pos hτ (show 0<a-b-τ by linarith)
  nlinarith only [hp]

/-- The completely unrestricted endpoint version requested for a gap>6S. -/
theorem exists_balanced_energy_decrease {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (δ e : ι → ℝ) (S a b : ℝ) (hS : 0≤S)
    (hδ : ∀ i∈s,δ i=-1 ∨ δ i=0 ∨ δ i=1)
    (hcounts : |∑ i∈s,δ i|≤1) (hbound : ∀ i∈s,|e i|≤2*S)
    (hload : (∑ i∈s,e i)=a-b) (hgap : 6*S<a-b) :
    ∃ T : Finset ι,T⊆s ∧ T.card≤2 ∧ (∑ i∈T,δ i)=0 ∧
      0<(∑ i∈T,e i) ∧ (∑ i∈T,e i)≤4*S ∧
      (a-(∑ i∈T,e i))^2+(b+(∑ i∈T,e i))^2<a^2+b^2 := by
  obtain ⟨T,hsub,hcard,hneutral,hpos,hupper⟩:=exists_balanced_transfer s δ e S hS hδ hcounts hbound (by rw [hload];linarith)
  exact ⟨T,hsub,hcard,hneutral,hpos,hupper,swap_energy_decreases a b _ hpos (by linarith)⟩

end OverfullWork.CompensatedWeightedBalance
