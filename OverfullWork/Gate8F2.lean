module

public import OverfullWork.FourSeedParameters
public import OverfullWork.MultigraphPartition
public import OverfullWork.FirstPhaseSeed

@[expose] public section


/-! # Constructed small-deficiency seed for multiplicity four

The partition, colouring and error budget are conclusions. The colour
classes are still partial matchings: regular completion belongs to 8F3.
-/
namespace OverfullWork.Gate8F2
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_efficient_four_seed (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 1000000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4)
    (hmD : m≤D) (hD : D≤2*m) :
    ∃ (r : ℕ) (L : Finset V) (k : ℕ) (C : (M.internalPart L).EdgeColoring k),
      1≤r ∧ r≤m ∧ 1000*(16*r+20)≤m ∧
      L.card=m ∧ Lᶜ.card=m ∧ x∈L ∧ y∉L ∧
      k≤D/2+7*r+4 ∧ m≤2*k ∧ k+300*(16*r+20)<D ∧
      (∀ i,(C.colourGraph i).edgesWithin L=(C.colourGraph i).edgesWithin Lᶜ) ∧
      (∀ i j,(C.colourGraph i).edgesWithin L≤(C.colourGraph j).edgesWithin L+1) ∧
      (∀ v,(C.missingPalette v).card≤8*r+8) ∧
      (∀ i,(C.missingSet L i).card=(C.missingSet Lᶜ i).card) ∧
      ∀ i,(C.missingSet L i).card≤16*r+18 := by
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=explicit_seed_parameters m hm
  let p:=MultiGraph.pairEmbedding x y hxy
  have hmuR : ∀ u v,(M.mult s(u,v):ℝ)≤4:=fun u v => by exact_mod_cast hmu s(u,v)
  obtain ⟨L,hL,hB,_,hx,hy,hdis⟩:=M.exists_balanced_degree_partition_center m hcard
    (by omega : 1≤m) p 0 4 (by norm_num) hmuR ((r:ℝ)/2) (by positivity) hsize
  have hp : p (0,true)=x := by
    change (if (true : Bool) then x else y)=x
    simp only [ite_true]
  have hpy : p (0,false)=y := by
    change (if (false : Bool) then x else y)=y
    simp only [Bool.false_eq_true,if_false]
  have hxL : x∈L:=hp ▸ hx
  have hyL : y∉L:=hpy ▸ hy
  have hdis' : ∀ v, |(M.degreeInto L v:ℝ)-(M.degreeInto Lᶜ v:ℝ)|<2*(r:ℝ) := by
    intro v
    have hh:=hdis v
    convert hh using 1
    ring
  have hsize' : 30*(m:ℝ)^4<(r:ℝ)^6 := by
    apply hsize.trans_le
    exact pow_le_pow_left₀ (by positivity) (by have hh : (0:ℝ)≤(r:ℝ):=Nat.cast_nonneg r;linarith) 6
  have hpalette:=MultiGraph.four_palette_size_of_partition_size m D r (by omega) hD hrm hsize'
  obtain ⟨k,C,hk,hkm,hbal,heq,hvert,hmiss,hcol⟩:=M.exists_efficient_balanced_internal_four L
    m D r hr hcard hL hB hreg hmu hmD hdis' hpalette
  exact ⟨r,L,k,C,hr,hrm,hsmall,hL,hB,hxL,hyL,hk,hkm,
    four_palette_with_reserve m D r k hmD hsmall hk,hbal,heq,hvert,hmiss,hcol⟩

/-- The constructed seed satisfies the actual initial completion
invariant, with a small error t and room for the sparse residue palette.
This proves an initial state, not termination or regular completion. -/
theorem exists_four_initial_state (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 1000000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4)
    (hmD : m≤D) (hD : D≤2*m) :
    ∃ (t : ℕ) (L : Finset V) (k : ℕ) (C : (M.internalPart L).EdgeColoring k),
      0<t ∧ 1000*t≤m ∧ L.card=m ∧ Lᶜ.card=m ∧ x∈L ∧ y∉L ∧
      k≤D/2+t ∧ m≤2*k ∧ k+300*t<D ∧
      (∀ v,(C.missingPalette v).card≤t) ∧
      (∀ i,(C.missingSet L i).card≤t) ∧
      (MultiGraph.PartialColouring.internalSeed L C).CompletionInvariant L x m t := by
  obtain ⟨r,L,k,C,hr,_,hsmall,hL,hB,hx,hy,hk,hkm,hreserve,hbal,_,hvert,_,hcol⟩:=
    exists_efficient_four_seed M x y hxy m D hm hcard hreg hmu hmD hD
  let t:=16*r+20
  have hv : ∀ v,(C.missingPalette v).card≤t:=by
    intro v
    have hh:=hvert v
    dsimp [t]
    omega
  have hc : ∀ i,(C.missingSet L i).card≤t:=by
    intro i
    have hh:=hcol i
    dsimp [t]
    omega
  have hkt : k≤D/2+t:=by dsimp [t];omega
  exact ⟨t,L,k,C,by dsimp [t];omega,hsmall,hL,hB,hx,hy,hkt,hkm,hreserve,hv,hc,
    MultiGraph.PartialColouring.internalSeed_invariant L x m t hL C hbal hv hc⟩

end OverfullWork.Gate8F2
