module

public import OverfullWork.EightEfficientSeed
public import OverfullWork.Gate8F2

@[expose] public section


/-! # Seed construction separated from numerical threshold selection -/
namespace SimpleGraph.MultiGraph

theorem eight_palette_size_of_partition_size (m D r : ℕ) (hm : 1≤m) (hD : D≤2*m)
    (hr : r≤m) (hsize : 30*(m:ℝ)^4<((r:ℝ)/4)^6) :
    15*(2*m:ℝ)*(D/2+r+2*r+1:ℕ)^3<(2*r:ℝ)^6 := by
  have hq : D/2+r+2*r+1≤5*m:=by omega
  have hqR : ((D/2+r+2*r+1:ℕ):ℝ)≤5*(m:ℝ):=by exact_mod_cast hq
  have hpow:=pow_le_pow_left₀ (Nat.cast_nonneg (D/2+r+2*r+1)) hqR 3
  have hmul:=mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤15*(2*(m:ℝ)) by positivity)
  have he : (15:ℝ)*(2*(m:ℝ))*(5*(m:ℝ))^3=3750*(m:ℝ)^4:=by ring
  have hm0 : (0:ℝ)≤(m:ℝ)^4:=by positivity
  norm_num [div_pow] at hsize
  calc
    _ ≤ 3750*(m:ℝ)^4:=by simpa only [he] using hmul
    _ < 64*(r:ℝ)^6:=by linarith
    _ = _ := by ring

end SimpleGraph.MultiGraph

namespace OverfullWork.Gate8G
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_four_seed_of_parameters (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D r : ℕ) (hr : 1≤r) (hrm : r≤m)
    (hsmall : 1000*(16*r+20)≤m) (hsize : 30*(m:ℝ)^4<((r:ℝ)/2)^6) (hcard : Fintype.card V=2*m)
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
    Gate8F2.four_palette_with_reserve m D r k hmD hsmall hk,hbal,heq,hvert,hmiss,hcol⟩

theorem exists_eight_seed_of_parameters (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D r : ℕ) (hr : 1≤r) (hrm : r≤m)
    (hsmall : 10000*(32*r+40)≤m) (hsize : 30*(m:ℝ)^4<((r:ℝ)/4)^6) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8)
    (hmD : m≤D) (hD : D≤2*m) :
    ∃ (r : ℕ) (L : Finset V) (k : ℕ) (C : (M.internalPart L).EdgeColoring k),
      1≤r ∧ r≤m ∧ 10000*(32*r+40)≤m ∧
      L.card=m ∧ Lᶜ.card=m ∧ x∈L ∧ y∉L ∧
      k≤D/2+15*r+8 ∧ m≤2*k ∧ k+300*(32*r+40)<D ∧
      (∀ i,(C.colourGraph i).edgesWithin L=(C.colourGraph i).edgesWithin Lᶜ) ∧
      (∀ i j,(C.colourGraph i).edgesWithin L≤(C.colourGraph j).edgesWithin L+1) ∧
      (∀ v,(C.missingPalette v).card≤16*r+16) ∧
      (∀ i,(C.missingSet L i).card=(C.missingSet Lᶜ i).card) ∧
      ∀ i,(C.missingSet L i).card≤32*r+34 := by
  let p:=MultiGraph.pairEmbedding x y hxy
  have hmuR : ∀ u v,(M.mult s(u,v):ℝ)≤8:=fun u v => by exact_mod_cast hmu s(u,v)
  obtain ⟨L,hL,hB,_,hx,hy,hdis⟩:=M.exists_balanced_degree_partition_center m hcard
    (by omega : 1≤m) p 0 8 (by norm_num) hmuR ((r:ℝ)/4) (by positivity) hsize
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
  have hpalette:=MultiGraph.eight_palette_size_of_partition_size m D r (by omega) hD hrm hsize
  obtain ⟨k,C,hk,hkm,hbal,heq,hvert,hmiss,hcol⟩:=M.exists_efficient_balanced_internal_eight L
    m D r hr hcard hL hB hreg hmu hmD hdis' hpalette
  exact ⟨r,L,k,C,hr,hrm,hsmall,hL,hB,hxL,hyL,hk,hkm,
    (by omega),hbal,heq,hvert,hmiss,hcol⟩


end OverfullWork.Gate8G
