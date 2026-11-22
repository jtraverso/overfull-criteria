module

public import OverfullWork.UniformSamplingBudget
public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Semidegree concentration for actual induced Mathlib digraphs under
uniform fixed-cardinality vertex sampling. This does not assert robust
expansion of the induced digraph: that requires the reduced-graph step. -/
namespace OverfullWork.InducedDigraphSampling
open Finset Real DirectedRobustExpansion UniformSubsetSampling
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

def induced (D : Digraph V) (X : Finset V) : Digraph X where
  Adj u v := D.Adj u.val v.val

noncomputable def inProfile (D : Digraph V) (v : V) : Finset V :=
  univ.filter fun u => D.Adj u v

noncomputable def outProfile (D : Digraph V) (v : V) : Finset V :=
  univ.filter fun u => D.Adj v u

theorem inProfile_card (D : Digraph V) (v : V) : (inProfile D v).card=inDegree D v := rfl

theorem outProfile_card (D : Digraph V) (v : V) : (outProfile D v).card=outDegree D v := rfl

theorem induced_inDegree (D : Digraph V) (X : Finset V) (v : X) :
    inDegree (induced D X) v=(X ∩ inProfile D v.val).card := by
  unfold inDegree inNeighbours
  apply card_bij (fun u _ => u.val)
  · intro u hu
    exact mem_inter.mpr ⟨u.property,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩⟩
  · intro u _ w _ h
    exact Subtype.ext h
  · intro u hu
    refine ⟨⟨u,(mem_inter.mp hu).1⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_inter.mp hu).2).2⟩

theorem induced_outDegree (D : Digraph V) (X : Finset V) (v : X) :
    outDegree (induced D X) v=(X ∩ outProfile D v.val).card := by
  unfold outDegree
  apply card_bij (fun u _ => u.val)
  · intro u hu
    exact mem_inter.mpr ⟨u.property,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩⟩
  · intro u _ w _ h
    exact Subtype.ext h
  · intro u hu
    refine ⟨⟨u,(mem_inter.mp hu).1⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_inter.mp hu).2).2⟩

noncomputable def profiles (D : Digraph V) (vb : V × Bool) : Finset V :=
  if vb.2 then outProfile D vb.1 else inProfile D vb.1

def BadSemidegreeSample (D : Digraph V) (k : ℕ) (ε : ℝ) (X : Finset V) : Prop :=
  (∃ v : X,ε*(k:ℝ) ≤ |(inDegree (induced D X) v:ℝ)-
    ((k:ℝ)/(Fintype.card V:ℝ))*(inDegree D v.val:ℝ)|) ∨
  (∃ v : X,ε*(k:ℝ) ≤ |(outDegree (induced D X) v:ℝ)-
    ((k:ℝ)/(Fintype.card V:ℝ))*(outDegree D v.val:ℝ)|)

end OverfullWork.InducedDigraphSampling

namespace OverfullWork.InducedDigraphSampling
open Finset Real DirectedRobustExpansion UniformSubsetSampling
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem exists_uniform_semidegree_threshold (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] (D : Digraph V) (k : ℕ),
      N ≤ Fintype.card V → k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
      probability k (BadSemidegreeSample D k ε) ≤ 1/(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_uniform_profile_threshold.{u,u} 2 (ε*c) (by norm_num) (mul_pos hε hc)
  refine ⟨N,?_⟩
  intro V _ D k hn hk hSize
  have hTail := hN (profiles D) k hn hk (by simp [Fintype.card_prod,Fintype.card_bool,mul_comm])
  have hScale : (ε*c)*(Fintype.card V:ℝ) ≤ ε*(k:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hSize hε.le
    nlinarith only [hh]
  apply (probability_mono k ?_).trans hTail
  intro X hBad
  rcases hBad with ⟨v,hv⟩|⟨v,hv⟩
  · refine ⟨(v.val,false),?_⟩
    change (ε*c)*(Fintype.card V:ℝ) ≤
      |((X ∩ inProfile D v.val).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((inProfile D v.val).card:ℝ)|
    rw [inProfile_card,←induced_inDegree D X v]
    exact hScale.trans hv
  · refine ⟨(v.val,true),?_⟩
    change (ε*c)*(Fintype.card V:ℝ) ≤
      |((X ∩ outProfile D v.val).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((outProfile D v.val).card:ℝ)|
    rw [outProfile_card,←induced_outDegree D X v]
    exact hScale.trans hv

def BadMinimumSample {V : Type u} [Fintype V] (D : Digraph V)
    (k : ℕ) (β : ℝ) (X : Finset V) : Prop :=
  (∃ v : X,(inDegree (induced D X) v:ℝ) ≤ β*(k:ℝ)) ∨
  (∃ v : X,(outDegree (induced D X) v:ℝ) ≤ β*(k:ℝ))

theorem exists_uniform_minimum_semidegree_threshold (c α ε : ℝ)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] (D : Digraph V) (k : ℕ),
      N ≤ Fintype.card V → k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      probability k (BadMinimumSample D k (α-ε)) ≤ 1/(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_uniform_semidegree_threshold.{u} c ε hc hε
  refine ⟨max N 2,?_⟩
  intro V _ D k hn hk hSize hIn hOut
  have hTail := hN D k (by omega) hk hSize
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  let p := (k:ℝ)/(Fintype.card V:ℝ)
  have hp : 0 ≤ p := by dsimp only [p];positivity
  have hId : p*(α*(Fintype.card V:ℝ))=α*(k:ℝ) := by dsimp only [p];field_simp
  have hExpected : ∀ d : ℝ,α*(Fintype.card V:ℝ) ≤ d → α*(k:ℝ) ≤ p*d := by
    intro d hd
    rw [←hId]
    exact mul_le_mul_of_nonneg_left hd hp
  apply (probability_mono k ?_).trans hTail
  intro X hBad
  rcases hBad with ⟨v,hv⟩|⟨v,hv⟩
  · left
    refine ⟨v,?_⟩
    have hh := hExpected _ (hIn v.val)
    have hAbs := neg_le_abs ((inDegree (induced D X) v:ℝ)-p*(inDegree D v.val:ℝ))
    change ε*(k:ℝ) ≤ |(inDegree (induced D X) v:ℝ)-p*(inDegree D v.val:ℝ)|
    nlinarith only [hh,hv,hAbs]
  · right
    refine ⟨v,?_⟩
    have hh := hExpected _ (hOut v.val)
    have hAbs := neg_le_abs ((outDegree (induced D X) v:ℝ)-p*(outDegree D v.val:ℝ))
    change ε*(k:ℝ) ≤ |(outDegree (induced D X) v:ℝ)-p*(outDegree D v.val:ℝ)|
    nlinarith only [hh,hv,hAbs]

end OverfullWork.InducedDigraphSampling
