module

public import OverfullWork.InternalEdges

@[expose] public section


namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Construct the actual internal graph plus a bounded selection of crossing
copies at the centre. This seed is not asserted to be regular. -/
theorem exists_center_adjusted_internal (M : MultiGraph V) (L : Finset V) (x : V) (D : ℕ)
    (hx : x ∈ L) (hreg : M.IsRegularOfDegree D)
    (hcross : M.degreeInto L x ≤ M.degreeInto Lᶜ x)
    (hmu : ∀ e, M.mult e ≤ 2) :
    ∃ F : MultiGraph V, (∀ e, F.mult e ≤ M.mult e) ∧
      (∀ u v, (u ∈ L ↔ v ∈ L) → F.mult s(u,v) = M.mult s(u,v)) ∧
      F.degree x = D/2 ∧
      ∀ v, v ≠ x → F.degree v ≤ (M.internalPart L).degree v + 2 := by
  let a : V → ℕ := fun v => if v ∈ Lᶜ then M.mult s(x,v) else 0
  have hs : (∑ v, a v) = M.degreeInto Lᶜ x := by
    simp only [a,degreeInto]
    rw [← sum_filter]
    have hc : univ.filter (fun v => v ∈ Lᶜ) = Lᶜ := by ext; simp
    rw [hc]
  have hdx : M.degreeInto L x + M.degreeInto Lᶜ x = D :=
    (M.degreeInto_add_compl L x).trans (hreg x)
  have hhalf : M.degreeInto L x ≤ D/2 := by omega
  let q := D/2 - M.degreeInto L x
  have hq : q ≤ ∑ v, a v := by rw [hs]; dsimp [q]; omega
  obtain ⟨r,hr,hrs⟩ := bounded_allocation a q hq
  have hr0 : ∀ v ∈ L, r v = 0 := by
    intro v hv
    simpa [a,hv] using hr v
  have hrx := hr0 x hx
  let R := starCopies x r hrx
  have hrM : ∀ v, r v ≤ M.mult s(x,v) := by
    intro v
    exact (hr v).trans (by dsimp [a]; split_ifs <;> omega)
  have hRle : ∀ u v, R.mult s(u,v) ≤ M.mult s(u,v) := by
    intro u v
    dsimp only [R]
    rw [starCopies_mult]
    by_cases hu : u=x
    · subst u
      simpa using hrM v
    · by_cases hv : v=x
      · subst v
        simpa only [if_neg hu,if_true,Sym2.eq_swap] using hrM u
      · simp [hu,hv]
  have hRi : ∀ u v, (u ∈ L ↔ v ∈ L) → R.mult s(u,v)=0 := by
    intro u v huv
    dsimp only [R]
    rw [starCopies_mult]
    by_cases hu : u=x
    · subst u
      simp only [ite_true]
      exact hr0 v (huv.mp hx)
    · by_cases hv : v=x
      · subst v
        simp only [if_neg hu,ite_true]
        exact hr0 u (huv.mpr hx)
      · simp [hu,hv]
  let F := (M.internalPart L).addCopies R
  refine ⟨F,?_,?_,?_,?_⟩
  · intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      change (M.internalPart L).mult s(u,v) + R.mult s(u,v) ≤ M.mult s(u,v)
      rw [internalPart_mult]
      by_cases huv : u ∈ L ↔ v ∈ L
      · rw [if_pos huv,hRi u v huv]; omega
      · rw [if_neg huv]; simpa using hRle u v
  · intro u v huv
    change (M.internalPart L).mult s(u,v) + R.mult s(u,v) = _
    rw [internalPart_covers M L u v huv,hRi u v huv,Nat.add_zero]
  · change ((M.internalPart L).addCopies R).degree x = _
    rw [degree_addCopies,degree_internalPart,if_pos hx]
    have hR : R.degree x=q := by dsimp [R]; rw [degree_starCopies_center,hrs]
    rw [hR]
    dsimp [q]
    omega
  · intro v hv
    change ((M.internalPart L).addCopies R).degree v ≤ _
    rw [degree_addCopies]
    have hR : R.degree v = r v := degree_starCopies_other x r hrx v hv
    rw [hR]
    have h := (hrM v).trans (hmu s(x,v))
    omega

theorem internal_degree_bound (M : MultiGraph V) (L : Finset V) (m D : ℕ)
    (hreg : M.IsRegularOfDegree D)
    (hdis : ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < (m:ℝ)/7) :
    ∀ v, 14*(M.internalPart L).degree v < 7*D+m := by
  intro v
  have hs : (M.degreeInto L v:ℝ)+(M.degreeInto Lᶜ v:ℝ) = (D:ℝ) := by
    exact_mod_cast (M.degreeInto_add_compl L v).trans (hreg v)
  obtain ⟨hl,hr⟩ := abs_lt.mp (hdis v)
  rw [degree_internalPart]
  by_cases hv : v ∈ L
  · rw [if_pos hv]
    have h : 14*(M.degreeInto L v:ℝ)<7*(D:ℝ)+(m:ℝ) := by linarith
    exact_mod_cast h
  · rw [if_neg hv]
    have h : 14*(M.degreeInto Lᶜ v:ℝ)<7*(D:ℝ)+(m:ℝ) := by linarith
    exact_mod_cast h

/-- An unconditional coloured seed from the oriented partition: every
internal copy is coloured, the centre is adjusted, and k< D. Completing
the colour classes to factors is a separate obligation. -/
theorem exists_coloured_internal_seed (M : MultiGraph V) (L : Finset V) (x : V) (m D : ℕ)
    (hm : 24576 ≤ m) (hx : x ∈ L) (hreg : M.IsRegularOfDegree D)
    (hdense : 12*m ≤ 7*D) (hcross : M.degreeInto L x ≤ M.degreeInto Lᶜ x)
    (hmu : ∀ e, M.mult e ≤ 2)
    (hdis : ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < (m:ℝ)/7) :
    ∃ (F : MultiGraph V) (k : ℕ), k<D ∧ 7*k≤6*D ∧
      (∀ e, F.mult e ≤ M.mult e) ∧
      (∀ u v, (u ∈ L ↔ v ∈ L) → F.mult s(u,v) = M.mult s(u,v)) ∧
      F.degree x=D/2 ∧ Nonempty (F.EdgeColoring k) := by
  obtain ⟨F,hF,hFi,hFx,hFo⟩ := M.exists_center_adjusted_internal L x D hx hreg hcross hmu
  have hi := M.internal_degree_bound L m D hreg hdis
  have hdeg : ∀ v, F.degree v ≤ 4*D/7 := by
    intro v
    by_cases hv : v=x
    · subst v
      rw [hFx]
      omega
    · have h := hFo v hv
      have hI := hi v
      have hroom : m+28 ≤ D := by omega
      omega
  let k := 3*(4*D/7)/2
  have hbudget : 7*k≤6*D := by dsimp [k]; omega
  have hk : k<D := by omega
  exact ⟨F,k,hk,hbudget,hF,hFi,hFx,F.exists_edgeColoring_shannon (4*D/7) hdeg⟩

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- From the original dense saturated graph, construct the partition and
an actually coloured internal seed with a strict colour budget. No
regularity of the seed or completion to factors is asserted. -/
theorem exists_dense_point_coloured_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m : ℕ) (hm : 24576 ≤ m) (hcard : Fintype.card V+1=2*m)
    (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    ∃ (L : Finset (Option V)) (F : MultiGraph (Option V)) (k : ℕ),
      L.card=m ∧ Lᶜ.card=m ∧ none ∈ L ∧ some y ∉ L ∧
      k<G.maxDegree ∧ 7*k≤6*G.maxDegree ∧
      (∀ e, F.mult e≤(pointExtension G).mult e) ∧
      (∀ u v, (u ∈ L ↔ v ∈ L) → F.mult s(u,v)=(pointExtension G).mult s(u,v)) ∧
      F.degree none=G.maxDegree/2 ∧ Nonempty (F.EdgeColoring k) := by
  obtain ⟨L,hL,hC,hx,hy,hcross,hdis,_⟩ :=
    exists_dense_oriented_point_partition G y m hm hcard hgap hsat hdense
  have hn : 1≤Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have hreg := regular_of_saturated G hn hsat
  have hd : 12*m≤7*G.maxDegree := by omega
  obtain ⟨F,k,hk,hbudget,hF,hFi,hFx,hcol⟩ :=
    (pointExtension G).exists_coloured_internal_seed L none m G.maxDegree hm hx hreg
      hd hcross (multiplicity_le_two G hgap) hdis
  exact ⟨L,F,k,hL,hC,hx,hy,hk,hbudget,hF,hFi,hFx,hcol⟩

end OverfullWork.MultigraphExtension
