module

public import OverfullWork.MultigraphPartition
public import OverfullWork.SimpleColouringBridge
public import OverfullWork.CanonicalRegularization

@[expose] public section


/-! # Degree discrepancy under actual regular completion

The partition is constructed on a contained simple graph. The extra
copies are charged to their exact remaining degree at each vertex.
No simplicity of crossing edges or bipartite robust expansion is asserted.
The existing sixth-moment partition theorem is reused unchanged.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem degreeInto_addCopies (M R : MultiGraph V) (A : Finset V) (v : V) :
    (M.addCopies R).degreeInto A v=M.degreeInto A v+R.degreeInto A v := by
  simp only [degreeInto,addCopies,sum_add_distrib]

theorem degreeInto_le_degree (M : MultiGraph V) (A : Finset V) (v : V) :
    M.degreeInto A v≤M.degree v := by
  have hh:=M.degreeInto_add_compl A v
  omega

/-- The imbalance of added edges is at most their degree at the vertex. -/
theorem discrepancy_addCopies_le (M R : MultiGraph V) (A : Finset V) (v : V) :
    |((M.addCopies R).degreeInto A v:ℝ)-((M.addCopies R).degreeInto Aᶜ v:ℝ)|≤
      |(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|+R.degree v := by
  rw [degreeInto_addCopies,degreeInto_addCopies]
  push_cast
  have hsplit:R.degreeInto A v+R.degreeInto Aᶜ v=R.degree v:=R.degreeInto_add_compl A v
  have hr:|(R.degreeInto A v:ℝ)-(R.degreeInto Aᶜ v:ℝ)|≤(R.degree v:ℝ):=by
    have hr₁:0≤(R.degreeInto A v:ℝ):=Nat.cast_nonneg _
    have hr₂:0≤(R.degreeInto Aᶜ v:ℝ):=Nat.cast_nonneg _
    have he:(R.degreeInto A v:ℝ)+(R.degreeInto Aᶜ v:ℝ)=(R.degree v:ℝ):=by exact_mod_cast hsplit
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ = |((M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ))+
          ((R.degreeInto A v:ℝ)-(R.degreeInto Aᶜ v:ℝ))| := by congr 1;ring
    _ ≤ |(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|+
      |(R.degreeInto A v:ℝ)-(R.degreeInto Aᶜ v:ℝ)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Completion charges only the missing degree relative to the contained
simple base, even when the added edges have large multiplicity. -/
theorem regular_discrepancy_from_simple (M : MultiGraph V) (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hreg : M.IsRegularOfDegree D)
    (hsub : ∀e,(ofSimpleGraph G).mult e≤M.mult e) (A : Finset V) (v : V) :
    |(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|≤
      |((ofSimpleGraph G).degreeInto A v:ℝ)-((ofSimpleGraph G).degreeInto Aᶜ v:ℝ)|+
        ((D-G.degree v:ℕ):ℝ) := by
  let R:=M.subtractCopies (ofSimpleGraph G)
  have hid:(ofSimpleGraph G).addCopies R=M:=add_subtract_of_le M _ hsub
  have hd:R.degree v=D-G.degree v:=by
    have hh:=degree_subtract_add M (ofSimpleGraph G) hsub v
    rw [hreg v,degree_ofSimpleGraph] at hh
    dsimp only [R]
    omega
  have h:=discrepancy_addCopies_le (ofSimpleGraph G) R A v
  rwa [hid,hd] at h

/-- The order threshold is chosen before the vertex type, graph,
regular completion and prescribed separated pairs. The error of a
completed vertex is bounded by the partition tolerance plus its exact
deficit from the contained simple base. -/
theorem exists_uniform_regular_completion_partition (ε : ℝ) (hε : 0<ε) :
    ∃m₀ : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (M : MultiGraph V) (m D : ℕ),
      m₀≤m → Fintype.card V=2*m → M.IsRegularOfDegree D →
      (∀e,(ofSimpleGraph G).mult e≤M.mult e) →
      ∀{t : ℕ},t≤m → ∀p : (Fin t×Bool) ↪ V,
      ∃A : Finset V,A.card=m ∧ Aᶜ.card=m ∧
        (∀i,(p (i,true)∈A ↔ p (i,false)∉A)) ∧
        ∀v,|(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|<
          ε*(m:ℝ)+((D-G.degree v:ℕ):ℝ) := by
  obtain ⟨m₀,hm₀⟩:=eventually_sixth_size ε hε
  refine ⟨m₀,?_⟩
  intro V _ _ G _ M m D hm hcard hreg hsub t ht p
  have hmu:∀v w,((ofSimpleGraph G).mult s(v,w):ℝ)≤1:=by
    intro v w
    simp only [ofSimpleGraph]
    split_ifs <;> norm_num
  obtain ⟨A,hA,hAc,hsep,hdis⟩:=(ofSimpleGraph G).exists_balanced_degree_partition
    m hcard ht p 1 (by norm_num) hmu (ε*(m:ℝ)) (by positivity) (hm₀ m hm)
  refine ⟨A,hA,hAc,hsep,?_⟩
  intro v
  have hb:=regular_discrepancy_from_simple M G D hreg hsub A v
  have hd:=hdis v
  simp only [one_mul] at hd
  linarith

/-- The support loses only the excess multiplicity at the star centre
when viewed from an ordinary vertex. -/
theorem star_degree_le_support_add (M : MultiGraph V) (x v : V)
    (hstar : M.IsStarAt x) (hv : v≠x) (K : ℕ)
    (hmu : M.mult s(x,v)≤K) : M.degree v≤M.supportGraph.degree v+K := by
  let G:=ofSimpleGraph M.supportGraph
  have hsub:∀e,G.mult e≤M.mult e:=by
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [G,ofSimpleGraph,SimpleGraph.mem_edgeSet,supportGraph]
      split_ifs <;> omega
  have hsum:∑w : V,(M.mult s(v,w)-G.mult s(v,w))≤K:=by
    have hrest:∀w,w≠x → M.mult s(v,w)-G.mult s(v,w)=0:=by
      intro w hw
      have hh:=hstar v w hv hw
      simp only [G,ofSimpleGraph,SimpleGraph.mem_edgeSet,supportGraph]
      split_ifs <;> omega
    rw [sum_eq_single x]
    · change M.mult s(v,x)-G.mult s(v,x)≤K
      have hh:M.mult s(v,x)≤K:=by simpa only [Sym2.eq_swap] using hmu
      omega
    · intro w _ hw
      exact hrest w hw
    · simp
  have hh:=degree_subtract_add M G hsub v
  have hR:(M.subtractCopies G).degree v=∑w : V,(M.mult s(v,w)-G.mult s(v,w)):=by
    rw [degree_eq_sum_mult]
    rfl
  rw [hR,degree_ofSimpleGraph] at hh
  omega

end SimpleGraph.MultiGraph

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset
open scoped Classical
variable {m : ℕ} {D : MultiGraph (Fin m×Bool)} {Δ : ℕ}

/-- The actual added layers have exactly the original vertex deficit. -/
theorem Completion.added_degree (c : Completion D Δ) (v : Fin m×Bool) :
    (c.L.addCopies c.N).degree v=Δ-D.degree v := by
  have hh:=c.regular v
  rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
  rw [MultiGraph.degree_addCopies]
  omega

theorem Completion.partition_discrepancy (c : Completion D Δ)
    (A : Finset (Fin m×Bool)) (v : Fin m×Bool) :
    |(((D.addCopies c.L).addCopies c.N).degreeInto A v:ℝ)-
        (((D.addCopies c.L).addCopies c.N).degreeInto Aᶜ v:ℝ)|≤
      |(D.degreeInto A v:ℝ)-(D.degreeInto Aᶜ v:ℝ)|+((Δ-D.degree v:ℕ):ℝ) := by
  have hassoc:(D.addCopies c.L).addCopies c.N=D.addCopies (c.L.addCopies c.N):=by
    apply MultiGraph.ext_mult
    intro e
    exact Nat.add_assoc _ _ _
  rw [hassoc]
  have hh:=MultiGraph.discrepancy_addCopies_le D (c.L.addCopies c.N) A v
  rwa [c.added_degree v] at hh

theorem Completion.simple_base_contained (c : Completion D Δ) :
    ∀e,(MultiGraph.ofSimpleGraph D.supportGraph).mult e≤
      ((D.addCopies c.L).addCopies c.N).mult e := by
  intro e
  induction e using Sym2.inductionOn with
  | hf a b =>
    simp only [MultiGraph.ofSimpleGraph,SimpleGraph.mem_edgeSet,MultiGraph.supportGraph,
      MultiGraph.addCopies]
    split_ifs <;> omega

/-- A genuine partition of the actual canonical completion, with the
remaining error displayed as deficit from the simple support of D. -/
theorem exists_uniform_canonical_partition (ε : ℝ) (hε : 0<ε) :
    ∃m₀ : ℕ,∀n : ℕ,∀D : MultiGraph (Fin (n+1)×Bool),∀Δ : ℕ,
      ∀c : Completion D Δ,m₀≤n+1 →
      ∀{t : ℕ},t≤n+1 → ∀p : (Fin t×Bool) ↪ (Fin (n+1)×Bool),
      ∃A : Finset (Fin (n+1)×Bool),A.card=n+1 ∧ Aᶜ.card=n+1 ∧
        (∀i,(p (i,true)∈A ↔ p (i,false)∉A)) ∧
        ∀v,|(((D.addCopies c.L).addCopies c.N).degreeInto A v:ℝ)-
            (((D.addCopies c.L).addCopies c.N).degreeInto Aᶜ v:ℝ)|<
          ε*((n+1:ℕ):ℝ)+((Δ-D.supportGraph.degree v:ℕ):ℝ) := by
  obtain ⟨m₀,hm₀⟩:=MultiGraph.exists_uniform_regular_completion_partition.{0} ε hε
  refine ⟨m₀,?_⟩
  intro n D Δ c hm t ht p
  exact hm₀ D.supportGraph ((D.addCopies c.L).addCopies c.N) (n+1) Δ hm
    (by simp [Nat.mul_comm]) c.regular c.simple_base_contained ht p

/-- At every ordinary vertex of a star base, the support deficit is
bounded by the original deficit plus its centre multiplicity bound. -/
theorem Completion.support_deficit_le (c : Completion D Δ)
    (x v : Fin m×Bool) (hstar : D.IsStarAt x) (hv : v≠x) (K : ℕ)
    (hmu : D.mult s(x,v)≤K) :
    Δ-D.supportGraph.degree v≤(Δ-D.degree v)+K := by
  have hh:=MultiGraph.star_degree_le_support_add D x v hstar hv K hmu
  have hreg:=c.regular v
  rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hreg
  omega

end OverfullWork.CanonicalRegularization
