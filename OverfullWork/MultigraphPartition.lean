module

public import OverfullWork.PairedPartition
public import OverfullWork.StarFactorizationSetup
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section


/-!
# Balanced degree partitions for bounded-multiplicity multigraphs

The partition is proved to exist; only numerical size and disjointness of
the prescribed pairs are assumed. This does not construct the regular
coloured internal cover needed by FactorizationAssembly.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def degreeInto (M : MultiGraph V) (L : Finset V) (v : V) : ℕ :=
  ∑ u ∈ L, M.mult s(v,u)

theorem degreeInto_add_compl (M : MultiGraph V) (L : Finset V) (v : V) :
    M.degreeInto L v + M.degreeInto Lᶜ v = M.degree v := by
  rw [degreeInto, degreeInto, sum_add_sum_compl, degree_eq_sum_mult]

theorem degreeInto_deviation (M : MultiGraph V) (L : Finset V) (v : V) :
    |2 * (M.degreeInto L v:ℝ) - (M.degree v:ℝ)| =
      |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| := by
  have h := M.degreeInto_add_compl L v
  have hr : (M.degreeInto L v:ℝ) + (M.degreeInto Lᶜ v:ℝ) = (M.degree v:ℝ) := by
    exact_mod_cast h
  congr 1
  linarith

/-- All prescribed pairs are separated, both sides have size m, and every
weighted degree discrepancy is less than K*b. The size criterion has no
dependence on the graph beyond its order and the multiplicity bound. -/
theorem exists_balanced_degree_partition (M : MultiGraph V) (m : ℕ)
    (hcard : Fintype.card V = 2*m) {t : ℕ} (ht : t ≤ m) (p : (Fin t × Bool) ↪ V)
    (K : ℝ) (hK : 0 < K) (hmu : ∀ u v, (M.mult s(u,v):ℝ) ≤ K)
    (b : ℝ) (hb : 0 ≤ b) (hsize : 30 * (m:ℝ)^4 < b^6) :
    ∃ L : Finset V, L.card = m ∧ Lᶜ.card = m ∧
      (∀ i, (p (i,true) ∈ L ↔ p (i,false) ∉ L)) ∧
      ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < K*b := by
  let w : V → V → ℝ := fun v u => (M.mult s(v,u):ℝ) / K
  have hw : ∀ v u, 0 ≤ w v u ∧ w v u ≤ 1 := by
    intro v u
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hK.le
    · exact (div_le_one hK).mpr (hmu v u)
  have hsize' : 15 * (Fintype.card V:ℝ) * (m:ℝ)^3 < b^6 := by
    rw [hcard]
    push_cast
    nlinarith [hsize]
  obtain ⟨L,hL,hC,hsep,hwL⟩ := OverfullWork.PairedPartition.exists_balanced_partition_prescribed
    hcard ht p w hw b hb hsize'
  refine ⟨L,hL,hC,hsep,fun v => ?_⟩
  have h := hwL v
  have he : (∑ u ∈ L, w v u) - (∑ u ∈ Lᶜ, w v u) =
      ((M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)) / K := by
    simp only [w, degreeInto, Nat.cast_sum, div_eq_mul_inv, sub_mul, sum_mul]
  rw [he, abs_div, abs_of_pos hK] at h
  have hc := (div_lt_iff₀ hK).mp h
  simpa only [mul_comm] using hc

/-- Name the side containing the prescribed centre; all other separation
and degree bounds survive exchanging the two sides. -/
theorem exists_balanced_degree_partition_center (M : MultiGraph V) (m : ℕ)
    (hcard : Fintype.card V = 2*m) {t : ℕ} (ht : t ≤ m) (p : (Fin t × Bool) ↪ V)
    (i₀ : Fin t) (K : ℝ) (hK : 0 < K) (hmu : ∀ u v, (M.mult s(u,v):ℝ) ≤ K)
    (b : ℝ) (hb : 0 ≤ b) (hsize : 30 * (m:ℝ)^4 < b^6) :
    ∃ L : Finset V, L.card = m ∧ Lᶜ.card = m ∧
      (∀ i, (p (i,true) ∈ L ↔ p (i,false) ∉ L)) ∧
      p (i₀,true) ∈ L ∧ p (i₀,false) ∉ L ∧
      ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < K*b := by
  obtain ⟨L,hL,hC,hsep,hdeg⟩ := M.exists_balanced_degree_partition m hcard ht p K hK hmu b hb hsize
  by_cases hx : p (i₀,true) ∈ L
  · exact ⟨L,hL,hC,hsep,hx,(hsep i₀).mp hx,hdeg⟩
  · refine ⟨Lᶜ,hC,by simpa using hL,?_,by simpa,?_,?_⟩
    · intro i
      simpa only [mem_compl, not_not] using (hsep i).not
    · simpa only [mem_compl, not_not] using not_not.mp ((hsep i₀).not.mp hx)
    · intro v
      simpa only [compl_compl, abs_sub_comm] using hdeg v

/-- An explicit choice for the asymptotic size: b=m/16 works for m>=24576.
The constant is deliberately elementary, not an optimized threshold. -/
theorem sixth_size_of_large (m : ℕ) (hm : 24576 ≤ m) :
    30 * (m:ℝ)^4 < ((m:ℝ)/16)^6 := by
  have hm' : (24576:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hp : 0 < (m:ℝ)^4 := by positivity
  have hsq : (503316480:ℝ) < (m:ℝ)^2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hsq hp
  rw [div_pow]
  norm_num
  nlinarith [hmul]

/-- The finite sixth-moment criterion gives arbitrarily small linear
discrepancy for all sufficiently large orders. -/
theorem eventually_sixth_size (ε : ℝ) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 30 * (m:ℝ)^4 < (ε*(m:ℝ))^6 := by
  obtain ⟨m₀,hm₀⟩ := exists_nat_gt (6/ε^3)
  refine ⟨m₀,fun m hm => ?_⟩
  have hm' : (m₀:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hlarge : 6/ε^3 < (m:ℝ) := hm₀.trans_le hm'
  have hmul : 6 < ε^3*(m:ℝ) := by
    have h := (div_lt_iff₀ (pow_pos hε 3)).mp hlarge
    nlinarith
  have hpos : (0:ℝ) < (m:ℝ) := by
    have hn : (0:ℝ) < 6/ε^3 := by positivity
    exact hn.trans hlarge
  have hsq : (30:ℝ) < (ε^3*(m:ℝ))^2 := by nlinarith [sq_nonneg (ε^3*(m:ℝ)-6)]
  calc
    _ < (ε^3*(m:ℝ))^2*(m:ℝ)^4 := mul_lt_mul_of_pos_right hsq (by positivity)
    _ = _ := by ring

/-- A uniform asymptotic statement for every graph of a given bounded
multiplicity and every family of disjoint prescribed pairs. -/
theorem exists_partition_threshold (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ M : MultiGraph V,
      Fintype.card V = 2*m → ∀ {t : ℕ}, ∀ _ht : t ≤ m,
      ∀ p : (Fin t × Bool) ↪ V, (∀ u v, (M.mult s(u,v):ℝ) ≤ K) →
      ∃ L : Finset V, L.card = m ∧ Lᶜ.card = m ∧
        (∀ i, (p (i,true) ∈ L ↔ p (i,false) ∉ L)) ∧
        ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < ε*(m:ℝ) := by
  obtain ⟨m₀,hm₀⟩ := eventually_sixth_size (ε/K) (div_pos hε hK)
  refine ⟨m₀,fun m hm M hc t ht p hmu => ?_⟩
  obtain ⟨L,hL,hC,hsep,hdis⟩ := M.exists_balanced_degree_partition m hc ht p K hK hmu
    (ε/K*(m:ℝ)) (by positivity) (hm₀ m hm)
  refine ⟨L,hL,hC,hsep,fun v => ?_⟩
  have he : K*(ε/K*(m:ℝ)) = ε*(m:ℝ) := by
    rw [← mul_assoc, mul_comm K (ε/K), div_mul_cancel₀ _ hK.ne']
  simpa only [he] using hdis v

/-- Concrete degree room for the subsequent matching constructions. -/
theorem degree_rooms_of_discrepancy (M : MultiGraph V) (L : Finset V) (m D : ℕ)
    (hreg : M.IsRegularOfDegree D) (hdense : 12*m ≤ 7*D)
    (hdis : ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < (m:ℝ)/8) :
    ∀ v, 3*m < 4 * M.degreeInto L v ∧ 3*m < 4 * M.degreeInto Lᶜ v := by
  intro v
  have hs : (M.degreeInto L v:ℝ) + (M.degreeInto Lᶜ v:ℝ) = (D:ℝ) := by
    exact_mod_cast (M.degreeInto_add_compl L v).trans (hreg v)
  have hd : 12*(m:ℝ) ≤ 7*(D:ℝ) := by exact_mod_cast hdense
  obtain ⟨hl,hr⟩ := abs_lt.mp (hdis v)
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
  constructor
  · have h : 3*(m:ℝ) < 4*(M.degreeInto L v:ℝ) := by linarith
    exact_mod_cast h
  · have h : 3*(m:ℝ) < 4*(M.degreeInto Lᶜ v:ℝ) := by linarith
    exact_mod_cast h

def pairEmbedding (x y : V) (hxy : x ≠ y) : (Fin 1 × Bool) ↪ V where
  toFun z := if z.2 then x else y
  inj' := by
    intro u v h
    apply Prod.ext (Subsingleton.elim _ _)
    cases hu : u.2 <;> cases hv : v.2 <;> simp_all

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Direct interface for the constructed point extension. The new centre
and any chosen old vertex are separated, with the centre in L. No
saturation or density is needed just to construct this partition. -/
theorem exists_balanced_point_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m : ℕ) (hcard : Fintype.card V + 1 = 2*m)
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (b : ℝ) (hb : 0 ≤ b) (hsize : 30 * (m:ℝ)^4 < b^6) :
    ∃ L : Finset (Option V), L.card = m ∧ Lᶜ.card = m ∧
      none ∈ L ∧ some y ∉ L ∧
      ∀ v, |((pointExtension G).degreeInto L v:ℝ) -
        ((pointExtension G).degreeInto Lᶜ v:ℝ)| < 2*b := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have hm : 1 ≤ m := by omega
  let p := MultiGraph.pairEmbedding (none : Option V) (some y) (by simp)
  have hc : Fintype.card (Option V) = 2*m := by simpa only [Fintype.card_option] using hcard
  have hmu : ∀ u v, ((pointExtension G).mult s(u,v):ℝ) ≤ 2 := by
    intro u v
    exact_mod_cast multiplicity_le_two G hgap s(u,v)
  obtain ⟨L,hL,hC,_,hx,hy,hd⟩ :=
    (pointExtension G).exists_balanced_degree_partition_center m hc hm p 0 2
      (by norm_num) hmu b hb hsize
  exact ⟨L,hL,hC,hx,hy,hd⟩

/-- Fully instantiated partition for the current saturated dense family.
The output has more than 3m/4 weighted neighbours in each part at every
vertex. It supplies no edge colouring or internal-cover existence. -/
theorem exists_dense_balanced_point_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m : ℕ) (hm : 24576 ≤ m) (hcard : Fintype.card V + 1 = 2*m)
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hsat : 2*G.edgeFinset.card = G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1) ≤ 7*G.maxDegree) :
    ∃ L : Finset (Option V), L.card = m ∧ Lᶜ.card = m ∧
      none ∈ L ∧ some y ∉ L ∧
      (∀ v, |((pointExtension G).degreeInto L v:ℝ) -
        ((pointExtension G).degreeInto Lᶜ v:ℝ)| < (m:ℝ)/8) ∧
      ∀ v, 3*m < 4*(pointExtension G).degreeInto L v ∧
        3*m < 4*(pointExtension G).degreeInto Lᶜ v := by
  obtain ⟨L,hL,hC,hx,hy,hd⟩ := exists_balanced_point_partition G y m hcard hgap
    ((m:ℝ)/16) (by positivity) (MultiGraph.sixth_size_of_large m hm)
  have hdis : ∀ v, |((pointExtension G).degreeInto L v:ℝ) -
      ((pointExtension G).degreeInto Lᶜ v:ℝ)| < (m:ℝ)/8 := by
    intro v
    convert hd v using 1; ring
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have hreg := regular_of_saturated G hn hsat
  have hdensity : 12*m ≤ 7*G.maxDegree := by omega
  exact ⟨L,hL,hC,hx,hy,hdis,
    (pointExtension G).degree_rooms_of_discrepancy L m G.maxDegree hreg hdensity hdis⟩

end OverfullWork.MultigraphExtension
