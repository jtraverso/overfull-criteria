module

public import OverfullWork.CriticalTwoColourReduction

@[expose] public section


/-! # Small missing mass for the constructed large-low-set layers

Every vertex outside the actual exception set receives degree two, so
all missing degree is supported on that small set. Both parity branches
construct the layer from G1, matching/projection choices and actual walks.
The two branches retain their own uniform scale; no equality of the
scales, future trimming rounds or no-overfull residue is asserted.
-/
namespace OverfullWork.SparseLowLayer
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Total degree missing from a two-degree layer, with natural truncation. -/
def layerMissing (L : SimpleGraph V) [DecidableRel L.Adj] : ℕ := ∑v,(2-L.degree v)

theorem layerMissing_eq_sum_on_exceptions (L : SimpleGraph V) [DecidableRel L.Adj]
    (U : Finset V) (hcore : ∀v∉U,L.degree v=2) :
    layerMissing L=∑v∈U,(2-L.degree v) := by
  have hz : (∑v∈Uᶜ,(2-L.degree v))=0 := by
    apply sum_eq_zero
    intro v hv
    rw [hcore v (mem_compl.mp hv),Nat.sub_self]
  have hs:=sum_add_sum_compl U (fun v=>2-L.degree v)
  simpa only [hz,Nat.add_zero,layerMissing] using hs.symm

theorem missing_le_twice_card_of_core_two (L : SimpleGraph V) [DecidableRel L.Adj]
    (U : Finset V) (hcore : ∀v∉U,L.degree v=2) : layerMissing L≤2*U.card := by
  rw [layerMissing_eq_sum_on_exceptions L U hcore]
  calc
    _ ≤ ∑_v∈U,2 := sum_le_sum (fun _ _=>Nat.sub_le _ _)
    _ = 2*U.card := by simp [Nat.mul_comm]

/-- A finite even certificate supplies an actual reduction and its mass bound. -/
theorem exists_sparse_of_even_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) (hD : 2≤G.maxDegree) (hUk : U.card≤k)
    (c : CriticalEvenLowLayer.Certificate G U) :
    ∃r : CriticalTwoColourReduction.Reduction G,layerMissing r.layer≤2*k := by
  let r : CriticalTwoColourReduction.Reduction G := {
    layer:=c.layer,le_original:=c.le_original,acyclic:=c.acyclic,
    degree_le_two:=c.degree_le_two,colourable:=c.colourable,
    demands:=CriticalTwoColourReduction.degree_demands_of_exact_residue G c.layer hD
      c.le_original c.residual_maxDegree,
    low_positive:=by intro w hw;rw [c.low_one_cover w hw],
    residual_maxDegree:=c.residual_maxDegree,residual_uncolourable:=c.residual_uncolourable }
  refine ⟨r,?_⟩
  exact (missing_le_twice_card_of_core_two c.layer U c.core_two_cover).trans
    (Nat.mul_le_mul_left 2 hUk)

/-- The odd extra edge and separated paths give the same missing-mass bound. -/
theorem exists_sparse_of_odd_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) (hD : 2≤G.maxDegree) (hUk : U.card≤k)
    (c : CriticalOddLowLayer.Certificate G U) :
    ∃r : CriticalTwoColourReduction.Reduction G,layerMissing r.layer≤2*k := by
  let r : CriticalTwoColourReduction.Reduction G := {
    layer:=c.layer,le_original:=c.le_original,acyclic:=c.acyclic,
    degree_le_two:=c.degree_le_two,colourable:=c.colourable,
    demands:=CriticalTwoColourReduction.degree_demands_of_exact_residue G c.layer hD
      c.le_original c.residual_maxDegree,
    low_positive:=c.low_positive,
    residual_maxDegree:=c.residual_maxDegree,residual_uncolourable:=c.residual_uncolourable }
  refine ⟨r,?_⟩
  exact (missing_le_twice_card_of_core_two c.layer U c.core_two_cover).trans
    (Nat.mul_le_mul_left 2 hUk)

/-- Uniform construction in the positive even-low-set case. Both the
exception count and the actual layer come from the same preparation scale. -/
theorem above_half_even_low_sparse (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        Even (lowVertices G).card → 2≤(lowVertices G).card →
        ∃r : CriticalTwoColourReduction.Reduction G,
          layerMissing r.layer≤2*(Fintype.card V/(4096*q^2)) := by
  obtain ⟨q,hq,N,hprep⟩:=CriticalCorePathPreparation.above_half_even_core_path_preparation.{u} ε hε
  refine ⟨q,hq,max N (16*q),?_⟩
  intro V _ _ G _ hn hc hdense heven htwo
  obtain ⟨hUk,⟨s⟩⟩:=hprep G ((le_max_left _ _).trans hn) hc hdense heven htwo
  have hn16 : 16*q≤Fintype.card V := (le_max_right _ _).trans hn
  have ha : 2≤Fintype.card V/(8*q) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    omega
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hD : 2≤G.maxDegree := by omega
  obtain ⟨c⟩:=CriticalEvenLowLayer.certificate_of_prepared G _ _ hc hD (by
    intro v hv
    have hh:=(mem_filter.mp hv).2
    omega) s
  exact exists_sparse_of_even_certificate G _ _ hD hUk c

/-- Uniform construction in the positive odd-low-set case. -/
theorem above_half_odd_low_sparse (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        Odd (lowVertices G).card → 3≤(lowVertices G).card →
        ∃r : CriticalTwoColourReduction.Reduction G,
          layerMissing r.layer≤2*(Fintype.card V/(4096*q^2)) := by
  obtain ⟨q,hq,N,hprep⟩:=CriticalOddCorePathPreparation.above_half_odd_core_path_preparation.{u} ε hε
  refine ⟨q,hq,max N (16*q),?_⟩
  intro V _ _ G _ hn hc hdense hodd hthree
  obtain ⟨hUk,⟨s⟩⟩:=hprep G ((le_max_left _ _).trans hn) hc hdense hodd hthree
  have hn16 : 16*q≤Fintype.card V := (le_max_right _ _).trans hn
  have ha : 2≤Fintype.card V/(8*q) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    omega
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hD : 2≤G.maxDegree := by omega
  obtain ⟨c⟩:=CriticalOddLowLayer.certificate_of_prepared G _ _ hc hD (by
    intro v hv
    have hh:=(mem_filter.mp hv).2
    omega) s
  exact exists_sparse_of_odd_certificate G _ _ hD hUk c

/-- One order threshold covers both large-low-set parities; the selected
scale is one of two constants fixed before the graph. -/
theorem above_half_many_low_sparse (ε : ℝ) (hε : 0<ε) :
    ∃qE qO : ℕ,2≤qE ∧ 2≤qO ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        2≤(lowVertices G).card →
        ∃q : ℕ,(q=qE ∨ q=qO) ∧ ∃r : CriticalTwoColourReduction.Reduction G,
          layerMissing r.layer≤2*(Fintype.card V/(4096*q^2)) := by
  obtain ⟨qE,hqE,NE,hE⟩:=above_half_even_low_sparse.{u} ε hε
  obtain ⟨qO,hqO,NO,hO⟩:=above_half_odd_low_sparse.{u} ε hε
  refine ⟨qE,qO,hqE,hqO,max NE NO,?_⟩
  intro V _ _ G _ hn hc hdense htwo
  by_cases he:Even (lowVertices G).card
  · obtain ⟨r,hr⟩:=hE G ((le_max_left _ _).trans hn) hc hdense he htwo
    exact ⟨qE,Or.inl rfl,r,hr⟩
  · have ho:Odd (lowVertices G).card:=Nat.not_even_iff_odd.mp he
    have hthree:3≤(lowVertices G).card:=by obtain ⟨k,hk⟩:=ho;omega
    obtain ⟨r,hr⟩:=hO G ((le_max_right _ _).trans hn) hc hdense ho hthree
    exact ⟨qO,Or.inr rfl,r,hr⟩

end OverfullWork.SparseLowLayer
