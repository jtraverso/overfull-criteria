module

public import OverfullWork.CanonicalPartitionStructure

@[expose] public section


/-! # Construct the exceptional vertices from the actual deficit budget

The exceptional set is the identified centre together with vertices
whose ordered-base deficit exceeds s. Its cardinality is proved by
finite summation from the certificate, not assumed as input.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.total_base_deficit_le (p : Candidate c) :
    (∑v : Fin (p.pairIndex+1)×Bool,(G.maxDegree-p.orderedBase.degree v))≤2*G.maxDegree+B := by
  have hOrd:(∑w : Outside c.setᶜ,(G.maxDegree-c.image.degree (some w)))=
      deficitMass G G.maxDegree c.set:=by
    simp_rw [Certificate.image,degree_some]
    have hh:(∑w : Outside c.setᶜ,(G.maxDegree-G.degree w.val))=
        ∑v∈c.setᶜᶜ,(G.maxDegree-G.degree v):=
      (sum_subtype c.setᶜᶜ (fun v=>mem_compl) (fun v=>G.maxDegree-G.degree v)).symm
    simpa only [compl_compl,deficitMass] using hh
  have hImage:(∑w : Vertices c.setᶜ,(G.maxDegree-c.image.degree w))≤2*G.maxDegree+B:=by
    rw [Fintype.sum_option,hOrd]
    have hb:=c.budget
    have hh:G.maxDegree-c.image.degree none≤G.maxDegree:=Nat.sub_le _ _
    omega
  calc
    _ = ∑v : Fin (p.pairIndex+1)×Bool,(G.maxDegree-c.image.degree (p.coordinates v)) :=by
      simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
    _ = ∑w : Vertices c.setᶜ,(G.maxDegree-c.image.degree w) :=
      p.coordinates.sum_comp (fun w : Vertices c.setᶜ=>G.maxDegree-c.image.degree w)
    _ ≤ _ :=hImage

noncomputable def Candidate.largeDeficitSet (p : Candidate c) (s : ℕ) :
    Finset (Fin (p.pairIndex+1)×Bool) :=
  univ.filter fun v=>s<G.maxDegree-p.orderedBase.degree v

noncomputable def Candidate.deficitExceptions (p : Candidate c) (s : ℕ) :
    Finset (Fin (p.pairIndex+1)×Bool) :=insert p.centre (p.largeDeficitSet s)

theorem Candidate.largeDeficit_card (p : Candidate c) (s : ℕ) :
    (p.largeDeficitSet s).card≤(2*G.maxDegree+B)/(s+1) := by
  have h₁:(s+1)*(p.largeDeficitSet s).card≤
      ∑v∈p.largeDeficitSet s,(G.maxDegree-p.orderedBase.degree v):=by
    calc
      _ = ∑_v∈p.largeDeficitSet s,(s+1) :=by simp [Nat.mul_comm]
      _ ≤ _ :=by
        apply sum_le_sum
        intro v hv
        have hh:=(mem_filter.mp hv).2
        omega
  have h₂:(∑v∈p.largeDeficitSet s,(G.maxDegree-p.orderedBase.degree v))≤
      ∑v : Fin (p.pairIndex+1)×Bool,(G.maxDegree-p.orderedBase.degree v):=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)
  apply (Nat.le_div_iff_mul_le (show 0<s+1 by omega)).mpr
  have hh:=p.total_base_deficit_le
  nlinarith only [h₁,h₂,hh]

theorem Candidate.deficitExceptions_card (p : Candidate c) (s : ℕ) :
    (p.deficitExceptions s).card≤1+(2*G.maxDegree+B)/(s+1) := by
  have hh:=card_insert_le p.centre (p.largeDeficitSet s)
  have hc:=p.largeDeficit_card s
  change (insert p.centre (p.largeDeficitSet s)).card≤_
  omega

theorem Candidate.small_support_deficit (p : Candidate c) (s : ℕ)
    (v : Fin (p.pairIndex+1)×Bool) (hv : v∉p.deficitExceptions s) :
    G.maxDegree-p.orderedBase.supportGraph.degree v≤s+c.setᶜ.card := by
  have hvc:v≠p.centre:=by intro he;subst v;exact hv (mem_insert_self _ _)
  have hSmall:G.maxDegree-p.orderedBase.degree v≤s:=by
    by_contra hn
    exact hv (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,by omega⟩))
  have hh:=p.completion.support_deficit_le p.centre v p.ordered_star hvc c.setᶜ.card
    (p.centre_multiplicity v)
  change G.maxDegree-p.orderedBase.supportGraph.degree v≤
    (G.maxDegree-p.orderedBase.degree v)+c.setᶜ.card at hh
  omega

end OverfullWork.NormalizedCanonicalCandidate
